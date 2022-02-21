#![feature(rustc_private)]
extern crate im;
extern crate pretty;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

extern crate rustc_resolve;
extern crate rustc_expand;
extern crate rustc_lint;

mod ast_to_rustspec;
mod hir_to_rustspec;
mod name_resolution;
mod rustspec;
mod rustspec_to_coq;
mod rustspec_to_easycrypt;
mod rustspec_to_fstar;
mod typechecker;
mod util;

use heck::TitleCase;
use im::{HashMap, HashSet};
use itertools::Itertools;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_errors::emitter::{ColorConfig, HumanReadableErrorType};
use rustc_errors::DiagnosticId;
use rustc_interface::{
    interface::{Compiler, Config},
    Queries,
};
use rustc_session::Session;
use rustc_session::{config::ErrorOutputType, search_paths::SearchPath};
use rustc_span::MultiSpan;
use serde::Deserialize;
use serde_json;
use std::env;
use std::fs::File;
use std::path::Path;
use std::process::Command;
use util::APP_USAGE;

struct HacspecCallbacks {
    output_filename: Option<String>,
    output_directory: Option<String>,
    output_type: Option<String>,
    target_directory: String,
}

const ERROR_OUTPUT_CONFIG: ErrorOutputType =
    ErrorOutputType::HumanReadable(HumanReadableErrorType::Default(ColorConfig::Auto));

trait HacspecErrorEmitter {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str);

    fn span_rustspec_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str);
}

impl HacspecErrorEmitter for Session {
    fn span_rustspec_err<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_err_with_code(s, msg, DiagnosticId::Error(String::from("Hacspec")));
    }

    fn span_rustspec_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_warn_with_code(s, msg, DiagnosticId::Error(String::from("Hacspec")));
    }
}

fn construct_module_string<T>(
    krate_path: String,
    krate_dir: String,
    ast_crates_map: &HashMap<String, T>,
) -> Option<String> {
    if ast_crates_map.contains_key(&krate_path.clone()) {
        Some(krate_path.clone())
    } else if ast_crates_map.contains_key(&(krate_path.clone() + "/mod")) {
        Some(krate_path.clone() + "/mod")
    } else if ast_crates_map.contains_key(&(krate_dir.clone() + "/" + krate_path.clone().as_str()))
    {
        Some(krate_dir.clone() + "/" + krate_path.clone().as_str())
    } else if ast_crates_map
        .contains_key(&(krate_dir.clone() + "/" + krate_path.clone().as_str() + "/mod"))
    {
        Some(krate_dir.clone() + "/" + krate_path.clone().as_str() + "/mod")
    } else {
        None
    }
}

fn construct_handle_crate_queue<'tcx>(
    compiler: &Compiler,
    handled: &mut HashSet<String>,
    krate_path: String,
    krate_dir: String,
    krate_items : Vec<rustc_ast::ptr::P<rustc_ast::ast::Item>>
) -> Result<Vec<((String, String), Vec<rustc_ast::ptr::P<rustc_ast::ast::Item>>)>, bool> {
    // Depth first handling, skip module if already visited
    if handled.contains(&krate_path) {
        return Err(true);
    }

    let mut krates = Vec::new();

    // Parse over the crate, loading modules and filling top_level_ctx
    for x in krate_items.clone().into_iter() {
        match &x.kind {
            // Whenever a module statement is encountered, add it to the queue
            rustc_ast::ast::ItemKind::Mod(
                rustc_ast::ast::Unsafe::No,
                rustc_ast::ast::ModKind::Loaded(items, _inline, _span), // _, // rustc_ast::ast::ModKind::Unloaded,
            ) => {
                match construct_handle_crate_queue(
                    compiler,
                    handled,
                    x.ident.name.to_ident_string(),
                    krate_path.clone(),
                    items.clone(),
                ) {
                    Ok(v) => krates.extend(v),
                    Err(false) => {
                        // If not able to handle module, stop compilation.
                        return Err(false);
                    }
                    Err(true) => (),
                }
            }
            _ => (),
        }
    }

    // Remove the modules statements from the crate
    let krate_items = krate_items
            .clone()
            .into_iter()
            .filter(|x| match x.kind {
                rustc_ast::ast::ItemKind::Mod(
                    rustc_ast::ast::Unsafe::No,
                    _, // rustc_ast::ast::ModKind::Unloaded
                ) => false,
                _ => true,
            })
        .collect();
    
    krates.push((
        (
            krate_path.clone(),
            krate_dir.clone(),
        ),
        krate_items,
    ));

    handled.insert(krate_path.clone());

    Ok(krates)
}

fn handle_crate<'tcx>(
    callback: &HacspecCallbacks,
    compiler: &Compiler,
    queries: &'tcx Queries<'tcx>,
    krate_path: String,
    krate_items : Vec<rustc_ast::ptr::P<rustc_ast::ast::Item>>
) -> Compilation {
    // Construct a queue of files to handle
    let krate_queue = match construct_handle_crate_queue(
        compiler,
        &mut HashSet::new(),
        krate_path,
        "".to_string(),
        krate_items,
    ) {
        Ok(v) => v,
        Err(false) => {
            // If not able to handle crate, stop compilation.
            return Compilation::Stop;
        }
        Err(true) => return Compilation::Continue, // Nothing at all, should probably never happen
    };

    let top_ctx_map: &mut HashMap<String, name_resolution::TopLevelContext> = &mut HashMap::new();
    let special_names_map: &mut HashMap<String, ast_to_rustspec::SpecialNames> =
        &mut HashMap::new();

    let krate_use_paths: &mut HashMap<String, Vec<String>> = &mut HashMap::new();

    // Get all 'use' dependencies per module
    let mut krate_queue_no_module_statements = Vec::new();
    for ((krate_path, krate_dir), krate_items) in krate_queue {
        krate_use_paths.insert(krate_path.clone(), Vec::new());

        // Parse over the crate, loading modules and filling top_level_ctx
        for x in krate_items.clone().into_iter() {
            match x.kind {
                // Load the top_ctx from the module specified in the use statement
                rustc_ast::ast::ItemKind::Use(ref tree) => {
                    match tree.kind {
                        rustc_ast::ast::UseTreeKind::Glob => {
                            krate_use_paths[&krate_path].push(
                                (&tree.prefix)
                                    .segments
                                    .last()
                                    .unwrap()
                                    .ident
                                    .name
                                    .to_ident_string(),
                            );
                        }
                        _ => (),
                    };
                }
                _ => (),
            }
        }

        // Remove the modules statements from the crate
        krate_queue_no_module_statements.push((
            (krate_path, krate_dir),
            krate_items
                .clone()
                .into_iter()
                .filter(|x| match x.kind {
                    rustc_ast::ast::ItemKind::Mod(
                        _,
                        _,
                        // rustc_ast::ast::Unsafe::No,
                        // rustc_ast::ast::ModKind::Unloaded,
                    ) => false,
                    rustc_ast::ast::ItemKind::Use(ref tree) => match tree.kind {
                        rustc_ast::ast::UseTreeKind::Glob => {
                            (&tree.prefix).segments.len() <= 1
                        }
                        _ => false,
                    },
                    rustc_ast::ast::ItemKind::ExternCrate(_) => false,
                    _ => true,
                })
                .collect(),
        ))
    }

    /////////////////////////////////
    // Start of actual translation //
    /////////////////////////////////

    let external_data = |imported_crates: &Vec<rustspec::Spanned<String>>| {
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            hir_to_rustspec::retrieve_external_data(&compiler.session(), &tcx, imported_crates)
        })
    };

    ///////////////////////////////////////////////////////////////////////////
    // Translate all modules from ast to rustspec (modules becomes programs) //
    ///////////////////////////////////////////////////////////////////////////

    let mut krate_queue_programs = Vec::new();
    for ((krate_path, krate_dir), krate_items) in krate_queue_no_module_statements {
        // Generate an empty context then fill it whenever an Use statement is encountered
        let new_specials = &mut ast_to_rustspec::SpecialNames {
            arrays: HashSet::new(),
            enums: HashSet::new(),
            aliases: HashMap::new(),
        };

        for krate_use_path_string in &krate_use_paths[&krate_path] {
            if let Some(krate_use_string) = construct_module_string(
                krate_use_path_string.clone(),
                krate_dir.clone(),
                special_names_map,
            ) {
                new_specials
                    .arrays
                    .extend(special_names_map[&krate_use_string].arrays.clone());
                new_specials
                    .enums
                    .extend(special_names_map[&krate_use_string].enums.clone());
                new_specials
                    .aliases
                    .extend(special_names_map[&krate_use_string].aliases.clone());
            }
        }

        let krate = match ast_to_rustspec::translate(
            &compiler.session(),
            &rustc_ast::ast::Crate { attrs: vec![], items: krate_items, span: rustc_span::DUMMY_SP },
            &external_data,
            new_specials,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("unable to translate to Hacspec due to out-of-language errors");
                return Compilation::Stop;
            }
        };

        (*special_names_map).insert(krate_path.clone(), new_specials.clone());

        krate_queue_programs.push(((krate_path, krate_dir), krate));
    }

    ///////////////////////////////
    // Typecheck all the modules //
    ///////////////////////////////

    let mut root_module: bool = true;
    let mut krate_queue_typechecked = Vec::new();
    for ((krate_path, krate_dir), krate) in krate_queue_programs {
        let new_top_ctx = &mut name_resolution::TopLevelContext {
            consts: HashMap::new(),
            functions: HashMap::new(),
            typ_dict: HashMap::new(),
        };

        for krate_use_path_string in &krate_use_paths[&krate_path] {
            if let Some(krate_use_string) = construct_module_string(
                krate_use_path_string.clone(),
                krate_dir.clone(),
                top_ctx_map,
            ) {
                new_top_ctx
                    .consts
                    .extend(top_ctx_map[&krate_use_string].consts.clone());
                new_top_ctx
                    .functions
                    .extend(top_ctx_map[&krate_use_string].functions.clone());
                new_top_ctx
                    .typ_dict
                    .extend(top_ctx_map[&krate_use_string].typ_dict.clone());
            }
        }

        let krate = match name_resolution::resolve_crate(
            &compiler.session(),
            krate,
            &external_data,
            new_top_ctx,
        ) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("found some Hacspec name resolution errors");
                return Compilation::Stop;
            }
        };

        let krate = match typechecker::typecheck_program(&compiler.session(), &krate, new_top_ctx) {
            Ok(krate) => krate,
            Err(_) => {
                compiler
                    .session()
                    .err("found some Hacspec typechecking errors");
                return Compilation::Stop;
            }
        };

        (*top_ctx_map).insert(krate_path.clone(), new_top_ctx.clone());
        krate_queue_typechecked.push(((krate_path, krate_dir), krate));
    }

    let imported_crates = (&krate_queue_typechecked).into_iter().fold(
        Vec::new(),
        |mut all_imported_crates, (_, krate)| {
            all_imported_crates.extend(name_resolution::get_imported_crates(&krate));
            all_imported_crates
        },
    );
    let imported_crates = imported_crates
        .into_iter()
        .filter(|(x, _)| x != "hacspec_lib" && x != "crate")
        .map(|(x, _)| x)
        .collect::<Vec<_>>();

    println!(
        " > Successfully typechecked{}{}",
        match &callback.output_filename {
            Some(file_name) => " ".to_string() + file_name,
            None => "".to_string(),
        },
        if imported_crates.len() == 0 {
            ".".to_string()
        } else {
            format!(
                ", assuming that the code in {} has also been Hacspec-typechecked",
                imported_crates.iter().format(", ")
            )
        }
    );

    ///////////////////////////////////
    // Generate all the output files //
    ///////////////////////////////////

    if let (Some(extension), Some(file_str)) = (&callback.output_type, &callback.output_directory) {
        let original_file = Path::new(file_str);

        for ((krate_path,_), krate) in krate_queue_typechecked {
            let file_name = if root_module {
                if let Some(file_name) = &callback.output_filename {
                    Path::new(&file_name.clone())
                        .with_extension("")
                        .to_str()
                        .unwrap()
                        .to_string()
                } else {
                    krate_path.clone() // TODO: Should this throw an error instead
                }
            } else {
                krate_path.clone()
            };
            root_module = false;

            let file = match extension.clone().as_str() {
                "fst" | "ec" | "json" => {
                    // Compute file name as output directory with crate local path (file_name)
                    (original_file).join(Path::new(
                        (file_name.clone().to_title_case().replace(" ", ".") + "." + extension)
                            .as_str(),
                    ))
                }
                "v" => {
                    // Compute file name as output directory with crate local path (file_name)
                    (original_file).join(Path::new(
                        (file_name.clone().to_title_case().replace(" ", "_") + "." + extension)
                            .as_str(),
                    ))
                }
                _ => {
                    compiler
                        .session()
                        .err("unknown backend extension for output files");
                    return Compilation::Stop;
                }
            };
            let file = file.to_str().unwrap();

            match extension.as_str() {
                "fst" => rustspec_to_fstar::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                "ec" => rustspec_to_easycrypt::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                "json" => {
                    let file = file.trim();
                    let path = Path::new(file);
                    let file = match File::create(&path) {
                        Err(why) => {
                            compiler.session().err(
                                format!("Unable to write to output file {}: \"{}\"", file, why)
                                    .as_str(),
                            );
                            return Compilation::Stop;
                        }
                        Ok(file) => file,
                    };
                    match serde_json::to_writer_pretty(file, &krate) {
                        Err(why) => {
                            compiler
                                .session()
                                .err(format!("Unable to serialize program: \"{}\"", why).as_str());
                            return Compilation::Stop;
                        }
                        Ok(_) => (),
                    };
                }
                "v" => rustspec_to_coq::translate_and_write_to_file(
                    &compiler.session(),
                    &krate,
                    &file,
                    &top_ctx_map[&krate_path],
                ),
                _ => {
                    compiler
                        .session()
                        .err("unknown backend extension for output file");
                    return Compilation::Stop;
                }
            }
        }
    }

    Compilation::Continue
}


// // TODO: https://doc.rust-lang.org/beta/nightly-rustc/src/rustc_expand/expand.rs.html#365-383
// // Recursively expand all macro invocations in this AST fragment.
// pub fn fully_expand_fragment(&mut self, input_fragment: AstFragment) -> AstFragment {
//     let orig_expansion_data = self.cx.current_expansion.clone();
//     let orig_force_mode = self.cx.force_mode;

//     // Collect all macro invocations and replace them with placeholders.
//     let (mut fragment_with_placeholders, mut invocations) =
//         self.collect_invocations(input_fragment, &[]);

//     // Optimization: if we resolve all imports now,
//     // we'll be able to immediately resolve most of imported macros.
//     self.resolve_imports();

//     // Resolve paths in all invocations and produce output expanded fragments for them, but
//     // do not insert them into our input AST fragment yet, only store in `expanded_fragments`.
//     // The output fragments also go through expansion recursively until no invocations are left.
//     // Unresolved macros produce dummy outputs as a recovery measure.
//     invocations.reverse();
//     let mut expanded_fragments = Vec::new();
//     let mut undetermined_invocations = Vec::new();
//     let (mut progress, mut force) = (false, !self.monotonic);
//     loop {
//         let Some((invoc, ext)) = invocations.pop() else {
//             self.resolve_imports();
//             if undetermined_invocations.is_empty() {
//                 break;
//             }
//             invocations = mem::take(&mut undetermined_invocations);
//             force = !mem::replace(&mut progress, false);
//             if force && self.monotonic {
//                 self.cx.sess.delay_span_bug(
//                     invocations.last().unwrap().0.span(),
//                     "expansion entered force mode without producing any errors",
//                 );
//             }
//             continue;
//         };

//         let ext = match ext {
//             Some(ext) => ext,
//             None => {
//                 let eager_expansion_root = if self.monotonic {
//                     invoc.expansion_data.id
//                 } else {
//                     orig_expansion_data.id
//                 };
//                 match self.cx.resolver.resolve_macro_invocation(
//                     &invoc,
//                     eager_expansion_root,
//                     force,
//                 ) {
//                     Ok(ext) => ext,
//                     Err(Indeterminate) => {
//                         // Cannot resolve, will retry this invocation later.
//                         undetermined_invocations.push((invoc, None));
//                         continue;
//                     }
//                 }
//             }
//         };

//         let ExpansionData { depth, id: expn_id, .. } = invoc.expansion_data;
//         let depth = depth - orig_expansion_data.depth;
//         self.cx.current_expansion = invoc.expansion_data.clone();
//         self.cx.force_mode = force;

//         let fragment_kind = invoc.fragment_kind;
//         let (expanded_fragment, new_invocations) = match self.expand_invoc(invoc, &ext.kind) {
//             ExpandResult::Ready(fragment) => {
//                 let mut derive_invocations = Vec::new();
//                 let derive_placeholders = self
//                     .cx
//                     .resolver
//                     .take_derive_resolutions(expn_id)
//                     .map(|derives| {
//                         derive_invocations.reserve(derives.len());
//                         derives
//                             .into_iter()
//                             .map(|(path, item, _exts)| {
//                                 // FIXME: Consider using the derive resolutions (`_exts`)
//                                 // instead of enqueuing the derives to be resolved again later.
//                                 let expn_id = LocalExpnId::fresh_empty();
//                                 derive_invocations.push((
//                                     Invocation {
//                                         kind: InvocationKind::Derive { path, item },
//                                         fragment_kind,
//                                         expansion_data: ExpansionData {
//                                             id: expn_id,
//                                             ..self.cx.current_expansion.clone()
//                                         },
//                                     },
//                                     None,
//                                 ));
//                                 NodeId::placeholder_from_expn_id(expn_id)
//                             })
//                             .collect::<Vec<_>>()
//                     })
//                     .unwrap_or_default();

//                 let (fragment, collected_invocations) =
//                     self.collect_invocations(fragment, &derive_placeholders);
//                 // We choose to expand any derive invocations associated with this macro invocation
//                 // *before* any macro invocations collected from the output fragment
//                 derive_invocations.extend(collected_invocations);
//                 (fragment, derive_invocations)
//             }
//             ExpandResult::Retry(invoc) => {
//                 if force {
//                     self.cx.span_bug(
//                         invoc.span(),
//                         "expansion entered force mode but is still stuck",
//                     );
//                 } else {
//                     // Cannot expand, will retry this invocation later.
//                     undetermined_invocations.push((invoc, Some(ext)));
//                     continue;
//                 }
//             }
//         };

//         progress = true;
//         if expanded_fragments.len() < depth {
//             expanded_fragments.push(Vec::new());
//         }
//         expanded_fragments[depth - 1].push((expn_id, expanded_fragment));
//         invocations.extend(new_invocations.into_iter().rev());
//     }

//     self.cx.current_expansion = orig_expansion_data;
//     self.cx.force_mode = orig_force_mode;

//     // Finally incorporate all the expanded macros into the input AST fragment.
//     let mut placeholder_expander = PlaceholderExpander::default();
//     while let Some(expanded_fragments) = expanded_fragments.pop() {
//         for (expn_id, expanded_fragment) in expanded_fragments.into_iter().rev() {
//             placeholder_expander
//                 .add(NodeId::placeholder_from_expn_id(expn_id), expanded_fragment);
//         }
//     }
//     fragment_with_placeholders.mut_visit_with(&mut placeholder_expander);
//     fragment_with_placeholders
// }

impl Callbacks for HacspecCallbacks {
    fn config(&mut self, config: &mut Config) {
        log::debug!(" --- hacspec config callback");
        log::trace!("     target directory {}", self.target_directory);
        config.opts.search_paths.push(SearchPath::from_cli_opt(
            &self.target_directory,
            ERROR_OUTPUT_CONFIG,
        ));
        config.crate_cfg.insert((
            String::from("feature"),
            Some(String::from("\"hacspec_attributes\"")),
        ));
    }

    fn after_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // queries.parse().unwrap();
        let mut krate;
        let resolver : rustc_middle::ty::ResolverOutputs;
        
        {
            let (_, _lint_store) = &*queries.register_plugins().unwrap().peek();
        }

        {
            let krate_and_resolver = queries.expansion().unwrap().peek_mut().clone(); // ?
            krate = (*krate_and_resolver.0).clone();

            // let krate: &rustc_ast::ast::Crate = &*(k.0.clone());
            // let mut krate: rustc_ast::ast::Crate = krate.clone();

            // for item in krate.items.clone() {
            //     println!("ITEM: {:#?}", item.kind);
            // }
            
            resolver = rustc_interface::interface::BoxedResolver::to_resolver_outputs(krate_and_resolver.1.clone());
            let lint_store = &*(krate_and_resolver.2.clone());

            // println!("{:?}", lint_store.get_lint_groups());
            // println!("{:?}", compiler.codegen_backend().metadata_loader())
            // # https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_interface/passes.rs.html#277-283
            
            // for local_id in resolver.definitions.iter_local_def_id() {
            //     println!("LID {:?}", local_id);
            // }
        }

        let mut krate: rustc_ast::ast::Crate = queries.parse().unwrap().take();

        let crate_name = queries.crate_name().unwrap().peek().clone();
        let sess = compiler.session();

        let arena = rustc_resolve::ResolverArenas::default();
        let resolver: &mut rustc_resolve::Resolver = &mut rustc_resolve::Resolver::new(
            sess,
            &krate.clone(),
            crate_name.as_str(),
            compiler.codegen_backend().metadata_loader(),
            &arena,
        );

        krate = {
            // let (_krate, lint_store) = queries.register_plugins().unwrap().take();
            // // resolver.access(|resolver| {

            // Create the config for macro expansion
            let features = sess.features_untracked();
            let recursion_limit = rustc_session::Limit::new(128); // get_recursion_limit(&krate.attrs, sess);
            let cfg = rustc_expand::expand::ExpansionConfig {
                features: Some(features),
                recursion_limit,
                trace_mac: sess.opts.debugging_opts.trace_macros,
                should_test: sess.opts.test,
                span_debug: sess.opts.debugging_opts.span_debug,
                proc_macro_backtrace: sess.opts.debugging_opts.proc_macro_backtrace,
                ..rustc_expand::expand::ExpansionConfig::default(crate_name.to_string())
            };
                
            // // let lint_store = rustc_interface::passes::LintStoreExpandImpl(lint_store);
            let mut ecx = rustc_expand::base::ExtCtxt::new(sess, cfg, resolver, None); // Some(&lint_store)

            // Expand macros now!
            // let krate = ecx.monotonic_expander().expand_crate(krate);

            let krate = {
                let file_path = match ecx.source_map().span_to_filename(krate.span) {
                    FileName::Real(name) => name
                        .into_local_path()
                        .expect("attempting to resolve a file path in an external file"),
                    other => PathBuf::from(other.prefer_local().to_string()),
                };
                let dir_path = file_path.parent().unwrap_or(&file_path).to_owned();
                ecx.root_path = dir_path.clone();
                ecx.current_expansion.module = std::rc::Rc::new(ModuleData {
                    mod_path: vec![Ident::from_str(&ecx.ecfg.crate_name)],
                    file_path_stack: vec![file_path],
                    dir_path,
                });
                let krate = self.fully_expand_fragment(AstFragment::Crate(krate)).make_crate();
                assert_eq!(krate.id, rustc_ast::ast::CRATE_NODE_ID);
                ecx.trace_macros_diag();
                krate
            }            
            // krate

            // The rest is error reporting

            sess.time("check_unused_macros", || {
                ecx.check_unused_macros();
            });

            let mut missing_fragment_specifiers: Vec<_> = ecx
                .sess
                .parse_sess
                .missing_fragment_specifiers
                .borrow()
                .iter()
                .map(|(span, node_id)| (*span, *node_id))
                .collect();
            missing_fragment_specifiers.sort_unstable_by_key(|(span, _)| *span);

            let recursion_limit_hit = ecx.reduced_recursion_limit.is_some();

            for (span, node_id) in missing_fragment_specifiers {
                let lint = rustc_lint::builtin::MISSING_FRAGMENT_SPECIFIER;
                let msg = "missing fragment specifier";
                resolver.lint_buffer().buffer_lint(lint, node_id, span, msg);
            }

            // Ok::<_,()>(krate)
            
            if recursion_limit_hit {
                // If we hit a recursion limit, exit early to avoid later passes getting overwhelmed
                // with a large AST
                Err(())
            } else {
                Ok(krate)
                }
        }.unwrap();

        
        queries.prepare_outputs().unwrap(); // ?
        queries.global_ctxt().unwrap(); // ?

        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                // ?
                let result = tcx.analysis(());
                result
            })
            .unwrap(); // ?

        krate.items = krate.items.into_iter().map(|x| {
            println!("{:?}", x);
            x
        }).collect();

        krate.items = krate.items
            .clone()
            .into_iter()
            .filter(|x| match x.kind {
                // rustc_ast::ast::ItemKind::Mod(
                //     _,
                //     _,
                //     // rustc_ast::ast::Unsafe::No,
                //     // rustc_ast::ast::ModKind::Unloaded,
                // ) => false,
                rustc_ast::ast::ItemKind::Use(ref tree) => match tree.kind {
                    rustc_ast::ast::UseTreeKind::Glob => {
                        (&tree.prefix).segments.len() <= 1
                    }
                    _ => false,
                },
                rustc_ast::ast::ItemKind::ExternCrate(_) => false,
                _ => true,
            })
            .collect();
                
        // let krate_parse = queries.parse().unwrap().take();
        // for i in 0..(krate_parse.items.len()-1) {
        //     println!("{:?}\nvs\n{:?}\n", krate.items[i].kind, krate_parse.items[i].kind);
        // }
        
        // fn after_analysis<'tcx>(
        //     &mut self,
        //     compiler: &Compiler,
        //     queries: &'tcx Queries<'tcx>,
        // ) -> Compilation {
        //     log::debug!(" --- hacspec after_analysis callback");
        //     let krate: rustc_ast::ast::Crate = queries.parse().unwrap().take();
        let crate_origin_file = compiler
            .build_output_filenames(compiler.session(), &[])
            .with_extension("")
            .to_str()
            .unwrap()
            .to_string();

        // Do depth first handling of modules starting search at crate root
        handle_crate(
            &self,
            compiler,
            queries,
            crate_origin_file,
            krate.items
        );

        Compilation::Stop
    }
}

// === Cargo Metadata Helpers ===

#[derive(Debug, Default, Deserialize)]
struct Dependency {
    name: String,
    #[allow(dead_code)]
    kind: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
struct Target {
    #[allow(dead_code)]
    name: String,
    #[allow(dead_code)]
    kind: Vec<String>,
    crate_types: Vec<String>,
    src_path: String,
}

#[derive(Debug, Default, Deserialize)]
struct Package {
    name: String,
    targets: Vec<Target>,
    dependencies: Vec<Dependency>,
}

#[derive(Debug, Default, Deserialize)]
struct Manifest {
    packages: Vec<Package>,
    target_directory: String,
}

// ===

/// Read the crate metadata and use the information for the build.
fn read_crate(
    manifest: Option<String>,
    package_name: Option<String>,
    args: &mut Vec<String>,
    callbacks: &mut HacspecCallbacks,
) {
    let manifest: Manifest = {
        let mut output = Command::new("cargo");
        let mut output_args = if let Some(manifest_path) = manifest {
            vec!["--manifest-path".to_string(), manifest_path]
        } else {
            Vec::<String>::new()
        };
        output_args.extend_from_slice(&[
            "--no-deps".to_string(),
            "--format-version".to_string(),
            "1".to_string(),
        ]);
        let output = output.arg("metadata").args(&output_args);
        let output = output.output().expect(" ⚠️  Error reading cargo manifest.");
        let stdout = output.stdout;
        if !output.status.success() {
            let error =
                String::from_utf8(output.stderr).expect(" ⚠️  Failed reading cargo stderr output");
            panic!("Error running cargo metadata: {:?}", error);
        }
        let json_string = String::from_utf8(stdout).expect(" ⚠️  Failed reading cargo output");
        serde_json::from_str(&json_string).expect(" ⚠️  Error reading to manifest")
    };

    // Pick the package of the given name or the only package available.
    let package = if let Some(package_name) = package_name {
        manifest
            .packages
            .iter()
            .find(|p| p.name == package_name)
            .expect(&format!(
                " ⚠️  Can't find the package {} in the Cargo.toml\n\n{}",
                package_name, APP_USAGE,
            ))
    } else {
        &manifest.packages[0]
    };
    log::trace!("Typechecking '{:?}' ...", package);

    // Take the first lib target we find. There should be only one really.
    // log::trace!("crate types: {:?}", package.targets);
    // log::trace!("package targets {:?}", package.targets);
    let target = package
        .targets
        .iter()
        .find(|p| {
            p.crate_types.contains(&"lib".to_string())
                || p.crate_types.contains(&"rlib".to_string())
        })
        .expect(&format!(" ⚠️  No target in the Cargo.toml\n\n{}", APP_USAGE));

    // Add the target source file to the arguments
    args.push(target.src_path.clone());

    // Add build artifact path.
    // This only works with debug builds.
    let deps = manifest.target_directory + "/debug/deps";
    callbacks.target_directory = deps;

    // Add the dependencies as --extern for the hacpsec typechecker.
    for dependency in package.dependencies.iter() {
        args.push(format!("--extern={}", dependency.name.replace("-", "_")));
    }

    if callbacks.output_filename == None {
        callbacks.output_filename = Some(package.name.clone())
    }
}

fn main() -> Result<(), usize> {
    pretty_env_logger::init();
    log::debug!(" --- hacspec");
    let mut args = env::args().collect::<Vec<String>>();
    log::trace!("     args: {:?}", args);

    // Args to pass to the compiler
    let mut compiler_args = Vec::new();

    // Drop and pass along binary name.
    compiler_args.push(args.remove(0));

    // Optionally get output directory.
    let output_filename_index = args.iter().position(|a| a == "-o");
    let output_filename = match output_filename_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally get output directory.
    let output_directory_index = args.iter().position(|a| a == "-dir");
    let output_directory = match output_directory_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally get output file extension.
    let output_type_index = args.iter().position(|a| a == "-e");
    let output_type = match output_type_index {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Optionally an input file can be passed in. This should be mostly used for
    // testing.
    let input_file = match args.iter().position(|a| a == "-f") {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Read the --manifest-path argument if present.
    let manifest = match args.iter().position(|a| a == "--manifest-path") {
        Some(i) => {
            args.remove(i);
            Some(args.remove(i))
        }
        None => None,
    };

    // Read the --sysroot. It must be present
    log::trace!("args: {:?}", args);
    match args.iter().position(|a| a.starts_with("--sysroot")) {
        Some(i) => {
            compiler_args.push(args.remove(i));
        }
        None => panic!(" ⚠️  --sysroot is missing. Please report this issue."),
    }

    let mut callbacks = HacspecCallbacks {
        output_filename,
        output_directory: if match output_type {
            Some(_) => None == output_directory,
            _ => false,
        } {
            Some(env::current_dir().unwrap().to_str().unwrap().to_owned())
        } else {
            output_directory
        },
        output_type,
        // This defaults to the default target directory.
        target_directory: env::current_dir().unwrap().to_str().unwrap().to_owned()
            + "/../target/debug/deps",
    };

    match input_file {
        Some(input_file) => {
            compiler_args.push(input_file);
            // If only a file is provided we add the default dependencies only.
            compiler_args.extend_from_slice(&[
                "--extern=abstract_integers".to_string(),
                "--extern=hacspec_derive".to_string(),
                "--extern=hacspec_lib".to_string(),
                "--extern=secret_integers".to_string(),
            ]);
        }
        None => {
            let package_name = args.pop();
            log::trace!("package name to analyze: {:?}", package_name);
            read_crate(manifest, package_name, &mut compiler_args, &mut callbacks);
        }
    }

    compiler_args.push("--crate-type=lib".to_string());
    compiler_args.push("--edition=2021".to_string());
    log::trace!("compiler_args: {:?}", compiler_args);
    let compiler = RunCompiler::new(&compiler_args, &mut callbacks);

    match compiler.run() {
        Ok(_) => Ok(()),
        Err(_) => Err(1),
    }
}
