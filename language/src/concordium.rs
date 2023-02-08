use rustc_ast::{
    ast::{self, AttrArgs, AttrKind, Attribute},
    node_id::NodeId,
    token::{Delimiter, Lit, LitKind as TokenLitKind, TokenKind},
    tokenstream::{TokenStream, TokenTree},
};
use serde::{ser::SerializeSeq, Serialize, Serializer};

#[derive(Clone, Serialize, Debug)]
pub struct InitData {
    pub contract: String,
    pub parameter: Option<String>,
}

#[derive(Clone, Serialize, Debug)]
pub struct ReceiveData {
    pub contract: String,
    pub name: String,
    pub parameter: Option<String>,
    pub payable: bool,
    pub logger: bool,
}

pub(crate) fn attribute_init(attr: &Attribute) -> Option<InitData> {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "init" => match attr.kind.clone() {
            rustc_ast::ast::AttrKind::Normal(p) => match &p.item.args {
                rustc_ast::ast::AttrArgs::Delimited(delim_args) => {
                    let inner_tokens = &delim_args.tokens;

                    let mut it = inner_tokens.trees();
                    it.next();
                    it.next();
                    let temp1 = match it.next().unwrap() {
                        TokenTree::Token(third_tok, ..) => match third_tok.kind {
                            TokenKind::Literal(l) => Some(l.symbol.to_string()),
                            _ => None,
                        },
                        _ => None,
                    }?;
                    it.next();
                    it.next();
                    it.next();
                    let temp2 = match it.next() {
                        Some(TokenTree::Token(third_tok, ..)) => match third_tok.kind {
                            TokenKind::Literal(l) => Some(l.symbol.to_string()),
                            _ => None,
                        },
                        _ => None,
                    };
                    Some(InitData {
                        contract: temp1,
                        parameter: temp2,
                    })
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn attribute_receive(attr: &Attribute) -> Option<ReceiveData> {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "receive" => match attr.kind.clone() {
            rustc_ast::ast::AttrKind::Normal(p) => match &p.item.args {
                rustc_ast::ast::AttrArgs::Delimited(delim_args) => {
                    let inner_tokens = &delim_args.tokens;

                    let mut it = inner_tokens.trees();
                    it.next();
                    it.next();
                    let temp = match it.next().unwrap() {
                        TokenTree::Token(third_tok, ..) => match third_tok.kind {
                            TokenKind::Literal(l) => Some(l.symbol.to_string()),
                            _ => None,
                        },
                        _ => None,
                    }?;
                    it.next();
                    it.next();
                    it.next();
                    let temp2 = match it.next().unwrap() {
                        TokenTree::Token(third_tok, ..) => match third_tok.kind {
                            TokenKind::Literal(l) => Some(l.symbol.to_string()),
                            _ => None,
                        },
                        _ => None,
                    }?;

                    let mut temp3 = None;
                    let mut payable = false;
                    let mut logger = false;

                    while true {
                        match it.next() {
                            Some(TokenTree::Token(third_tok, ..)) => match third_tok.kind {
                                TokenKind::Literal(l) => temp3 = Some(l.symbol.to_string()),
                                TokenKind::Ident(l, _) => match l.to_string().as_str() {
                                    "enable_logger" => logger = true,
                                    "payable" => payable = true,
                                    _ => (),
                                },
                                _ => (),
                            },
                            None => {
                                break;
                            }
                            _ => (),
                        };
                    }

                    Some(ReceiveData {
                        contract: temp,
                        name: temp2,
                        parameter: temp3,
                        payable: payable,
                        logger: logger,
                    })
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}
