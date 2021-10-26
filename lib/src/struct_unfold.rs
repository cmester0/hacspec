#[macro_export]
macro_rules! unfold_struct {
    (
        struct $struct_name:ident {
            $($field_name:ident : $field_type:ty),*$(,)+
        }
    ) => {
	#[derive(Clone)]
        pub struct $struct_name ($(pub $field_type),*);
    };
}

#[macro_export]
macro_rules! translate_field {
    ( $fn_name:ident, $enum_name_from:ty, $enum_name_to:ty, $($rest:ident),* ) => {
	fn $fn_name(their_ident : $enum_name_from) -> $enum_name_to {
	    match their_ident {
		$(<$enum_name_from>::$rest => <$enum_name_to>::$rest),*
	    }
	}
    }
}

    // ($ty:ty) => {
    // 	fn their_to_my_$ty(their_ident : $ty) -> $ty {
    // 	    their_ident
    // 	}
    // },

// #[macro_export]
// macro_rules! struct_to_unfold_struct_translations {
//     (
// 	$unfold_struct:ident,
//         pub struct $struct_name:ident {
//             $($field_name:ident : $field_type:ty),*$(,)+
//         }
//     ) => {
// 	$(translate_field!($field_name, $field_type)),*
	
//         fn their_to_my_struct (their_struct : $struct_name) -> $unfold_struct {
// 	    $unfold_struct ($(their_struct.$field_name),*) // [their_struct.]$($field_name)+
// 	}
	
//         // fn my_to_their_$struct_name (my_struct : $unfold_struct) -> $struct_name {
// 	//     let $unfold_struct ($($field_name),*) = my_struct;
// 	// }	
//     };
// }
