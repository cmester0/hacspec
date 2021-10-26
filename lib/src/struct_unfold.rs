#[macro_export]
macro_rules! unfold_struct {
    (
        $vis:vis struct $struct_name:ident {
            $($field_vis:vis $field_name:ident : $field_type:ty),*$(,)+
        }
    ) => {
        $vis type $struct_name = ($($field_type),*);
    };
}

// #[allow(non_camel_case_types)]
// #[derive(Clone)]
// $vis struct $struct_name ($($field_vis $field_type),*);

