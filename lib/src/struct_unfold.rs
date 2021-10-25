#[macro_export]
macro_rules! unfold_struct {
    (
     struct $struct_name:ident {
        $(
        $field_name:ident : $field_type:ty
        ),*$(,)+
    }
    ) => {
            pub type $struct_name = (
                $(
                    $field_type
                ),*
            );
    }
}
