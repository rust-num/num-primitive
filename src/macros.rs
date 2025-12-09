/// Forward a method to an inherent method
macro_rules! forward {
    ($(fn $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[inline]
        fn $method(self $( , $arg : $ty )* ) -> $ret {
            Self::$method(self $( , $arg )* )
        }
    )*};
    ($(fn $method:ident ( &self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[inline]
        fn $method(&self $( , $arg : $ty )* ) -> $ret {
            Self::$method(self $( , $arg )* )
        }
    )*};
    ($(fn $method:ident ( $( $arg:ident : $ty:ty ),* ) -> $ret:ty ; )*) => {$(
        #[inline]
        fn $method($( $arg : $ty ),* ) -> $ret {
            Self::$method($( $arg ),* )
        }
    )*};
    ($(unsafe fn $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[inline]
        unsafe fn $method(self $( , $arg : $ty )* ) -> $ret {
            // SAFETY: we're just passing through here!
            unsafe { Self::$method(self $( , $arg )* ) }
        }
    )*};
}

/// Declare a `const` that copies an original value
macro_rules! use_consts {
    ($base:ident :: { $( $name:ident : $ty:ty ,)+ }) => {
        $(const $name: $ty = $base :: $name;)+
    };
}
