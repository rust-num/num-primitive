/// Forward a method to an inherent method
macro_rules! forward {
    ($(fn $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[doc = forward_doc!($method)]
        #[inline]
        fn $method(self $( , $arg : $ty )* ) -> $ret {
            Self::$method(self $( , $arg )* )
        }
    )*};
    ($(fn $method:ident ( &self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[doc = forward_doc!($method)]
        #[inline]
        fn $method(&self $( , $arg : $ty )* ) -> $ret {
            Self::$method(self $( , $arg )* )
        }
    )*};
    ($(fn $method:ident ( $( $arg:ident : $ty:ty ),* ) -> $ret:ty ; )*) => {$(
        #[doc = forward_doc!($method)]
        #[inline]
        fn $method($( $arg : $ty ),* ) -> $ret {
            Self::$method($( $arg ),* )
        }
    )*};
    ($(unsafe fn $method:ident ( self $( , $arg:ident : $ty:ty )* ) -> $ret:ty ; )*) => {$(
        #[doc = forward_doc!($method)]
        #[inline]
        unsafe fn $method(self $( , $arg : $ty )* ) -> $ret {
            // SAFETY: we're just passing through here!
            unsafe { Self::$method(self $( , $arg )* ) }
        }
    )*};
}

/// A string suitable for method `#[doc = ...]`
macro_rules! forward_doc {
    ($method:ident) => {
        concat!(
            "See the inherent [`",
            stringify!($method),
            "`][Self::",
            stringify!($method),
            "] method."
        )
    };
}

/// Declare a `const` that copies an original value
macro_rules! use_consts {
    ($base:ident :: { $( $name:ident : $ty:ty ,)+ }) => {
        $(const $name: $ty = $base :: $name;)+
    };
}
