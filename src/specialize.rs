macro_rules! specialize_trait {
    ($(#[$($attr:tt)*])* $name:ident: $($bound:tt)*) => {
        $(#[$($attr)*])*
        pub trait $name<Target: ?Sized, Output>: Sized {
            fn base(self) -> Output;

            fn specialized(self) -> Output
            where
                Target: $($bound)*;
        }
    };
}

macro_rules! specialize_dispatcher {
    ($(#[$($attr:tt)*])* $fnname:ident: $trait:ident) => {
        $(#[$($attr)*])*
        #[inline(always)]
        fn $fnname<Output, S: $trait<Self, Output>>(
            specialization: S,
        ) -> Output {
            specialization.base()
        }
    };
}

macro_rules! specialize_impl {
    ($(#[$($attr:tt)*])* $fnname:ident: $trait:ident) => {
        $(#[$($attr)*])*
        #[inline(always)]
        fn $fnname<Output, S: $trait<Self, Output>>(
            specialization: S,
        ) -> Output  {
            specialization.specialized()
        }
    };
}

macro_rules! specialize_forward {
    (
        $(#[$($attr:tt)*])* [$($lt:lifetime,)* $target:ident: $($tbound:tt)*] [ $($typat:tt)* ]
        $fnname:ident: $trait:ident: $($bound:tt)*
    ) => {
        $(#[$($attr)*])*
        #[inline(always)]
        fn $fnname<Output, S: $trait<Self, Output>>(
            specialization: S,
        ) -> Output {
            #[repr(transparent)]
            struct Wrap<S>(S);

            impl<$($lt,)* S, $target: $($tbound)*, Output> $trait<$target, Output> for Wrap<S>
            where
                S: $trait<$($typat)*, Output>,
            {
                #[inline(always)]
                fn base(self) -> Output {
                    <S as $trait<$($typat)*, Output>>::base(self.0)
                }

                #[inline(always)]
                fn specialized(self) -> Output
                where
                    $target: $($bound)*,
                {
                    <S as $trait<$($typat)*, Output>>::specialized(self.0)
                }
            }

            T::$fnname::<Output, Wrap<S>>(Wrap(specialization))
        }
    };
}
