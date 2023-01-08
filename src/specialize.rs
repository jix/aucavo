macro_rules! specialize_trait {
    ($(#[$($attr:tt)*])* $name:ident: $($bound:tt)*) => {
        $(#[$($attr)*])*
        pub trait $name<Target: ?Sized, Input, Output>: Sized {
            fn base(self, input: Input) -> Output;

            fn specialized(self, input: Input) -> Output
            where
                Target: $($bound)*;
        }
    };
}

macro_rules! specialize_dispatcher {
    ($(#[$($attr:tt)*])* $fnname:ident: $trait:ident) => {
        $(#[$($attr)*])*
        #[inline(always)]
        fn $fnname<Input, Output, S: $trait<Self, Input, Output>>(
            specialization: S,
            input: Input,
        ) -> Output {
            specialization.base(input)
        }
    };
}

macro_rules! specialize_impl {
    ($(#[$($attr:tt)*])* $fnname:ident: $trait:ident) => {
        $(#[$($attr)*])*
        #[inline(always)]
        fn $fnname<Input, Output, S: $trait<Self, Input, Output>>(
            specialization: S,
            input: Input,
        ) -> Output  {
            specialization.specialized(input)
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
        fn $fnname<Input, Output, S: $trait<Self, Input, Output>>(
            specialization: S,
            input: Input,
        ) -> Output {
            #[repr(transparent)]
            struct Wrap<S>(S);

            impl<$($lt,)* S, $target: $($tbound)*, Input, Output> $trait<$target, Input, Output> for Wrap<S>
            where
                S: $trait<$($typat)*, Input, Output>,
            {
                #[inline(always)]
                fn base(self, input: Input) -> Output {
                    <S as $trait<$($typat)*, Input, Output>>::base(self.0, input)
                }

                #[inline(always)]
                fn specialized(self, input: Input) -> Output
                where
                    $target: $($bound)*,
                {
                    <S as $trait<$($typat)*, Input, Output>>::specialized(self.0, input)
                }
            }

            T::$fnname::<Input, Output, Wrap<S>>(Wrap(specialization), input)
        }
    };
}
