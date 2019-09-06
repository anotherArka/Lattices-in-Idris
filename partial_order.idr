module partial_order 

is_Refl : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Refl ty lt = (a : ty) -> (lt a a)

is_Trans : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Trans ty lt = (a, b, c : ty) -> (lt a b) -> (lt b c) -> (lt a c)

is_Antisym : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Antisym ty lt = (a, b : ty) -> (lt a b) -> (lt b a) -> (a = b)

is_Partial_Order : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Partial_Order ty lt = (is_Refl ty lt , ( is_Trans ty lt , is_Antisym ty lt))
