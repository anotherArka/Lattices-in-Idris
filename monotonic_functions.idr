module monotonic_functions

import partial_order

------------------------------------------------------------------------
is_monotonic_function : (ty : Type) -> (lt : ty -> ty -> Type) ->
    (f : ty -> ty) -> Type
is_monotonic_function ty lt f =
    (a , b : ty) -> (lt a b) -> (lt (f a) (f b))

-------------------------------------------------------------------
