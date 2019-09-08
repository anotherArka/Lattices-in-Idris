module monotonic_functions

import partial_order

------------------------------------------------------------------------
monotonic_function_type : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
monotonic_function_type ty lt = (f : (ty -> ty) ** (
    (a , b : ty) -> (lt a b) -> (lt (f a) (f b))))

----------------------------------------------------------------------------
order_on_monotonic_function : (ty : Type) -> (lt : ty -> ty -> Type) ->
    (f , g : monotonic_function_type ty lt) -> Type

order_on_monotonic_function ty lt
    (f ** f_monotonic_pf) (g ** g_monotonic_pf) =
    (a : ty) -> (lt (f a) (g a))

----------------------------------------------------------------------------
order_on_monotonic_function_is_refl : (ty -> Type) ->
    (lt : ty -> ty -> Type) -> (pf_refl : is_refl ty lt) ->
    (f : monotonic_function_type ty lt) ->
    (order_on_monotonic_function ty lt f f)

order_on_monotonic_function_is_refl ty lt pf_refl (f ** f_monotonic_pf) a =
    pf_refl (f a)

----------------------------------------------------------------------------
order_on_monotonic_function_is_trans : (ty -> Type) ->
    (lt : ty -> ty -> Type) -> (pf_trans : is_trans ty lt) ->
    (f , g , h : monotonic_function_type ty lt) ->
    (order_on_monotonic_function ty lt f g) ->
    (order_on_monotonic_function ty lt g h) ->
    (order_on_monotonic_function ty lt f h)

order_on_monotonic_function_is_trans ty lt pf_trans (f ** f_monotonic_pf)
    (g ** g_monotonic_pf) (h ** h_monotonic_pf)
    f_lt_g_pf g_lt_h_pf a =
        pf_trans (f a) (g a) (h a) (f_lt_g_pf a) (g_lt_h_pf a)

----------------------------------------------------------------------------
order_on_monotonic_function_is_weakly_antisym : (ty -> Type) ->
    (lt : ty -> ty -> Type) -> (pf_antisym : is_antisym ty lt) ->
    (f , g : monotonic_function_type ty lt) ->
    (order_on_monotonic_function ty lt f g) ->
    (order_on_monotonic_function ty lt g f) ->
    (a : ty) -> (((fst f) a) = (fst g) a)

order_on_monotonic_function_is_weakly_antisym ty lt pf_antisym
    (f ** f_monotonic_pf) (g ** g_monotonic_pf)
    f_lt_g_pf g_lt_f_pf a =
        pf_antisym (f a) (g a) (f_lt_g_pf a) (g_lt_f_pf a)
