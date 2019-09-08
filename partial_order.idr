module partial_order 

-----------------------------------------------------------------------
public export
is_refl : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_refl ty lt = (a : ty) -> (lt a a)

---------------------------------------------------------------------------------
public export
is_trans : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_trans ty lt = (a, b, c : ty) -> (lt a b) -> (lt b c) -> (lt a c)

------------------------------------------------------------------------------------
public export
is_antisym : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_antisym ty lt = (a, b : ty) -> (lt a b) -> (lt b a) -> (a = b)

------------------------------------------------------------------------------------
public export
is_partial_order : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_partial_order ty lt = (is_refl ty lt , ( is_trans ty lt , is_antisym ty lt))
