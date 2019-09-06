module partial_order 

-----------------------------------------------------------------------
public export
is_Refl : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Refl ty lt = (a : ty) -> (lt a a)

---------------------------------------------------------------------------------
public export
is_Trans : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Trans ty lt = (a, b, c : ty) -> (lt a b) -> (lt b c) -> (lt a c)

------------------------------------------------------------------------------------
public export
is_Antisym : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Antisym ty lt = (a, b : ty) -> (lt a b) -> (lt b a) -> (a = b)

------------------------------------------------------------------------------------
public export
is_Partial_Order : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_Partial_Order ty lt = (is_Refl ty lt , ( is_Trans ty lt , is_Antisym ty lt))
