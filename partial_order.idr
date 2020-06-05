module partial_order

---------------------------------------------------------------------------------
public export
interface Reflexive_order (ty : Type) (lt : ty -> ty -> Type) where
    proof_of_reflexivity : (a : ty) -> (lt a a)
----------------------------------------------------------------------------------
public export
interface Transitive_order (ty : Type) (lt : ty -> ty -> Type) where
    proof_of_transitivity : (a, b : ty) -> (lt a b) -> (lt b c) -> (lt a c)
----------------------------------------------------------------------------------
public export
interface Antisymmetric_order (ty : Type) (lt : ty -> ty -> Type) where
    proof_of_antisymmetry : (a, b : ty) -> (lt a b) -> (lt b a) -> (a = a)
----------------------------------------------------------------------------------
public export
interface (Reflexive_order ty lt, Transitive_order ty lt, Antisymmetric_order ty lt) 
    => Partial_order (ty : Type) (lt : ty -> ty -> Type) where
----------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
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
