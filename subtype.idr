module subtype 

------------------------------------------------------------------------------
||| A subtype of a type ty is given by a function from ty to Bool
public export
Subtype_of : (ty : Type) -> Type
Subtype_of ty = ty -> Type

--------------------------------------------------------------------------
||| This function helps in defining properties of a subtype
public export
subtype_helper : Bool -> Type
subtype_helper True = ()
subtype_helper False = Void

------------------------------------------------------------------------------------
||| subtype property
public export
subtype_property : (ty : Type) -> (sy : Subtype_of ty) -> (p : ty -> Type) -> Type
subtype_property ty sy p = (a : ty) -> (sy a) -> (p a)

---------------------------------------------------------------------------------
||| The empty subset of any type
public export
empty_subset : (ty : Type) -> (Subtype_of ty)
empty_subset ty = \x => Void

---------------------------------------------------------------
||| Proof that everything is true for the empty type
public export
subtype_lemma_1 : (ty : Type) -> (p : ty -> Type) -> (subtype_property ty (empty_subset ty) p)
subtype_lemma_1 ty p a element_of_void = void element_of_void
--------------------------------------------------------------------------------------------------



