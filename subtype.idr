module subtype 


------------------------------------------------------------------------------
||| A substype of a type ty is given by a function from ty to Bool
Subtype_of : (ty : Type) -> Type
Subtype_of ty = ty -> Bool

--------------------------------------------------------------------------
||| This function helps in defining properties of a subtype
subtype_helper : Bool -> Type
subtype_helper True = ()
subtype_helper False = Void

||| subtype property
subtype_property : (ty : Type) -> (sy : Subtype_of ty) -> (p : ty -> Type) -> Type
subtype_property ty sy p = (a : ty) -> (subtype_helper (sy a)) -> (p a)
