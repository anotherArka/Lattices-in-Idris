module propositions

is_proposition : (ty : Type) -> Type 
is_proposition ty = (a, b : ty) -> (a = b)
    
is_set : (ty : Type) -> Type
is_set ty = (a, b : ty) -> (is_proposition (a = b))

||| Due to pattern matching in idris, each type is a set
all_are_sets : (ty : Type) -> (is_set ty)
all_are_sets ty a a Refl Refl = Refl

product_equality_helper : {u, v : Type} -> 
  (a, c : u) -> (b, d : v) ->
  (a = c) -> (b = d) -> ((a, b) = (c, d))
product_equality_helper a a b b Refl Refl = Refl

product_equality : {u, v : Type} -> (x, y : (u,v)) -> 
  ((fst x) = (fst y)) -> ((snd x) = (snd y)) -> (x = y)
product_equality (a, b) (c, d) pf1 pf2 = 
  product_equality_helper a c b d pf1 pf2   
  