module propositions

is_proposition : (ty : Type) -> Type 
is_proposition ty = (a, b : ty) -> (a = b)
    
is_set : (ty : Type) -> Type
is_set ty = (a, b : ty) -> (is_proposition (a = b))

propositions_are_sets : (ty : Type) -> (is_proposition ty) -> (is_set ty)
propositions_are_sets ty proof_of_propositionality a b pf_1 pf_2= let
    pf = proof_of_propositionality a b
    
    in
    ?rhs
    
