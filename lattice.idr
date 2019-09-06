module lattice

import partial_order
import subtype

----------------------------------------------------------------------------------------------------------------------
join : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
join ty lt = (a , b : ty) -> (lub : ty ** ((lt a lub), ((lt b lub) , ((ub : ty) -> (lt a ub) -> (lt b ub) -> (lt lub ub)))))

-----------------------------------------------------------------------------------------------------------------------
meet : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
meet ty lt =  (a , b : ty) -> (glb : ty ** ((lt glb a), ((lt glb b) , ((lb : ty) -> (lt lb a) -> (lt lb b) -> (lt lb glb)))))

----------------------------------------------------------------------------------------------------------------------
is_lattice : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
is_lattice ty lt = (join ty lt, meet ty lt)

-------------------------------------------------------------------------------------------------------------
is_lower_bound : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (bound : ty) -> Type
is_lower_bound ty lt sy bound = subtype_property ty sy less_than where 
    less_than : ty -> Type
    less_than a = lt bound a

--------------------------------------------------------------------------------------------------------------    
is_upper_bound : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (bound : ty) -> Type
is_upper_bound ty lt sy bound = subtype_property ty sy greater_than where 
    greater_than : ty -> Type
    greater_than a = lt a bound
    
---------------------------------------------------------------------------------------------------------    
is_lub : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (lub : ty) -> Type
is_lub ty lt sy lub = 
    (is_upper_bound ty lt sy lub,
     (upper_bound : ty) -> (is_upper_bound ty lt sy upper_bound) -> (lt lub upper_bound))
        
---------------------------------------------------------------------------------------------------------------        
is_glb : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (glb : ty) -> Type
is_glb ty lt sy glb = 
    (is_lower_bound ty lt sy glb,
     (lower_bound : ty) -> (is_lower_bound ty lt sy lower_bound) -> (lt lower_bound glb)) 
     
        
