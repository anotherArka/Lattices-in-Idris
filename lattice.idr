module lattice

import partial_order
import subtype

is_lower_bound : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (bound : ty) -> Type
is_lower_bound ty lt sy bound = subtype_property ty sy less_than where 
    less_than : ty -> Type
    less_than a = lt bound a
    
is_upper_bound : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (bound : ty) -> Type
is_upper_bound ty lt sy bound = subtype_property ty sy greater_than where 
    greater_than : ty -> Type
    greater_than a = lt bound a
    
is_lub : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (lub : ty) -> Type
is_lub ty lt sy lub = 
    (is_upper_bound ty lt sy lub,
     (upper_bound : ty) -> (is_upper_bound ty lt sy upper_bound) -> (lt lub upper_bound))
        
is_glb : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (glb : ty) -> Type
is_glb ty lt sy glb = 
    (is_upper_bound ty lt sy glb,
     (lower_bound : ty) -> (is_lower_bound ty lt sy lower_bound) -> (lt lower_bound glb))         
