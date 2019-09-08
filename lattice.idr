module lattice

import partial_order
import subtype

------------------------------------------------------------------------------------------------------------------
||| Type of joins of a lattice
public export
join_type : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
join_type ty lt = (a , b : ty) -> (lub : ty **
    ((lt a lub), ((lt b lub) , ((ub : ty) -> (lt a ub) -> (lt b ub) -> (lt lub ub)))))

-----------------------------------------------------------------------------------------------------------------
||| Type of meets of a lattice
public export
meet_type : (ty : Type) -> (lt : ty -> ty -> Type) -> Type
meet_type ty lt =  (a , b : ty) -> (glb : ty **
    ((lt glb a), ((lt glb b) , ((lb : ty) -> (lt lb a) -> (lt lb b) -> (lt lb glb)))))

------------------------------------------------------------------------------------------------------------------
is_lattice : (ty : Type) -> (lt : ty -> ty -> Type) -> (pf : is_partial_order ty lt) -> Type
is_lattice ty lt pf = (join_type ty lt, meet_type ty lt)

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

------------------------------------------------------------------------------------------------------------
is_glb : (ty : Type) -> (lt : ty -> ty -> Type) -> (sy : Subtype_of ty) -> (glb : ty) -> Type
is_glb ty lt sy glb =
    (is_lower_bound ty lt sy glb,
     (lower_bound : ty) -> (is_lower_bound ty lt sy lower_bound) -> (lt lower_bound glb))

------------------------------------------------------------------------------------------------------------
is_join_complete_lattice : (ty : Type) -> (lt : ty -> ty -> Type) ->
    (pf_partial_order : is_partial_order ty lt) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) -> Type

is_join_complete_lattice ty lt pf_partial_order pf_lattice =
    (sub : Subtype_of ty) -> (lub_of_sub : ty) ->
    (is_lub ty lt sub lub_of_sub)

------------------------------------------------------------------------------------------------------------------
is_meet_complete_lattice : (ty : Type) -> (lt : ty -> ty -> Type) ->
    (pf_partial_order : is_partial_order ty lt) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) -> Type

is_meet_complete_lattice ty lt pf_partial_order pf_lattice =
    (sub : Subtype_of ty) -> (glb_of_sub : ty) ->
    (is_glb ty lt sub glb_of_sub)

------------------------------------------------------------------------------------------------------------------
is_complete_lattice : (ty : Type) -> (lt : ty -> ty -> Type) ->
    (pf_partial_order : is_partial_order ty lt) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) -> Type

is_complete_lattice ty lt pf_partial_order pf_lattice =
    (is_join_complete_lattice ty lt pf_partial_order pf_lattice,
     is_meet_complete_lattice ty lt pf_partial_order pf_lattice)
