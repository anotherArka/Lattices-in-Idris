module fixedpoint

import partial_order
import monotonic_functions
import lattice
import subtype
		
is_prefixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) ->
                   (a : ty) -> Type
is_prefixedpoint ty lt f a = (lt a (f a))

----------------------------------------------------------------------------------------------

is_postfixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) ->
                    (a : ty) -> Type
is_postfixedpoint ty lt f a = (lt (f a) a)

----------------------------------------------------------------------------------------------

is_fixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) ->
                (a : ty) -> Type
is_fixedpoint ty lt f a = (a = (f a))

----------------------------------------------------------------------------------------------

||| If lt is a partial order then prefixedpoint and postfixedpoint implies 
||| fixededpoint

fixedpoint_lemma_1 : (ty : Type) -> (lt : ty -> ty -> Type) -> (is_partial_order ty lt) ->
                     (f : ty -> ty) -> (a : ty) -> 
                     (is_prefixedpoint ty lt f a) -> (is_postfixedpoint ty lt f a) ->
                     (is_fixedpoint ty lt f a)
fixedpoint_lemma_1 ty lt pf_partial_order f a pf_pre pf_post = let
    pf_anti_sym = snd (snd pf_partial_order)
    in
    pf_anti_sym a (f a) pf_pre pf_post
    
-----------------------------------------------------------------------------------------------
||| the type of prefixpoints of a monotonic function on a partial order
prefixedpoint_type : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
                   (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) -> Type 
prefixedpoint_type ty lt f pf_partial_order pf_monotonic =
    (a : ty ** (is_prefixedpoint ty lt f a))
-----------------------------------------------------------------------------------------------
||| the subtype of prefixedpoints of a function on a partial order
prefixedpoint_subtype : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> (Subtype_of ty)
prefixedpoint_subtype ty lt f a = (is_prefixedpoint ty lt f a)	

-----------------------------------------------------------------------------------------------
||| highest prefixfixedpoint of a function on a complete lattice
highest_prefixedpoint_with_pf : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
                      (pf_partial_order : is_partial_order ty lt) ->
                      (pf_lattice : is_lattice ty lt pf_partial_order) ->
                      (is_complete_lattice ty lt pf_partial_order pf_lattice) -> 
                      (a : ty ** (is_lub ty lt (prefixedpoint_subtype ty lt f) a))

highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice = let
    pf_join_complete = fst pf_complete_lattice    
    lub_of_pre = pf_join_complete (prefixedpoint_subtype ty lt f)	
    in
    lub_of_pre
 
                                  







    
