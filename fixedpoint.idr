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
    
---------------------------------------------------------------------------------------------------------
||| If g is the lub of prefixedpoints then f(g) is an upper bound of prefixedpoints
f_highest_prefixedpoint_is_an_upper_bound_of_prefixedpoints : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
    (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) ->
    (pf_complete_lattice : is_complete_lattice ty lt pf_partial_order pf_lattice) ->
    (is_upper_bound ty lt (prefixedpoint_subtype ty lt f) 
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))) 

f_highest_prefixedpoint_is_an_upper_bound_of_prefixedpoints ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice a pf_pre_a = let
    lub_pre_is_upper_bound_of_pre = (fst (snd (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
    a_is_lt_lub_pre = lub_pre_is_upper_bound_of_pre a pf_pre_a
    f_a_is_lt_f_lub_pre = pf_monotonic a 
        (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)) 
        a_is_lt_lub_pre
    pf_trans = (fst (snd pf_partial_order))    
    a_is_lt_f_lub_pre = pf_trans a (f a) 
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
        pf_pre_a f_a_is_lt_f_lub_pre
    in
    a_is_lt_f_lub_pre
    
---------------------------------------------------------------------------------------------------------
||| If g is the lub of prefixedpoints then g <= f(g)
highest_prefixedpoint_is_less_than_f_highest_prefixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
    (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) ->
    (pf_complete_lattice : is_complete_lattice ty lt pf_partial_order pf_lattice) ->
    (lt (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))))

highest_prefixedpoint_is_less_than_f_highest_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice = let
    lub_pre_is_lub = snd (snd (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))
    lub_pre_is_less_than_f_lub_pre = lub_pre_is_lub 
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))) 
        (f_highest_prefixedpoint_is_an_upper_bound_of_prefixedpoints ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice)
    in        
    lub_pre_is_less_than_f_lub_pre    
--------------------------------------------------------------------------------------------------------------------------------------------
||| If g is the lub of prefixedpoints then f(g) is prefixedpoint
f_highest_prefixedpoint_is_a_prefixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
    (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) ->
    (pf_complete_lattice : is_complete_lattice ty lt pf_partial_order pf_lattice) ->
    (is_prefixedpoint ty lt f (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))))
    
f_highest_prefixedpoint_is_a_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice = 
    pf_monotonic (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
        (highest_prefixedpoint_is_less_than_f_highest_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice)
-------------------------------------------------------------------------------------------------------------------------------------------
||| If g is the lub of prefixedpoints then g >= f(g)
highest_prefixedpoint_is_greater_than_f_highest_prefixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
    (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) ->
    (pf_complete_lattice : is_complete_lattice ty lt pf_partial_order pf_lattice) ->
    (lt (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
        (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))

highest_prefixedpoint_is_greater_than_f_highest_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice = let
    lub_pre_is_upper_bound_of_pre = (fst (snd (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
    in
    lub_pre_is_upper_bound_of_pre (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
        (f_highest_prefixedpoint_is_a_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice)
       
-------------------------------------------------------------------------------------------------------------------------------------------
||| lub of prefixedpoints is a fixedpoint
highest_prefixedpoint_is_a_fixedpoint : (ty : Type) -> (lt : ty -> ty -> Type) -> (f : ty -> ty) -> 
    (pf_partial_order : is_partial_order ty lt) -> (is_monotonic ty lt f) ->
    (pf_lattice : is_lattice ty lt pf_partial_order) ->
    (pf_complete_lattice : is_complete_lattice ty lt pf_partial_order pf_lattice) -> 
    (is_fixedpoint ty lt f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))     
highest_prefixedpoint_is_a_fixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice = let
    pf_anti_sym = snd (snd pf_partial_order)
    in
    pf_anti_sym (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice))
        (f (fst (highest_prefixedpoint_with_pf ty lt f pf_partial_order pf_lattice pf_complete_lattice)))
        (highest_prefixedpoint_is_less_than_f_highest_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice)
        (highest_prefixedpoint_is_greater_than_f_highest_prefixedpoint ty lt f pf_partial_order pf_monotonic pf_lattice pf_complete_lattice)
    
 
                                  







    
