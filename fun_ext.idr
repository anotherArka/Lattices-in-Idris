module fun_ext

||| The axiom of funcional extensionality
public export
fun_ext : (domain , range : Type) -> (f , g : domain -> range) ->
    (pf_eq : (a : domain) -> ((f a) = (g a))) -> (f = g)
