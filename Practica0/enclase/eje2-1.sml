open tigerabs

structure Ej2 =
struct

  fun  cantprints (CallExp ({func = "print", args = []},_)) = raise Fail "print error"
    | cantprints (CallExp ({func = "print",args = [StringExp _]},_)) = 0
    | cantprints (CallExp ({func = "print", args = x::(y::xs)},_)) = raise Fail "print error"
    | cantprints (CallExp ({func = "print",args = [x]},_)) = cantprints x + 1
    | cantprints (CallExp ({func = _, args = xs},_)) = foldr(fn (x,n) => cantprints x + n) 0 xs
    | cantprints (VarExp _) = 0
    | cantprints (UnitExp _) = 0
    | cantprints (NilExp _) = 0
    | cantprints (IntExp _) = 0
    | cantprints (StringExp _) = 0
    | cantprints (OpExp ({right = e1, oper = _, left = e2},_)) = cantprints e1 + cantprints e2
    | cantprints (RecordExp ({fields = xs, typ = _},_)) = foldr(fn ((_,e),n) => cantprints e + n) 0 xs
    | cantprints (SeqExp (xs,_)) = foldr(fn (x,n) => cantprints x + n) 0 xs
    | cantprints (AssignExp ({var = _, exp = e},_)) = cantprints e
    | cantprints (IfExp ({test = e1, then' = e2, else' = (SOME e3)},_)) = cantprints e1 + cantprints e2 + cantprints e3
    | cantprints (IfExp ({test = e1, then' = e2, else' = NONE},_)) = cantprints e1 + cantprints e2
    | cantprints (WhileExp ({test = e1, body = e2}, _)) = cantprints e1 + cantprints e2
    | cantprints (ForExp ({var = _, escape = _, lo = e1, hi = e2, body = e3}, _)) = cantprints e1 + cantprints e2 + cantprints e3
    | cantprints (LetExp ({decs = decls, body = e1}, _)) =  foldr(fn (x,n) => cantprintsDecs x + n) 0 decls+ cantprints e1
    | cantprints (BreakExp _) = 0
    | cantprints (ArrayExp ({typ = _, size = e1, init = e2}, _)) = cantprints e1 + cantprints e2

  and fun cantprintsDecs (FunctionDec ({name = _, params = _, result = _, body = e1}, _)) = cantprints e1

(*
  dec = FunctionDec of ({name: symbol, params: field list,
		result: symbol option, body: exp} * pos) list
	| VarDec of {name: symbol, escape: bool ref,
		     typ: symbol option, init: exp} * pos
	| TypeDec of ({name: symbol, ty: ty} * pos) list

  fun cantplus ... =
  ...
*)

end
