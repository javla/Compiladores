structure eje2 :> eje2  =
struct
open tigerabs

fun  cantprintsExp (CallExp ({func = "print", args = []},_)) = raise Fail "print error"
   | cantprintsExp (CallExp ({func = "print",args = [StringExp _]},_)) = 0
   | cantprintsExp (CallExp ({func = "print", args = x::(y::xs)},_)) = raise Fail "print error"
   | cantprintsExp (CallExp ({func = "print",args = [x]},_)) = cantprintsExp x + 1
   | cantprintsExp (CallExp ({func = _, args = xs},_)) = foldr(fn (x,n) => cantprintsExp x + n) 0 xs
   | cantprintsExp (VarExp _) = 0
   | cantprintsExp (UnitExp _) = 0
   | cantprintsExp (NilExp _) = 0
   | cantprintsExp (IntExp _) = 0
   | cantprintsExp (StringExp _) = 0
   | cantprintsExp (OpExp ({right = e1, oper = _, left = e2},_)) = cantprintsExp e1 + cantprintsExp e2
   | cantprintsExp (RecordExp ({fields = xs, typ = _},_)) = foldr(fn ((_,e),n) => cantprintsExp e + n) 0 xs
   | cantprintsExp (SeqExp (xs,_)) = foldr(fn (x,n) => cantprintsExp x + n) 0 xs
   | cantprintsExp (AssignExp ({var = _, exp = e},_)) = cantprintsExp e
   | cantprintsExp (IfExp ({test = e1, then' = e2, else' = (SOME e3)},_)) = cantprintsExp e1 + cantprintsExp e2 + cantprintsExp e3
   | cantprintsExp (IfExp ({test = e1, then' = e2, else' = NONE},_)) = cantprintsExp e1 + cantprintsExp e2
   | cantprintsExp (WhileExp ({test = e1, body = e2}, _)) = cantprintsExp e1 + cantprintsExp e2
   | cantprintsExp (ForExp ({lo = e1, hi = e2, body = e3,...}, _)) = cantprintsExp e1 + cantprintsExp e2 + cantprintsExp e3
   | cantprintsExp (LetExp ({decs = decls, body = e1}, _)) =  foldr(fn (x,n) => cantprintsDecs x + n) 0 decls + cantprintsExp e1
   | cantprintsExp (BreakExp _) = 0
   | cantprintsExp (ArrayExp ({typ = _, size = e1, init = e2}, _)) = cantprintsExp e1 + cantprintsExp e2

and cantprintsDecs (FunctionDec xs) = foldr(fn (x,n) => descAux x + n) 0 xs
  | cantprintsDecs (VarDec ({init = e,...},_)) = cantprintsExp e
  | cantprintsDecs (TypeDec _) = 0

and descAux ({name = _, params = _, result = _, body = e1}, _) =  cantprintsExp e1

and suma (x,y) = x + y

end
