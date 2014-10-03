structure tigerseman :> tigerseman =
struct

(* Ignoramos los breaks mal puestos*)

(*Operaciones básicas copiadas de la carpeta*)

infix -- ---
infix rs ls

fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun l -- e = List.filter (op <> rs e) l
fun fst (x, _) = x and snd (_, y) = y
fun lp --- e = List.filter ((op <> rs e) o fst) lp


fun printList(nil) = (
    print("\n");
    ())
  | printList(x::xs) = (
    print(x);
    print(" ");
    printList(xs)
    );

open tigerabs
open tigersres

open tigerpp

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
tabNueva(),
[("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
tabNueva(),
[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
 ("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
 ("getchar", Func{level=mainLevel, label="getstr",
		  formals=[], result=TString, extern=true}),
 ("ord", Func{level=mainLevel, label="ord",
	      formals=[TString], result=TInt, extern=true}),
 ("chr", Func{level=mainLevel, label="chr",
	      formals=[TInt], result=TString, extern=true}),
 ("size", Func{level=mainLevel, label="size",
	       formals=[TString], result=TInt, extern=true}),
 ("substring", Func{level=mainLevel, label="substring",
		    formals=[TString, TInt, TInt], result=TString, extern=true}),
 ("concat", Func{level=mainLevel, label="concat",
		 formals=[TString, TString], result=TString, extern=true}),
 ("not", Func{level=mainLevel, label="not",
	      formals=[TInt], result=TInt, extern=true}),
 ("exit", Func{level=mainLevel, label="exit",
	       formals=[TInt], result=TUnit, extern=true})
])

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
    let
	val a = case !r of
		    SOME t => t
		  | NONE => raise Fail "No debería pasar! (1)"
    in
	tiposIguales a b
    end
  | tiposIguales a (TTipo (_, r)) =
    let
	val b = case !r of
		    SOME t => t
		  | NONE => raise Fail "No debería pasar! (2)"
    in
	tiposIguales a b
    end
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
	fun trexp(VarExp v) = trvar(v)
	  | trexp(UnitExp _) = {exp=(), ty=TUnit}
	  | trexp(NilExp _)= {exp=(), ty=TNil}
	  | trexp(IntExp(i, _)) = {exp=(), ty=TInt}
	  | trexp(StringExp(s, _)) = {exp=(), ty=TString}
	  | trexp(CallExp({func = f, args = xs}, nl)) =		
	    (* NOSOTROS *)		
	    let
		val {formals = argsType, result = resultType, ...} =
		    case tabBusca(f,venv) of
			SOME (Func e) => e
		      | NONE => error("Función no declarada", nl)
		      | _ => error("No es una función", nl)
		fun compararListaTipos [] [] = true
		  | compararListaTipos _ [] = error("Mayor cantidad de argumentos", nl)
		  | compararListaTipos [] _ = error("Menor cantidad de argumento", nl)
		  | compararListaTipos (x::xs) (y::ys) =
                    let val {ty = expType, ...} = trexp x
                    in
		        if tiposIguales expType y then
                            compararListaTipos xs ys
		        else
                            false 
                    end
	    in
		if (compararListaTipos xs argsType) then
		    {exp=(), ty = TFunc (argsType, resultType)}
		else
		    error("Distintos tipos", nl)
	    end
	  | trexp(OpExp({left, oper=EqOp, right}, nl)) =
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper, right}, nl)) = 
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr then
		    case oper of
			PlusOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | MinusOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | TimesOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | DivideOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | _ => raise Fail "No debería pasar! (3)"
		else error("Error de tipos", nl)
	    end
	  | trexp(RecordExp({fields, typ}, nl)) =
	    let
		(* Traducir cada expresión de fields *)
		val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

		(* Buscar el tipo *)
		val (tyr, cs) = case tabBusca(typ, tenv) of
				    SOME t => (case tipoReal t of
						   TRecord (cs, u) => (TRecord (cs, u), cs)
						 | _ => error(typ^" no es de tipo record", nl))
				  | NONE => error("Tipo inexistente ("^typ^")", nl)
				                 
		(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
		fun verificar [] [] = ()
		  | verificar (c::cs) [] = error("Faltan campos", nl)
		  | verificar [] (c::cs) = error("Sobran campos", nl)
		  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
		    if s<>sy then error("Error de campo", nl)
		    else if tiposIguales ty t then verificar cs ds
		    else error("Error de tipo del campo "^s, nl)
		val _ = verificar cs tfields
	    in
		{exp=(), ty=tyr}
	    end
	  | trexp(SeqExp(s, nl)) =
	    let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	    in	{ exp=(), ty=tipo } end
	  | trexp(AssignExp({var = SimpleVar s, exp = e}, nl)) =
            let
                val {ty = expType, ...} = trexp e
                val {ty = varType, ...} = trvar ((SimpleVar s),nl)
            in
                if (tabEsta(s, venv))
                then error("Intentando asignar variable Read Only",nl)
                else
                    if tiposIguales expType varType then
                        {exp=(), ty = TUnit }
                    else
                        error("Error de tipos en asignación", nl)
            end
	  | trexp(AssignExp ({var, exp}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, ...} = trexp exp
                val {ty = varType, ...} = trvar (var,nl)
            in
                if tiposIguales expType varType then
                    {exp=(), ty = TUnit }
                else
                    error("Error de tipos en asignación", nl)
            end
	  | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
	    let val {exp=testexp, ty=tytest} = trexp test
		val {exp=thenexp, ty=tythen} = trexp then'
		val {exp=elseexp, ty=tyelse} = trexp else'
	    in
		if tipoReal tytest=TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
		else error("Error de tipos en if" ,nl)
	    end
	  | trexp(IfExp({test, then', else'=NONE}, nl)) =
	    let val {exp=exptest,ty=tytest} = trexp test
		val {exp=expthen,ty=tythen} = trexp then'
	    in
		if tipoReal tytest=TInt andalso tythen=TUnit then {exp=(), ty=TUnit}
		else error("Error de tipos en if", nl)
	    end
	  | trexp(WhileExp({test, body}, nl)) =
	    let
		val ttest = trexp test
		val tbody = trexp body
	    in
		if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
		else if tipoReal (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
		else error("El cuerpo de un while no puede devolver un valor", nl)
	    end
	  | trexp(ForExp({var, lo = e1, hi = e2, body = e3, ...}, nl)) =
	    (* NOSOTROS *)
            let
                val {ty = typeLo, ...} = trexp e1
                val {ty = typeHi, ...} = trexp e2
                val venv' = tabInserta (var,IntReadOnly,venv)
                val {ty = typeBody, ...} = transExp (venv', tenv) e3
            in
                if(not((tiposIguales typeLo typeHi) andalso (tiposIguales TInt typeLo)))
                then error("Expresiones en for, NO enteras",nl)
                else
                    if(not(tiposIguales typeBody TUnit))
                    then error("Cuerpo del for no es de tipo Unit",nl)
                    else
                        {exp = (), ty = TUnit}
            end
	  | trexp(LetExp({decs, body}, _)) =
	    let
		val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
		val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
	    in 
		{exp=(), ty=tybody}
	    end
	  | trexp(BreakExp nl) =
            (*NOSOTROS*)
	    {exp=(), ty=TUnit}
	  | trexp(ArrayExp({typ, size = e1, init = e2}, nl)) =
            (*NOSOTROS*)
            let
                val _ = (print("2º entorno: "); prTenv tenv)
                
                val {ty = typeSize, ...} = trexp e1
                val {ty = typeInit, ...} = trexp e2 (* la expresion init siempre existe?, puede ser cualquier tipo? *)

                

                val (t,u) = (case tabBusca (typ,tenv) of
                                 SOME (TArray (t,u)) => (t,u)
                               | SOME tt => error("se esperaba tipo array y "^typ^" no es array",nl)
                               | NONE => error(typ^" no esta definido",nl))
                val _ = if(not(tiposIguales typeSize TInt)) then
                            error("Tamaño NO es entero en arreglo",nl)
                        else
                            if(not(tiposIguales typeInit t)) then
                                error("Tipo init no coincide con tipo del arreglo",nl)
                            else ()
            in
                {exp = (), ty = TArray(typeInit,u)}
            end
	and trvar(SimpleVar s, nl) =
            (* NOSOTROS *)
            let
		val varType =
		    case tabBusca (s, venv) of
			SOME (Var {ty = t}) => t
                      | SOME (IntReadOnly) => TInt
                      | SOME _ => error ("Variable inválida", nl)
		      | NONE => error("Variable inexistente", nl)
            in
		{exp=(), ty=varType}
            end
	  | trvar(FieldVar(v, s), nl) =
            (*NOSOTROS*)
            let
                val {ty = typeVar, ...} = trvar (v,nl)
            in
                (case typeVar of
                     TRecord (xs,_) =>
                     (case List.find(fn (nameMember,_,_) => nameMember = s) xs of
                          SOME (_,t,_) => {exp = (), ty = t}
                        | NONE => error("Record: miembro inexistente",nl))
                   | _ => error("Record: no es un record",nl))
            end
	  | trvar(SubscriptVar(v, e), nl) =
	    (*NOSOTROS*)
            let
                val {ty = typeExp, ...} = trexp e
                val {ty = typeVar, ...} = trvar (v,nl)
            in
                if (not(tiposIguales typeExp TInt)) then
                    error("La expresion no es de tipo Int",nl)
                else
                    case typeVar of
                        TArray (t,unique) => {exp = (), ty = t}
                      | _ => error("Se intenta acceder a algo que no es un arreglo",nl)
                
            end
        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
	    (*NOSOTROS*)
            let
                val {ty = typeExp, ...} = trexp init
                val venv' = tabInserta(name,Var {ty=typeExp},venv)
            in
                (venv',tenv,[]) 
            end
	  | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let
                val _ = (print("1º entorno: "); prTenv tenv)
                val {ty = typeExp, ...} = trexp init
                val typeVar = (case tabBusca (s,tenv) of
                                   SOME t => t
                                 | NONE => error ("El tipo "^s^" no esta definido\n", pos))
            (*   SOME (Var {ty = t}) => t *)
            (* | SOME IntReadOnly => error("Variable de solo lectura",pos) *)
            (* | SOME (Func _) => error("Tipo funcion",pos)  *)
            (* | NONE => raise Fail ("Error -- línea "^Int.toString(pos)^": El tipo "^s^" no esta definido\n") *)
                val _ = (print (showT typeVar) ; print (" ") ; print (showT typeExp))
                        
            in
                if (not(tiposIguales typeExp typeVar)) then
                    error("VarDec: tipo de expresion incorrecta",pos)
                else
                    let
                        val venv' = tabInserta(name,Var {ty=typeExp},venv)
                    in
                        (venv',tenv,[])
                    end
            end
	  | trdec (venv,tenv) (FunctionDec fs) =
            (*NOSOTROS*)
            let (* checkNames devuelve el numero de linea en que se dio el error *)
                fun checkNames [] = ~1
                    | checkNames (( {name=n,...} , nl)::xs) =
                      let 
                          val res = List.all (fn ({name=m,...},_) => m <> n) xs
                      in
                      if res then
                          checkNames xs
                      else
                          nl
                      end
                val nl = checkNames fs
                val _ = if (nl <> ~1) then error("mas de una funcion con el mismo nombre",nl) else ()
                
                (* esta funcion toma un record de la forma {name: symbol, escape: bool ref, typ: ty} y devuelve una tupla de la forma (string, Tipo, int) *)
                (* fun genRecordTuple (r as {name = s, typ = t, ...}) = let val t1 = genTipo r *)
                (*                                                      in (s, t1, 0) end *)
 
                (* esta funcion toma un record de la forma {name: symbol, escape: bool ref, typ: ty} y devuelve un elemento de tipo Tipo*)
                fun genTipo {name = s, typ = t, ...} =
                    let val tTipo = (case t of
                                         NameTy n => (case tabBusca (n,tenv) of
                                                          NONE => raise Fail ("Argumento de tipo no declarado en la funcion: "^s)
                                                        | SOME ttipo => ttipo)
                                       | _ => raise Fail ("Tipo del argumento inválido"))
                    in (s,tTipo) end
                fun putVars ([], env) = env  
                  | putVars (((s,vtype)::xs), env) = tabRInserta(s, Var {ty = vtype}, putVars (xs,env))
                fun putFuncs ([], env) = env  
                  | putFuncs (((s,ftype)::xs), env) = tabRInserta(s, ftype, putFuncs (xs,env))
                (* esta funcion la utilizaremos para agregar cada una de las funciones de fs a venv *)
                fun genEnvEntry  ({name = s, params = ps, result = NONE, body = exp}, pos) =
                    let val fmlPairs = map genTipo ps
                        val venv' = putVars (fmlPairs,venv)
                        val {ty = tBody, ...} = transExp (venv',tenv) exp
                        val fmls = map (#2) fmlPairs
                    in 
                        if not(tiposIguales TUnit tBody) then
                            error("Error de tipo en el retorno", pos)
                        else
                            (s,Func {level = (), label = tigertemp.newlabel()^s, formals = fmls, result = TUnit, extern = false})
                    end
                  | genEnvEntry ({name = s, params = ps, result = (SOME n), body = exp}, pos) =
                    let
                        val ttipo = (case tabBusca (n,tenv) of
                                        NONE => error("Tipo de funcion no declarado", pos)
                                      | SOME t => t)
                        val fmlPairs = map genTipo ps
                        val venv' = putVars (fmlPairs,venv)
                        val {ty = tBody, ...} = transExp (venv',tenv) exp
                        val fmls = map (#2) fmlPairs
                    in
                        if not(tiposIguales ttipo tBody) then
                            error("Error de tipo en el retorno", pos)
                        else
                            (s,Func {level = (), label = tigertemp.newlabel()^s, formals = fmls, result = TUnit, extern = false})
                    end
                val envEntryList = map genEnvEntry fs
                val venv' = putFuncs (envEntryList,venv)
            in
                (venv', tenv, [])
            end
	  | trdec (venv,tenv) (TypeDec ts) =
            (*NOSOTROS*)
            let
                val firstNL = (#2(hd ts))

                fun buscaArrRecords lt =
                    let fun buscaRecs [] recs = recs
                          | buscaRecs ((r as {name, ty = RecordTy _}) :: t) recs = buscaRecs t (r :: recs)
                          | buscaRecs ((r as {name, ty = ArrayTy _}) :: t) recs = buscaRecs t (r ::recs)
                          | buscaRecs (_ :: t) recs = buscaRecs t recs
                    in buscaRecs lt [] end

                fun genPares lt =
                    let
                        val lrecs = buscaArrRecords lt
                        fun genP [] res = res
                           |genP ({name, ty = NameTy s} :: t) res =
                            genP t ((s,name)::res)
                           |genP ({name, ty = ArrayTy s} :: t) res =
                            genP t ((s,name) :: res)
                           |genP ({name,ty = RecordTy lf} :: t) res =
                            let fun recorre ({typ = NameTy x, ...} :: t) =
                                    (case List.find ((op = rs x) o #name) lrecs  of
                                         SOME _ => recorre t
                                        |_ => x :: recorre t)
                                  | recorre (_ :: l) = recorre l
                                  | recorre [] = []
                                val res' = recorre lf
                                val res'' = List.map (fn x => (x,name)) res'
                            in genP t (res'' @ res) end
                    in
                        genP lt []
                    end

                (* procesa lista ordenada, no procesa Arrays ni Records *)
                fun procesaInicial [] decs recs env = env
                  | procesaInicial (sorted as (h::t)) decs recs env =
                    let
                        fun filt h {name, ty=NameTy t} = h = t
                          | filt h {name, ty=ArrayTy t} = h = t
                          | filt h {name, ty=RecordTy lt} = List.exists (fn {name, ...} => h = name) lt
                        val (ps,ps') = List.partition (filt h) decs
                        val ttopt = case List.find (fn {name,ty} => name = h) recs of
                                        SOME _ => NONE
                                      | NONE => (case tabBusca(h, env) of
                                                     SOME t => SOME t
                                                   | _ => raise error (h^" Tipo inexistente", firstNL))
                        val env' = case ttopt of
                                       SOME tt => List.foldr (fn ({name, ty=NameTy _}, env) => tabInserta(name, tt, env)
                                                             | (_, env) => env) env ps
                                     | _ => env
                    in procesaInicial t ps' recs env' end
                        
                (* procesa records y arrays *)
                fun procRecordsArrays recs env =
                    let
                        fun buscaEnv env' t =
                            case tabBusca(t, env) of
                                SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                              | SOME tt => tt
                              | _ => (case tabBusca(t, env') of
                                          SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                        | SOME tt => tt
                                        | _ => case List.find (fn {name, ...} => name = t) recs of
                                                   SOME {name, ...} => TTipo(name, ref NONE)
                                                 | _ => error (t^" Tipo inexistente", firstNL))
                        fun precs [] env' = env'
                          | precs ({name, ty=RecordTy lf} :: t) env' =
                            let
                                val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                                     | (_, l) => l) [] lf
                                val (_, lf'')= List.foldl (fn ((x,y),(n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf'
                                val env'' = tabInserta (name, TRecord (lf'', ref ()), env')
                            in precs t env'' end

                          | precs ({name, ty=ArrayTy ty} :: t) env' =
                            precs t (tabInserta (name, TArray (buscaEnv env' ty, ref ()), env'))

                          | precs _ _ = error ("Error interno: Proceso de Records", firstNL)
                    in precs recs (fromTab env) end
                        
                (* reemplaza los tipos "punteros" a NONE, por punteros al record del cual son miembros *)
                fun fijaNONE [] env = env                  
                  (*No se daría nunca*)
                  | fijaNONE ((name, TArray (TTipo (s, ref NONE), u)) :: t) env =
                    (case tabBusca(s, env) of
                         SOME (r as (TRecord _)) => fijaNONE t (tabRInserta (name, TArray (TTipo (s, ref (SOME r)), u) , env))
                       | _ => error (s^" Tipo inexistente", firstNL))

                  | fijaNONE ((name, TRecord (lf, u)) :: t) env =
                    let
                        (* fun busNONE ((s, TTipo (t, ref NONE), u), l) =
                            ((s, TTipo (t, ref (SOME (tabSaca (t, env)))), u) :: l) *)
                        fun busNONE ((s, TTipo (t, r), u), l) = 
                            (case !r of
                                 NONE => let val _ = r := SOME (tabSaca (t, env))
                                         in (s, TTipo (t,r), u) :: l end
                               | SOME e => (s, TTipo (t, r), u) :: l)
                          | busNONE (d, l) = d :: l
                        val lf' = List.foldl busNONE [] lf
                    in fijaNONE t (tabRInserta(name, TRecord (lf', u), env)) end
                  | fijaNONE (_ :: t) env = fijaNONE t env
                                                   
                (* ?????? Consulta. *)
                (* fun fijaRecords decs env = *)
                (*     let *)
                (*         fun buscaEnv t = *)
                (*             case tabBusca (t, env) of *)
                (*                 SOME t' => t' *)
                (*               | _ => error (t^" Tipo inexistente", firstNL) *)
                                           
                (*         fun fija1 (name, TTipo (s, ref NONE), i) = *)
                (*             (name, TTipo (s, ref (SOME (buscaEnv s))), i) *)
                (*           | fija1 (name, TRecord (lf, u), i) = *)
                (*             let *)
                (*                 val (nr, r) = valOf (List.find (fn (_,TRecord (_, u')) => u = u' *)
                (*                                                | _ => false) decs) *)
                (*             in (name, TTipo (nr, ref (SOME r)), i) end *)
                (*           | fija1 x = x *)
                                          
                (*         fun fija (name, TRecord (lf, u)) =  *)
                (*             (name, TRecord (List.map fija1 lf, u))  *)
                (*           | fija x = x *)
                (*     in List.map fija decs end *)
                                                   
                (* Fija tipos en un batch *)
                fun fijatipos batch env =
                    let
                        val pares = genPares batch
                        val ordered = topsort.topsort pares
                        
                        val _ = (print("El topsort devuelve: "); printList(ordered))
                        
                        val recs = buscaArrRecords batch
                        val env' = procesaInicial ordered batch recs env

                        val _ = (print("Tabla en el 1º procesa: ") ; printTab (env'); print("\n"))
                        val env'' = procRecordsArrays recs env'
                        val _ = (print("Tabla en el 2º procesa: ") ; printTab (env''); print("\n"))
                        
                        val env'''= fijaNONE (tabAList env'') env''
                                                
                    in env''' end
            in
                let
                    val tenv' = fijatipos (map (#1) ts) tenv
                    val _ = (print("Tabla: ") ; prTenv tenv')
                in
                    (venv, tenv', [])
                end
            end
    in trexp end

fun transProg ex =
    let	val main =
	    LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
					result= SOME "int", body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) main
	(* val _ = transExp(tab_vars, tab_tipos) ex (\* despues hay que cambiarlo *\) *)
    in	print "bien!\n" end
end
