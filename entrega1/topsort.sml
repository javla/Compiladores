(*Operaciones básicas agregadas de la carpeta*)

infix -- ---
infix rs ls

fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun l -- e = List.filter (op <> rs e) l
fun fst (x, _) = x and snd (_, y) = y
fun lp --- e = List.filter ((op <> rs e) o fst) lp

open tigerabs

exception Ciclo


local (* Sort topolo'gico *)
	fun cmp(x, y) = x=y
	fun mem(x, []) = false
	| mem(x, y::l) = cmp(x, y) orelse mem(x, l)
	fun nexts(a, []) = []
	| nexts(a, (x, y)::pairs) =
		if cmp(a, x) then y::nexts(a, pairs) else nexts(a, pairs)
in
	fun topsort graph =
		let	fun sort([], path, visited) = visited
			| sort(x::xs, path, visited) =
				if mem(x, path) then raise Fail "ciclo!"
				else sort(xs, path,
						if mem(x, visited) then visited
						else x::sort(nexts(x, graph), x::path, visited))
			val (starts, _) = ListPair.unzip graph
		in	sort(starts, [], []) end
end
(*
(* 3 *)
(* a esto hay que mejorarlo mucho! *)
fun integraTEnvs(env, env') =
	let	val res = fromTab env
		fun aux(c, v) = tabRInserta(c, v, res)
	in
		tabAplica(aux, env');
		res
	end
(*------------------------------*)

fun muestra(s, t)=
	let	fun aux(NameTy t) = print("NameTy "^t)
		| aux(ArrayTy t) = print("ArrayTy "^t)
		| aux(RecordTy l) =
			let	fun f{name, typ,...} =
					(print(name^" "); aux typ)
			in
				(print "RecordTy "; app f l)
			end
	in
		print s; print "    "; aux t; print "\n"
	end
fun string2Ty(s, t) = (NameTy s, t)
val t = colectaNameTy prueba
val l = List.map string2Ty (tabAList t);
val r = topsort l;
*)

(*Copio la generacíon de pares de la carpeta*)
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

(*La copie mal, asi que esto está mal*)
(* fun topsort p = *)
(*     let *)
(*         fun candidato p e = *)
(*             List.filter (fn e => List.all ((op <> rs e) o  snd) p) *)
(*         fun tsort p [] res = rev res *)
(*           | tsort [] st res = rev (st @ res) *)
(*           | tsort p (st as (h :: t)) res = *)
(*             let val x = (hd (candidato st p )) *)
(*                         handle Empty => raise Ciclo *)
(*             in tsort (p --- x) (st -- x) (x :: res) end *)
(*         fun elementos lt = *)
(*             List.foldr (fn (x,y,l) => *)
(*                              let val l1 = case List.find (op = rs x) l of *)
(*                                               NONE => x :: l | _ => l *)
(*                                  val l2 = case List.find (op = rs y) l1 of *)
(*                                               NONE => y :: l | _ => l1 *)
(*                              in l2 end) [] lt *)
(*     in tsort p (elementos p) [] *)
(*     end *)
