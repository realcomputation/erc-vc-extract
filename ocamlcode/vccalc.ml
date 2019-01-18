open Ast
open Context
open Typing
open Logic
open Reduction
open Exporter
open Errors
open Log
open Utilities
open Loader





(* print a predicate which exactly defines semantic of t under ctx *)
let rec hfun_sem (t : termtree) (ctx : (string, data_type) Hashtbl.t) : foltree =
	match termtree_type t ctx with
	| None -> raise (EngineErr "predicate semantic extraction ill-typed1")
	| Some dtype ->
	(	
		match t with
		|	Variable s -> Identity (AInput, AVariable s)
		|   Const z -> Identity (AInput, AZConst z)
		|   RConst r -> Identity (AInput, ARConst r)

		(* exists w1 w2, @ = w1*w2 /\ h(r1)(w1) /\ h(r2)(w2) *)
		|   Mult (r1, r2) -> 
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		(ExistensialQ(v1, Real, ExistensialQ(v2, Real, 
			Conjunction(
				Identity(AInput, AMult(AVariable v1, AVariable v2)), 
			Conjunction(
				fol_application (hfun_sem r1 ctx) (AVariable v1), 
				fol_application (hfun_sem r2 ctx) (AVariable v2))))))

		(* exists w, @ * w = 1 /\ h(r)(w) *)
		|   Div r ->
		let v = ("_v"^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		(ExistensialQ(v, Real, 
			Conjunction(
				Identity(ARConst(1), AMult(AInput, AVariable v)),
				fol_application (hfun_sem r ctx) (AVariable v))))

		(* exists w1 w2, @ = w1 + w2 /\ h(t1)(w1) /\ h(t2)(w2) *)
		|   Plus (t1, t2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			(freshvar := !freshvar+2);
			(ExistensialQ(v1, dtype, ExistensialQ(v2, dtype, 
				Conjunction(
					Identity(AInput, APlus(AVariable v1, AVariable v2)), 
				Conjunction(
					fol_application (hfun_sem t1 ctx) (AVariable v1), 
					fol_application (hfun_sem t2 ctx) (AVariable v2))))))


		(* exists w, @ = - w /\ h(t)(w) *)
		|   Minus t ->
			let v = ("_v"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			(ExistensialQ(v, dtype, 
				Conjunction(
					Identity(AInput, AMinus (AVariable v)), 
					fol_application (hfun_sem t ctx) (AVariable v))))

	(* @=1 /\ exists w1 w2, h(z1)(w1) /\ h(z2)(w2) /\ w1 = w2 
   \/  @=0 /\ exists w1 w2, h(z1)(w1) /\ h(z2)(w2) /\ w1 <> w2
	 *)

		|  Eq (z1, z2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			let v3 = ("_v"^(string_of_int (!freshvar +3))) in
			let v4 = ("_v"^(string_of_int (!freshvar +4))) in
			(freshvar := !freshvar+4);
			Disjunction(
				Conjunction(
					Identity(AInput, AZConst 1),
				Conjunction(
					ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
						Conjunction(
							fol_application (hfun_sem z1 ctx) (AVariable v1),
							fol_application (hfun_sem z2 ctx) (AVariable v2)))),
					Identity(AVariable v1, AVariable v2))),

				Conjunction(
					Identity(AInput, AZConst 0),
				Conjunction(
					ExistensialQ(v3, Int, ExistensialQ(v4, Int, 
						Conjunction(
							fol_application (hfun_sem z1 ctx) (AVariable v3),
							fol_application (hfun_sem z2 ctx) (AVariable v4)))),
					Neg (Identity(AVariable v1, AVariable v2)))))
		
	(*  forall w1 w2, (h(r1)(w1)/\h(r2)(w2) -> (w1=w2->False)) /\
		/\ v=1 /\ exists w1 w2, h(r1)(w1) /\ h(r2)(w2) /\ w1 > w2
		/\ v=0 /\ exists w1 w2, h(r1)(w1) /\ h(r2)(w2) /\ w1 < w2



	{v : forall v1 v2, (h(r1)(v1)/\h(r2)(v2) -> (v1 <> v2) /\
			((v=1/\exists v1 v2, v1>v2/\h(r1)(v1)/\h(r1)(v1)) \/ 
			(v=0/\exists v1 v2, v1<v2/\h(r1)(v1)/\h(r2)(v2))) } *)	
		|   Gt (r1, r2) ->
			let v3 = ("_v"^(string_of_int (!freshvar +1))) in
			let v4 = ("_v"^(string_of_int (!freshvar +2))) in
			let v5 = ("_v"^(string_of_int (!freshvar +3))) in
			let v6 = ("_v"^(string_of_int (!freshvar +4))) in
			(freshvar := !freshvar+4);
			Disjunction(
				Conjunction(
					Identity(AInput, AZConst 1), 
						ExistensialQ(v3, dtype, ExistensialQ(v4, dtype, 
							Conjunction(
								Greater(AVariable v3,AVariable v4), 
							Conjunction(
								fol_application (hfun_sem r1 ctx) (AVariable v3), 
								fol_application (hfun_sem r2 ctx) (AVariable v4)))))),
						
				Conjunction(
					Identity(AInput, AZConst 0), 
						ExistensialQ(v5, dtype, ExistensialQ(v6, dtype, 
							Conjunction(
								Greater(AVariable v6, AVariable v5), 
							Conjunction(
								fol_application (hfun_sem r1 ctx) (AVariable v5), 
								fol_application (hfun_sem r2 ctx) (AVariable v6)))))))

	(*  {v : v=1 /\ h(t)(0) \/ v=0 /\ (exists z, (z!=0) /\ (h(t)(z)))}*)
		|   Neg z -> 
			let v = ("_v"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			Disjunction (
				Conjunction (
					Identity (AInput, AZConst 1), fol_application (hfun_sem z ctx) (AZConst 0)),
					Conjunction (
						Identity (AInput, AZConst 0), 
						ExistensialQ(v, Int, Conjunction (fol_application (hfun_sem z ctx) (AVariable v),  Neg (Identity (AVariable v, AZConst 0))))))

	(*  {v : (v=1 /\ exists z1 z2, z1 neq 0 /\ z2 neq 0 /\ h(t1)(z1) /\ h(t2)(z2)

			v = 0 /\ h(t1)(0) \/ h(t2)(0) /\ (
				(forall z1, h(t1)(z1) -> z1 = 0 /\ forall z2, h(t2)(z2) -> z2 = 0
				\/ exists z1 z2, h(t1)(z1) /\ h(t2)(z2)  
			)
				  /\ (forall z1, h(t1)(z1) -> z1 neq 0 /\ forall z2, h(t2)(z2) -> z2 neq 0 
				  	\/ exists z1 z2, )
	
) \/ (v=0 /\ h(t1)(0) \/ h(t2)(0))} *)
 	|   And (z1, z2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			(freshvar := !freshvar+2);
			Disjunction(
				Conjunction(
					Identity (AInput, AZConst 1),
					ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
						Conjunction(Neg (Identity(AVariable v1, AZConst 0)),
							Conjunction(Neg (Identity(AVariable v2, AZConst 0)),
								Conjunction(
									fol_application (hfun_sem z1 ctx) (AVariable v1),
									fol_application (hfun_sem z2 ctx) (AVariable v2))))))),
				Conjunction(Identity(AInput, AZConst 0),
						Disjunction(
							fol_application (hfun_sem z1 ctx) (AZConst 0),
							fol_application (hfun_sem z2 ctx) (AZConst 0))))

	(*  {v : ((v=1 /\ exists z1 z2, (z1 neq 0 /\ z2 neq 0) /\ (h(t1)(z1) \/ h(t2)(z2))) \/ (v=0 /\ h(t1)(0) /\ h(t2)(0))} *)
	|   Or (z1, z2) -> 
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			(freshvar := !freshvar+2);
			Disjunction(
				Conjunction(
					Identity (AInput, AZConst 0),
						Conjunction(
							fol_application (hfun_sem z1 ctx) (AZConst 0),
							fol_application (hfun_sem z2 ctx) (AZConst 0))),
				Conjunction(
					Identity(AInput, AZConst 1),
					ExistensialQ(v1, Int, ExistensialQ(v2, Int,
						Conjunction(
							 		Neg (Identity (AVariable v1, AZConst 0)),
						Conjunction(Neg (Identity (AVariable v2, AZConst 0)),
							Disjunction(
								fol_application (hfun_sem z1 ctx) (AVariable v1),
								fol_application (hfun_sem z2 ctx) (AVariable v2))))))))





(*	Primitive functions *)
(*  {v : (v = 0 /\ exists k, h(t1)(k)) \/ (v=1 /\ exists k, h(t1)(k))}  *)
	| Select tl ->
		hfun_sem_sel 0 tl ctx

(*  {v : exists n, v = prec n /\ h(t)(n) *)
	|   Iota t ->
		let v = ("_v"^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		ExistensialQ(v, Int, Conjunction (Identity (AInput, Prec (AVariable v)), fol_application (hfun_sem t ctx) (AVariable v)))

(*  {v : exists v1, v2 : Z, h(t1)(v1) /\ h(t2)(v2) /\ ((v1 > v2 /\ v = v1) \/ (v1 = v2 /\ v = v1) \/ (v2 > v1 /\ v = v2)) *)
 	|   Max (t1, t2) -> 
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		(match dtype with
			| Int -> 
				ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
					Conjunction(Conjunction(fol_application (hfun_sem t1 ctx) (AVariable v1), fol_application (hfun_sem t2 ctx) (AVariable v2)),
								Disjunction(Conjunction(Greater(AVariable v1,AVariable v2), Identity(AInput, AVariable v1)),
									Disjunction(Conjunction(Identity(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
												Conjunction(Greater(AVariable v2, AVariable v1), Identity(AInput, AVariable v2)))))))

			| Real ->
				ExistensialQ(v1, Real, ExistensialQ(v2, Real, 
					Conjunction(Conjunction(fol_application (hfun_sem t1 ctx) (AVariable v1), fol_application (hfun_sem t2 ctx) (AVariable v2)),
								Disjunction(Conjunction(Greater(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
									Disjunction(Conjunction(Identity(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
												Conjunction(Greater(AVariable v2, AVariable v1), Identity(AInput, AVariable v2)))))))
			| _ -> raise (EngineErr "ill typed")
		)


(*  {v : \w. 
			(exists v1. h(t1)(v1) /\ v <> 0) -> (exists v2. h(t2)(v2))
			(h(t1)(0) -> (exists v3. h(t3)(v3))
				exists v4. w = v4 /\ h(t2)(v4) /\ exists v5. h(t1)(v1) /\ v1 <> 0
			\/	exists v6. w = v6 /\ h(t3)(v6) /\ h(t1)(0)
			\/	Neg (exists v7. h(t1)(v7)) /\ exists v8. w=v8 /\ h(t2)(v8) /\ h(t3)(v8) /\ forall v9. h(t2)(v8) /\ h(t3)(v8) -> v7 = v8

	(exists v1 v2, (h(t1)(v1) /\ v1 ~= 0 /\ h(t2)(v)) \/ (h(t3)(v) /\ h(t1)(0))  *)
 	|   Inlinecond (t1,t2,t3) ->
		let d = dtype in
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		let v3 = ("_v"^(string_of_int (!freshvar +3))) in
		let v4 = ("_v"^(string_of_int (!freshvar +4))) in
		let v5 = ("_v"^(string_of_int (!freshvar +5))) in
		let v6 = ("_v"^(string_of_int (!freshvar +6))) in
		let v7 = ("_v"^(string_of_int (!freshvar +7))) in
		let v8 = ("_v"^(string_of_int (!freshvar +8))) in
		let v9 = ("_v"^(string_of_int (!freshvar +9))) in
		(freshvar := !freshvar+9);
		let l1 = Implication(ExistensialQ(v1, Int, Conjunction(fol_application (hfun_sem t1 ctx) (AVariable v1), Neg(Identity (AZConst 0, AVariable v1)))), 
							ExistensialQ(v2, d, fol_application (hfun_sem t2 ctx) (AVariable v2))) in
		let l2 = Implication(fol_application (hfun_sem t1 ctx) (AZConst 0), ExistensialQ (v3, d, fol_application (hfun_sem t3 ctx) (AVariable v3))) in
		let l3 = Conjunction(ExistensialQ(v4, d, Conjunction(Identity(AInput, AVariable v4), fol_application (hfun_sem t2 ctx) (AVariable v4))),
							ExistensialQ(v5, Int, Conjunction(fol_application (hfun_sem t1 ctx) (AVariable v5), Neg (Identity (AZConst 0, AVariable v5))))) in
		let l4 = Conjunction(ExistensialQ(v6, d, Conjunction(Identity(AInput, AVariable v6), fol_application (hfun_sem t3 ctx) (AVariable v6))),
							fol_application (hfun_sem t1 ctx) (AZConst 0)) in
		let l5 = Conjunction(Neg(ExistensialQ(v7, Int, fol_application (hol_semantic t1 ctx) (AVariable v7))),
							ExistensialQ(v8, d, 
												Conjunction(
												Conjunction(Identity(AInput, AVariable v8), 
												Conjunction(fol_application (hol_semantic t2 ctx) (AVariable v8),
															fol_application (hol_semantic t3 ctx) (AVariable v8))),
												UniversialQ(v9, d, Implication(
																	Conjunction(fol_application (hol_semantic t2 ctx) (AVariable v9),
																				fol_application (hol_semantic t3 ctx) (AVariable v9)),
																	Identity(AVariable v8, AVariable v9)))))) in 
		Conjunction(l1, Conjunction(l2, Disjunction(l3, Disjunction(l4, l5))))



(*	ETC *)
(* X[t] = {v : (exists n, v = \pi_n T /\ h(t)(n)) /\ forall n, h(t)(n) -> 0<= n < d(T) } *)
	|   Access (s, t) -> 
						let v1 = ("_v"^(string_of_int (!freshvar +1))) in
						(freshvar := !freshvar+1);
						if Hashtbl.mem ctx s then
						(match Hashtbl.find ctx s with
						| Inta d -> 
							ExistensialQ(v1, Int, Conjunction(Identity(AProjection (AVariable s, AVariable v1), AInput), 
														fol_application (hfun_sem t ctx) (AVariable v1)))
						| Reala d ->
							ExistensialQ(v1, Int, Conjunction(Identity(AProjection (AVariable s, AVariable v1), AInput), 
														fol_application (hol_semantic t ctx) (AVariable v1)))

						| _ -> raise (EngineErr "ill typed")
						)
					else raise (EngineErr "ill typed")

(* if s is single valued
	v => exists z1, ..., zd. v = f(z1,...,zd) /\ h(ti)(zi) /\ /\_i p_i->q_i /\
	     forall z1, ..., zd. \/_i p_i



 *)
	|   Application (s, tl) -> 

		if Hashtbl.mem mfun s then
		begin
			(* list of fresh typed variables *)
			let tvs = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error occrued")) in
			(* conjunctive form of that tvs satisfies h(zi)(tvs_i) *)
			let term1 = list_to_conj (bind_list tvs (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			(* /\ p_i -> q_i *)
			let term3 = list_to_conj (impl_list (Hashtbl.find mfunfol s)) in
			(* list of strings of tvs *)
			let names = snd (split_list (snd (split_list tvs))) in
			(* p_i -> q_i [@i -> z_i] *)
			let nterm = fol_replace_list term3  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find mfun s)) 1))) (bind_list names (fun k -> AVariable k))) in
			let firstpart = 
			existence_from_list (snd (split_list tvs)) (Conjunction(term1, fol_replace nterm "@res" AInput)) in


(* 			let tvs2 = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (PlainError "")) in
			let term12 = list_to_conj (bind_list tvs2 (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in *)
			let term22 = list_to_disj (fst (split_list (Hashtbl.find mfunfol s))) in 
(* 			let names2 = snd (split_list (snd (split_list tvs2))) in
 *)
			let mterm = fol_replace_list term22  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find mfun s)) 1))) (bind_list names (fun k -> AVariable k))) in
			
(* 			let lastpart =
			universial_from_list (snd (split_list tvs2)) (mterm) in  *)
			Conjunction(firstpart, mterm)
		end
		else
		if Hashtbl.mem sfun s then
		begin
			let tvs = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error occured")) in
			let term1 = list_to_conj (bind_list tvs (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			let names = snd (split_list (snd (split_list tvs))) in
			let firstpart = existence_from_list (snd (split_list tvs)) (Conjunction(term1, 
															Identity(AInput,
																AApplication(s, bind_list names (fun k -> AVariable k))))) in 
			
(* 			let tvs2 = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (PlainError "")) in
			let term12 = list_to_conj (bind_list tvs2 (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
 *)			let term22 = list_to_disj (fst (split_list (Hashtbl.find sfunfol s))) in 
(* 			let names2 = snd (split_list (snd (split_list tvs2))) in
 *)			let mterm = fol_replace_list term22  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find sfun s)) 1))) (bind_list names (fun k -> AVariable k))) in
(* 			let lastpart =
			universial_from_list (snd (split_list tvs2)) (mterm) in 
 *)			
			Conjunction(firstpart, mterm)			


		end
		else raise (EngineErr "error occured")


(* {v : v = 1 /\ exists k, h(z)(k) /\ forall k, h(z)(k) -> k <> 0*)
	|   Test (z) -> 
		let v1 = ("_test"^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		Conjunction(
			Identity(AInput, AZConst 1), 
			ExistensialQ(v1, Int, Conjunction (fol_application (hfun_sem z ctx) (AVariable v1),
			Neg (Identity (AVariable v1, AZConst 0)))))
								
)



(* print a predicate which exactly defines semantic of t under ctx *)
and hol_semantic (t : termtree) (ctx : (string, data_type) Hashtbl.t) : foltree =
	match termtree_type t ctx with
	| None -> 	raise (EngineErr "predicate semantic extraction ill-typed")
	| Some dtype ->
	(	
		match t with
		|	Variable s -> Identity (AInput, AVariable s)
		|   Const z -> Identity (AInput, AZConst z)
		|   RConst r -> Identity (AInput, ARConst r)

		(* exists w1 w2, @ = w1*w2 /\ h(r1)(w1) /\ h(r2)(w2) *)
		|   Mult (r1, r2) -> 
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		(ExistensialQ(v1, Real, ExistensialQ(v2, Real, 
			Conjunction(
				Identity(AInput, AMult(AVariable v1, AVariable v2)), 
			Conjunction(
				fol_application (hol_semantic r1 ctx) (AVariable v1), 
				fol_application (hol_semantic r2 ctx) (AVariable v2))))))

		(* exists w, @ * w = 1 /\ h(r)(w) *)
		|   Div r ->
		let v = ("_v"^(string_of_int (!freshvar +1))) in
		let w = ("_v"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		Conjunction(
			(ExistensialQ(v, Real, 
				Conjunction(
					Identity(ARConst(1), AMult(AInput, AVariable v)),
					fol_application (hol_semantic r ctx) (AVariable v)))),
			(UniversialQ(w, Real, 
				Implication(
					fol_application (hol_semantic r ctx) (AVariable w),
					Neg (Identity (AVariable w, ARConst 0))))))

		(* exists w1 w2, @ = w1 + w2 /\ h(t1)(w1) /\ h(t2)(w2) *)
		|   Plus (t1, t2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			(freshvar := !freshvar+2);
			(match dtype with
				| Int ->
						(ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
							Conjunction(
								Identity(AInput, APlus(AVariable v1, AVariable v2)), 
							Conjunction(
								fol_application (hol_semantic t1 ctx) (AVariable v1), 
								fol_application (hol_semantic t2 ctx) (AVariable v2))))))
				| Real ->
						(ExistensialQ(v1, Real, ExistensialQ(v2, Real, 
							Conjunction(
								Identity(AInput, APlus(AVariable v1, AVariable v2)), 
							Conjunction(
								fol_application (hol_semantic t1 ctx) (AVariable v1), 
								fol_application (hol_semantic t2 ctx) (AVariable v2))))))
				
				| _ -> raise (EngineErr "ill typed")
			)

		(* exists w, @ = - w /\ h(t)(w) *)
		|   Minus t ->
			let v = ("_v"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			(match dtype with
				| Int ->
					(ExistensialQ(v, Int, 
						Conjunction(
							Identity(AInput, AMinus (AVariable v)), 
							fol_application (hol_semantic t ctx) (AVariable v))))
				| Real ->
					(ExistensialQ(v, Real, 
						Conjunction(
							Identity(AInput, AMinus (AVariable v)), 
							fol_application (hol_semantic t ctx) (AVariable v))))

				| _ -> raise (EngineErr "ill typed")
			)

	(* @=1 /\ exists w1 w2, h(z1)(w1) /\ h(z2)(w2) /\ w1 = w2 
   \/  @=0 /\ exists w1 w2, h(z1)(w1) /\ h(z2)(w2) /\ w1 <> w2
	 *)

		|  Eq (z1, z2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			let v3 = ("_v"^(string_of_int (!freshvar +3))) in
			let v4 = ("_v"^(string_of_int (!freshvar +4))) in
			(freshvar := !freshvar+4);
			Disjunction(
				Conjunction(
					Identity(AInput, AZConst 1),
				Conjunction(
					ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
						Conjunction(
							fol_application (hol_semantic z1 ctx) (AVariable v1),
							fol_application (hol_semantic z2 ctx) (AVariable v2)))),
					Identity(AVariable v1, AVariable v2))),

				Conjunction(
					Identity(AInput, AZConst 0),
				Conjunction(
					ExistensialQ(v3, Int, ExistensialQ(v4, Int, 
						Conjunction(
							fol_application (hol_semantic z1 ctx) (AVariable v3),
							fol_application (hol_semantic z2 ctx) (AVariable v4)))),
					Neg (Identity(AVariable v1, AVariable v2)))))
		
	(*  forall w1 w2, (h(r1)(w1)/\h(r2)(w2) -> (w1=w2->False)) /\
		/\ v=1 /\ exists w1 w2, h(r1)(w1) /\ h(r2)(w2) /\ w1 > w2
		/\ v=0 /\ exists w1 w2, h(r1)(w1) /\ h(r2)(w2) /\ w1 < w2



	{v : forall v1 v2, (h(r1)(v1)/\h(r2)(v2) -> (v1 <> v2) /\
			((v=1/\exists v1 v2, v1>v2/\h(r1)(v1)/\h(r1)(v1)) \/ 
			(v=0/\exists v1 v2, v1<v2/\h(r1)(v1)/\h(r2)(v2))) } *)	
		|   Gt (r1, r2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			let v3 = ("_v"^(string_of_int (!freshvar +3))) in
			let v4 = ("_v"^(string_of_int (!freshvar +4))) in
			let v5 = ("_v"^(string_of_int (!freshvar +5))) in
			let v6 = ("_v"^(string_of_int (!freshvar +6))) in
			(freshvar := !freshvar+6);
			Conjunction(
				UniversialQ(v1, Real, UniversialQ(v2, Real, 
					Implication (
						Conjunction (fol_application (hol_semantic r1 ctx) (AVariable v1), fol_application (hol_semantic r2 ctx) (AVariable v2)), 
						( Neg (Identity(AVariable v1, AVariable v2)))))),
				
				Disjunction(
					Conjunction(
						Identity(AInput, AZConst 1), 
							ExistensialQ(v3, Real, ExistensialQ(v4, Real, 
								Conjunction(
									Greater(AVariable v3,AVariable v4), 
								Conjunction(
									fol_application (hol_semantic r1 ctx) (AVariable v3), 
									fol_application (hol_semantic r2 ctx) (AVariable v4)))))),
							
					Conjunction(
						Identity(AInput, AZConst 0), 
							ExistensialQ(v5, Real, ExistensialQ(v6, Real, 
								Conjunction(
									Greater(AVariable v6, AVariable v5), 
								Conjunction(
									fol_application (hol_semantic r1 ctx) (AVariable v5), 
									fol_application (hol_semantic r2 ctx) (AVariable v6))))))))

	(*  {v : v=1 /\ h(t)(0) \/ v=0 /\ (exists z, (z!=0) /\ (h(t)(z)))}*)
		|   Neg z -> 
			let v = ("_v"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			Disjunction (
				Conjunction (
					Identity (AInput, AZConst 1), fol_application (hol_semantic z ctx) (AZConst 0)),
					Conjunction (
						Identity (AInput, AZConst 0), 
						ExistensialQ(v, Int, Conjunction (fol_application (hol_semantic z ctx) (AVariable v),  Neg (Identity (AVariable v, AZConst 0))))))

	(*  {v : (v=1 /\ exists z1 z2, z1 neq 0 /\ z2 neq 0 /\ h(t1)(z1) /\ h(t2)(z2)

			v = 0 /\ h(t1)(0) \/ h(t2)(0) /\ (
				(forall z1, h(t1)(z1) -> z1 = 0 /\ forall z2, h(t2)(z2) -> z2 = 0
				\/ exists z1 z2, h(t1)(z1) /\ h(t2)(z2)  
			)
				  /\ (forall z1, h(t1)(z1) -> z1 neq 0 /\ forall z2, h(t2)(z2) -> z2 neq 0 
				  	\/ exists z1 z2, )
	
) \/ (v=0 /\ h(t1)(0) \/ h(t2)(0))} *)
 	|   And (z1, z2) ->
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			let v3 = ("_v"^(string_of_int (!freshvar +3))) in
			let v4 = ("_v"^(string_of_int (!freshvar +4))) in
			let v5 = ("_v"^(string_of_int (!freshvar +5))) in
			let v6 = ("_v"^(string_of_int (!freshvar +6))) in
			(freshvar := !freshvar+6);
			Disjunction(
				Conjunction(
					Identity (AInput, AZConst 1),
					ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
						Conjunction(Neg (Identity(AVariable v1, AZConst 0)),
							Conjunction(Neg (Identity(AVariable v2, AZConst 0)),
								Conjunction(
									fol_application (hol_semantic z1 ctx) (AVariable v1),
									fol_application (hol_semantic z2 ctx) (AVariable v2))))))),
				Conjunction(Identity(AInput, AZConst 0),
					Disjunction(
						Disjunction(
							Conjunction(
								fol_application (hol_semantic z1 ctx) (AZConst 0),
								UniversialQ(v3, Int, Implication(fol_application (hol_semantic z1 ctx) (AVariable v3), Identity (AVariable v3, AZConst 0)))),
							Conjunction(
								fol_application (hol_semantic z2 ctx) (AZConst 0),
								UniversialQ(v4, Int, Implication(fol_application (hol_semantic z2 ctx) (AVariable v4), Identity (AVariable v4, AZConst 0))))),
						Conjunction(
							Conjunction(
								ExistensialQ(v5, Int, fol_application (hol_semantic z1 ctx) (AVariable v5)),
								ExistensialQ(v6, Int, fol_application (hol_semantic z2 ctx) (AVariable v6))),
							Disjunction(
								fol_application (hol_semantic z1 ctx) (AZConst 0),
								fol_application (hol_semantic z2 ctx) (AZConst 0))))))

	(*  {v : ((v=1 /\ exists z1 z2, (z1 neq 0 /\ z2 neq 0) /\ (h(t1)(z1) \/ h(t2)(z2))) \/ (v=0 /\ h(t1)(0) /\ h(t2)(0))} *)
	|   Or (z1, z2) -> 
			let v1 = ("_v"^(string_of_int (!freshvar +1))) in
			let v2 = ("_v"^(string_of_int (!freshvar +2))) in
			let v3 = ("_v"^(string_of_int (!freshvar +3))) in
			let v4 = ("_v"^(string_of_int (!freshvar +4))) in
			let v5 = ("_v"^(string_of_int (!freshvar +5))) in
			let v6 = ("_v"^(string_of_int (!freshvar +6))) in
			(freshvar := !freshvar+6);
			Disjunction(
				Conjunction(
					Identity (AInput, AZConst 0),
				Conjunction(
					fol_application (hol_semantic z1 ctx) (AZConst 0),
					fol_application (hol_semantic z2 ctx) (AZConst 0))),
				Conjunction(Identity(AInput, AZConst 1),
					Disjunction(
						Disjunction(
							Conjunction(
								ExistensialQ(v1, Int, fol_application (hol_semantic z1 ctx) (AVariable v1)),
								Neg (fol_application (hol_semantic z1 ctx) (AZConst 0))),
							Conjunction(
								ExistensialQ(v2, Int, fol_application (hol_semantic z2 ctx) (AVariable v2)),
								Neg (fol_application (hol_semantic z2 ctx) (AZConst 0)))),

						Conjunction(
							Conjunction(
								ExistensialQ(v3, Int, fol_application (hol_semantic z1 ctx) (AVariable v5)),
								ExistensialQ(v4, Int, fol_application (hol_semantic z2 ctx) (AVariable v6))),
							Disjunction(
								ExistensialQ(v5, Int, Conjunction(Neg (Identity(AZConst 0, AVariable v5)), fol_application (hol_semantic z1 ctx) (AVariable v5))),
								ExistensialQ(v6, Int, Conjunction(Neg (Identity(AZConst 0, AVariable v6)), fol_application (hol_semantic z2 ctx) (AVariable v6))))))))


(*	Primitive functions *)
(*  {v : (v = 0 /\ exists k, h(t1)(k)) \/ (v=1 /\ exists k, h(t1)(k))}  *)
	| Select tl ->
		let firstpart = hfun_sem_sel 0 tl ctx in
		let v = ("_v"^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		let safety = list_to_disj (bind_list tl (fun at -> hol_semantic at ctx)) in
		Conjunction(firstpart, ExistensialQ(v, Int, fol_application safety (AVariable v)))

(*  {v : exists n, v = prec n /\ h(t)(n) *)
	|   Iota t ->
		let v = ("_v"^(string_of_int (!freshvar +1))) in
		(freshvar := !freshvar+1);
		ExistensialQ(v, Int, Conjunction (Identity (AInput, Prec (AVariable v)), fol_application (hol_semantic t ctx) (AVariable v)))

(*  {v : exists v1, v2 : Z, h(t1)(v1) /\ h(t2)(v2) /\ ((v1 > v2 /\ v = v1) \/ (v1 = v2 /\ v = v1) \/ (v2 > v1 /\ v = v2)) *)
 	|   Max (t1, t2) -> 
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		(match dtype with
			| Int -> 
				ExistensialQ(v1, Int, ExistensialQ(v2, Int, 
					Conjunction(Conjunction(fol_application (hol_semantic t1 ctx) (AVariable v1), fol_application (hol_semantic t2 ctx) (AVariable v2)),
								Disjunction(Conjunction(Greater(AVariable v1,AVariable v2), Identity(AInput, AVariable v1)),
									Disjunction(Conjunction(Identity(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
												Conjunction(Greater(AVariable v2, AVariable v1), Identity(AInput, AVariable v2)))))))

			| Real ->
				ExistensialQ(v1, Real, ExistensialQ(v2, Real, 
					Conjunction(Conjunction(fol_application (hol_semantic t1 ctx) (AVariable v1), fol_application (hol_semantic t2 ctx) (AVariable v2)),
								Disjunction(Conjunction(Greater(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
									Disjunction(Conjunction(Identity(AVariable v1, AVariable v2), Identity(AInput, AVariable v1)),
												Conjunction(Greater(AVariable v2, AVariable v1), Identity(AInput, AVariable v2)))))))
			| _ -> raise (EngineErr "ill typed")
		)


(*  {v : \w. 
			(exists v1. h(t1)(v1) /\ v <> 0) -> (exists v2. h(t2)(v2))
			(h(t1)(0) -> (exists v3. h(t3)(v3))
				exists v4. w = v4 /\ h(t2)(v4) /\ exists v5. h(t1)(v1) /\ v1 <> 0
			\/	exists v6. w = v6 /\ h(t3)(v6) /\ h(t1)(0)
			\/	Neg (exists v7. h(t1)(v7)) /\ exists v8. w=v8 /\ h(t2)(v8) /\ h(t3)(v8) /\ forall v9. h(t2)(v8) /\ h(t3)(v8) -> v7 = v8

	(exists v1 v2, (h(t1)(v1) /\ v1 ~= 0 /\ h(t2)(v)) \/ (h(t3)(v) /\ h(t1)(0))  *)
 	|   Inlinecond (t1,t2,t3) ->
		let d = dtype in
		let v1 = ("_v"^(string_of_int (!freshvar +1))) in
		let v2 = ("_v"^(string_of_int (!freshvar +2))) in
		let v3 = ("_v"^(string_of_int (!freshvar +3))) in
		let v4 = ("_v"^(string_of_int (!freshvar +4))) in
		let v5 = ("_v"^(string_of_int (!freshvar +5))) in
		let v6 = ("_v"^(string_of_int (!freshvar +6))) in
		let v7 = ("_v"^(string_of_int (!freshvar +7))) in
		let v8 = ("_v"^(string_of_int (!freshvar +8))) in
		let v9 = ("_v"^(string_of_int (!freshvar +9))) in
		(freshvar := !freshvar+9);
		let l1 = Implication(ExistensialQ(v1, Int, Conjunction(fol_application (hol_semantic t1 ctx) (AVariable v1), Neg(Identity (AZConst 0, AVariable v1)))), 
							ExistensialQ(v2, d, fol_application (hol_semantic t2 ctx) (AVariable v2))) in
		let l2 = Implication(fol_application (hol_semantic t1 ctx) (AZConst 0), ExistensialQ (v3, d, fol_application (hol_semantic t3 ctx) (AVariable v3))) in
		let l3 = Conjunction(ExistensialQ(v4, d, Conjunction(Identity(AInput, AVariable v4), fol_application (hol_semantic t2 ctx) (AVariable v4))),
							ExistensialQ(v5, Int, Conjunction(fol_application (hol_semantic t1 ctx) (AVariable v5), Neg (Identity (AZConst 0, AVariable v5))))) in
		let l4 = Conjunction(ExistensialQ(v6, d, Conjunction(Identity(AInput, AVariable v6), fol_application (hol_semantic t3 ctx) (AVariable v6))),
							fol_application (hol_semantic t1 ctx) (AZConst 0)) in
		let l5 = Conjunction(Neg(ExistensialQ(v7, Int, fol_application (hol_semantic t1 ctx) (AVariable v7))),
							ExistensialQ(v8, d, 
												Conjunction(
												Conjunction(Identity(AInput, AVariable v8), 
												Conjunction(fol_application (hol_semantic t2 ctx) (AVariable v8),
															fol_application (hol_semantic t3 ctx) (AVariable v8))),
												UniversialQ(v9, d, Implication(
																	Conjunction(fol_application (hol_semantic t2 ctx) (AVariable v9),
																				fol_application (hol_semantic t3 ctx) (AVariable v9)),
																	Identity(AVariable v8, AVariable v9)))))) in 
		Conjunction(l1, Conjunction(l2, Disjunction(l3, Disjunction(l4, l5))))



(*	ETC *)
(* X[t] = {v : (exists n, v = \pi_n T /\ h(t)(n)) /\ forall n, h(t)(n) -> 0<= n < d(T) } *)
	|   Access (s, t) -> 
						let v1 = ("_v"^(string_of_int (!freshvar +1))) in
						let v2 = ("_v"^(string_of_int (!freshvar +2))) in
						(freshvar := !freshvar+2);
						if Hashtbl.mem ctx s then
						(match Hashtbl.find ctx s with
						| Inta d -> 
							Conjunction(ExistensialQ(v1, Int, Conjunction(Identity(AProjection (AVariable s, AVariable v1), AInput), 
														fol_application (hol_semantic t ctx) (AVariable v1))),
										UniversialQ(v2, Int, Implication(fol_application (hol_semantic t ctx) (AVariable v2),
																		Conjunction(Greater(AZConst d, AVariable v2),
																			(Greater (AVariable v2, AZConst (-1)))))))
						| Reala d ->
							Conjunction(ExistensialQ(v1, Int, Conjunction(Identity(AProjection (AVariable s, AVariable v1), AInput), 
														fol_application (hol_semantic t ctx) (AVariable v1))),
										UniversialQ(v2, Int, Implication(fol_application (hol_semantic t ctx) (AVariable v2),
																		Conjunction(Greater(AZConst d, AVariable v2),
																			(Greater (AVariable v2, AZConst (-1)))))))

						| _ -> raise (EngineErr "ill typed")
						)
					else raise (EngineErr "ill typed")

(* if s is single valued
	v => exists z1, ..., zd. v = f(z1,...,zd) /\ h(ti)(zi) /\ /\_i p_i->q_i /\
	     forall z1, ..., zd. \/_i p_i



 *)
	|   Application (s, tl) -> 

		if Hashtbl.mem mfun s then
		begin
			(* list of fresh typed variables *)
			let tvs = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error")) in
			(* conjunctive form of that tvs satisfies h(zi)(tvs_i) *)
			let term1 = list_to_conj (bind_list tvs (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			(* /\ p_i -> q_i *)
			let term3 = list_to_conj (impl_list (Hashtbl.find mfunfol s)) in
			(* list of strings of tvs *)
			let names = snd (split_list (snd (split_list tvs))) in
			(* p_i -> q_i [@i -> z_i] *)
			let nterm = fol_replace_list term3  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find mfun s)) 1))) (bind_list names (fun k -> AVariable k))) in
			let firstpart = 
			existence_from_list (snd (split_list tvs)) (Conjunction(term1, fol_replace nterm "@res" AInput)) in


			let tvs2 = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error")) in
			let term12 = list_to_conj (bind_list tvs2 (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			let term22 = list_to_disj (fst (split_list (Hashtbl.find mfunfol s))) in 
			let names2 = snd (split_list (snd (split_list tvs2))) in
			let mterm = fol_replace_list term22  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find mfun s)) 1))) (bind_list names2 (fun k -> AVariable k))) in
			let lastpart =
			universial_from_list (snd (split_list tvs2)) (Implication(term12, mterm)) in 
			Conjunction(firstpart, lastpart)
		end
		else
		if Hashtbl.mem sfun s then
		begin
			let tvs = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error")) in
			let term1 = list_to_conj (bind_list tvs (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			let names = snd (split_list (snd (split_list tvs))) in
			let firstpart = existence_from_list (snd (split_list tvs)) (Conjunction(term1, 
															Identity(AInput,
																AApplication(s, bind_list names (fun k -> AVariable k))))) in 
			
			let tvs2 = bind_list tl (fun t -> match termtree_type t ctx with Some d -> (t, fresh_of_type d) | _ -> raise (EngineErr "error")) in
			let term12 = list_to_conj (bind_list tvs2 (fun t -> let (term, (tp, name)) = t in fol_application (hol_semantic term ctx) (AVariable name))) in
			let term22 = list_to_disj (fst (split_list (Hashtbl.find sfunfol s))) in 
			let names2 = snd (split_list (snd (split_list tvs2))) in
			let mterm = fol_replace_list term22  
			(merge_list (snd (split_list (typed_list (fst (Hashtbl.find sfun s)) 1))) (bind_list names2 (fun k -> AVariable k))) in
			let lastpart =
			universial_from_list (snd (split_list tvs2)) (Implication(term12, mterm)) in 
			
			Conjunction(firstpart, lastpart)			


		end
		else raise (EngineErr "error occrued")


(* {v : v = 1 /\ exists k, h(z)(k) /\ forall k, h(z)(k) -> k <> 0*)
	|   Test (z) -> 
		let v1 = ("_test"^(string_of_int (!freshvar +1))) in
		let v2 = ("_test"^(string_of_int (!freshvar +2))) in
		(freshvar := !freshvar+2);
		Conjunction(
			Identity(AInput, AZConst 1), 
		Conjunction(
			ExistensialQ(v1, Int, fol_application (hol_semantic z ctx) (AVariable v1)),
			UniversialQ(v2, Int, Implication(
				fol_application (hol_semantic z ctx) (AVariable v2),
				 Neg (Identity (AVariable v2, AZConst 0))))))
								
)


and hfun_sem_sel (n : int) (tl : termtree list) (ctx : (string, data_type) Hashtbl.t) =
	match tl with
	| t :: l -> 
	(
		let v = ("_v"^(string_of_int (!freshvar +1))) in 
		(freshvar := !freshvar + 1); 
		Disjunction(
			Conjunction(
				Identity (AInput, AZConst n),
				ExistensialQ (v, Int, fol_application (hfun_sem t ctx) (AVariable v))),
			hfun_sem_sel (n+1) l ctx)
	)
	| [] -> False

let rec assigned_vars (s : statementtree) (ctx : (string, data_type) Hashtbl.t): typed_variable list =
	match s with
	|	Empty -> []
	|   Sequence (s1, s2) -> assigned_vars s1 ctx @ assigned_vars s2 ctx
	|   Newvariable (s, t) -> [(Hashtbl.find ctx s, s)]
	|   Assignment (s, t) -> [(Hashtbl.find ctx s, s)]
	|   ArrayAssign (s, t, e) ->[(Hashtbl.find ctx s, s)]
	|   Conditional (b, s1, s2) -> assigned_vars s1 ctx @ assigned_vars s2 ctx
	|   Whileloop (b, s, i, v) -> assigned_vars s ctx

let rec bind_with_fresh (f : foltree) (v : typed_variable list) : foltree = 
	match v with
	| s :: l -> 
		(let w = ("_"^(snd s)^(string_of_int (!freshvar+1))) in
		(freshvar := !freshvar+1);
		bind_with_fresh (UniversialQ(w, fst s, fol_replace f (snd s) (AVariable w))) l)
	| [] -> f



(* only will used during wp_calc simplifying *)
let fol_application_simpl (a : foltree) (x : atermtree) =
	let simpl =	fol_reduce (fol_application a x) in
	reduction_log := (!reduction_log)^("\n================\n\n application \n\n"^(print_foltree a)^"\n\n is further reduced to \n\n"^(print_foltree simpl));
	simpl



let hol_semantic_simpl (a : termtree) (ctx : (string, data_type) Hashtbl.t ) = 
	let sem = hol_semantic a ctx in
	reduction_log := (!reduction_log)^("\n================\n\nSemantic of "^(print_ttree a)^" is \n\n"^(print_foltree sem));
	let sem_simpl = fol_reduce sem in
	reduction_log := (!reduction_log)^("\n\nis reduced to\n\n"^(print_foltree sem_simpl));
	sem_simpl

let rec wp_calc (s : statementtree) (q : foltree) (ctx : (string, data_type) Hashtbl.t) : (foltree * (string, data_type) Hashtbl.t) = 
	(* (print_endline (print_foltree q)); *)
	match s with
	| Empty -> (q, ctx)
	| Sequence (s1, s2) -> (match wp_calc s2 q ctx with 
								| p, ctx ->	wp_calc s1 p ctx)							
	| Newvariable (v, t) -> 
			let w = ("_new"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			(UniversialQ(w, Hashtbl.find ctx v,
				Implication (fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w), fol_replace q v (AVariable w))), ctx)

	(* forall w : dt, h(t)(w) -> Q[v => w]  *)
	| Assignment (v, t) ->
			let w = ("_assign"^(string_of_int (!freshvar +1))) in
			(freshvar := !freshvar+1);
			(UniversialQ(w, Hashtbl.find ctx v,
				Implication (fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w), fol_replace q v (AVariable w))), ctx)

	| ArrayAssign (v, t, e) -> 
			let w1 = ("_array"^(string_of_int (!freshvar +1))) in
			let w2 = ("_array"^(string_of_int (!freshvar +2))) in
			let w3 = ("_array"^(string_of_int (!freshvar +3))) in
			let w4 = ("_array"^(string_of_int (!freshvar +4))) in
			let w5 = ("_array"^(string_of_int (!freshvar +5))) in
			(freshvar := !freshvar+5);
			(match Hashtbl.find ctx v with
			| Reala d ->
				(Conjunction(ExistensialQ(w1, Int, (ExistensialQ(w2, Real, 
								Conjunction(fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w1),
											fol_application_simpl (hol_semantic_simpl e ctx) (AVariable w2))))),

					Conjunction(UniversialQ(w3, Int, Implication(fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w3),
																Conjunction(Greater(AZConst d, AVariable w3), Greater(AVariable w3, AZConst (-1))))),
								UniversialQ(w4, Int, UniversialQ(w5, Real,
									Implication(Conjunction(
															fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w4),
															fol_application_simpl (hol_semantic_simpl e ctx) (AVariable w5)),
												fol_replace q v (ASub(AVariable v,AVariable  w4,AVariable  w5))))))), ctx)
			| Inta d ->
			(Conjunction(ExistensialQ(w1, Int, (ExistensialQ(w2, Int, 
							Conjunction(fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w1),
										fol_application_simpl (hol_semantic_simpl e ctx) (AVariable w2))))),

				Conjunction(UniversialQ(w3, Int, Implication(fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w3),
															Conjunction(Greater(AZConst d, AVariable w3), Greater(AVariable w3, AZConst (-1))))),
							UniversialQ(w4, Int, UniversialQ(w5, Int,
								Implication(Conjunction(
														fol_application_simpl (hol_semantic_simpl t ctx) (AVariable w4),
														fol_application_simpl (hol_semantic_simpl e ctx) (AVariable w5)),
											fol_replace q v (ASub(AVariable v, AVariable w4, AVariable w5))))))), ctx)
			| _ -> raise (EngineErr "ill typed")
		)




	(* ∃k.h(z)(k) ∧ (∃k.h(z)(k) ∧ k != 0 → wp(S1, Q)) ∧ (h(z)(0) → wp(S2, Q)) *)
	| Conditional (b, s1, s2) -> 
			let w = ("_if"^(string_of_int (!freshvar +1))) in
			let w2 = ("_if"^(string_of_int (!freshvar +2))) in
			(freshvar := !freshvar+2);
			(
			Conjunction(
				ExistensialQ(w, Int, fol_application_simpl (hol_semantic_simpl b ctx) (AVariable w)),
				Conjunction(
					Implication (
						ExistensialQ (w2, Int, Conjunction(
							fol_application_simpl (hol_semantic_simpl b ctx) (AVariable w2),
							Neg (Identity (AVariable w2, AZConst 0)))),
						(fst (wp_calc s1 q ctx))),
					Implication (
						fol_application_simpl (hol_semantic_simpl b ctx) (AZConst 0),
						(fst (wp_calc s2 q ctx))
					)
				)
			)
		, ctx)


	| Whileloop (b, s, i, v) -> 
		let v1 = ("_loop"^(string_of_int (!freshvar +1))) in
		let v2 = ("_loop"^(string_of_int (!freshvar +2))) in
		let v3 = ("_loop"^(string_of_int (!freshvar +3))) in
		let c0 = ("_loopc0"^(string_of_int (!freshvar +4))) in
		let c = ("_loopc"^(string_of_int (!freshvar +5))) in
		(freshvar := !freshvar+5);

		let inferpost = Implication(Conjunction(i, fol_application_simpl (hol_semantic_simpl b ctx) (AZConst 0)), q) in
		let infersafe = Implication(i, ExistensialQ(v1, Int, fol_application_simpl (hol_semantic_simpl b ctx) (AVariable v1))) in
		let loopbody = ExistensialQ(c0, Real, UniversialQ(c, Real, 
					Implication (
						Conjunction(i,
						Conjunction(ExistensialQ(v2, Int, Conjunction(fol_application_simpl (hol_semantic_simpl b ctx) (AVariable v2),
																	Neg (Identity (AVariable v2, AZConst 0)))),
												Identity (v, AVariable c))),
						fst (wp_calc s (Conjunction(i, Greater(APlus(AVariable c, AMinus (AVariable c0)),v))) ctx)))) in
		let loopvar = Implication (Greater(ARConst 0, v), 
							UniversialQ(v3, Int, Implication ( fol_application_simpl (hol_semantic_simpl b ctx) (AVariable v3), Identity (AVariable v3, AZConst 0)))) in
		 (Conjunction (i, 
		 	Conjunction (bind_with_fresh inferpost (assigned_vars s ctx),
		 		Conjunction (bind_with_fresh infersafe (assigned_vars s ctx),
		 			Conjunction (bind_with_fresh loopbody (assigned_vars s ctx),
		 				bind_with_fresh loopvar (assigned_vars s ctx))))), ctx)


(* alter input into v -> $v *)
let rec alter_variables (q : foltree) (tl : typed_variable list) : foltree =
	match tl with
	| (_, s) :: l -> alter_variables (fol_replace q s (AVariable ("$"^s))) l
	| [] -> q

let rec restore_variables (q : foltree) (tl : typed_variable list) : foltree =
	match tl with
	| (_, s) :: l -> restore_variables (fol_replace q ("$"^s) (AVariable s)) l
	| [] -> q

let rec alter_tv_list (tl : typed_variable list) : typed_variable list =
	match tl with
	| (t, s) :: l -> (t, ("$"^s)) :: (alter_tv_list l)
	| [] -> []

let rec quantify_input (vr : typed_variable list)(f : foltree) :foltree =
	match vr with
	| (t, v) :: l -> UniversialQ(v, t, quantify_input l f)
	| [] -> f

(* exists z, h(t)(z) /\ forall z, h(t)(z) -> Q(z, x1', x2', ..., xn') *)
let wp_calc_prog (vr : typed_variable list) (s : statementtree) (t : termtree) (p : foltree) (q : foltree) (ctx : (string, data_type) Hashtbl.t) = 
	let v1 = ("_out"^(string_of_int (!freshvar +1))) in
	let v2 = ("_out"^(string_of_int (!freshvar +2))) in
	(freshvar := !freshvar+2);
	match load_input_ctx ctx (alter_tv_list vr) with
	| Some ctx ->
		(	match termtree_type t ctx with
			| Some Int -> 	let postcond = Conjunction(ExistensialQ(v1, Int, fol_application (hol_semantic t ctx) (AVariable v1)),
													UniversialQ(v2, Int, Implication (fol_application (hol_semantic t ctx) (AVariable v2), fol_replace (alter_variables q vr) "@res" (AVariable v2))))
							in
							let impl = Implication(p, restore_variables (fst (wp_calc s postcond ctx)) vr) in
							quantify_input vr impl
			
			| Some Real -> 	let postcond = Conjunction(ExistensialQ(v1, Real, fol_application (hol_semantic t ctx) (AVariable v1)),
													UniversialQ(v2, Real, Implication (fol_application (hol_semantic t ctx) (AVariable v2), fol_replace (alter_variables q vr) "@res" (AVariable v2))))
							in
							let impl = Implication(p,  restore_variables (fst (wp_calc s postcond ctx)) vr) in
							quantify_input vr impl
			| _ -> raise (EngineErr "something wrong... ")
		)
	| _ -> raise (EngineErr "something wrong...")
	

let rec print_sem_list (at : term_pre list) (ctx : (string, data_type) Hashtbl.t) =
	match at with
	| a :: l -> 
		let (dt, a) = termtree_type_pre a ctx in
		let sem = hol_semantic a ctx in 
		let simpl = fol_reduce sem in
		"==========\nSemantic of "^(print_ttree a)^" is:\n\n"^
		(print_foltree sem)^
		"\n\n Can be reduced to:  \n\n"^
		(print_foltree simpl)^
		"\n\n"^(print_sem_list l ctx)
	| _ -> ""




let rec print_foltree_list2 (a : foltree list) : string =
	match a with
 	| v :: l -> (print_foltree (reduce_quantifiers v))^"\n\n"^(print_foltree_list2 l)
	| _ -> ""

let rec print_dnf_coj_list (a : foltree list) : string =
	match a with
	| v :: l -> (print_dnf_list (simplify_dnf (dnf_to_list (prenex_dnf (v)).mainfol)))^"\n\n"^(print_dnf_coj_list l)
	| _ -> ""


let vc_extract () =
	let precond = !parsed_precond in
	let postcond = !parsed_postcond in
	let vr = !parsed_input in
	let s = !parsed_stmt in
	let rt = !parsed_return in
	let ctxf = !parsed_final_ctx in
	wp_calc_prog vr s rt precond postcond ctxf



