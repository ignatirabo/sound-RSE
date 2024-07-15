open Syntax

let rec s_to_saux : Lang.stmt -> Lang.stmt_aux = function
  | Sassign (v,e) -> Aassign (v,e)
  | Sinput v -> Ainput v
  | Sif (e,b1,b2) ->
    let b1a = b_to_baux b1 in
    let b2a = b_to_baux b2 in
    Aif (e,b1a,b2a)
  | Swhile (e,b) ->
    let ba = b_to_baux b in
    Awhile (e,ba)
and b_to_baux (b : Lang.block) =
  let ba = List.fold_left
    (fun ba s -> s_to_saux s :: ba)
    [] b in
  List.rev ba

let rec saux_to_s (s: Lang.stmt_aux) : Lang.stmt =
  match s with
  | Aassign (v,e)-> Sassign (v,e)
  | Ainput v -> Sinput v
  | Aif (e,b1a,b2a) ->
    let b1 = baux_to_b b1a in
    let b2 = baux_to_b b2a in
    Sif (e,b1,b2)
  | Awhile (e,ba) | Aloop (e,ba) ->
    let b = baux_to_b ba in
    Swhile (e,b)
and baux_to_b (ba: Lang.block_aux) =
  let b = List.fold_left
    (fun b s -> saux_to_s s :: b)
    [] ba in
  List.rev b

let vars_in_expr (e: Lang.expr) : Var.VSet.t =
  let rec aux (e: Lang.expr) (vars: Var.VSet.t) =
    match e with
    | Evar v -> Var.VSet.add v vars
    | Euop (_, e0) -> aux e0 vars
    | Eop (e0, _, e1) ->
      let vars = aux e0 vars in
      let vars = aux e1 vars in
      vars
    | _ -> vars in
  aux e Var.VSet.empty

let vars (b: Lang.block) : Var.VSet.t =
  let rec aux_s (s: Lang.stmt) (res: Var.VSet.t) =
    match s with
    | Sassign (v,e) ->
      let res = Var.VSet.union (vars_in_expr e) res in
      Var.VSet.add v res
    | Sinput v -> Var.VSet.add v res
    | Sif (e,b0,b1) ->
      let e_res = vars_in_expr e in
      let res = Var.VSet.union e_res res in
      let res = aux_b b0 res in
      let res = aux_b b1 res in
      res
    | Swhile (e,b) ->
      let e_res = vars_in_expr e in
      let res = Var.VSet.union e_res res in
      let res = aux_b b res in
      res
  and aux_b (b: Lang.block) (res: Var.VSet.t) =
    match b with
    | [] -> res
    | s::b ->
      let res = aux_s s res in
      aux_b b res
  in
  let res = aux_b b Var.VSet.empty in
  res

(* Flags *)
(* This flags are used to notice certain events. *)
(* let const_max_ite = 4 *)

let filter_split (b: 'a -> bool) (ls: 'a list) =
  List.fold_left
    (fun (ls_t, ls_f) a ->
        if b a then
          ((a :: ls_t), ls_f)
        else
          (ls_t, (a :: ls_f)))
    ([],[]) ls
