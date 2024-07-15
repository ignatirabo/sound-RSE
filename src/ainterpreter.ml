open Apron

module AIu = Ainterpreter_utils
module VarS = Syntax.Var
module Lang = Syntax.Lang
module Ops = Syntax.Ops

module type STATE_DOMAIN =
  sig
    type astate
    (* Threshold *)
    val lthr: Threshold.t ref
    val set_thr: Threshold.t -> unit
    (* Printing *)
    val pp: string -> out_channel -> astate -> unit
    (* Top *)
    val top: VarS.t list -> astate
    (* Bounds *)
    val get_range_of_var: VarS.t -> astate -> (int option * int option) option
    (* Lattice operations *)
    val is_le: astate -> astate -> bool
    val join: astate -> astate -> astate
    val widen: astate -> astate -> astate
    (* Abstract Operations *)
    val post_cond: Lang.expr -> astate -> astate
    val post_input: VarS.t -> astate -> astate
    val post_assign: VarS.t -> Lang.expr -> astate -> astate
    (* Variables, functions and block operations *)
    val block_enter: astate -> astate
    val block_exit: astate -> astate
    val function_entry: astate -> astate
    val function_exit: astate -> astate -> astate
    val var_new: VarS.t -> astate -> astate
    (* Properties *)
    val get_constraints: astate -> Lang.expr list
    val is_sat: astate -> bool
  end

module type PRE_APRON =
  sig
    type t
    val man: t Manager.t
  end
module PA_box =
  (struct
    type t = Box.t
    let man: t Manager.t =
      Box.manager_alloc ()
  end: PRE_APRON)
module PA_oct =
  (struct
    type t = Oct.t
    let man: t Manager.t =
      Oct.manager_alloc ()
  end: PRE_APRON)
module PA_polka =
  (struct
    type t = Polka.strict Polka.t
    let man: t Manager.t =
      Polka.manager_alloc_strict ()
  end: PRE_APRON)
module PA_polka_eq =
  (struct
    type t = Polka.equalities Polka.t
    let man: t Manager.t =
      Polka.manager_alloc_equalities ()
  end: PRE_APRON)

module E = Apron.Environment
type 'a man = 'a Apron.Manager.t
type env = E.t
module A = Abstract1

module Dom_Apron (PA: PRE_APRON) : STATE_DOMAIN =
  struct
    type u = PA.t
    (* Abstract states *)
    type astate = u A.t
    (* "Manager" for the abstract domain *)
    let man = PA.man
    (* Threshold *)
    let lthr = ref []
    let set_thr thr = lthr := thr
    (* Printing *)
    let t_2stri (ind: string) (x: astate): string =
      let s0 =
        Printf.sprintf "%s%s\n" ind
          (AIu.environment_2str (A.env x)) in
      let s1 = AIu.linconsarray_2stri ind
          (A.to_lincons_array man x) in
      Printf.sprintf "%s%s" s1 s0
    let pp indent chan a =
      Printf.fprintf chan "%s" (t_2stri indent a)
    (* Top *)
    let top (l: VarS.t list): astate =
      let l = List.map (fun x -> Var.of_string (VarS.get_vname x)) l in
      let env = E.make (Array.of_list l) [| |] in
      A.top man env
    (* Bounds *)
    let get_range_of_var _ _ = failwith "unimp: range_of_var"
    (* Lattice operations *)
    let is_le a0 a1 = A.is_leq man a0 a1
    let join a0 a1 =  A.join man a0 a1
    let widen a0 a1 =
      if List.length !lthr = 0 then
        A.widening man a0 a1
      else
        let earr = Threshold.thr_to_lincons !lthr (A.env a0) in
        A.widening_threshold man a0 a1 earr
    (* Abstract Operations *)
    let post_cond e a =
      let env = A.env a in
      let eacons = Tcons1.array_make env 1 in
      let c = AIu.translate_cons env e in
      Tcons1.array_set eacons 0 c;
      A.meet_tcons_array man a eacons
    let post_input x a =
      let a = A.forget_array man a [| Var.of_string (VarS.get_vname x) |] false in
      post_cond (Lang.Eop (Evar x, Oge, Ecsti 0)) a
    let post_assign x e (a: astate): astate =
      A.assign_texpr_array man a
        [| Var.of_string (VarS.get_vname x) |]
        [| AIu.translate_expr (A.env a) e |] None
    (* Variables, functions and block operations *)
    let block_enter (a: astate): astate = a
    let block_exit (a: astate): astate = a
    let function_entry _ = failwith "function_enter"
    let function_exit _ = failwith "function_exit"
    let var_new _ _ = failwith "var_new"
    (* Accessors *)
    let get_constraints a =
      let l = A.to_lincons_array man a in
      (* Translate each lincons to expr *)
      let lincons_list = ref [] in
      for i = 0 to Lincons1.array_length l - 1 do
        let cons = Lincons1.array_get l i in
        let expr = AIu.lincons_2expr cons in
        lincons_list := expr :: !lincons_list
      done;
      !lincons_list
    let is_sat a =
      AIu.linconsarray_sat (A.to_lincons_array man a)
  end

module type ABSTRACT_INTERPRETER =
  sig
    module D : STATE_DOMAIN
    val alfp : (D.astate -> D.astate) -> D.astate -> D.astate
    val stmt_assign : Lang.stmt -> D.astate -> D.astate
    val stmt_input : Lang.stmt -> D.astate -> D.astate
    val stmt_if : Lang.stmt -> D.astate -> D.astate
    val stmt_loop : Lang.stmt -> D.astate -> D.astate
    val analyze_prog : Prog.t -> Threshold.t -> D.astate
  end

module Ai (D: STATE_DOMAIN) : ABSTRACT_INTERPRETER =
  struct
    module D = D
    (* Abstract least fixpoint *)
    let rec alfp f a =
      if !(Utils.debug) then
        Printf.printf "enter ALFP\n\n";
      (* TODO: determine which one to use *)
      let a_next = (D.join a (f a)) in
      (* let a_next = f a in *)
      let a_widen = D.widen a a_next in
      if !(Utils.debug) then
        Printf.printf "ALFP:\na:\n%aa_next:\n%aa_widen:\n%a\n"
          (D.pp "") a (D.pp "") a_next (D.pp "") a_widen;
      if D.is_le a_widen a then a
      else alfp f a_widen

    let stmt_assign s a =
      match s with
      | Lang.Sassign (v,e) -> D.post_assign v e a
      | _ -> raise (Failure "Wrong statement.")
    let stmt_input s a =
      match s with
      | Lang.Sinput v -> D.post_input v a
      | _ -> raise (Failure "Wrong statement.")

    let rec stmt_if s a =
      match s with
      | Lang.Sif (e,b0,b1) ->
        let apre0 = D.post_cond e a in
        let apost0 = ai_block apre0 b0 in
        let apre1 = D.post_cond (Lang.expr_neg e) a in
        let apost1 = ai_block apre1 b1 in
        D.join apost0 apost1
      | _ -> raise (Failure "Wrong statement.")

    and stmt_loop s a =
      match s with
      | Lang.Swhile (e,b) -> 
        if !(Utils.debug) then
          Printf.printf "stmt_loop a:\n%a\n\n" (D.pp "") a;
        let f = fun a -> ai_block (D.post_cond e a) b in
        let inv = alfp f a in
        D.post_cond (Lang.expr_neg e) inv
      | _ -> raise (Failure "Wrong statement.")

    (* Abstract interpreter for statements *)
    and ai_stmt a s =
      if !(Utils.debug) then
        Printf.printf "ai_stmt pre:\n%a\n%a\n\n" (D.pp "") a
          (Prog.pp_stat "  ") s;
      let apost : D.astate =
        match s with
        | Sinput _ ->      stmt_input s a
        | Sassign (_,_) -> stmt_assign s a
        | Sif (_,_,_) ->   stmt_if s a
        | Swhile (_, _) -> stmt_loop s a in
      if !(Utils.debug) then
        Printf.printf "ai_stmt after:\n%a\n\n" (D.pp "") apost;
      apost
    and ai_list a b =
      List.fold_left ai_stmt a b
    and ai_block a b =
      D.block_exit (ai_list (D.block_enter a) b)
    let analyze_prog (p: Prog.prog) (uthr: Threshold.t) =
      let ainit = D.top p.pglobs in
      D.set_thr uthr;
      Printf.printf "Initial state: %a" (D.pp "    ") ainit;
      let afinal = ai_block ainit p.pmain in
      Printf.printf "Final state:\n%a" (D.pp "    ") afinal;
      afinal
  end
