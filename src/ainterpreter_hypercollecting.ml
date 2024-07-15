(* Static Analysis - Hypercollecting Semantics *)
(* open Syntax
open Utils.SecMap *)

module V = Syntax.Var
module L = Syntax.Lang
module SM = Sec_map

(*******************************************)
(* State Domain                            *)
(*******************************************)
module type STATE_DOMAIN =
  sig
    type astate
    type elt
    (* Printing *)
    val pp: out_channel -> astate -> unit
    (* Lattice operations *)
    val join: astate -> astate -> astate
    (* val lub: astate -> astate -> astate *)
    (* Set operations *)
    val union: astate -> astate -> astate
    val subset: astate -> astate -> bool
    (* Abstract operations *)
    val post_input: V.t -> astate -> astate
    val post_assign: V.t -> L.expr -> astate -> astate
    val post_if: L.expr -> L.block -> L.block -> astate -> astate -> astate -> astate
    (* Variables, functions and block operations *)
    val ast_from_sec: SM.t -> astate
    val block_enter: astate -> astate
    val block_exit: astate -> astate
    (* Testing *)
    val to_astate: elt list -> astate
    val equal: astate -> astate -> bool
    val vars_in_level: astate -> int -> V.VSet.t
  end

(*******************************************)
(* Abstract interpreter                    *)
(*******************************************)
module Ai = functor (D: STATE_DOMAIN) ->
  struct
    (* Abstract least fixpoint *)
    let alfp f a =
      let rec aux a0 =
        let a1 = f a0 in
        if D.subset a0 a1 then
          a0
        else
          aux (D.join a0 a1)
      in aux a
    (* Abstract interpreter for statements *)
    let rec ai_stmt a s =
      if !Utils.debug then
        Printf.printf "State:\n%a\n%a\n" D.pp a (Prog.pp_stat "  ") s;
      let apost =
        match s with
        | L.Sassign (x, e) -> D.post_assign x e a
        | Sinput v -> D.post_input v a
        | Sif (e, b0, b1) ->
            let a0 = ai_block a b0 in
            let a1 = ai_block a b1 in
            D.post_if e b0 b1 a a0 a1
        | Swhile (e, b0) ->
            let b = [L.Sif (e, b0, [])] in
            let f a = ai_block a b in
            alfp f a in
      if !Utils.debug then
        Printf.printf "result:\n%a\n\n" D.pp apost;
      apost
    and ai_list a b =
      List.fold_left ai_stmt a b
    and ai_block a b =
      D.block_exit (ai_list (D.block_enter a) b)
    let analyze_prog (p: Prog.t) =
      let low_vars : V.VSet.t = V.VMap.fold
        (fun v n acc -> if n = 0 then (V.VSet.add v acc) else acc)
        p.psec V.VSet.empty in
      let ainit = D.ast_from_sec p.psec in
      let d = ai_block ainit p.pmain in
      (* Check state for low-equality *)
      let d_low = D.vars_in_level d 0 in
      let is_low = V.VSet.equal low_vars d_low in
      Printf.printf "Final state:\n%a\n" D.pp d;
      if is_low then
        Printf.printf "Program is noninterferent."
      else
        Printf.printf "Cannot prove program is noninterferent.\n";
      (d, V.VSet.equal low_vars d_low, false)
  end
