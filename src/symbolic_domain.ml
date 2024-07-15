open Pre
open Syntax.Lang
open Syntax.Var
open Symbolic_path

let debug = Utils.debug

module type SYMBOLIC_DOMAIN = sig
  module SP : SYMBOLIC_PATH
  module P := SP.P
  type zexpr := P.zexpr
  type zval = zexpr
  val zval_to_list : zval -> zexpr list
  val zval_from_list : zexpr list -> zval
  (* we need some kind of relation between zval and zexpr *)
  type sp := SP.t
  type svm = zval VMap.t
  type state
  val pp: string -> out_channel -> state -> unit
  (* Structure *)
  (* val top: state *)
  val new_state: ?svm:svm option -> Prog.t option -> state

  val svm_empty: svm
  val svm_update: var -> zval -> svm -> svm
  val svm_of_map: zval VMap.t -> svm
  val svm_iter: (var -> zval -> unit) -> svm -> unit
  val svm_fold: (var -> zval -> 'a -> 'a) -> svm -> 'a -> 'a
  val svm_mapi: (var -> zval -> 'a) -> svm -> 'a VMap.t
  val svm_find: var -> svm -> zval 

  (* This functions can be defined all the same for any of these Domains *)
  val get_sp: state -> sp
  val get_svm: state -> svm
  val set_sp: sp -> state -> state
  val set_svm: svm -> state -> state
  (* This functions can be defined all the same for any of these Domains *)

  val add_var: state -> var -> state
  val add_constraint: ?id:SP.id option -> expr -> state -> state
  val find: var -> state -> zval
  val assign: var -> zval -> state -> state
  val diff: state -> state -> VSet.t -> VSet.t
  val reduction: state -> state
  (* Abstract *)
  val post_input: var -> state -> state
  val post_assign: var -> expr -> state -> state
  val post_if: expr -> state -> (string * state * P.zstatus) list
  val post_loop: expr -> state -> (string * state * P.zstatus) list
end

module Ss (SP:SYMBOLIC_PATH) : SYMBOLIC_DOMAIN =
  struct
    module SP = SP
    module P = SP.P 

    type zexpr = P.zexpr
    type zval = zexpr
    let zval_to_list zv = [ zv ]
    let zval_from_list zlist =
      if List.length zlist = 1 then
        List.hd zlist
      else
        raise (Failure "Ss.zval_from_list: wrong list size.")

    (** Symbolic Path representing the path take by the pair of executions *)
    type sp = SP.t
    let id1 = SP.int_2id 1

    (** Symbolic Variable Map: used to map variables with it's symbolic values. *)
    type svm = zexpr VMap.t

    (** Kappa-state: single symbolic execution state *)
    type state = {
      svm : svm; (** Symbolic map *)
      sp : sp; (** Symbolic path *)
    }

    (* Placeholder reduction *)
    let reduction a = a

    (**********
     * Prints *
     **********)
    (** Pretty print for abstract states *)
    let pp indent chan a =
      Printf.fprintf chan "%sSymbolic variable map: " indent;
      VMap.iter
        (fun v e -> Printf.fprintf chan "%s%s->%a; " indent (get_vname v) P.print_expr e)
        a.svm;
      Printf.fprintf chan "\n";
      let sp = a.sp in
      begin
        if SP.length sp > 0 then
          (Printf.fprintf chan "%sSymbolic path: " indent;
          let sp_list : zexpr list = SP.to_list sp in
          P.print_prop chan sp_list;
          Printf.printf "\n")
        else
          Printf.fprintf chan "%sSymbolic path: empty\n" indent
      end

    (*************
     * Functions *
     *************)
    let svm_empty = VMap.empty
    let svm_update v zv svm = VMap.add v zv svm

    let svm_of_map svm = svm
    let svm_iter = VMap.iter
    let svm_fold = VMap.fold
    let svm_mapi = VMap.mapi
    let svm_find = VMap.find

    let get_sp k = k.sp
    let get_svm k = k.svm
    let set_sp sp k = {k with sp=sp}
    let set_svm svm k = {k with svm=svm}

    (** Generate new name for an abstract value and register it *)
    let assign (v: var) (zv: zexpr) (k: state) =
      let svm = svm_update v zv k.svm in
      { k with svm }

    (** Get variables found in astate *)
    let find (v: var) (k: state) =
      VMap.find v k.svm
    let add_var (k: state) (v: var)  =
      let str = Prog.new_name v 0 in
      assert(MP.is_single str);
      let s = P.mk_string (MP.get_single str) in
      let exp = P.mk_const s in
      assign v exp k

    let diff (k1: state) (k2: state) (vset: VSet.t) : VSet.t =
      VSet.fold (fun v res ->
        try
          if !debug then Printf.printf "DIFF: var %s -> %s, %s: " (get_vname v) (P.to_string (VMap.find v k1.svm)) (P.to_string (VMap.find v k2.svm));
          if 0 = P.compare (VMap.find v k1.svm) (VMap.find v k2.svm) then begin
            if !debug then Printf.printf "Equal\n";
            res
          end else begin
            if !debug then Printf.printf "Not equal\n";
            VSet.add v res
          end
        with Not_found -> res)
        vset VSet.empty

    let add_constraint ?id:(id=None) (e: expr) (k: state) =
      let id =
        if Option.is_some id then Option.get id
        else id1 in
      let e' = P.expr_eval e k.svm in
      { k with sp = SP.add id e' k.sp }

    let new_state ?svm:(svm=None) (p: Prog.t option) : state =
      let k = { svm=VMap.empty ; sp=SP.empty } in
      match svm with
      | None ->
        let vars = (Option.get p).pglobs in
        let k = List.fold_left add_var k vars in
        k
      | Some svm ->
        let k = set_svm svm k in
        k

    (** Assign expression e to variable v on abstract state a0 *)
    let post_assign (v: var) (e: expr) (k: state): state =
      if (get_vname v = "assert") then
        let e'= P.expr_eval e k.svm in
        let assertion = P.mk_not e' in
        let sp = SP.add id1 assertion k.sp in
        let (status, solver) = P.check (SP.to_list sp) in
        let _ = match status with
          | P.SAT ->
            begin
              Printf.printf "  assertion violated\n";
              match P.get_string_model (SP.to_list sp) (status, solver) with
              | Some m -> Printf.printf "  Model: \n%s\n" m
              | None -> Printf.printf "  Failed to get model.\n"
            end;
          | _ -> Printf.printf  "  assertion verified\n" in
        k
      else
        let e' = P.expr_eval e k.svm in
        assign v e' k

    (** Assign random value to variable v on abstract state a0 *)
    (* Note: this case is unclear, so don't worry about it *)
    let post_input (v: var) (k: state) : state =
      add_var k v

    (** Apply e's contraints to a0, based on boolean values bool0 and bool1 *)
    let post_if e k : (string * state * P.zstatus) list =
      let e' = P.expr_eval e k.svm in

      let se_true = e' in
      let se_false = P.mk_not e' in

      let sp_t = SP.add id1 se_true k.sp in
      let sp_f = SP.add id1 se_false k.sp in

      let aux sp = (
        let status, _ = P.check (SP.to_list sp) in
        ({ k with sp }, status)) in

      let (kt, statt) = aux sp_t in
      let (kf, statf) = aux sp_f in
      [("T", kt, statt) ; ("F", kf, statf)]

    let post_loop e k =
      post_if e k
  end
