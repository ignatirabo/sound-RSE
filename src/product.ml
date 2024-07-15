open Ainterpreter
open Single_symbolic
open Syntax
(* open Utils *)
open Prog

(* We cannot be more general than this I think, because the domains are very specific *)
module type PAIR_PRODUCT_DOMAIN =
  sig
    module SE: SINGLE_SYMBOLIC_EXEC
    module B : ABSTRACT_INTERPRETER
    module SP = SE.D.SP
    module P := SP.P
    type zexpr := P.zexpr
    type zval = zexpr
    val zval_to_list : zval -> zexpr list
    val zval_from_list : zexpr list -> zval
    (* we need some kind of relation between zval and zexpr *)
    type sp := SP.t
    type svm = zval Var.VMap.t
    type state = SE.D.state * B.D.astate
    val pp: string -> out_channel -> state -> unit
    (* Structure *)
    (* val top: state *)
    val new_state: ?svm:svm option -> Prog.t option -> state

    val svm_empty: svm
    val svm_update: Var.t -> zval -> svm -> svm
    val svm_of_map: zval Var.VMap.t -> svm
    val svm_iter: (Var.t -> zval -> unit) -> svm -> unit
    val svm_fold: (Var.t -> zval -> 'a -> 'a) -> svm -> 'a -> 'a
    val svm_mapi: (Var.t -> zval -> 'a) -> svm -> 'a Var.VMap.t
    val svm_find: Var.t -> svm -> zval 

    (* This functions can be defined all the same for any of these Domains *)
    val get_sp: state -> sp
    val get_svm: state -> svm
    val set_sp: sp -> state -> state
    val set_svm: svm -> state -> state
    (* This functions can be defined all the same for any of these Domains *)

    val add_var: state -> Var.t -> state
    val add_constraint: ?id:SP.id option -> Lang.expr -> state -> state
    val find: Var.t -> state -> zval
    val assign: Var.t -> zval -> state -> state
    val diff: state -> state -> Var.VSet.t -> Var.VSet.t
    val reduction: state -> state
    (* Abstract *)
    val post_input: Var.t -> state -> state
    val post_assign: Var.t -> Lang.expr -> state -> state
    val post_if: Lang.expr -> state -> (string * state * P.zstatus) list
    val post_loop: Lang.expr -> state -> (string * state * P.zstatus) list
  end

module Pr_Single_Apron (SE : SINGLE_SYMBOLIC_EXEC) (B : ABSTRACT_INTERPRETER) : PAIR_PRODUCT_DOMAIN =
  struct
    module SE = SE
    module B = B
    module BD = B.D

    module S = SE.D

    type zval = S.zval

    module SP = S.SP
    let id1 = SP.int_2id 1
    type svm = S.svm

    (* module C =  *)

    type state = S.state * BD.astate

    (* let top vars : state =
      let k = S.top in
      let i = B.top vars in
      (k, i) *)
    let new_state ?svm:(svm=None) p =
      let ainit = S.new_state ~svm:svm p in
      let vars = S.svm_fold (fun v _ acc -> v::acc) (S.get_svm ainit) [] in
      (ainit, BD.top vars)
    (* let init ?svm:(svm=None) p =
      let b_a, ainit, f, id = S.init ~svm:svm p in
      (b_a, (ainit, B.top p.pglobs), f, id) *)

    (* let pp _ _ _ =
      raise (Failure "Product.pp not implemented") *)
    let pp indent chan a =
      let indent' = String.concat "" [indent;"  "] in
      Printf.fprintf chan "%sSingle-Symbolic state:\n%a%sNumeric state:\n%a\n"
        indent (S.pp indent') (fst a) indent (BD.pp indent') (snd a)

    (* let block_enter a = a
    let block_exit a = a *)

    let get_sp (k, _) = S.get_sp k
    let get_svm (k, _) = S.get_svm k
    let set_sp sp (k, i) = S.set_sp sp k, i
    let set_svm svm (k, i) = S.set_svm svm k, i
    let svm_find = S.svm_find
    let svm_update = S.svm_update
    let svm_empty = S.svm_empty
    let zval_from_list = S.zval_from_list
    let zval_to_list = S.zval_to_list
    let svm_of_map svm = S.svm_of_map  svm
    let svm_mapi = S.svm_mapi
    let svm_iter = S.svm_iter
    let svm_fold = S.svm_fold
    let assign v e (k, i) =
      (* assign in k but leave i alone *)
      let k = S.assign v e k in
      (* let i = I.astate_update v.vname I.AV.aval_top i in *)
      (k, i)
    let find v (k, _) = S.find v k
    let add_constraint ?id:(id=None)e (k, i) = (S.add_constraint ~id:id e k, i)
    let add_var (k, i) v =
      let k = S.add_var k v in
      let i = BD.var_new v i in
      (k, i)
    let diff (k,_) (k',_) vars =
      S.diff k k' vars

    let reduction (k,b: state) =
      let ctrs = BD.get_constraints b in
      let zexpm : zval Var.VMap.t =  S.get_svm k in
      let zexpm = Var.VMap.map (fun zv -> List.hd (S.zval_to_list zv)) zexpm in
      let ctrs = List.map (fun e -> SP.P.expr_eval e zexpm) ctrs in
      let sp : SP.P.zexpr list = ctrs @ (SP.to_list (S.get_sp k)) in
      (S.set_sp (SP.from_list id1 sp) k), b

    let post_assign v e (k, i) =
      let k = S.post_assign v e k in
      let i = BD.post_assign v e i in
      (k, i)

    let post_input v (k, i) =
      let k = S.post_input v k in
      let i = BD.post_input v i in
      (k, i)

    let post_if e (k, i) =
      let (k, i) = reduction (k,i) in
      let (kts, kfs) = match S.post_if e k with
        | kts::kfs::[] -> (kts,kfs)
        | _ -> raise (Failure "wrong length post_if.") in
      let (_, kt, ts) = kts in
      let (_, kf, fs) = kfs in
      let i_t = BD.post_cond e i in
      let i_f = BD.post_cond (Lang.expr_neg e) i in
      let a_ts = "T", (kt, i_t), ts in
      let a_fs = "F", (kf, i_f), fs in
      [ a_ts ; a_fs ]

    let post_loop = post_if
  end

(** User defined threshold *)
let uthr : (Threshold.t option) ref = ref None

(* Module implementing the approximation of the reduced product for domains Single-Symbolic and Intervals. *)
module Pr_Exec (D : PAIR_PRODUCT_DOMAIN) : SINGLE_SYMBOLIC_EXEC =
  struct
    module D  = D
    module PR = D
    module SE = PR.SE
    module B = PR.B

    module S = SE.D
    module SP = S.SP
    module C = SE.C

    module BD = B.D

    module L = Lang

    type config = Lang.block_aux * PR.state * Flag.t * Id.t * C.t
    let create_config b s f id c = (b,s,f,id,c)

    let lthr_ref: Threshold.t ref = ref []
    let set_thr (lthr: Threshold.t) =
      if List.length lthr > 0 then begin
        lthr_ref := lthr;
        SE.set_thr lthr;
        BD.set_thr lthr;
        Printf.printf "User threshold set in Product domain.\n"
      end

    let init ?svm:(svm=None) (p: Prog.prog) : config =
      let b = Syntax_aux.b_to_baux p.Prog.pmain in
      let svm : S.svm option =
        try
          Some (D.svm_mapi (fun _ zv -> S.zval_from_list (D.zval_to_list zv)) (Option.get svm))
        with _ -> None in
      let k = S.new_state ~svm:svm (Some p) in
      let a = BD.top p.pglobs in
      let f = Flag.empty in
      let id = Id.make false in
      let c = C.empty in
      (b,(k,a),f,id,c)

    let get_block (b,_,_,_,_) = b
    let get_state (_,a,_,_,_) = a
    let get_flag (_,_,f,_,_) = f
    let get_id (_,_,_,id,_) = id
    let get_counter (_,_,_,_,c) = c
    let set_flag f (b,s,_,id,c) = (b,s,f,id,c)
    let set_state s (b,_, f,id,c) = (b,s,f,id,c)
    let set_block b (_,s,f,id,c) = (b,s,f,id,c)
    let set_id id (b,s,f,_,c) = (b,s,f,id,c)
    let set_counter c (b,s,f,id,_) = (b,s,f,id,c)

    (* TODO: fix this *)
    let modif (b,(k,_),f,id,c) = SE.modif (b,k,f,id,c)

    (** Calculate assignment *)
    let rec stmt_assign (b,(k,a),f,id,c) : config =
      match b with
      | L.Aassign (v,e)::_ ->
        let (b,k,f,id,c) = SE.stmt_assign (b,k,f,id,c) in
        let a = B.stmt_assign (L.Sassign (v,e)) a in
        (b,(k,a),f,id,c)
      | _ -> raise (Failure "Wrong statement.")

    (** Calculate input *)
    and stmt_input (b,(k,a),f,id,c) : config =
      match b with
      | L.Ainput v::_ ->
        let (b,k,f,id,c) = SE.stmt_input (b,k,f,id,c) in
        let a = B.stmt_input (L.Sinput v) a in
        (b,(k,a),f,id,c)
      | _ -> raise (Failure "Wrong statement.")

    and stmt_if (b,(k,a),f,id,c) : config option * config option =
      match b with
      | L.Aif (e,_,_)::_ ->
        let kct, kcf = SE.stmt_if (b,k,f,id,c) in
        let ct =
          try
            if !Utils.debug then Printf.printf "PR-IF-T is SAT, state %a.\n" (Id.pp "") id;
            let (b,k,f,id,c) = Option.get kct in
            let a = BD.post_cond e a in
            Some (b,(k,a),f,id,c)
          with _ ->
            if !Utils.debug then Printf.printf "PR-IF-T is UNSAT, state %a.\n" (Id.pp "") id;
            None in
        let cf =
          try
            if !Utils.debug then Printf.printf "PR-IF-F is SAT, state %a.\n" (Id.pp "") id;
            let (b,k,f,id,c) = Option.get kcf in
            let a = BD.post_cond (L.expr_neg e) a in
            Some (b,(k,a),f,id,c)
          with _ ->
            if !Utils.debug then Printf.printf "PR-IF-F is UNSAT, state %a.\n" (Id.pp "") id;
            None in
        ct, cf
      | _ -> raise (Failure "Wrong statement.")

    and stmt_while (b,(k,a),f,id,c) : config =
      match b with
      | L.Awhile (_,_)::_ ->
        let (b,k,f,id,c) = SE.stmt_while (b,k,f,id,c) in
        (b,(k,a),f,id,c)
      | _ -> raise (Failure "Wrong statement.")

    and stmt_loop_norm (b,(k,a),f,id,c) : config option * config option =
      match b with
      | L.Aloop (e,_)::_ ->
        let kct, kcf = SE.stmt_loop_norm (b,k,f,id,c) in
        let ct : config option =
          try
            if !Utils.debug then Printf.printf "PR-LOOP-T is SAT, state %a.\n" (Id.pp "") id;
            let (b,k,f,id,c) = Option.get kct in
            let a = BD.post_cond e a in
            Some (b,(k,a),f,id,c)
          with _ ->
            if !Utils.debug then Printf.printf "PR-LOOp-T is UNSAT, state %a.\n" (Id.pp "") id;
            None in
        let cf =
          try
            if !Utils.debug then Printf.printf "PR-LOOP-F is SAT, state %a.\n" (Id.pp "") id;
            let (b,k,f,id,c) = Option.get kcf in
            let a = BD.post_cond (L.expr_neg e) a in
            Some (b,(k,a),f,id,c)
          with _ ->
            if !Utils.debug then Printf.printf "PR-LOOP-F is UNSAT, state %a.\n" (Id.pp "") id;
            None in
        ct, cf
      | _ -> raise (Failure "Wrong statement.")

    and stmt_loop_max ?modset:(modset=None) ?dirty:(dirty=false)  (b,(k,a),f,id,c) : config =
      match b with
      | Lang.Aloop (e,b0)::_ ->
        let (b,k,f,id,c) = SE.stmt_loop_max ~modset:modset ~dirty:dirty (b,k,f,id,c) in
        let b0' = Syntax_aux.baux_to_b b0 in
        let a = B.stmt_loop (Lang.Swhile (e,b0')) a in
        (* Return final configuration *)
        (b,(k,a),f,id,c)
      | _ -> raise (Failure "stmt_loop_max: wrong block")

    and exec_stmt (prc: config) : config list =
      let (b,(k,a),f,id,c) = prc in
      match b with
      | [] -> [ prc ]
      | s::_ ->
        if !Utils.debug then Printf.printf "State %a:\n%a\n%a\n" (Id.pp "") id (D.pp "  ") (k,a)
          (Prog.pp_stat "  ") (Syntax_aux.saux_to_s s);
        let conf_post = match C.step b c, s with
          | (true, c'), Lang.Aassign _ ->
            [ stmt_assign (b,(k,a),f,id,c') ]
          | (true, c'), Lang.Ainput _ ->
            [ stmt_input (b,(k,a),f,id,c') ]
          | (true, c'), Lang.Aif _ ->
            let (kt, kf) = stmt_if (b,(k,a),f,id,c') in
            (match kt, kf with
            | None, None -> []
            | Some kt, None -> [ kt ]
            | None, Some kf -> [ kf ]
            | Some kt, Some kf -> [ kt ; kf ])
          | (true, c'), Lang.Awhile _ ->
              [ stmt_while (b,(k,a),f,id,c') ]
          | (true, c'), Lang.Aloop _ ->
              let cl, cr =  stmt_loop_norm (b,(k,a),f,id,c') in
              let cl = if Option.is_some cl then [ Option.get cl ] else [] in
              let cr = if Option.is_some cr then [ Option.get cr ] else [] in
              cl @ cr
          | (false, c'), Lang.Aloop _ ->
              [ stmt_loop_max (b,(k,a),Flag.add Flag.MAX_ITE f,id,c') ]
          | _ -> raise (Failure "exec_stmt: counter/block discrepancy.") in 
        conf_post

    and exec_list (cs: config list) : config list =
      let rec aux (cs: config list) (finalcs: config list) = (
      match cs with
      | [] -> finalcs
      | conf::cs ->
        let ls = exec_stmt conf in
        (* Separate final configs from others *)
        let ls_final, ls_cont = List.fold_left
          (fun (ls_final, ls_cont) conf ->
            if get_block conf = [] then
              ((conf :: ls_final), ls_cont)
            else
              (ls_final, (conf::ls_cont)))
          ([],[]) ls in
        aux (cs @ ls_cont) (ls_final @ finalcs)) in
      aux cs []

    (** Execute configuration. *)
    and exec_block (conf: config) : config list =
      exec_list [ conf ]

    let analyze_prog p (lthr: Threshold.t) : config list =
      Printf.printf "Analyzing with product semantics.\n";
      set_thr lthr;
      let prc : config = init p in
      let prc_f = exec_block prc in
      Printf.printf "\nFinal branches: %d\n" (List.length prc_f);
      List.iter
        (fun (prc: config) ->
          let _,(k,a),_,id,_ = prc in
          Printf.printf "State %a:\n%a\n" (Id.pp "") id (PR.pp "  ") (k,a)) prc_f;
      prc_f

  end
