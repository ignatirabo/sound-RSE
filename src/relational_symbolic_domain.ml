open Symbolic_domain
open Single_symbolic
open Syntax

module type RELATIONAL_SYMBOLIC_DOMAIN = sig
  module SE : SINGLE_SYMBOLIC_EXEC
  type zexpr := SE.D.SP.P.zexpr
  type zval = zexpr * zexpr
  val zval_to_list : zval -> zexpr list
  val zval_from_list : zexpr list -> zval
  (* we need some kind of relation between zval and zexpr *)
  type sp := SE.D.SP.t
  type svm = SE.D.svm
  type state = SE.D.state * SE.D.state
  val pp: string -> out_channel -> state -> unit
  val pp_id: string -> out_channel -> state -> Id.t -> unit
  (* Structure *)
  val new_state: ?svm:(svm*svm) option -> Prog.t option -> state

  val svm_empty: svm * svm
  val svm_of_map: zval Var.VMap.t -> svm * svm
  val svm_iter: (Var.t -> zval -> unit) -> svm * svm -> unit
  val svm_fold: (Var.t -> zval -> 'a -> 'a) -> svm * svm -> 'a -> 'a
  val svm_mapi: (Var.t -> zval -> 'a) -> svm * svm -> 'a Var.VMap.t
  val svm_find: Var.t -> svm * svm -> zval 

  (* This functions can be defined all the same for any of these Domains *)
  val get_sp: state -> sp * sp
  val get_svm: state -> svm * svm
  val set_sp: sp -> bool -> state -> state
  val set_svm: svm -> bool -> state -> state

  val get_svm_left: state -> SE.D.svm
  val get_svm_right: state -> SE.D.svm
  val get_state_left: state -> SE.D.state
  val get_state_right: state -> SE.D.state

  val add_var: state -> Var.t -> state
  val add_constraint: Lang.expr -> state -> state
  val find: Var.t -> state -> zval
  val assign: Var.t -> zval -> state -> state
  val diff: state -> state -> Var.VSet.t -> Var.VSet.t
  val reduction: state -> state
  (* Abstract *)
  val post_input: Var.t -> state -> state
  val post_assign: Var.t -> Lang.expr -> state -> state
  val post_if: Lang.expr -> state -> (string * state * SE.D.SP.P.zstatus) list
  val post_loop: Lang.expr -> state -> (string * state * SE.D.SP.P.zstatus) list

  val rel_to_sec: state -> Sec_map.t
  val equal_in_vars: state -> Var.VSet.t -> bool
  val sm_mod_r: Sec_map.t -> Var.VSet.t -> state -> state
end

module RelSD (SE:SINGLE_SYMBOLIC_EXEC) : RELATIONAL_SYMBOLIC_DOMAIN =
  struct
    open Lang
    module F = Flag
    module MP = Maybe_pair
    module SM = Sec_map

    module SE = SE
    module S = SE.D
    module SP = S.SP
    module P = SP.P

    module VMap = Var.VMap
    module VSet = Var.VSet

    type zexpr = P.zexpr
    type zval = P.zexpr * P.zexpr
    let zval_to_list (zvl,zvr) = [ zvl ; zvr ]
    let zval_from_list = function
    | [ zvl ; zvr ] -> zvl,zvr 
    | _ -> raise (Failure "zval_from_list: wrong list length.")

    type sp = SP.t
    let idl = SP.int_2id 1
    let idr = SP.int_2id 2
    type svm = S.svm

    let svm_empty = S.svm_empty, S.svm_empty
    let svm_update v (zvl, zvr) (svml,svmr) = S.svm_update v zvl svml, S.svm_update v zvr svmr
    let svm_find v (svml,svmr) = S.svm_find v svml, S.svm_find v svmr
    let svm_of_map _ =
      raise (Failure "svm_of_map not implemented.")
      (* S.svm_of_map smap, S.svm_of_map smap' *)
    let svm_iter f (svml,svmr) =
      S.svm_iter (fun v zvl -> f v (zvl,S.svm_find v svmr)) svml
    let svm_fold f (svml,svmr) =
      S.svm_fold (fun v zvl -> f v (zvl,S.svm_find v svmr)) svml
    let svm_mapi f (svml,svmr) =
      S.svm_mapi (fun v zvl -> f v (zvl,S.svm_find v svmr)) svml

    type state = S.state * S.state

    let pp (indent: string) chan (d: state) =
      Printf.fprintf chan "%a\n%a" (S.pp indent) (fst d) (S.pp indent) (snd d)

    let pp_id indent chan r id =
      Printf.fprintf chan "%sRelational state ID: %a\n" indent (Id.pp "") id;
      pp indent chan r

    (** Create initial abstract state from program *)
    let new_state ?svm:(svm=None) (p:Prog.t option) : state =
      let svml,svmr =
        begin
          match svm with
          | None ->
            let p = Option.get p in
            List.fold_left
              (fun svm v ->
                let nn = Prog.new_name v (VMap.find v p.psec) in
                let zv_pair : zval =
                  begin
                    if MP.is_single nn then
                      let str0 = MP.get_single nn in
                      let s0 = P.mk_string str0 in
                      let exp0 : zexpr = P.mk_const s0 in
                      (exp0, exp0)
                    else
                      let (str0, str1) = MP.get_pair nn in
                      let s0 = P.mk_string str0 in
                      let s1 = P.mk_string str1 in
                      let exp0 = P.mk_const s0 in
                      let exp1 = P.mk_const s1 in
                      (exp0, exp1)
                  end in
                svm_update v zv_pair svm) svm_empty p.pglobs
          | Some (svml,svmr) -> svml,svmr
        end in
      S.new_state ~svm:(Some svml) None, S.new_state ~svm:(Some svmr) None

    (* TODO *)
    let diff _ _ _ = raise (Failure "Undefined diff.")

    let get_sp (sl,sr) : sp * sp = S.get_sp sl, S.get_sp sr
    let get_svm (sl,sr) : svm * svm = S.get_svm sl, S.get_svm sr

    let get_svm_left (sl,_) = S.get_svm sl
    let get_svm_right (_,sr) = S.get_svm sr

    let get_state_left (sl,_) = sl
    let get_state_right (_,sr) = sr

    let set_sp sp left (sl,sr) = 
      if left then (S.set_sp sp sl,sr)
      else (sl, S.set_sp sp sr)
    let set_svm svm left (sl,sr) =
      if left then (S.set_svm svm sl,sr) else (sl, S.set_svm svm sr)
    let assign v (zvl,zvr) (sl,sr) : state = 
      S.assign v zvl sl, S.assign v zvr sr
    let add_var_aux r v i =
      if i = 0 then
        let str = MP.get_single (Prog.new_name v 0) in
        let s = P.mk_string str in
        let exp = P.mk_const s in
        assign v (exp,exp) r
      else
        let str0, str1 = MP.get_pair (Prog.new_name v 1) in
        let s0 = P.mk_string str0 in
        let s1 = P.mk_string str1 in
        let exp0 = P.mk_const s0 in
        let exp1 = P.mk_const s1 in
        assign v (exp0,exp1) r
    let add_var r v = add_var_aux r v 1 

    let add_constraint (e: expr) (sl,sr: state) =
      let sl = S.add_constraint ~id:(Some idl) e sl in
      let sr = S.add_constraint ~id:(Some idr) e sr in
      (sl,sr)

    let find v (sl,sr) =
      S.find v sl, S.find v sr

    (** Calculate secmap of abstract state *)
    let rel_to_sec (sl,sr: state) : SM.t =
      Var.VMap.fold
        (fun v zvl acc ->
          let zvr = S.find v sr in
            if zvl = zvr then SM.add v 0 acc else SM.add v 1 acc)
        (S.get_svm sl) SM.empty

    let is_equal v (sl,sr: state) =
      let vzl,vzr = svm_find v (S.get_svm sl, S.get_svm sr) in
      vzl = vzr 

    exception Innapropiate_secmap

    (** Modify abstract state to reflect information from secmap.
        Iterate over values of variable set, using secmap information when available.
        If information is not available, wipe variable.
        Return relational state with these changes.
        @param sm Security map that reflect differences
        @param w Set of modifiable variables
        @param r Relational symbolic state to modify *)
    let sm_mod_r (sm: SM.t) (w: Var.VSet.t) (sl,sr: state) : state =
      if !debug then Printf.printf "Entering sm_mod_ast.\n";
      let aux v svm_p : svm * svm =
        (let i = try SM.find v sm with Not_found ->
          if is_equal v (sl,sr) then 0
          else 1 in
        if i = 0 then
          let str: string = MP.get_single (Prog.new_name v 0) in
          let s = P.mk_string str in
          let exp = P.mk_const s in
          svm_update v (exp,exp) svm_p
        else if i = 1 then
          let str0, str1 = MP.get_pair (Prog.new_name v 1) in
          let s0 = P.mk_string str0 in
          let s1 = P.mk_string str1 in
          let exp0 = P.mk_const s0 in
          let exp1 = P.mk_const s1 in
          svm_update v (exp0,exp1) svm_p
        else
          raise Innapropiate_secmap) in
      let svml,svmr = Var.VSet.fold (fun v svm_p -> aux v svm_p) w (S.get_svm sl, S.get_svm sr) in
      S.set_svm svml sl, S.set_svm svmr sr 

    let reduction s = s

    (* Abstract operations *)

    (** Assign expression e to variable v on abstract state a0 *)
    let post_assign (v: Var.t) (e: expr) (sl,sr: state) : state =
      S.post_assign v e sl, S.post_assign v e sr

    (** Assign random value to variable v on abstract state a0 *)
    (* Note: this case is not used *)
    let post_input (v: Var.t) (sl,sr: state) : state =
      S.post_input v sl, S.post_input v sr

    (** Apply e's contraints to a0, based on boolean values bool0 and bool1 *)
    let post_if e r : (string * state * P.zstatus) list =
      let (sl_ts, sl_fs) = match S.post_if e (fst r) with
        | sl_ts::sl_fs::[] -> (sl_ts,sl_fs)
        | _ -> raise (Failure "wrong length post_if.") in
      let (sr_ts, sr_fs) = match S.post_if e (snd r) with
        | sr_ts::sr_fs::[] -> (sr_ts,sr_fs)
        | _ -> raise (Failure "wrong length post_if.") in
      let (str_lt, s_lt, zstat_lt),(str_lf, s_lf, zstat_lf) = sl_ts, sl_fs in
      if !Utils.debug then
        Printf.printf "RD - POST-IF\nleft true: %s, %a;%a\nleft false: %s, %a;%a\n"
          str_lt P.pp_zstatus zstat_lt (S.pp "  ") s_lt 
          str_lf P.pp_zstatus zstat_lf (S.pp "  ") s_lf;
      let aux (_,sl,ls) (_,sr,rs) =
        begin
          match ls, rs with
          | P.SAT, P.SAT ->
            let status, _ = P.check (SP.to_list (S.get_sp sl) @ SP.to_list (S.get_sp sr)) in
            "", (sl, sr), status
          | _ -> "", (sl, sr), P.UNSAT
        end in
      let rtt = aux sl_ts sr_ts in
      let rff = aux sl_fs sr_fs in
      let rtf = aux sl_ts sr_fs in
      let rft = aux sl_fs sr_ts in
      [ rtt ; rff ; rtf ; rft ]

    let post_loop e d =
      post_if e d

    (** Given an abstract state a, return true iff is low-equal, meaning
        all low variables share the same value in both executions.
        If the abstract state fails to be low-equal, we print a possible model. *)
    let equal_in_vars (r : state) (vs: VSet.t) : bool =
      let ni : P.zexpr list = Var.VSet.fold
          (fun v ni ->
            try
              ignore (Var.VSet.find v vs);
              let (zvl,zvr) : zval = find v r in
              if zvl != zvr then
                let se = P.mk_eq zvl zvr in
                se::ni
              else
                ni
            with Not_found ->
              ni) vs [] in
      if (List.length ni) = 0 then (Printf.printf "Low variables are necessarily low.\n"; true)
      else
        begin
          let prop =
            begin
              let sp_l,sp_r = get_sp r in
              let sp : zexpr list = SP.to_list sp_l @ SP.to_list sp_r in
              match List.length ni with
              | 0 -> sp
              | 1 ->
                let ni = P.mk_not (List.hd ni) in
                ni::sp
              | _ ->
                let ni_and = P.mk_and ni in
                let ni_and = P.mk_not ni_and in
                ni_and::sp
            end in
            begin
              if List.length prop = 0 then
                Printf.printf "Non-interference prop is empty.\n"
              else
                Printf.printf "Non-interference prop:\n%a\n" P.print_prop prop
            end;
            let status, solver = P.check prop in
            if status = P.SAT then
              begin
                begin
                  match P.get_string_model prop (status, solver) with
                  | Some m ->
                    Printf.printf "Model:\n%s\n" m
                  | None ->
                    Printf.printf "Failed to get model.\n"
                end;
                false
              end
            else
              true
        end
  end
