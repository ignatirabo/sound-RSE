open Syntax
open Relational_symbolic_domain

(*******************************************)
(* Relational symbolic execution               *)
(*******************************************)
module Rse (RD : RELATIONAL_SYMBOLIC_DOMAIN) =
  struct
    module RD = RD
    module SE = RD.SE
    module C = SE.C
    module S = SE.D
    module SP = S.SP
    module P = SP.P

    module VSet = Var.VSet
    module VMap = Var.VMap
    module L = Lang

    type config = Lang.block_rel * RD.state * Flag.t * Id.t * C.t

    (* Z3 and utilities *)
    let low_set = ref VSet.empty

    let init (p: Prog.t) : config =
      let b =
        (let b = p.pmain in
        let b = Syntax_aux.b_to_baux b in
        L.Rnormal b) in
      let r = RD.new_state (Some p) in
      let f = Flag.empty in
      let id = Id.make false in
      let c = C.empty in
      b,r,f,id,c

    let combine_kconf_lists (kcl_ls: SE.config list) (kcr_ls: SE.config list) (b: Lang.block_aux) : config list =
      if List.length kcl_ls = 0 || List.length kcr_ls = 0 then []
      else
        let aux_map (kcl: SE.config) (kcr: SE.config) : config =
          (match kcl, kcr with
          | (_,kl,fl,_,c), (_,kr,fr,_,_) ->
            let sp_r = SP.replace_id (SP.int_2id 1) (SP.int_2id 2) (S.get_sp kr) in
            let r = kl, S.set_sp sp_r kr in
            let id = Id.make false in
            let f = Flag.join fl fr in
            (L.Rnormal b,r,f,id,c)) in
        let aux_fold acc kcl =
          List.map (aux_map kcl) kcr_ls @ acc in
        List.fold_left aux_fold [] kcl_ls

    (** Compute assignment statement *)
    let stmt_assign (b,r,f,id,c) : config =
      match b with 
      | L.Rnormal (L.Aassign (v,e)::b) -> L.Rnormal b, RD.post_assign v e r, f, id, c
      | _ ->
        Printf.printf "block: %a\n" (Prog.pp_block_aux "") (L.get_normal b);
        raise (Failure "rse stmt_assign: wrong block")

    (** Compute input statement *)
    let stmt_input (b,r,f,id,c) : config =
      match b with
      | L.Rnormal (Lang.Ainput v::b) ->
        L.Rnormal b, RD.post_input v r, f, id, c
      | _ ->
        raise (Failure "rse stmt_input: wrong block")

    (** Compute if statement *)
    let stmt_if (b,r,f,id,c) :
      config option * config option * config option * config option =
      match b with
      | L.Rnormal (Lang.Aif (e,b0,b1)::b) ->
      (* We calculate the possible paths *)
        let (r_ttp, r_ffp, r_tfp, r_ftp) = match RD.post_if e r with
            | r_ttp::r_ffp::r_tfp::r_ftp::[] -> (r_ttp, r_ffp, r_tfp, r_ftp)
            | _ -> raise (Failure "wrong length RD.post_if.") in
        let ctt =
          (match r_ttp with
          | _,r_tt,P.SAT ->
            if !Utils.debug then Printf.printf "D-IF-TT is SAT, state %a.\n" (Id.pp "") id;
            Some (L.Rnormal (b0@b), r_tt, f, id, c)
          | _,_,_ ->
            if !Utils.debug then Printf.printf "D-IF-TT is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        let cff =
          (match r_ffp with
          | _,r_ff,P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-IF-FF is SAT, new state %a.\n" (Id.pp "") nid;
            Some (L.Rnormal (b1@b), r_ff, f, nid, c)
          | _,_,_ ->
            if !Utils.debug then Printf.printf "D-IF-FF is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        let ctf = 
          (match r_tfp with
          | _,r_tf,P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-IF-TF is SAT, new state %a.\n" (Id.pp "") nid;
            Some (L.Rcomp (b0,b1,b), r_tf, f, nid, c)
          | _,_,_ ->
            if !Utils.debug then Printf.printf "D-IF-TF is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        let cft =
          (match r_ftp with
          | _,r_ft,P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-IF-FT is SAT, new state %a.\n" (Id.pp "") nid;
            Some (L.Rcomp (b1,b0,b), r_ft, f, nid, c)
          | _,_,_ ->
            if !Utils.debug then Printf.printf "D-IF-FT is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        ctt, cff, ctf, cft
      | _ ->
        raise (Failure "rse stmt_if: wrong block")

    (** Compute while statement *)
    let stmt_while (b,r,f,id,c) : config =
      match b with
      | L.Rnormal (L.Awhile (e,b0)::b) -> L.Rnormal (L.Aloop (e,b0)::b), r, f, id, c
      | _ -> raise (Failure "rse stmt_while: wrong block")

    let stmt_loop_norm (b,r,f,id,c) :
      config option * config option * config option * config option =
      if !Utils.debug then
        Printf.printf "DSE Loop Norm.\n";
      match b with
      | L.Rnormal (Lang.Aloop (e,b0)::b) ->
        (let (r_ttp, r_ffp, r_tfp, r_ftp) = match RD.post_loop e r with
          | r_ttp::r_ffp::r_tfp::r_ftp::[] -> (r_ttp, r_ffp, r_tfp, r_ftp)
          | _ -> raise (Failure "wrong length RD.post_if.") in
        (* Calculate double states *)
        let ctt = begin
          match r_ttp with
          | _, r_tt, P.SAT ->
            if !Utils.debug then
              Printf.printf "D-LOOP-TT is SAT, state %a.\n" (Id.pp "") id;
            Some (L.Rnormal (b0@(Lang.Aloop(e,b0))::b), r_tt, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-TT is UNSAT, state %a.\n" (Id.pp "") id;
            None
        end in
        let cff = begin
          match r_ffp with
          | _, r_ff, P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-LOOP-FF is SAT, new state %a.\n" (Id.pp "") nid;
            let c = C.delete c in
            Some (L.Rnormal b, r_ff, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-FF is UNSAT, state %a.\n" (Id.pp "") id;
            None
        end in
        (* Executions get separated *)
        let ctf = begin
          match r_tfp with
          | _, r_tf, P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-LOOP-TF is SAT, new state %a.\n" (Id.pp "") nid;
            Some (L.Rcomp (b0@[Lang.Aloop(e,b0)],[],b), r_tf, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-TF is UNSAT, state %a.\n" (Id.pp "") id;
            None
        end in
        let cft = begin
          match r_ftp with
          | _, r_ft, P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "D-LOOP-FT is SAT, new state %a.\n" (Id.pp "") nid;
            Some (L.Rcomp ([],b0@[Lang.Aloop(e,b0)],b), r_ft, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-FT is UNSAT, state %a.\n" (Id.pp "") id;
            None
        end in
        (ctt,cff,ctf,cft))
      | _ ->
        raise (Failure "rse stmt_loop_norm: wrong block")

    let stmt_loop_max ((b,r,f,id,c): config) : config =
      if !Utils.debug_funenter then Printf.printf "RelSE Loop Max nodep.\n";
      match b with
      | L.Rnormal (L.Aloop (e,b0)::b1) ->
        begin
          (* 1. Calculate modified variables *)
          let w : VSet.t =
            (let t_id = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            let vars = S.svm_fold (fun v _ vars -> v::vars) (RD.get_svm_left r) [] in
            let p = Some { Prog.pglobs=vars ; Prog.psec=VMap.empty ; Prog.pprocs=[] ; Prog.pmain=[]} in
            let k = SE.D.new_state p in
            let kc : SE.config = (b0, SE.D.add_constraint e k, f, t_id, SE.C.empty) in
            SE.modif kc) in
          (* 2. Clear variables modified *)
          let r = Var.VSet.fold (fun v r -> RD.add_var r v) w r in
          (* 3. Negate guard *)
          let r : RD.state =
            (let not_e = L.Euop (Onot, e) in
            RD.add_constraint not_e r) in
          let (_,sl,_,_,_) = SE.stmt_loop_max ~dirty:true ((L.Aloop (e,b0)::b1),(fst r),f,id,c) in
          let (_,sr,_,_,_) = SE.stmt_loop_max ~dirty:true ((L.Aloop (e,b0)::b1),(snd r),f,id,c) in
          (* 2. Apply reduction *)
          let sl' = S.reduction sl in
          let sr' = S.reduction sr in
          let r = sl',sr' in
          if !Utils.debug then Printf.printf "Before reduction, left:\n%a\n" (S.pp "  ") sl;
          if !Utils.debug then Printf.printf "After reduction, left:\n%a\n" (S.pp "  ") sl';
          if !Utils.debug then Printf.printf "Before reduction, right:\n%a\n" (S.pp "  ") sr;
          if !Utils.debug then Printf.printf "After reduction, right:\n%a\n" (S.pp "  ") sr';
          L.Rnormal b1, r, Flag.add Flag.MAX_ITE f, id, c
        end
      | _ -> raise (Failure "rse stmt_loop_max: wrong block.")

    (** Interpret abstract state over a statement *)
    let rec exec_conf ((b, r, f, id, c): config) (stmt_loop_max : config -> config) : config list =
      match b with
      | L.Rnormal [] | L.Rcomp ([],[],[]) -> [ b, r, f, id, c ]
      | L.Rnormal (s::_) ->
        let conf_post =
          let step = C.step_rel b c in
          if !Utils.debug then
            Printf.printf "Rse exec_conf: Rnormal, step = %b\nblock =\n%a\nstate =\n%a\n" (fst step) (Prog.pp_block_rel "  ") b (RD.pp "") r;
          match step, s with
          | (true, c'), Lang.Aassign _ ->
            [ stmt_assign (b,r,f,id,c') ]
          | (true, c'), Lang.Ainput _ ->
            [ stmt_input (b,r,f,id,c') ]
          | (true, c'), Lang.Aif _ ->
            let (rtt, rff, rtf, rft) = stmt_if (b,r,f,id,c') in
            let l = if Option.is_some rtt then [ Option.get rtt ] else [] in
            let l = if Option.is_some rff then (Option.get rff)::l else l in
            let l = if Option.is_some rtf then (Option.get rtf)::l else l in
            if Option.is_some rft then (Option.get rft)::l else l
          | (true, c'), Lang.Awhile _ ->
            [ stmt_while (b,r,f,id,c') ]
          | (true, c'), Lang.Aloop _ ->
            let (rtt, rff, rtf, rft) = stmt_loop_norm (b,r,f,id,c') in
            let l = if Option.is_some rtt then [ Option.get rtt ] else [] in
            let l = if Option.is_some rff then (Option.get rff)::l else l in
            let l = if Option.is_some rtf then (Option.get rtf)::l else l in
            if Option.is_some rft then (Option.get rft)::l else l
          | (false, c'), Lang.Aloop _ ->
            [ stmt_loop_max (b,r,f,id,c') ]
          | _ -> raise (Failure "exec_stmt: counter/block discrepancy.") in 
        conf_post
      | L.Rcomp (b0,b1,b2) ->
        let kl : S.state = RD.get_state_left r in
        let kl_ls = SE.exec_block (b0,kl,f,Id.make ~message:["COMP"] true, c) in
        let kr : S.state = RD.get_state_right r in
        let kr_ls = SE.exec_block (b1,kr,f,Id.make ~message:["COMP"] true, c) in
        combine_kconf_lists kl_ls kr_ls b2

    (** We assume final states are part of final configurations. *)
    and exec_list (cs: config list) (stmt_loop_max : config -> config) : config list =
      let rec aux (cs: config list) (finalcs: config list) =
        begin
          match cs with
          | [] -> finalcs
          | c::cs ->
            let ls: config list = exec_conf c stmt_loop_max in
            (* Separate final configs from others *)
            let (ls_final, ls_cont): config list * config list =
              let aux' (ls_f,ls_c) conf = (match conf with
                | L.Rnormal [],_,_,_,_ | L.Rcomp ([],[],[]),_,_,_,_ -> (conf :: ls_f, ls_c)
                | _ -> ls_f, (conf :: ls_c)) in
              List.fold_left aux' ([],[]) ls in
            aux (cs @ ls_cont) (ls_final @ finalcs)
        end in
      aux cs []

    (** Analyze programs
        @param p Program to analyze*)
    let analyze_prog' (p: Prog.t) (lthr: Threshold.t) (stmt_loop_max : config -> config) =
      SE.set_thr lthr;
      let low_vars = VMap.filter (fun _ sec -> sec = 0) p.psec in
      let low_vars = VMap.fold (fun v _ vset -> VSet.add v vset) low_vars VSet.empty in
      low_set := low_vars;
      let cinit : config = init p in
      let cfinal = exec_list [ cinit ] stmt_loop_max in
      (* Last reduction at the end *)
      let cfinal = List.map
        (fun (b,(k_l,k_r),f,id,c) ->
          let k_l = S.reduction k_l in
          let k_r = S.reduction k_r in
          (b,(k_l,k_r),f,id,c))
        cfinal in
      Printf.printf "Final branches: %d\n\n" (List.length cfinal);
      let is_low_equal = ref true in
      let bug_found = ref false in
      let bug_configs = ref [] in
      List.iter
        (fun (_,r,f,id,c) ->
          RD.pp_id "  " stdout r id;
          if !Utils.debug then Printf.printf "f length: %d\n" (List.length f);
          let nle = not (RD.equal_in_vars r !low_set) in
          if nle then
            begin
              is_low_equal := false;
              let is_app = List.exists (fun f -> f = Flag.MAX_ITE) f in
              if is_app then
                Printf.printf "Insecure branch.\n\n"
              else
                begin
                  bug_found := true;
                  bug_configs := ([],r,f,id,c) :: !bug_configs;
                  Printf.printf "Vulnerability found.\n\n"
                end
            end
          else
            Printf.printf "Secure branch.\n\n")
        cfinal;
      begin
        if !is_low_equal then
          Printf.printf "\nProgram is non-interferent.\n"
        else if !bug_found then
          Printf.printf "\nProgram is insecure, vulnerabilities found.\n"
        else
          Printf.printf "\nCannot prove program secure or insecure.\n"
      end;
      if !Utils.debug then Printf.printf "Id counter: %d, Temporal id counter: %d\n"
        !Id.global_id !Id.global_temp_id;
      (cfinal, !is_low_equal, !bug_found)
    
    let analyze_prog p thr = analyze_prog' p thr stmt_loop_max
  end

module RseDep (RD : RELATIONAL_SYMBOLIC_DOMAIN) = struct
  (* include Rse(RD) *)
  module R = Rse(RD)
  open R
  let stmt_loop_max_dep ((b,r,f,id,c): config) : config =
    if !Utils.debug then Printf.printf "RelSE loop max with Dep.\n";
    match b with
    | L.Rnormal (L.Aloop (e,b0)::b1) ->
      begin
        (* 1. Create dep astate *)
        let module Dep = Dependences.Dep(Lattice.Latt_default)(SE)(Pre.Z3pre) in
        let module A = Ainterpreter_hypercollecting.Ai(Dep) in
        let sm = RD.rel_to_sec r in
        let baux = L.get_normal b in
        let b = Syntax_aux.baux_to_b baux in
        let dep_a = Dep.ast_from_sec sm in
        (* 2. Run dep analysis *)
        let dep_a' = A.ai_stmt dep_a (Swhile (e, b)) in
        (* 3. Get sm from dep astate *)
        let vs = Syntax_aux.vars [ L.Swhile (e,b) ] in
        let s = Dep.diff dep_a dep_a' vs in
        if !Utils.debug then Printf.printf "Calculated SecMap: %a\n" Sec_map.pp s;
        (* 4. Read secmap with changes and reflect this to the s.e. astate *)
        let w : VSet.t =
          (let t_id = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
          let vars = S.svm_fold (fun v _ vars -> v::vars) (RD.get_svm_left r) [] in
          let p = Some { Prog.pglobs=vars ; Prog.psec=VMap.empty ; Prog.pprocs=[] ; Prog.pmain=[]} in
          let k = SE.D.new_state p in
          let kc : SE.config = (b0, SE.D.add_constraint e k, f, t_id, SE.C.empty) in
          SE.modif kc) in
        let r = RD.sm_mod_r s w r in
        (* 5. Negate guard *)
        let r : RD.state =
          (let not_e = L.Euop (Onot, e) in
          RD.add_constraint not_e r) in
        let (_,kl,_,_,_) = SE.stmt_loop_max ~dirty:true ((L.Aloop (e,b0)::b1),(fst r),f,id,c) in
        let (_,kr,_,_,_) = SE.stmt_loop_max ~dirty:true ((L.Aloop (e,b0)::b1),(snd r),f,id,c) in
        if !Utils.debug then Printf.printf "Before reduction:\n%a\n" (RD.pp "  ") r;
        (* 6. Apply reduction *)
        let r = S.reduction kl, S.reduction kr in
        if !Utils.debug then Printf.printf "After reduction:\n%a\n" (RD.pp "  ") r;
        L.Rnormal b1,r,Flag.add Flag.MAX_ITE f,id,c
      end
    | _ -> raise (Failure "rse_dep stmt_loop_max: wrong block.")

    let analyze_prog p thr = analyze_prog' p thr stmt_loop_max_dep

end