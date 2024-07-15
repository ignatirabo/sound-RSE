open Analysis
open Syntax
open Symbolic_domain
open Counter

(** Maybe_pair.single symbolic execution *)
module type SINGLE_SYMBOLIC_EXEC =
  sig
    include SYMBOLIC_ANALYSIS
    val modif: config -> Var.VSet.t
    val create_config: Lang.block_aux -> D.state -> Flag.t -> Id.t -> C.t -> config
  end

module Sse (S:SYMBOLIC_DOMAIN)(C:COUNTER) : SINGLE_SYMBOLIC_EXEC =
  struct
    module D = S
    module P = D.SP.P
    module C = C

    type config = Lang.block_aux * D.state * Flag.t * Id.t * C.t
    let create_config b k f i c =
      (b,k,f,i,c)

    (** Create initial abstract configuration from program *)
    let init ?svm:(svm=None) (p: Prog.prog) : config =
      let b = p.pmain in
      let b = Syntax_aux.b_to_baux b in
      let k = match svm with
        | None -> D.new_state (Some p)
        | Some _ -> D.new_state ~svm:svm (Some p) in
      (b, k, [], Id.make false, C.empty)

    let lthr_ref = ref []
    let set_thr l = lthr_ref := l
    let get_flag (_,_,f,_,_) = f
    let get_state (_,k,_,_,_) = k
    let get_block (b,_,_,_,_) = b
    let get_id (_,_,_,id,_) = id
    let get_counter (_,_,_,_,c) = c
    let set_flag f (b,k,_,id,c) = (b,k,f,id,c)
    let set_state k (b,_,f,id,c) = (b,k,f,id,c)
    let set_block b (_,k,f,id,c) = (b,k,f,id,c)
    let set_id id (b,k,f,_,c) = (b,k,f,id,c)
    let set_counter c (b,k,f,id,_) = (b,k,f,id,c)

    (** Calculate assignment *)
    let rec stmt_assign (b,k,f,id,c) : config =
      match b with
      | Lang.Aassign (v,e)::b ->
        (b, D.post_assign v e k, f, id, c)
      | _ ->
        Printf.printf "block: %a\n" (Prog.pp_block_aux "") b;
        raise (Failure "stmt_assign: wrong block")

    (** Calculate input *)
    and stmt_input (b,k,f,id,c) : config =
      match b with
      | Lang.Ainput v::b ->
        (b, D.post_input v k, f, id, c)
      | _ -> raise (Failure "stmt_input: wrong block")

    (** Calculate if *)
    and stmt_if (b,k,f,id,c) : config option * config option =
      match b with
      | Lang.Aif (e,b0,b1)::b ->
        (* We calculate the possible paths *)
        let (kts, kfs) = match D.post_if e k with
          | kts::kfs::[] -> (kts,kfs)
          | _ -> raise (Failure "wrong length post_if.") in
        let kt = (match kts with
          | "T", kt, P.SAT ->
            if !Utils.debug then Printf.printf "S-IF-T is SAT, state %a.\n" (Id.pp "") id;
            Some (b0 @ b, kt, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "S-IF-T is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        let kf = (match kfs with
          | "F", kf, P.SAT ->
            let nid = Id.make ~message:(Id.get_message id) (Id.get_temporal id) in
            if !Utils.debug then Printf.printf "S-IF-F is SAT, new state %a.\n" (Id.pp "") nid;
            Some (b1 @ b, kf, f, nid, c)
          | _ ->
            if !Utils.debug then Printf.printf "S-IF-F is UNSAT, state %a.\n" (Id.pp "") id;
            None) in
        (kt, kf)
      | _ -> raise (Failure "stmt_if: wrong block")

    (** Compute while *)
    and stmt_while (b,k,f,id,c) : config =
      match b with
      | Lang.Awhile (e,body)::b -> (Lang.Aloop (e,body)::b, k, f, id, c)
      | _ -> raise (Failure "stmt_while: wrong block or max-ite")

    and stmt_loop_norm ((b,k,f,id,c): config) : config option * config option =
      match b with
      | Lang.Aloop (e,body)::b ->
        let (kts, kfs) = match D.post_loop e k with
          | kts::kfs::[] -> (kts,kfs)
          | _ -> raise (Failure "wrong length post_loop.") in
        let kt' = (match kts with
          | "T", kt, P.SAT ->
            if !Utils.debug then Printf.printf "D-LOOP-T is SAT.\n";
            let b' : Lang.block_aux = body @ (Lang.Aloop (e,body)::b) in
            Some (b', kt, f, id, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-T is UNSAT.\n";
            None) in
        let kf' = (match kfs with
          | "F", kf, P.SAT ->
            if !Utils.debug then Printf.printf "D-LOOP-F is SAT.\n";
            let c = C.delete c in
            Some (b, kf, f, Id.make false, c)
          | _ ->
            if !Utils.debug then Printf.printf "D-LOOP-F is UNSAT.\n";
            None) in
        kt', kf'
      | _ -> raise (Failure "stmt_loop_norm: wrong block")

    and stmt_loop_max ?modset:(modset=None) ?dirty:(dirty=false) (b,k,f,id,c) : config =
      if dirty then
        (b,k,f,id,c)
      else 
        match b with
        | Lang.Aloop (e,body)::b ->
          let w = match modset with
            | None ->
              let k_temp = D.add_constraint e k in
              modif (body, k_temp, [Flag.LOOP_APPROX], Id.make ~message:["MODIF"] true, C.empty)
            | Some w ->
              if !Utils.debug then Printf.printf "Using already calculated modif set.\n";
              w in
          if !Utils.debug then begin
            Printf.printf "Calculated set size for modif: %d Vars: " (Var.VSet.cardinal w);
            Var.VSet.iter (fun v -> Printf.printf "%s;" (Var.get_vname v)) w;
            Printf.printf "\n";
          end;
          (* Create new temp state that is clear of variables in W *)
          let k_temp = Var.VSet.fold (fun v k -> D.add_var k v) w k in
          (* Add negated guard to SP *)
          let ne = (Lang.Euop (Onot, e)) in
          let k = D.add_constraint ne k_temp in
          (* Return final configuration *)
          (b, k, f, id, c)
        | _ -> raise (Failure "stmt_loop_max: wrong block")

    (** Execute one step of configuration. *)
    and exec_stmt (b,k,f,id,c) : config list =
      match b with
      | [] -> [ ([],k,f,id,c) ]
      | s::_ ->
        if !Utils.debug then Printf.printf "State %a:\n%a\n%a\n" (Id.pp "") id (D.pp "  ") k
          (Prog.pp_stat "  ") (Syntax_aux.saux_to_s s);
        let conf_post = match C.step b c, s with
          | (true, c'), Lang.Aassign _ ->
            [ stmt_assign (b,k,f,id,c') ]
          | (true, c'), Lang.Ainput _ ->
            [ stmt_input (b,k,f,id,c') ]
          | (true, c'), Lang.Aif _ ->
            let (kt, kf) = stmt_if (b,k,f,id,c') in
            (match kt, kf with
            | None, None -> []
            | Some kt, None -> [ kt ]
            | None, Some kf -> [ kf ]
            | Some kt, Some kf -> [ kt ; kf ])
          | (true, c'), Lang.Awhile _ ->
              [ stmt_while (b,k,f,id,c') ]
          | (true, c'), Lang.Aloop _ ->
              let cl, cr =  stmt_loop_norm (b,k,f,id,c') in
              let cl = if Option.is_some cl then [ Option.get cl ] else [] in
              let cr = if Option.is_some cr then [ Option.get cr ] else [] in
              cl @ cr
          | (false, c'), Lang.Aloop _ ->
              [ stmt_loop_max (b,k,Flag.add Flag.MAX_ITE f,id,c') ]
          | _ -> raise (Failure "exec_stmt: counter/block discrepancy.") in 
        conf_post

    (** Execute list of configurations until final configuration is reached. *)
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

    (** Execute configuration and return set of modifiable variables. *)
    and modif (cinit: config) : Var.VSet.t =
      let rec modif_aux baux vset : Var.VSet.t =
        match baux with
        | [] -> vset
        | (Lang.Aassign (v,_))::baux
        | (Lang.Ainput v)::baux ->
            modif_aux baux (Var.VSet.add v vset)
        | (Lang.Aif (_, b0, b1))::baux ->
            let vset = modif_aux b0 vset in
            let vset = modif_aux b1 vset in
            modif_aux baux vset
        | (Lang.Awhile (_,b0))::baux
        | (Lang.Aloop (_,b0))::baux ->
            let vset = modif_aux b0 vset in
            modif_aux baux vset
      in
      let b = get_block cinit in
      if !Utils.debug then Printf.printf "Begin modif calculation for following block:\n";
      if !Utils.debug then Printf.printf "%a" (Prog.pp_block_aux "  ") b;
      (* Steps: *)
      (* Get assigned variables in block *)
      let vset = modif_aux b Var.VSet.empty in
      if !Utils.debug then Printf.printf "modif_aux includes %d vars.\n" (Var.VSet.cardinal vset);
      (* Clear variables in vset *)
      let k = Var.VSet.fold (fun v k -> D.add_var k v) vset (get_state cinit) in
      let cinit = set_state k cinit in
      (* 2. Execute SSE over k-configuration *)
      let cfinal = exec_block cinit in
      (* 3. If the value of a variable chanexpr list refged, then that variables is in W set *)
      let vset = List.fold_left (fun res conf ->
        let d = D.diff (get_state cinit) (get_state conf) vset in
        Var.VSet.union res d)
        Var.VSet.empty cfinal in
      vset

    (** Analyze program *)
    let analyze_prog p thr =
      set_thr thr;
      let cinit = init p in
      let cfinal = exec_block cinit in
      let cfinal = List.map (fun (b,k,f,id,c) -> (b,k,f,Id.set_message "Final" id,c)) cfinal in
      Printf.printf "\nFinal branches: %d\n" (List.length cfinal);
        List.iter
          (fun (kc: config) ->
            let _,k,_,id,_ = kc in
            Printf.printf "id: %a\n%a" (Id.pp "") id (D.pp "  ") k)
          cfinal;
      cfinal
  end
