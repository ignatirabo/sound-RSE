open Mode

(* Temporal opens *)
(* open Dependences *)

module AI = Ainterpreter

open Syntax

let analyze p (mode, rel_dom, non_rel_dom, apron) : bool * bool =
  match mode with
  | M_interpret -> begin
    match Interpreter.interp_prog_trc p with
    | Interpreter.Trc (memi, memf) ->
      Printf.printf "Initial memory: %a\n" Interpreter.mem_pp memi;
      Printf.printf "Final memory: %a\n" Interpreter.mem_pp memf;
      (false, false)
    | Bottom ->
      Printf.printf "Trace is bottom\n";
      (false, false)
    end
  | M_nonrel ->
    begin
      match non_rel_dom with
      | S_sse ->
        Printf.printf "SoundSE.\n";
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module A = Single_symbolic.Sse(S)(C) in
        let  _ = A.analyze_prog p [] in
        (false, false)
      | S_apron ->
        Printf.printf "Numerical domain.\n";
        let module D = AI.Dom_Apron(AI.PA_box) in
        let module A = AI.Ai(D) in
        let _ = A.analyze_prog p [] in
        (false, false)
      | S_all ->
        Printf.printf "SSE + Numerical domain.\n";
        (match apron with
        | A_box ->
          let module D = AI.Dom_Apron(AI.PA_box) in
          let module B = AI.Ai(D) in
          let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
          let module C = Counter.CounterConstant4 in
          let module SE = Single_symbolic.Sse(S)(C) in
          let module PR = Product.Pr_Single_Apron(SE)(B) in
          let module A = Product.Pr_Exec(PR) in
          let _ = A.analyze_prog p [] in
          (false, false)
        | A_polka ->
          let module D = AI.Dom_Apron(AI.PA_polka) in
          let module B = AI.Ai(D) in
          let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
          let module C = Counter.CounterConstant4 in
          let module SE = Single_symbolic.Sse(S)(C) in
          let module PR = Product.Pr_Single_Apron(SE)(B) in
          let module A = Product.Pr_Exec(PR) in
          let _ = A.analyze_prog p [] in
          (false, false))
      | _ ->  raise (Failure "Undefined non-rel domain.")
    end
  | M_rel ->
    (match rel_dom, non_rel_dom with
    | D_dep, _ ->
        Printf.printf "Dependences.\n";
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module SE = Single_symbolic.Sse(S)(C) in
        let module D = Dependences.Dep(Lattice.Latt_default)(SE)(Pre.Z3pre) in
        let module A = Ainterpreter_hypercollecting.Ai(D) in
        let (_,b,b') = A.analyze_prog p in
        b,b'
    | D_none, _ -> raise (Failure "Not possible.")
    | D_rse, S_sse | D_rse, S_none ->
      Printf.printf "RelSE with SSE.\n";
      let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
      let module C = Counter.CounterConstant4 in
      let module SE = Single_symbolic.Sse(S)(C) in
      let module RD = Relational_symbolic_domain.RelSD(SE) in 
      let module A = Relational_symbolic.Rse(RD) in
      let (_,b,b') = A.analyze_prog p Threshold.empty in
      (b,b')
    | D_rse, S_all | D_rse, S_apron ->
      Printf.printf "RelSE with SSE + Numerical domain.\n";
      (match apron with
      | A_box ->
        let module D = AI.Dom_Apron(AI.PA_box) in
        let module B = AI.Ai(D) in
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module SE = Single_symbolic.Sse(S)(C) in
        let module PR = Product.Pr_Single_Apron(SE)(B) in
        let module PRE = Product.Pr_Exec(PR) in
        let module RD = Relational_symbolic_domain.RelSD(PRE) in 
        let module A = Relational_symbolic.Rse(RD) in
        let (_,b,b') = A.analyze_prog p Threshold.empty in
        (b,b')
      | A_polka -> 
        let module D = AI.Dom_Apron(AI.PA_polka) in
        let module B = AI.Ai(D) in
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module SE = Single_symbolic.Sse(S)(C) in
        let module PR = Product.Pr_Single_Apron(SE)(B) in
        let module PRE = Product.Pr_Exec(PR) in
        let module RD = Relational_symbolic_domain.RelSD(PRE) in 
        let module A = Relational_symbolic.Rse(RD) in
        let (_,b,b') = A.analyze_prog p Threshold.empty in
        (b,b')
      )
    | D_all, S_sse | D_all, S_none ->
      Printf.printf "RelSE with Dependences and SSE.\n";
      let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
      let module C = Counter.CounterConstant4 in
      let module SE = Single_symbolic.Sse(S)(C) in
      let module RD = Relational_symbolic_domain.RelSD(SE) in 
      let module A = Relational_symbolic.RseDep(RD) in
      let (_,b,b') = A.analyze_prog p Threshold.empty in
      (b,b')
    | D_all, S_all | D_all, S_apron ->
      Printf.printf "RelSE with SSE + Numerical domain and Dependences.\n"; flush stdout;
      (match apron with
      | A_box -> 
        let module D = AI.Dom_Apron(AI.PA_box) in
        let module B = AI.Ai(D) in
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module SE = Single_symbolic.Sse(S)(C) in
        let module PR = Product.Pr_Single_Apron(SE)(B) in
        let module PRE = Product.Pr_Exec(PR) in
        let module RD = Relational_symbolic_domain.RelSD(PRE) in 
        let module A = Relational_symbolic.RseDep(RD) in
        let (_,b,b') = A.analyze_prog p Threshold.empty in
        (b,b')
      | A_polka -> 
        let module D = AI.Dom_Apron(AI.PA_polka) in
        let module B = AI.Ai(D) in
        let module S = Symbolic_domain.Ss(Symbolic_path.SPath(Pre.Z3pre)) in
        let module C = Counter.CounterConstant4 in
        let module SE = Single_symbolic.Sse(S)(C) in
        let module PR = Product.Pr_Single_Apron(SE)(B) in
        let module PRE = Product.Pr_Exec(PR) in
        let module RD = Relational_symbolic_domain.RelSD(PRE) in 
        let module A = Relational_symbolic.RseDep(RD) in
        let (_,b,b') = A.analyze_prog p Threshold.empty in
        (b,b')))

let test_program (p: Prog.t) : (string * bool * bool) list = 
  (* RedSoundRSE: Dep with RedSoundSE: Polyhedra *)
  Printf.printf "Start M_rel, D_all, S_all, A_polka\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_all, S_all, A_polka) in
  let t = [("RedSoundRSE: Dep with RedSoundSE: Polyhedra", loweq, bug)] in
  (* RedSoundRSE: Dep with RedSoundSE: Intervals *)
  Printf.printf "Start M_rel, D_all, S_all, A_box\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_all, S_all, A_box) in
  let t = ("RedSoundRSE: Dep with RedSoundSE: Intervals", loweq, bug)::t in
  (* RedSoundRSE: Dep with SoundSE *)
  Printf.printf "Start M_rel, D_all, S_sse, A_box\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_all, S_sse, A_box) in
  let t = ("RedSoundRSE: Dep with SoundSE", loweq, bug)::t in
  (* SoundRSE with RedSoundSE: Polyhedra *)
  Printf.printf "Start M_rel, D_rse, S_all, A_polka\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_rse, S_all, A_polka) in
  let t = ("SoundRSE with RedSoundSE: Polyhedra", loweq, bug)::t in
  (* SoundRSE with RedSoundSE: Intervals *)
  Printf.printf "Start M_rel, D_rse, S_all, A_box\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_rse, S_all, A_box) in
  let t = ("SoundRSE with RedSoundSE: Intervals", loweq, bug)::t in
  (* SoundRSE with SoundSE *)
  Printf.printf "Start M_rel, D_rse, S_sse, A_box\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_rse, S_sse, A_box) in
  let t = ("SoundRSE with SoundSE", loweq, bug)::t in
  (* Dependences *)
  Printf.printf "Start M_rel, D_dep, S_none, A_box\n"; flush stdout;
  let (loweq, bug) = analyze p (M_rel, D_dep, S_none, A_box) in
  let t = ("Dependences", loweq, bug)::t in
  t

let test () =
  let programs = ["programs/vmcai/prog-2a.code"; "programs/vmcai/prog-2b.code"; "programs/vmcai/prog-2c.code";
    "programs/vmcai/prog-2d.code"; "programs/vmcai/prog-8a.code"; "programs/vmcai/prog-8b.code";
    "programs/vmcai/prog-8c.code"; "programs/vmcai/prog-8d.code"] in
  let programs = List.map (fun f -> (f, prog f)) programs in
  let programs = List.fold_left
    (fun acc (f,p) ->
      Printf.printf "Testing %s\n" f; flush stdout;
      StringMap.add f (test_program p) acc)
    StringMap.empty programs in
  programs

let main ( ) =
  Printf.printf "Starting.\n";
  try begin
    let (smode, mode, rdom, nrdom, apron, filename) = parse() in
    begin
      match smode with
      | SM_file ->
        Printf.printf "File mode.\n";
        let p = prog filename in
        ignore (analyze p (mode, rdom, nrdom, apron))
      | SM_test ->
        Printf.printf "Testing mode.\n"; flush stdout;
        let t = test() in
        let aux_bool b = if b then "Yes" else "No" in
        (* Generate CSV *)
        let oc = open_out "test.csv" in
        Printf.fprintf oc "Filename,Analysis,Noninterferent?,Bug found?\n";
        Printf.printf "Filename,Analysis,Noninterferent?,Bug found?\n"; flush stdout;
        Syntax.StringMap.iter (fun f l->
          List.iter (fun (s, ni, bug) -> 
            Printf.fprintf oc "%s,%s,%s,%s\n" f s (aux_bool ni) (aux_bool bug);
            Printf.printf "%s,%s,%s,%s\n" f s (aux_bool ni) (aux_bool bug);
            flush stdout) l) t;
        close_out oc;
    end;
    Printf.printf "Finished.\n"
  end with _ -> Printf.printf "Failed to parse.\n"

let _ = ignore (main ( ))
