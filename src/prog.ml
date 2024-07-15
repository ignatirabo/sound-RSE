open Syntax

(** Procedures *)
type proc = { pname: string ;     (* proc name *)
              pbody: Lang.block ;      (* proc body, a block *) }

(** Programs *)
type prog = { pglobs: Var.t list ;  (* global variables *)
              psec: int Var.VMap.t; (* security level *)
              pprocs: proc list ;   (* procedures *)
              pmain:  Lang.block ;       (* body of main *) }
let empty_prog = {pglobs=[] ;  psec=Var.VMap.empty ; pprocs=[] ; pmain=[]}
type t = prog

module SSet = Set.Make(String)
let used_names = ref SSet.empty
let clear_names : unit =
  used_names := SSet.empty
let new_name (v: Var.t) (i: int) : string Maybe_pair.t =
  if i > 0 then
    begin
      let rec aux vname = function
      | (i0, i1) ->
        let str0 = String.concat "" [vname; "_"; Int.to_string i0] in
        let str1 = String.concat "" [vname; "_"; Int.to_string i1] in
        let op0 = (try Some (SSet.find str0 !used_names)
        with Not_found -> None) in
        let op1 = (try Some (SSet.find str1 !used_names)
        with Not_found -> None) in
        if (op0 = None && op1 = None) then (
          used_names := SSet.add str0 !used_names;
          used_names := SSet.add str1 !used_names;
          Maybe_pair.pair (str0, str1))
        else
          aux vname (i0+2, i1+2) in
      aux (Var.get_vname v) (0, 1)
    end
  else
    begin
      let rec aux vname = function
      | i0 ->
        let str0 = String.concat "" [vname; "_"; Int.to_string i0] in
        let op0 = (try Some (StringSet.find str0 !used_names)
        with Not_found -> None) in
        if (op0 = None ) then (
          used_names := StringSet.add str0 !used_names;
          Maybe_pair.single str0)
        else
          aux vname (i0+1) in
      aux (Var.get_vname v) 0
    end

(* Binding variables *)
(* - Fixes the type of each variable occurrence
 * - Rejects programs with undefined variables
 * - Rejects programs with calls to undefined procedures *)
let binding prog =
  let do_procname pname body =
    let rec do_stat env s =
      let rec do_vname n = function
        | [ ] ->
            failwith (Printf.sprintf "var %s not found in proc %s" n pname)
        | x :: env ->
            if n = Var.get_vname x then x else do_vname n env in
      let do_var x = do_vname (Var.get_vname x) env in
      let rec do_expr e =
        match e with
        | Lang.Ecsti _ | Lang.Ecstb _ -> e
        | Lang.Evar x -> Lang.Evar (do_var x)
        | Lang.Euop (o, e0) -> Lang.Euop (o, do_expr e0)
        | Lang.Eop (e0, o, e1) -> Lang.Eop (do_expr e0, o, do_expr e1) in
      match s with
      | Lang.Sassign (x, e) ->
          env, Lang.Sassign (do_var x, do_expr e)
      | Lang.Sinput x ->
          env, Lang.Sinput (do_var x)
      | Lang.Sif (e, b0, b1) ->
          env, Lang.Sif (do_expr e, do_block env b0, do_block env b1)
      | Lang.Swhile (e, b) ->
          env, Lang.Swhile (do_expr e, do_block env b)
    and do_block env block =
      let _, block =
        List.fold_left
          (fun (env,b) stat ->
            let env, stat = do_stat env stat in
            env, stat :: b
          ) (env, [ ]) block in
      List.rev block in
    { pname = pname ;
      pbody = do_block prog.pglobs body } in
  let do_proc p = do_procname p.pname p.pbody in
  { prog with
    pprocs = List.map do_proc prog.pprocs;
    pmain  = (do_procname "main" prog.pmain).pbody }

(* Pretty-printing *)
let rec pp_expr chan = function
  | Lang.Ecsti i -> Printf.fprintf chan "%d" i
  | Lang.Ecstb b -> Printf.fprintf chan "%b" b
  | Lang.Evar x -> Printf.fprintf chan "%s" (Var.get_vname x)
  | Lang.Euop (o, e0) ->
      Printf.fprintf chan "%s (%a)" (Ops.uop_2str o) pp_expr e0
  | Lang.Eop (e0, o, e1) ->
      Printf.fprintf chan "(%a) %s (%a)" pp_expr e0 (Ops.op_2str o) pp_expr e1
let rec pp_stat indent chan = function
  | Lang.Sassign (x, e) ->
      Printf.fprintf chan "%s%s = %a;\n" indent (Var.get_vname x) pp_expr e
  | Lang.Sinput x ->
      Printf.fprintf chan "%sinput( %s );\n" indent (Var.get_vname x)
  | Lang.Sif (e, b0, b1) ->
      let indentn = indent^"    " in
      if List.length b1 = 0 then
        Printf.fprintf chan "%sif( %a ){\n%a%s}\n" indent pp_expr e
          (pp_block indentn) b0 indent
      else
        Printf.fprintf chan "%sif( %a ){\n%a%s} else {\n%a%s}\n" indent pp_expr e
          (pp_block indentn) b0 indent (pp_block indentn) b1 indent
  | Lang.Swhile (e, b) ->
      let indentn = indent^"    " in
      Printf.fprintf chan "%swhile( %a ){\n%a%s}\n" indent pp_expr e
        (pp_block indentn) b indent
and pp_block indent chan = function
  | [ ] -> ( )
  | s :: b -> Printf.fprintf chan "%a%a" (pp_stat indent) s (pp_block indent) b
let rec pp_stmt_aux indent chan = function
  | Lang.Aassign (x, e) ->
      Printf.fprintf chan "%s%s = %a;\n" indent (Var.get_vname x) pp_expr e
  | Lang.Ainput x ->
      Printf.fprintf chan "%sinput( %s );\n" indent (Var.get_vname x)
  | Lang.Aif (e, b0, b1) ->
      let indentn = indent^"    " in
      if List.length b1 = 0 then
        Printf.fprintf chan "%sif( %a ){\n%a%s}\n" indent pp_expr e
          (pp_block_aux indentn) b0 indent
      else
        Printf.fprintf chan "%sif( %a ){\n%a%s} else {\n%a%s}\n" indent pp_expr e
          (pp_block_aux indentn) b0 indent (pp_block_aux indentn) b1 indent
  | Awhile (e, b) ->
      let indentn = indent^"    " in
      Printf.fprintf chan "%swhile( %a ){\n%a%s}\n" indent pp_expr e
        (pp_block_aux indentn) b indent
  | Aloop (e, b) ->
      let indentn = indent^"    " in
      Printf.fprintf chan "%sloop( %a ){\n%a%s}\n" indent pp_expr e
        (pp_block_aux indentn) b indent
and pp_block_aux indent chan = function
  | [ ] -> ( )
  | s :: b -> Printf.fprintf chan "%a%a" (pp_stmt_aux indent) s (pp_block_aux indent) b
and pp_block_rel indent chan = function
  | Lang.Rnormal b -> Printf.fprintf chan "Rnormal: "; pp_block_aux indent chan b
  | Lang.Rcomp (bl,br,b) ->
    begin
      Printf.fprintf chan "Rcomp:\n left block: ";
      pp_block_aux indent chan bl;
      Printf.fprintf chan "right block: ";
      pp_block_aux indent chan br;
      Printf.fprintf chan "tail block: ";
      pp_block_aux indent chan b;
    end

let pp_decl indent chan v =
  Printf.fprintf chan "%s%s %s;\n" indent (typ_2str (Var.get_vtype v)) (Var.get_vname v)
let pp_security chan (sec : int Var.VMap.t) =
  let aux indent chan sec = Var.VMap.iter
    (fun v i ->
      Printf.fprintf chan "%s%s -> %d\n" indent (Var.get_vname v) i)
    sec in
  Printf.fprintf chan "security:\n  {\n%a  }\n" (aux "    ") sec
let pp_proc chan p =
  Printf.fprintf chan "%s:\n  {\n%a  }\n" p.pname (pp_block "    ") p.pbody
let pp_prog chan p =
  List.iter (pp_decl "" chan) p.pglobs;
  pp_security chan p.psec;
  List.iter (pp_proc chan) p.pprocs;
  pp_proc chan { pname = "main" ; pbody = p.pmain }
let pp_globs chan p =
  Printf.fprintf chan "{";
  Printf.fprintf chan " %s" (Var.get_vname (List.hd p.pglobs));
  List.iter
    (fun v -> Printf.printf "; %s" (Var.get_vname v))
    (List.tl p.pglobs);
  Printf.fprintf chan " }"