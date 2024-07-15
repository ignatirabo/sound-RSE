open Syntax
open Syntax.Ops
open Syntax.Lang

(** Definition of memory states and operations over them *)
(* A memory state is simply an association list that
 * collects the stack of variables *)
type value =
  | Vint of int
  | Vbool of bool
type mem = (string * value) list

(** Operations on memories *)
(* Empty memory *)
let mem_empty = [ ]
let mem_read (n: string) (m: mem): value =
  let rec aux = function
    | [ ] -> failwith (Printf.sprintf "read: variable %s not found" n)
    | (var, value) :: m -> if n = var then value else aux m in
  aux m
(* Add a new variable to memory *)
let mem_add (x: Var.t) (mem: mem): mem =
  let v =
    match Var.get_vtype x with
    | Tint -> Vint 0
    | Tbool -> Vbool true in
  (Var.get_vname x, v) :: mem
(* Write into a variable *)
let mem_update (n: string) (v: value) (m: mem): mem =
  let rec aux = function
    | [ ] -> failwith (Printf.sprintf "update: variable %s not found" n)
    | ((var, ov) as r) :: m ->
        if n = var then
          match v, ov with
          | Vint _, Vint _ | Vbool _, Vbool _ -> (var, v) :: m
          | _, _ -> failwith "incorrect type"
        else r :: aux m in
  aux m
(* Pretty printing *)
let mem_pp chan mem =
  Printf.fprintf chan "|";
  List.iter
    (function
      | s, Vint  i -> Printf.fprintf chan "%s:%d|" s i
      | s, Vbool b -> Printf.fprintf chan "%s:%b|" s b
    ) mem;
  Printf.fprintf chan "\n"
(* Slice at depth *)
let mem_slice_depth n l =
  let k = List.length l in
  assert (n <= k);
  let rec aux i l =
    if i = 0 then [], l
    else let u, v = aux (i-1) (List.tl l) in List.hd l :: u, v in
  aux (k - n) l


(** Get functions *)
let get_proc (p: Prog.prog) n =
  let rec aux = function
    | [ ] -> failwith "procedure not found"
    | p0 :: env -> if n = p0.Prog.pname then p0.Prog.pbody else aux env in
  aux p.pprocs


(** Interpreter *)
let eval_uop o v0 =
  match o, v0 with
  | Onot, Vbool b -> Vbool (not b)
  | _, _ -> failwith "unary-operator"
let eval_op o v0 v1 =
  match o, v0, v1 with
  | Oadd, Vint i0 , Vint i1  -> Vint  (i0 + i1)
  | Osub, Vint i0 , Vint i1  -> Vint  (i0 - i1)
  | Omul, Vint i0 , Vint i1  -> Vint  (i0 * i1)
  | Odiv, Vint i0 , Vint i1  -> Vint  (i0 / i1)
  | Omod, Vint i0 , Vint i1  -> Vint  (i0 mod i1)
  | Ole , Vint i0 , Vint i1  -> Vbool (i0 <= i1)
  | Olt , Vint i0 , Vint i1  -> Vbool (i0 < i1)
  | Oge , Vint i0 , Vint i1  -> Vbool (i0 >= i1)
  | Ogt , Vint i0 , Vint i1  -> Vbool (i0 > i1)
  | Oeq , Vint i0 , Vint i1  -> Vbool (i0 = i1)
  | One , Vint i0 , Vint i1  -> Vbool (i0 <> i1)
  | Oeq , Vbool b0, Vbool b1 -> Vbool (b0 = b1)
  | One , Vbool b0, Vbool b1 -> Vbool (b0 <> b1)
  | Oand, Vbool b0, Vbool b1 -> Vbool (b0 && b1)
  | Oor,  Vbool b0, Vbool b1 -> Vbool (b0 || b1)
  | _, _, _ -> failwith "binary-operator"
let eval_expr mem e =
  let rec aux = function
    | Ecsti i -> Vint i
    | Ecstb b -> Vbool b
    | Evar v -> mem_read (Var.get_vname v) mem
    | Euop (o, e0) -> eval_uop o (aux e0)
    | Eop (e0, o, e1) -> eval_op o (aux e0) (aux e1) in
  aux e
let rec eval_stmt p mem s =
  Printf.printf "=> %a\n" mem_pp mem;
  match s with
  | Sassign (x, e) -> mem_update (Var.get_vname x) (eval_expr mem e) mem
  | Sif (e, bt, bf) ->
      begin
        match eval_expr mem e with
        | Vbool true -> eval_block_body p mem bt
        | Vbool false -> eval_block_body p mem bf
        | _ -> failwith "not a boolean"
      end
  | Swhile (e, b) ->
      begin
        match eval_expr mem e with
        | Vbool true -> eval_stmt p (eval_block_body p mem b) s
        | Vbool false -> mem
        | _ -> failwith "not a boolean"
      end
  | Sinput x -> mem_update (Var.get_vname x) (Vint (Random.int 1000)) mem
and eval_list p mem = function
  | [ ] -> mem
  | s :: b -> eval_list p (eval_stmt p mem s) b
and eval_block_body p mem b =
  let mem0 = eval_list p mem b in
  let rec aux i l = if i = 0 then l else aux (i-1) (List.tl l) in
  aux (List.length mem0 - List.length mem) mem0
let interp_prog (p: Prog.prog) =
  (* 1. construct initial memory *)
  let m = List.fold_left (fun mem x -> mem_add x mem) mem_empty p.pglobs in
  (* 2. evaluate main *)
  eval_block_body p m p.pmain

(** Typer *)
let type_prog (p: Prog.prog) =
  let rec find_var env x =
    match env with
    | [ ] -> failwith "typ: variable not found"
    | a :: b -> if x = (Var.get_vname a) then (Var.get_vtype a) else find_var b x in
  let rec typ_expr env = function
    | Ecsti _ -> Tint
    | Ecstb _ -> Tbool
    | Evar x  -> find_var env (Var.get_vname x)
    | Euop (Onot, e0) ->
        if typ_expr env e0 != Tbool then failwith "uni-op: not";
        Tbool
    | Eop (e0, o, e1) ->
        match typ_expr env e0, o, typ_expr env e1 with
        | Tint , Oadd, Tint  -> Tint
        | Tint , Osub, Tint  -> Tint
        | Tint , Omul, Tint  -> Tint
        | Tint , Odiv, Tint  -> Tint
        | Tint , Ole , Tint  -> Tbool
        | Tint , Oeq , Tint  -> Tbool
        | Tbool, Oeq , Tbool -> Tbool
        | Tbool, Oand, Tbool -> Tbool
        | Tbool, Oor , Tbool -> Tbool
        | _    , _   , _     -> failwith "typ: bin-op" in
  let rec typ_stmt env = function
    | Sassign (x, e) ->
        let t = typ_expr env e in
        if t = (Var.get_vtype x) then env else failwith "typ: assign"
    | Sinput x ->
        if (Var.get_vtype x)!= Tint then failwith "typ: input";
        env
    | Sif (e, b0, b1) ->
        if typ_expr env e != Tbool then failwith "typ: if";
        ignore (typ_block env b0);
        ignore (typ_block env b1);
        env
    | Swhile (e, b) ->
        if typ_expr env e != Tbool then failwith "typ: while";
        ignore (typ_block env b);
        env
  and typ_block env = function
    | [ ] -> env
    | s :: b -> typ_block (typ_stmt env s) b in
  (* Types of the global variables *)
  ignore (typ_block p.pglobs p.pmain);
  List.iter (fun (pr: Prog.proc) -> ignore (typ_block p.pglobs pr.pbody)) p.pprocs

(** Trace *)
type trc = Bottom | Trc of mem * mem

exception BottomTrace

let trc_initial t =
  match t with
  | Bottom -> raise BottomTrace
  | Trc (i,_) -> i
let trc_final t =
  match t with
  | Bottom -> raise BottomTrace
  | Trc (_,f) -> f

let interp_prog_trc (p: Prog.prog) =
  let i = List.fold_left (fun mem x -> mem_add x mem) mem_empty p.pglobs in
  let f = eval_block_body p i p.pmain in
  Trc (i,  f)

(* For l-equivalence, I need to define _pre.
   This function _pre will evaluate expressions that can be either
   int or bool, so it has signature trc -> expr -> value *)
let eval_expr_pre t e =
  let f = trc_final t in
  eval_expr f e