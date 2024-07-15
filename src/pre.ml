module MP = Maybe_pair

module type PRE =
  sig
    type zexpr
    type zstatus = SAT | UNSAT | UNKNOWN
    type zsymbol
    type zsolver
    (* val ctx: Z3.context *)
    (* val isort: Z3.Sort.sort *)
    (* Expressions *)
    val mk_true: zexpr
    val mk_false: zexpr
    val mk_numeral_i: int -> zexpr
    val mk_bool: bool -> zexpr
    val mk_string: string -> zsymbol
    val mk_const: zsymbol -> zexpr
    val mk_add: zexpr list -> zexpr
    val mk_sub: zexpr list -> zexpr
    val mk_mul: zexpr list -> zexpr
    val mk_div: zexpr -> zexpr -> zexpr
    val mk_mod: zexpr -> zexpr -> zexpr
    val mk_le: zexpr -> zexpr -> zexpr
    val mk_lt: zexpr -> zexpr -> zexpr
    val mk_eq: zexpr -> zexpr -> zexpr
    val mk_not: zexpr -> zexpr
    val mk_ge: zexpr -> zexpr -> zexpr
    val mk_gt: zexpr -> zexpr -> zexpr
    val mk_and: zexpr list -> zexpr
    val mk_or: zexpr list -> zexpr
    val to_string: zexpr -> string
    (* Check *)
    val check: zexpr list -> zstatus * zsolver
    val get_string_model: zexpr list -> zstatus * zsolver -> string option
    val compare: zexpr -> zexpr -> int
    val print_expr: out_channel -> zexpr -> unit
    val print_prop: out_channel -> zexpr list -> unit
    (* let uop_eval (uop : Syntax.Ops.uop) (se : zexpr) =
    let op_eval (op : Syntax.Ops.op) (se0 : zexpr) (se1: zexpr) = *)
    val expr_eval : Syntax.Lang.expr -> zexpr Syntax.Var.VMap.t -> zexpr
    val expr_eval_pair : Syntax.Lang.expr -> zexpr MP.t Syntax.Var.VMap.t -> zexpr MP.t
    val pp_zstatus : out_channel -> zstatus -> unit
  end

module Z3pre : PRE =
  struct
    type zexpr = Z3.Expr.expr
    type zstatus = SAT | UNSAT | UNKNOWN
    type zsymbol = Z3.Symbol.symbol
    type zsolver = Z3.Solver.solver
    let cfg = [("model", "true"); ("proof", "false")]
    let ctx = (Z3.mk_context cfg)
    let isort = (Z3.Arithmetic.Integer.mk_sort ctx)
    (* Expressions *)
    let mk_true = Z3.Boolean.mk_true ctx
    let mk_false = Z3.Boolean.mk_false ctx
    let mk_numeral_i = Z3.Arithmetic.Integer.mk_numeral_i ctx
    let mk_bool = Z3.Boolean.mk_val ctx
    let mk_string = Z3.Symbol.mk_string ctx
    let mk_const = (fun s -> Z3.Expr.mk_const ctx s isort)
    let mk_add = Z3.Arithmetic.mk_add ctx
    let mk_sub = Z3.Arithmetic.mk_sub ctx
    let mk_mul = Z3.Arithmetic.mk_mul ctx
    let mk_div = Z3.Arithmetic.mk_div ctx
    let mk_mod = Z3.Arithmetic.Integer.mk_mod ctx
    let mk_le = Z3.Arithmetic.mk_le ctx
    let mk_lt = Z3.Arithmetic.mk_lt ctx
    let mk_eq = Z3.Boolean.mk_eq ctx
    let mk_not = Z3.Boolean.mk_not ctx
    let mk_ge = Z3.Arithmetic.mk_ge ctx
    let mk_gt = Z3.Arithmetic.mk_gt ctx
    let mk_and = Z3.Boolean.mk_and ctx
    let mk_or = Z3.Boolean.mk_or ctx
    let to_string = Z3.Expr.to_string
    (* Aux *)
    (* let zstatus_to_Z3status zstat =
      match zstat with
      | SAT -> Z3.Solver.SATISFIABLE
      | UNSAT -> Z3.Solver.UNSATISFIABLE
      | UNKNOWN -> Z3.Solver.UNKNOWN *)
    let z3status_to_zstatus z3stat =
      match z3stat with
      | Z3.Solver.SATISFIABLE -> SAT
      | Z3.Solver.UNSATISFIABLE -> UNSAT
      | Z3.Solver.UNKNOWN -> UNKNOWN
    (* Check *)
    let check zls =
      let g = Z3.Goal.mk_goal ctx true false false in
      Z3.Goal.add g zls;
      let solver = Z3.Solver.mk_solver ctx None in
      List.iter (fun a -> (Z3.Solver.add solver [ a ])) (Z3.Goal.get_formulas g);
      let zstat = z3status_to_zstatus (Z3.Solver.check solver []) in
      (zstat, solver)
    let get_string_model zls (zstat, zsolv) =
      if List.length zls > 0 && zstat = SAT then
        let m = Z3.Solver.get_model zsolv in
        match m with
        | Some m -> Some (Z3.Model.to_string m)
        | None -> None
      else
        None
    let compare = Z3.Expr.compare

    let print_expr chan e = Printf.fprintf chan "%s" (to_string e)
    let rec print_prop chan xs : unit =
      match xs with
      | [] -> ()
      | [x] -> print_expr chan x
      | x::y::xs ->
        Printf.fprintf chan "%a /\\ " print_expr x;
        print_prop chan (y::xs)

    let uop_eval (uop : Syntax.Ops.uop) (se : zexpr) =
      match uop with
      | Onot -> mk_not se

    (** Evaluate binary operation op with Z3 expressions se0 and se1 *)
    let op_eval (op : Syntax.Ops.op) (se0 : zexpr) (se1: zexpr) =
      match op with
      | Oadd -> mk_add [se0; se1]
      | Osub -> mk_sub [se0; se1]
      | Omul -> mk_mul [se0; se1]
      | Odiv -> mk_div se0 se1
      | Omod -> mk_mod se0 se1
      | Ole -> mk_le se0 se1
      | Olt -> mk_lt se0 se1
      | Oeq -> mk_eq se0 se1
      | One -> mk_not (mk_eq se0 se1)
      | Oge -> mk_ge se0 se1
      | Ogt -> mk_gt se0 se1
      | Oand -> mk_and [se0; se1]
      | Oor -> mk_or [se0; se1]

    (** Evaluate expression e with abstract state a,
        transforming it to a pair of Z3 expressions *)
    let rec expr_eval (e : Syntax.Lang.expr) (m : zexpr Syntax.Var.VMap.t) : zexpr =
      match e with
      | Ecsti n ->
        let i = mk_numeral_i n in
        i
      | Ecstb b ->
        let b = mk_bool b in
        b
      | Evar v ->
        Syntax.Var.VMap.find v m
      | Euop (op, e) ->
        let e' = expr_eval e m in
        uop_eval op e'
      | Eop (e0, op, e1) ->
        let e0' = expr_eval e0 m in
        let e1' = expr_eval e1 m in
        op_eval op e0' e1'

    let rec expr_eval_pair (e : Syntax.Lang.expr) (m : zexpr MP.t Syntax.Var.VMap.t) : zexpr MP.t =
      match e with
      | Ecsti n ->
        let i = mk_numeral_i n in
        Maybe_pair.single i
      | Ecstb b ->
        let b = mk_bool b in
        Maybe_pair.single b
      | Evar v ->
        Syntax.Var.VMap.find v m
      | Euop (op, e) ->
        begin
          match expr_eval_pair e m with
          | MP.Single e'     -> MP.single (uop_eval op e')
          | MP.Pair (e',e'') -> MP.pair (uop_eval op e', uop_eval op e'')
        end
      | Eop (e0, op, e1) ->
        let e0' = expr_eval_pair e0 m in
        let e1' = expr_eval_pair e1 m in
        match e0', e1' with
        | MP.Single e0', MP.Single e1' -> MP.Single (op_eval op e0' e1')
        | _, _ ->
          let el = op_eval op (MP.left e0') (MP.left e1') in
          let er = op_eval op (MP.right e0') (MP.right e1') in
          MP.Pair (el, er)
    
    let pp_zstatus chan = function
    | SAT -> Printf.fprintf chan "SAT"
    | UNSAT -> Printf.fprintf chan "UNSAT"
    | UNKNOWN -> Printf.fprintf chan "UNKNOWN"
  end