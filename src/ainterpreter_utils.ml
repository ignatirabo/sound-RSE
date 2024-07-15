open Apron

(* Turning Apron level 0 structures into strings *)
let coeff_2str (c: Coeff.t): string =
  match c with
  | Coeff.Scalar scal -> Scalar.to_string scal
  | Coeff.Interval _ -> failwith "pp_coeff-interval"
let coeff_2int (c: Coeff.t): int =
  match c with
  | Coeff.Scalar scal ->
    begin
      let f = match scal with
        | Float f -> f
        | Mpqf f -> Mpqf.to_float f
        | Mpfrf f -> Mpfrf.to_float f in
      int_of_float f
    end
  | Coeff.Interval _ -> failwith "int_coeff-interval"
let unop_2str (u: Texpr0.unop): string =
  match u with
  | Texpr0.Neg ->  "-"
  | Texpr0.Cast -> "cast"
  | Texpr0.Sqrt -> "sqrt"
let binop_2str (b: Texpr0.binop): string =
  match b with
  | Texpr0.Add -> "+"
  | Texpr0.Sub -> "-"
  | Texpr0.Mul -> "*"
  | Texpr0.Div -> "/"
  | Texpr0.Mod -> "%"
  | Texpr0.Pow -> "^"
let cons_op_2str (typ: Lincons0.typ): string =
  match typ with
  | Lincons1.EQ    -> "="
  | Lincons1.DISEQ -> "!="
  | Lincons1.SUP   -> ">"
  | Lincons1.SUPEQ -> ">="
  | Lincons1.EQMOD s -> Printf.sprintf "==(%s)" (Scalar.to_string s)
let cons_op_2op (typ: Lincons0.typ): Syntax.Ops.op =
  match typ with
  | Lincons1.EQ    -> Oeq
  | Lincons1.DISEQ -> One
  | Lincons1.SUP   -> Ogt
  | Lincons1.SUPEQ -> Oge
  | Lincons1.EQMOD _ -> failwith "cons_op_2op: EQMOD"
let cons_trailer_2str (typ: Lincons0.typ): string =
  match typ with
  | Lincons1.EQ    -> " = 0"
  | Lincons1.DISEQ -> " != 0"
  | Lincons1.SUP   -> " > 0"
  | Lincons1.SUPEQ -> " >= 0"
  | Lincons1.EQMOD s -> Printf.sprintf " == 0 (%s)" (Scalar.to_string s)
(* Turning Apron level 1 structures into strings *)
let texpr1_2str (te: Texpr1.t): string =
  let rec aux_expr (e: Texpr1.expr): string =
    match e with
    | Texpr1.Cst c -> coeff_2str c
    | Texpr1.Var v -> Var.to_string v
    | Texpr1.Unop (u, te0, _, _) ->
        Printf.sprintf "%s (%s)" (unop_2str u) (aux_expr te0)
    | Texpr1.Binop (b, te0, te1, _, _) ->
        Printf.sprintf "(%s) %s (%s)"
          (aux_expr te0) (binop_2str b) (aux_expr te1) in
  aux_expr (Texpr1.to_expr te)
(* Debug pp for environments *)
let environment_2str (env: Environment.t): string =
  let ai, af = Environment.vars env in
  (* Check no Real vars *)
  assert (Array.length af = 0);
  let isbeg = ref true in
  let s =
    Array.fold_left
      (fun (acc: string) (v: Var.t) ->
        let sep =
          if !isbeg then
            begin
              isbeg := false;
              ""
            end
          else "; " in
        Printf.sprintf "%s%s%s" acc sep (Var.to_string v)
      ) "" ai in
  Printf.sprintf "[|%s|]" s

(* Extraction of integer variables *)
let get_ivars (env: Environment.t): Var.t array =
  let ivars, fvars = Environment.vars env in
  if Array.length fvars > 0 then failwith "unimp: floating-point vars";
  ivars

(* Determines if set of constraints is SAT *)
let linconsarray_sat (a: Lincons1.earray): bool =
  let f_lincons (cons: Lincons1.t) =
    if Lincons1.is_unsat cons then false
    else true in
  (* Array of cons1 *)
  let ac1 =
    Array.mapi
      (fun i _ -> Lincons1.array_get a i)
      a.Lincons1.lincons0_array in
  Array.fold_left
    (fun (acc: bool) cons -> acc && (f_lincons cons)) true ac1
    
(* Turns a set of constraints into a string *)
let linconsarray_2stri (ind: string) (a: Lincons1.earray): string =
  (* Extraction of the integer variables *)
  let env = a.Lincons1.array_env in
  let ivars = get_ivars env in
  (* pretty-printing of a constraint *)
  let f_lincons (cons: Lincons1.t): string =
    if Lincons1.is_unsat cons then Printf.sprintf "%sUNSAT lincons\n" ind
    else
      (* print non zero coefficients *)
      let mt = ref false in
      let str0 =
        Array.fold_left
          (fun str v ->
            let c =
              try Lincons1.get_coeff cons v
              with exn ->
                failwith (Printf.sprintf "get_coeff, var %s, exn %s"
                            (Var.to_string v) (Printexc.to_string exn));
            in
            if not (Coeff.is_zero c) then
              begin
                let var = Var.to_string v in
                let str_ext = Printf.sprintf "%s . %s" (coeff_2str c) var in
                if !mt then
                  Printf.sprintf "%s + %s" str str_ext
                else
                  begin
                    mt := true;
                    str_ext
                  end
              end
            else str
          ) "" ivars in
      (* print the constant *)
      let str1 =
        let d0 = coeff_2str (Lincons1.get_cst cons) in
        if !mt then Printf.sprintf "%s + %s" str0 d0
        else d0 in
      (* print the relation *)
      Printf.sprintf "%s%s %s\n" ind str1
        (cons_trailer_2str (Lincons1.get_typ cons)) in
  (* Array of cons1 *)
  let ac1 =
    Array.mapi
      (fun i _ -> Lincons1.array_get a i)
      a.Lincons1.lincons0_array in
  Array.fold_left
    (fun (acc: string) cons ->
      Printf.sprintf "%s%s" acc (f_lincons cons)
    ) "" ac1

let lincons_2expr (cons: Lincons1.t) : Syntax.Lang.expr =
  if Lincons1.is_unsat cons then
    begin
      Printf.printf "\nUNSAT lincons";
      Ecstb false
    end
  else
    let env = Lincons1.get_env cons in
    let ivars = get_ivars env in
    let cst : Syntax.Lang.expr = Ecsti (coeff_2int (Lincons1.get_cst cons)) in
    let linexpr = Array.fold_left
      (fun expr v : Syntax.Lang.expr ->
        let c =
          try coeff_2int (Lincons1.get_coeff cons v)
          with exn ->
            failwith (Printf.sprintf "get_coeff, var %s, exn %s"
              (Var.to_string v) (Printexc.to_string exn));
        in
        let v = Syntax.Var.make (Var.to_string v) Syntax.Tint in
        let m : Syntax.Lang.expr = match c with
        | 0 -> Ecsti 0
        | 1 -> Evar v
        | _ -> Eop (Ecsti c, Omul, (Evar v)) in
        match m with
        | Ecsti 0 -> expr
        | _ -> Eop (m, Oadd, expr))
      cst ivars
    in
    let op = cons_op_2op (Lincons1.get_typ cons) in
    Eop (linexpr, op, Ecsti 0)

(* Translation into Apron expressions, with environment *)
let translate_op : Syntax.Ops.op -> Texpr0.binop = function
  | Oadd -> Texpr1.Add
  | Osub -> Texpr1.Sub
  | Omul -> Texpr1.Mul
  | Odiv -> Texpr1.Div
  | Omod -> Texpr1.Mod
  | _    -> failwith "binary operator, unsupported"
let translate_cond : Syntax.Ops.op -> Lincons0.typ = function
  | Oeq  -> Tcons1.EQ
  | One  -> Tcons1.DISEQ
  | Olt  -> Tcons1.SUP
  | Ole  -> Tcons1.SUPEQ
  | _    -> failwith "condition, unsupported"
let rec translate_expr (env: Environment.t) : Syntax.Lang.expr -> Texpr1.t = function
  | Ecsti i -> Texpr1.cst env (Coeff.s_of_int i)
  | Ecstb _ -> failwith "boolean constant, unsupported"
  | Evar  v -> Texpr1.var env (Var.of_string (Syntax.Var.get_vname v))
  | Euop  _ -> failwith "negation, unsupported"
  | Eop (e0, b, e1) ->
      Texpr1.binop
        (translate_op b)
        (translate_expr env e0)
        (translate_expr env e1) Texpr1.Int Texpr1.Near
let translate_cons (env: Environment.t) : Syntax.Lang.expr -> Tcons1.t = function
  | Ecstb b ->
      if b then (* tautology constraint 0 = 0 *)
        let ex = translate_expr env (Ecsti 0) in
        Tcons1.make ex Tcons1.EQ
      else (* anti-tautology constraint 1 = 0 *)
        let ex = translate_expr env (Ecsti 1) in
        Tcons1.make ex Tcons1.EQ
  | Eop (e0, Oeq, e1) ->
      Tcons1.make (translate_expr env (Eop (e1, Osub, e0))) Tcons1.EQ
  | Eop (e0, One, e1) ->
      Tcons1.make (translate_expr env (Eop (e1, Osub, e0))) Tcons1.DISEQ
  | Eop (e0, Ole, e1) ->
      Tcons1.make (translate_expr env (Eop (e1, Osub, e0))) Tcons1.SUPEQ
  | Eop (e0, Olt, e1) ->
      Tcons1.make (translate_expr env (Eop (e1, Osub, e0))) Tcons1.SUP
  | Eop (e0, Oge, e1) ->
      Tcons1.make (translate_expr env (Eop (e0, Osub, e1))) Tcons1.SUPEQ
  | Eop (e0, Ogt, e1) ->
      Tcons1.make (translate_expr env (Eop (e0, Osub, e1))) Tcons1.SUP
  | _ -> failwith "condition, unsupported"