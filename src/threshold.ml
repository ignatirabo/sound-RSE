open Apron

module VarS = Syntax.Var
module Ops = Syntax.Ops

type threshold = ((int * VarS.t) list * int option * Ops.op) list
type t = threshold

let empty = []

let to_typ (o: Ops.op) : Lincons1.typ =
  match o with
  | Oeq -> Lincons1.EQ
  | One -> Lincons1.DISEQ
  | Oge -> Lincons1.SUPEQ
  | Ogt -> Lincons1.SUP
  | _ -> failwith "to_typ: unexpected binary operator"

let to_linexpr (l : (int * VarS.t) list) (c: int option) (e: Environment.t) =
  let l =
    List.map
      (fun (i, v) ->
        Coeff.s_of_int i, Var.of_string (VarS.get_vname v))
      l in
  let c = match c with
    | None -> None
    | Some i -> Some (Coeff.s_of_int i) in
  let le = Linexpr1.make e in
  Linexpr1.set_list le l c;
  le

let to_lincons (l : (int * VarS.t) list) (c: int option) (o: Ops.op) (e: Environment.t) =
  let le = to_linexpr l c e in
  let typ = to_typ o in
  Lincons1.make le typ

let thr_to_lincons (thr: threshold) (e: Environment.t): Lincons1.earray =
  let n = List.length thr in
  let earr = Lincons1.array_make e n in
  List.iteri
    (fun i (l, c, o) ->
      let lc = to_lincons l c o e in
      Lincons1.array_set earr i lc)
    thr;
  earr
