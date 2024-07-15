(** Types: integers or booleans *)
type typ = Tint | Tbool
let typ_2str = function
  | Tint  -> "int"
  | Tbool -> "bool"

module type VAR = sig
  type t
  type var = t
  val make: string -> typ -> t
  val get_vname: t -> string
  val get_vtype: t -> typ
  val compare: t -> t -> int
  module VMap : Map.S with type key = var
  module VSet : Set.S with type elt = var 
end

module Var : VAR = struct
  (** Variables are defined by a name and a unique integer ID *)
  type t = { vname: string; (* name *)
             vtype: typ   } (* type *)
  type var = t
  let make s t = { vname = s ; vtype = t }
  let get_vname v = v.vname
  let get_vtype v = v.vtype
  let compare v0 v1 = String.compare (get_vname v0) (get_vname v1)
  module VOrd = struct type t = var let compare = compare end
  module VMap = Map.Make(VOrd)
  module VSet = Set.Make(VOrd)
end


module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

(** Operations *)
module Ops = struct
  (* unary *)
  type uop = Onot
  (* binary *)
  type op =
  | Oadd | Osub | Omul | Odiv | Omod
  (* comparisons *)
  | Ole | Olt | Oeq | One | Oge | Ogt
  (* logics *)
  | Oand | Oor
  let uop_2str = function
    | Onot  -> "!"
  let op_2str = function
    | Oadd  -> "+"
    | Osub  -> "-"
    | Omul  -> "*"
    | Odiv  -> "/"
    | Omod  -> "%"
    | Ole   -> "<="
    | Olt   -> "<"
    | Ogt   -> ">"
    | Oge   -> ">="
    | Oeq   -> "="
    | One   -> "!="
    | Oand  -> "&&"
    | Oor   -> "||"
end

module Lang = struct
  open Ops
  type expr =
    | Ecsti of int                 (* integer constant *)
    | Ecstb of bool                (* boolean constant *)
    | Evar of Var.t                  (* variable *)
    | Euop of Ops.uop * expr           (* unary negation *)
    | Eop of expr * Ops.op * expr      (* binary op *)
  let expr_neg = function
    | Ecsti _ | Evar _ -> failwith "negation"
    | Ecstb b -> Ecstb (not b)
    | Euop (Onot, e) -> e
    | Eop (e0, o, e1) ->
        let no =
          match o with
          | Oadd | Osub | Omul | Odiv | Omod | Oor | Oand -> failwith "negation"
          | Oeq -> One
          | One -> Oeq
          | Ole -> Ogt
          | Olt -> Oge
          | Oge -> Olt
          | Ogt -> Ole in
        Eop (e0, no, e1)

  (** Statements *)
  type stmt =
    | Sassign of Var.t * expr      (* assignment *)
    | Sinput of Var.t              (* random integer value *)
    | Sif of expr * block * block  (* conditional statement *)
    | Swhile of expr * block       (* while *)
  and block = stmt list

  type stmt_aux =
    | Aassign of Var.t * expr
    | Ainput of Var.t
    | Aif of expr * block_aux * block_aux
    | Awhile of expr * block_aux
    | Aloop of expr * block_aux
  and block_aux = stmt_aux list

  type block_rel =
    | Rnormal of block_aux
    | Rcomp of block_aux * block_aux * block_aux

  let is_normal (b: block_rel) : bool =
    match b with
    | Rnormal _ -> true
    | _ -> false

  let get_normal (b: block_rel) : block_aux =
    match b with
    | Rnormal b -> b
    | Rcomp _ -> raise (Failure "block_rel not normal in get_normal.")

  let get_comp (b: block_rel) : block_aux * block_aux * block_aux =
    match b with
    | Rnormal _ -> raise (Failure "block_rel not composed in get_comp.")
    | Rcomp (b0,b1,b2) -> (b0,b1,b2)
end
