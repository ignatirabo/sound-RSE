open Syntax.Var

type secmap = int VMap.t
type t = secmap
let empty = VMap.empty
let add v i (sm: secmap) =
  VMap.add v i sm
let vars (sm: secmap) =
  let aux v _ vars = v::vars in
  VMap.fold aux sm []
let fold = VMap.fold
let find = VMap.find
let cardinal = VMap.cardinal
let of_list ps pglobs : secmap =
  let rec aux (vm: int VMap.t) = function
  | [] -> vm
  | v::pglobs ->
    try
      let p = List.find (fun p -> 0 = compare (fst p) v) ps in
      let vm = VMap.add (fst p) (snd p) vm in
      aux vm pglobs
    with Not_found ->
      let vm = VMap.add v 0 vm in
      aux vm pglobs in
  aux VMap.empty pglobs
let pp chan sm =
  VMap.iter (fun v s -> Printf.fprintf chan "%s -> %d; " (Syntax.Var.get_vname v) s) sm