type rel = D of int | U of int

module IntOrd = struct type t = int let compare = Stdlib.compare end ;;
module RelOrd = struct type t = rel let compare = Stdlib.compare end ;;
module IntSet = Set.Make(IntOrd)
module RelSet = Set.Make(RelOrd)
module IntMap = Map.Make(IntOrd)

type t = {
  lset: IntSet.t;
  lmap: RelSet.t IntMap.t;
  lup: Bitv.t array;
  ldown: Bitv.t array
}

let init (s: IntSet.t) (m: RelSet.t IntMap.t) : t =
  let c = IntSet.cardinal s in
  (* This is wrong, it gives the same Bitv to every row *)
  let u = Array.make c (Bitv.create c false) in
  for i = 0 to c - 1 do
    u.(i) <- Bitv.create c false
  done;
  let d = Array.make c (Bitv.create c false) in
  for i = 0 to c - 1 do
    d.(i) <- Bitv.create c false
  done;
  (* Load initial map data to arrays, then it's easy to calculate trcl when needed *)
  IntMap.iter
    (fun k s ->
      RelSet.iter
        (fun r ->
          match r with
          | D i ->
            Bitv.set d.(k) i true
          | U i ->
            Bitv.set u.(k) i true)
        s)
    m;
  { lset=s; lmap=m; lup=u; ldown=d }

let mat_copy (mat: Bitv.t array) : Bitv.t array =
  let sz = Array.length mat in
  let nmat = Array.make sz (Bitv.create sz false) in
  for i = 0 to sz - 1 do
    nmat.(i) <- Bitv.copy mat.(i)
  done;
  nmat

let set l = l.lset

let set_map f (s: IntSet.t) : IntSet.t =
  IntSet.map f s

let elements l = IntSet.elements l.lset

(** Lattice dimensions *)
let dim (l: t) : int =
  IntSet.cardinal l.lset

let up l = l.lup

let down l = l.ldown

let get_row (mat: Bitv.t array) (n: int): Bitv.t =
  mat.(n)

(* Add row m to n*)
let union_row (mat: Bitv.t array) (n: int) (m: int) : unit =
  mat.(n) <- Bitv.bw_or mat.(n) mat.(m)

let rec trcl_row (mat: Bitv.t array) (n : int) (chk : bool array) : unit =
  let sz = Array.length mat in
  for i = 0 to sz - 1 do
    if Bitv.get mat.(n) i = true then (
      if chk.(i) = false then (
        chk.(i) <- true;
        trcl_row mat i chk
      );
      union_row mat n i
    )
  done;
  Bitv.set mat.(n) n true

(** Calculate transitive closure of matrice of bit vectors *)
let trcl (mat: Bitv.t array) : unit =
  let sz = Array.length mat in
  let chk = Array.make sz false in
  for i = 0 to sz - 1 do
    if chk.(i) = false then
      chk.(i) <- true;
      trcl_row mat i chk
  done

let lesser (l: t) (x: int) (y: int) : bool =
  Bitv.get l.lup.(x) y

let greater (l: t) (x: int) (y: int) : bool =
  Bitv.get l.ldown.(x) y

exception BadCalculation

let glb (l: t) (s: IntSet.t) : int =
  let mat = mat_copy l.ldown in
  trcl mat;
  let bitv = Bitv.create (IntSet.cardinal l.lset) true in
  let rec aux (bitv: Bitv.t) = function
  | [] -> bitv
  | h::tl ->
    let bitv = Bitv.bw_and bitv mat.(h) in
    aux bitv tl in
  let bitv = aux bitv (IntSet.elements s) in
  let rec aux (bitv: Bitv.t) = function
  | [] -> raise BadCalculation
  | h::tl ->
    if mat.(h) = bitv then
      h
    else
      aux bitv tl in
  aux bitv (IntSet.elements l.lset)

module type LATTICE =
  sig
    val l: t
    val dim: int
  end

module Latt_default =
  (struct
    let l : t =
      let l_set = IntSet.of_list [0;1] in
      let l_rel = IntMap.empty in
      let rel_set_0 = RelSet.of_list [U 1] in
      let rel_set_1 = RelSet.of_list [D 0] in
      let l_rel = IntMap.add 0 rel_set_0 l_rel in
      let l_rel = IntMap.add 1 rel_set_1 l_rel in
      init l_set l_rel

    let dim = 2
  end:LATTICE)