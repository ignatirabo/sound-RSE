open Pre

module type SYMBOLIC_PATH =
  sig
    module P : PRE
    type elt := P.zexpr
    type id
    type t
    val empty : t
    val add : id -> elt -> t -> t
    val id_2int: id -> int
    val int_2id: int -> id
    val get_of_id: id -> t -> t
    val to_list: t -> elt list
    val from_list: id -> elt list -> t
    val union: t -> t -> t
    val replace_id: id -> id -> t -> t
    val length: t -> int
  end

module SPath (P:PRE) : SYMBOLIC_PATH =
  struct
    module P = P
    type elt = P.zexpr
    type id = int
    let compare (id0,ze0) (id1,ze1) =
      let cmp_id = Int.compare id0 id1 in
      if cmp_id = 0 then
        begin
          let cmp_ze = P.compare ze0 ze1 in
          if cmp_ze = 0 then 0
          else if cmp_ze < 0 then -1
          else 1
        end
      else if cmp_id < 0 then -1
      else 1
    module SpOrd = struct type t = id*elt let compare = compare end
    module SpSet = Set.Make(SpOrd)
    type t = SpSet.t

    let empty = SpSet.empty
    let add i e t = SpSet.add (i,e) t

    let id_2int i = i
    let int_2id i = i

    let get_of_id i = SpSet.filter (fun ((i',_):id*elt) -> i = i')
    let to_list sp = SpSet.fold (fun (_,e) acc -> e::acc) sp []
    let from_list i ls = List.fold_left (fun acc e -> SpSet.add (i,e) acc) SpSet.empty ls

    let union sp1 sp2 =
      SpSet.union sp1 sp2

    let replace_id id1 id2 sp =
      SpSet.map (fun (i,e) -> if i = id1 then (id2,e) else (id1,e)) sp 

    let length = SpSet.cardinal
  end