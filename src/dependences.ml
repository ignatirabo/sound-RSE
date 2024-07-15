open Lattice
open Single_symbolic
open Syntax
open Pre

module SM = Sec_map
module V = Syntax.Var
module Lang = Syntax.Lang

module Dep (L: LATTICE) (SE: SINGLE_SYMBOLIC_EXEC) (P: PRE) =
  (struct
    module IntOrd = struct type t = int let compare = Stdlib.compare end ;;
    module IntMap = Map.Make(IntOrd)
    (* Lattice elements are ints, variables are strings *)
    type astate = StringSet.t IntMap.t
    type elt = int * string

    (* Auxiliary functions *)
    (* Create empty dep from lattice *)
    let init : astate =
      let dim = L.dim in
      let d = IntMap.empty in
      let rec aux n d =
        if n < dim then
          let d = IntMap.add n StringSet.empty d in
          aux (n+1) d
        else
          d
      in
      aux 0 d

    let remove v d : astate =
      let name = V.get_vname v in
      IntMap.map (fun s -> StringSet.remove name s) d

    let find lx d : string =
      let l = fst lx in
      let x = snd lx in
      let s = IntMap.find l d in
      try StringSet.find x s
      with e -> raise e

    let rec l_agreement e l d : bool =
      match e with
      | Lang.Ecstb _ -> true
      | Ecsti _ -> true
      | Euop (_,e) -> l_agreement e l d
      | Eop (e1,_,e2) ->
        let l1 = l_agreement e1 l d in
        let l2 = l_agreement e2 l d in
        l1 && l2
      | Evar x ->
        try let _ = find (l,V.get_vname x) d in true
        with Not_found -> false

    (** Returns the set of modifiable variables of command s *)
    (* We use Single Symbolic domain to do this *)
    let modif (b : Lang.block) : V.VSet.t =
      let vars : V.t list = V.VSet.elements (Syntax_aux.vars b) in
      let p = { Prog.pglobs = vars;
        psec = V.VMap.empty;
        pprocs = [];
        pmain = b } in
      let k = SE.init p in
      SE.modif k

    let add i x d : astate =
      let s = IntMap.find i d in
      let s = StringSet.add x s in
      IntMap.update i (fun _ -> Some s) d

    exception Wrong_statement

    (* Printing *)
    let pp chan (d: astate) =
      Printf.fprintf chan "|";
      IntMap.iter
        (fun k s ->
          StringSet.iter
            (fun x ->
              Printf.fprintf chan " %d->%s |" k x) s
        ) d;
      Printf.fprintf chan "\n"

    (* Lattice operations *)
    let join d0 d1 : astate =
      (* Calculated as dependency intersection *)
      IntMap.mapi
        (fun l ss0 ->
          try
            let ss1 = IntMap.find l d1 in
            StringSet.inter ss0 ss1
          with Not_found ->
            StringSet.empty
        ) d0

    let lub d0 d1 : astate = join d0 d1

    (* Set operations *)
    let union d0 d1 : astate =
      IntMap.fold
        (fun (x0: int) s0 acc ->
          StringSet.fold
            (fun (y: string) (acc: astate) ->
              (* add x0=>y to acc *)
              let cur_x0 =
                try IntMap.find x0 acc with Not_found -> StringSet.empty in
              let new_x0 = StringSet.add y cur_x0 in
              IntMap.add x0 new_x0 acc
            ) s0 acc
        ) d0 d1

    (* Test whether d0 is a subset of d1 *)
    let subset d0 d1 : bool =
      IntMap.fold
        (fun k ss0 b ->
          try
            let ss1 = IntMap.find k d1 in
            (* Opposed to trivial *)
            b && StringSet.subset ss0 ss1
          with Not_found ->
            false
        ) d0 true

    (* Abstract operations *)
    let post_input v d0 : astate =
      let f _ ss = StringSet.add (V.get_vname v) ss in
      let d1 = remove v d0 in
      let d2 = init in
      let d2 = IntMap.mapi f d2 in
      union d1 d2

    let post_assign v e d0 : astate =
      let f l ss =
        (if l_agreement e l d0 then
          StringSet.add (V.get_vname v) ss
        else
          ss) in
      let d1 = remove v d0 in
      let d2 = init in
      let d2 = IntMap.mapi f d2 in
      union d1 d2

    let post_if e b0 b1 d d0 d1 =
      let w = modif [ Sif (e,b0,b1) ] in
      let aux w : StringSet.t =
        let vars = V.VSet.elements w in
        let strings = List.map (fun v -> (V.get_vname v)) vars in
        StringSet.of_list strings
      in
      let w = aux w in
      let d' = init in
      IntMap.mapi
        (fun l _ ->
          if l_agreement e l d then
            let ss1 = IntMap.find l d0 in
            let ss2 = IntMap.find l d1 in
            StringSet.inter ss1 ss2
          else (
            let ss' = IntMap.find l d in
            StringSet.diff ss' w))
        d'

    (* Variables, functions and block operations *)

    (** Transform a security map into an abstract state *)
    let ast_from_sec (sec_map: int V.VMap.t) : astate =
      (* TODO: this function is a mess, optimize this by folding over the security map. *)
      let vars = List.map (fun (k,_) -> k) (V.VMap.bindings sec_map) in
      let mat = Lattice.mat_copy (Lattice.up L.l) in
      Lattice.trcl mat;
      let d = init in
      let rec aux d (xs: V.t list) : astate =
        match xs with
        | [] -> d
        | x::xs ->
          (* Bitv.to_list returns the list of all indiced set to true *)
          let ind = Bitv.to_list mat.(V.VMap.find x sec_map) in
          let rec aux' d ind : astate =
          match ind with
          | [] -> d
          | i::ind ->
            let d = add i (V.get_vname x) d in
            aux' d ind
          in
          let d = aux' d ind in
          aux d xs
        in
      aux d vars

    let block_enter d0 = d0
    let block_exit d0 = d0

    (* Testing *)
    let to_astate xs : astate =
      let d = init in
      let rec aux d = function
      | [] -> d
      | (i,s)::xs ->
        aux (add i s d) xs in
      aux d xs

    (** Equality operator for dep. abstract states *)
    let equal d0 d1 : bool =
      IntMap.equal (StringSet.equal) d0 d1

    let alpha_hs (d: astate) (vs: V.VSet.t) : Sec_map.t =
      let rec aux (v: V.t) (s: IntSet.t) (ls: int list) : int =
        match ls with
        | [] -> glb L.l s
        | i::ls ->
          try
            ignore (find (i, (V.get_vname v)) d);
            aux v (IntSet.add i s) ls
          with Not_found ->
            aux v s ls in
      V.VSet.fold (fun v sm ->
        let l_list = Lattice.elements L.l in
        let i = aux v IntSet.empty l_list in
        SM.add v i sm)
        vs SM.empty

    (** Return secmap of variables that changed security between the two abstract states.
        The resulting secmap has the value from the last argument
        @param d0 Initial dependencies abstract state
        @param d1 Posterior dependencies abstract state
        @param vars Set of variables to iterate over
     *)
    let diff d0 d1 (vs: V.VSet.t) : SM.t =
      let d0 = alpha_hs d0 vs in
      let d1 = alpha_hs d1 vs in
      V.VSet.fold (fun v sm ->
        try
          let i0 = SM.find v d0 in
          let i1 = SM.find v d1 in
          if i0 = i1 then sm
          else SM.add v i1 sm
        with Not_found ->
          Printf.printf "Variable not found in diff function.";
          raise Not_found)
        vs SM.empty
    
    let vars_in_level (d: astate) n : V.VSet.t =
      StringSet.fold (fun s acc -> V.VSet.add (V.make s Syntax.Tint) acc)
        (IntMap.find n d) V.VSet.empty
  end)
