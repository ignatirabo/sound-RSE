open Syntax

let counter_debug = ref false

module type COUNTER = sig
  type t
  val max: int
  val empty: t
  val step: Lang.block_aux -> t -> bool * t
  val step_rel: Lang.block_rel -> t -> bool * t
  val delete: t -> t
end

module CounterConstant4 : COUNTER = struct
  type t = int list
  let max = 4
  let empty: t = [] 
  let step (b_a: Lang.block_aux) counter =
    match b_a, counter with
    | Lang.Aloop (_,_)::_, h::counter  ->
      if !counter_debug then
        Printf.printf "counter head = %d\n\n" h;
      if h < max then
        true, h+1::counter
      else
        false, counter
    | Lang.Awhile (_,_)::_, _ ->
      if !counter_debug then
        Printf.printf "new counter\n\n";
      true, 0::counter
    | _, _ -> true, counter
  let step_rel b_r counter =
    match b_r with
    | Lang.Rnormal b -> step b counter
    | Lang.Rcomp _ -> raise (Failure "step of Rcomp not supported.")

  let delete c =
    if !counter_debug then
      Printf.printf "delete counter\n\n";
    match c with
    | [] -> []
    | _::cs -> cs
end

module CounterConstant8 : COUNTER = struct
  type t = int list
  let max = 8
  let empty: t = [] 
  let step (b_a: Lang.block_aux) counter =
    match b_a, counter with
    | Lang.Aloop (_,_)::_, h::counter  ->
      if !counter_debug then
        Printf.printf "counter head = %d\n\n" h;
      if h < max then
        true, h+1::counter
      else
        false, counter
    | Lang.Awhile (_,_)::_, _ ->
      if !counter_debug then
        Printf.printf "new counter\n\n";
      true, 0::counter
    | _, _ -> true, counter
  let step_rel b_r counter =
    match b_r with
    | Lang.Rnormal b -> step b counter
    | Lang.Rcomp _ -> raise (Failure "step of Rcomp not supported.")

  let delete c =
    if !counter_debug then
      Printf.printf "delete counter\n\n";
    match c with
    | [] -> []
    | _::cs -> cs
end