type 'a maybe_pair = Single of 'a | Pair of 'a * 'a
type 'a t = 'a maybe_pair
exception BadPairAccess
let single a = Single a
let pair (a, a') = Pair (a, a')
let is_single = function
| Single _ -> true
| Pair _ -> false
let is_pair mp = not (is_single mp)
let get_single = function
| Single a -> a
| _ -> raise BadPairAccess
let get_pair = function
| Pair (a, a') -> (a, a')
| _ -> raise BadPairAccess
let left = function
| Single a -> a
| Pair (a, _) -> a
let right = function
| Single a -> a
| Pair (_, a') -> a'
let pp_pair (p: out_channel -> 'a -> unit) chan (mp : 'a maybe_pair) =
  if is_single mp then
    let l = get_single mp in
    Printf.fprintf chan "<%a>" p l
  else
    let (l, r) = get_pair mp in
    Printf.fprintf chan "<%a,%a>" p l p r