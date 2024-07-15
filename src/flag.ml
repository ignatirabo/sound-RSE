type flag_constr = MAX_ITE | LOOP_APPROX
type flag = flag_constr list
type t = flag
let empty = []
let rec check_flag (fc:flag_constr) (f:flag) =
  match f with
  | h::f ->
    if h = fc then true
    else check_flag fc f
  | [] -> false
let add fc f = fc::f
let join f1 f2 = f1 @ f2