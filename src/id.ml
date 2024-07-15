(** Id for states *)
type id = int * bool * string list
type t = id
let global_id = ref 0
let global_temp_id = ref 0
let make ?message:(message=[]) temp : id =
  if temp then
    begin
      global_temp_id := !global_temp_id - 1;
      (!global_temp_id, temp, message)
    end
  else
    begin
      global_id := !global_id + 1;
      (!global_id, temp, message)
    end
let get_id (i,_,_) = i
let get_temporal (_,b,_) = b
let get_message (_,_,s) = s
let set_message s (i,b,_) = (i,b,[s])
let update_message s (i,b,s') = (i,b,s@s')
let pp indent chan ((i, b, s): id) =
  match b, s with
  | true, [] ->
    Printf.fprintf chan "%s(%d, Temporary)" indent i
  | true, _ ->
    Printf.fprintf chan "%s(%d, Temporary, %s)" indent i (String.concat "; " s)
  | false, [] ->
    Printf.fprintf chan "%s(%d)" indent i
  | false, s ->
    Printf.fprintf chan "%s(%d, %s)" indent i (String.concat "; " s)
