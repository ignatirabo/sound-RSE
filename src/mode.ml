type apron =
  | A_box
  | A_polka

type non_rel_dom =
  | S_none
  | S_all
  | S_sse
  | S_apron

type rel_dom =
  | D_none
  | D_all
  | D_dep
  | D_rse

type mode =
  | M_interpret
  | M_rel
  | M_nonrel

type smode =
  | SM_test
  | SM_file

let smode_not_test = function
  | SM_test -> false
  | _ -> true

let str_to_int_list (s: string) : int list =
  let l : string list = String.split_on_char ',' s in
  List.map int_of_string l

let str_to_apron (s: string) : apron =
  match s with
  | "intvs" -> A_box
  | "polyhedra" -> A_polka
  | _ -> failwith "Unkown Apron domain"
let apron_to_str = function
  | A_box -> "Intvs"
  | A_polka -> "Polyhedra"

let str_to_nonrel (s: string) : non_rel_dom =
  match s with
  | "sse" -> S_sse
  | "redsse" -> S_all
  | _ -> failwith "Unkown non-relational domain"
let non_rel_dom_to_str = function
  | S_none -> "None"
  | S_sse -> "SoundSE"
  | S_apron-> "Apron"
  | S_all -> "SoundSE+Apron"

let str_to_rel (s: string) : rel_dom =
  match s with
  | "rse" -> D_rse
  | "dep" -> D_dep
  | _ -> failwith "Unkown relational domain"

let thr (str: string) =
  let lexbuf = Lexing.from_string str in
  try Thr_parser.expr_list Thr_lexer.read lexbuf
  with Parsing.Parse_error ->
    failwith (Printf.sprintf "Parsing failed.")
  

let parse ( ) =
  Printf.printf "Parsing input.\n";
  let filename = ref ""
  and mode: mode ref = ref M_interpret
  and smode: smode ref = ref SM_file
  and rel_dom: rel_dom ref  = ref D_none
  and non_rel_dom: non_rel_dom ref  = ref S_none
  and apron: apron ref = ref A_box in
  let lthr: Threshold.t ref = ref [] in
  let aux_non_rel nr =
    (match !non_rel_dom, nr with
    | S_none, nr -> non_rel_dom := nr
    | S_sse, S_apron | S_apron, S_sse -> non_rel_dom := S_all
    | _ -> raise (Failure "Not possible."));
    match !mode with
    | M_interpret -> mode := M_nonrel
    | _ -> () in
  let set_mode m = Arg.Unit (fun () -> mode := m) in
  let set_smode m = Arg.Unit (fun () -> smode := m) in
  let set_threshold = Arg.String (fun s -> lthr := thr s) in
  let set_non_rel nr =
    Arg.Unit (fun () -> aux_non_rel nr) in
  let set_apron a = Arg.Unit (fun () -> apron := a; aux_non_rel S_apron) in
  let set_rel r =
    let aux () =
        ((match !rel_dom, r with
        | D_none, r -> rel_dom := r
        | D_rse, D_dep | D_dep, D_rse -> rel_dom := D_all
        | _ -> raise (Failure "Not possible."));
        mode := M_rel) in
    Arg.Unit aux in
  let set_debug = Arg.Set Utils.debug in
  let set_debug_counter = Arg.Set Counter.counter_debug in
  Arg.parse
    [ "--test", set_smode SM_test, "test";
      "--interpret", set_mode M_interpret, "interpret";
      "--rse", set_rel D_rse, "set relational symbolic execution";
      "--dep", set_rel D_dep, "set dependences";
      "--sse", set_non_rel S_sse, "set single symbolic execution";
      "--intvs", set_apron A_box, "set internvals";
      "--poly", set_apron A_polka, "set polyhedra";
      "--thr", set_threshold, "set user threshold";
      "--debug", set_debug, "set debug prints";
      "--debug-counter", set_debug_counter, "set debug prints for counter";
    ] (fun s -> filename := s) "file";
  if String.length !filename = 0 && smode_not_test !smode then
    failwith "Filename is empty."
  else
    (!smode, !mode, !rel_dom, !non_rel_dom, !apron, !filename)

let prog filename : Prog.prog =
  Printf.printf "filename: %s\n" filename;
  let file = Unix.openfile filename [ Unix.O_RDONLY ] 0o644 in
  let channel = Unix.in_channel_of_descr file in
  let lexbuf = Lexing.from_channel channel in
  let prog =
    try Parser.prog Lexer.token lexbuf
    with Parsing.Parse_error ->
      failwith (Printf.sprintf "Parsing failed at line %d."
                  !Lexer.num_line) in
  (* Display of the parsed code and binding of the AST *)
  let prog = Prog.binding prog in
  Printf.printf "Parsing and binding done\ncode:\n\n%a\n" Prog.pp_prog prog;
  prog
