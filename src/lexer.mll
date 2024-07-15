{
open Parser
let h = Hashtbl.create 10
let _ =
  List.iter (fun (a, b) -> Hashtbl.add h a b)
    [ "bool"     , K_BOOL  ;
      "else"     , K_ELSE  ;
      "false"    , C_FALSE ;
      "if"       , K_IF    ;
      "input"    , K_INPUT ;
      "int"      , K_INT   ;
      "main"     , K_MAIN  ;
      "security" , K_SEC   ;
      "true"     , C_TRUE  ;
      "while"    , K_WHILE ]
let fstring s = try Hashtbl.find h s with Not_found -> NAME s
let num_line = ref 1
}

let cdigit = ['0'-'9']
let letter = ['a'-'z']|['A'-'Z']
let letterdigit = ['a'-'z']|['A'-'Z']|['0'-'9']
let cint   = cdigit+
let cvar   = 'V''[' cint ']'
let var    = letter letterdigit*
let cnint  = '-'cint

rule token = parse
| ' ' | '\t'  { token lexbuf }
| '\n'     { incr num_line; token lexbuf }

| var      { fstring (Lexing.lexeme lexbuf) }
| cint     { INT (int_of_string (Lexing.lexeme lexbuf)) }
| cnint    { INT (int_of_string (Lexing.lexeme lexbuf)) }

| '+'      { O_ADD }
| '-'      { O_SUB }
| '*'      { O_MUL }
| '/'      { O_DIV }
| '%'      { O_MOD }
| "<="     { O_LE  }
| '<'      { O_LT  }
| ">="     { O_GE  }
| '>'      { O_GT  }
| '='      { O_EQ  }
| "!="     { O_NE  }
| "&&"     { O_AND }
| "||"     { O_OR  }

| '('      { LPAR }
| ')'      { RPAR }
| '{'      { LBRACE }
| '}'      { RBRACE }
| ':'      { COLON }
| ';'      { SEMICOLON }
| "(*" [^ '\n']* "*)" { token lexbuf }

| _  as c  { Printf.printf "character: %c\n" c; failwith "unbound char" }
| eof      { EOF }
