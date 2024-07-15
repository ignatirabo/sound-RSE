%token <string> NAME
%token <int>    INT

%token C_TRUE C_FALSE

%token O_ADD O_SUB O_MUL O_DIV O_MOD
%token O_LE  O_LT O_GE O_GT O_EQ O_NE
%token O_AND O_OR

%token K_ASSERT K_BOOL K_ELSE K_IF K_INPUT K_INT K_MAIN K_SEC K_WHILE

%token LPAR RPAR LBRACE RBRACE COLON SEMICOLON
%token EOF
%type <Syntax.Lang.stmt>  stmt
%type <Syntax.Lang.block> block
%type <Prog.t>  prog
%start stmt block prog
%%

var:
| NAME              { Syntax.Var.make $1 Syntax.Tint }
expr:
| expr0             { $1 }
expr0:
| expr0 O_OR expr1  { Syntax.Lang.Eop ($1, Syntax.Ops.Oor, $3) }
| expr1             { $1 }
expr1:
| expr1 O_AND expr2 { Syntax.Lang.Eop ($1, Syntax.Ops.Oand, $3) }
| expr2             { $1 }
expr2:
| expr2 O_EQ expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.Oeq, $3) }
| expr2 O_NE expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.One, $3) }
| expr2 O_LE expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.Ole, $3) }
| expr2 O_LT expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.Olt, $3) }
| expr2 O_GE expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.Oge, $3) }
| expr2 O_GT expr3  { Syntax.Lang.Eop ($1, Syntax.Ops.Ogt, $3) }
| expr3             { $1 }
expr3:
| expr3 O_ADD expr4 { Syntax.Lang.Eop ($1, Syntax.Ops.Oadd, $3) }
| expr3 O_SUB expr4 { Syntax.Lang.Eop ($1, Syntax.Ops.Osub, $3) }
| expr4             { $1 }
expr4:
| expr4 O_MUL expr5 { Syntax.Lang.Eop ($1, Syntax.Ops.Omul, $3) }
| expr4 O_DIV expr5 { Syntax.Lang.Eop ($1, Syntax.Ops.Odiv, $3) }
| expr4 O_MOD expr5 { Syntax.Lang.Eop ($1, Syntax.Ops.Omod, $3) }
| expr5             { $1 }
expr5:
| C_TRUE            { Syntax.Lang.Ecstb true }
| C_FALSE           { Syntax.Lang.Ecstb false }
| INT               { Syntax.Lang.Ecsti $1 }
| var               { Syntax.Lang.Evar $1 }
| LPAR expr0 RPAR   { $2 }

decl:
| K_BOOL var SEMICOLON { $2 }
| K_INT  var SEMICOLON { $2 }

stmt:
| var O_EQ expr SEMICOLON
    { Syntax.Lang.Sassign ($1, $3) }
| K_INPUT LPAR var RPAR SEMICOLON
    { Syntax.Lang.Sinput $3 }
| K_IF LPAR expr RPAR LBRACE block RBRACE K_ELSE LBRACE block RBRACE
    { Syntax.Lang.Sif ($3, $6, $10) }
| K_WHILE LPAR expr RPAR LBRACE block RBRACE
    { Syntax.Lang.Swhile ($3, $6) }

block:
|               { [ ] }
| stmt block    { $1 :: $2 }

globals:
|               { [ ] }
| decl globals  { $1 :: $2 }

delta:
| var O_EQ INT SEMICOLON { ($1,$3) }

sec:
| { [ ] }
| delta sec { $1 :: $2 }

security:
| K_SEC COLON LBRACE sec RBRACE { $4 }

proc_def:
| COLON LBRACE block RBRACE { $3 }

proc:
| NAME proc_def { { Prog.pname=$1 ; Prog.pbody=$2 } }

procs:
|               { [ ] }
| proc procs    { $1 :: $2 }

main:
| K_MAIN proc_def { $2 }

prog:
| globals security procs main EOF
    { { Prog.pglobs = $1 ;
        Prog.psec   = Sec_map.of_list $2 $1 ;
        Prog.pprocs = $3 ;
        Prog.pmain  = $4 } }

