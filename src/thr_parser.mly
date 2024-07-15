%token <string> NAME
%token <int>    INT

%token O_ADD O_MUL O_SUB
%token O_GE O_GT O_EQ O_NE

%token LBRAC RBRAC
%token LPAR RPAR
%token COMMA DELIM

%type <Threshold.t> expr_list
%start expr_list
%%

var:
  | NAME { Syntax.Var.make $1 Syntax.Tint }

coeff:
  | INT { $1 }

term:
  | var O_MUL coeff { ($3, $1) }
  | coeff O_MUL var { ($1, $3) }
  | var { (1, $1) }

linexpr:
  | term { [ $1 ] }
  | term O_ADD linexpr { $1 :: $3 }

op:
  | O_EQ { Syntax.Ops.Oeq }
  | O_NE { Syntax.Ops.One }
  | O_GE { Syntax.Ops.Oge }
  | O_GT { Syntax.Ops.Ogt }

ctr:
  | coeff O_ADD linexpr op INT { ($3, Some $1, $4) }
  | linexpr op INT { ($1, None, $2) }

ctrs:
  | { [ ] }
  | ctr ctrs { $1 :: $2 }
  | ctr COMMA ctrs { $1 :: $3 }

expr_list:
  | LBRAC ctrs RBRAC { $2 }
