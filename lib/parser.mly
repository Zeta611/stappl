%{
open Parse_tree
%}

%token <int> INT
%token <float> REAL
%token <bool> BOOL
%token <string> ID
%token IF THEN ELSE FUN LET IN
%token PLUS MINUS NEG MULT DIV RPLUS RMINUS RNEG RMULT RDIV EQ NE LT GT RLT RGT AND OR NOT
%token SAMPLE OBSERVE
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COMMA COLON SEMICOLON
%token EOF

%nonassoc IN
%right SEMICOLON
%nonassoc ELSE
%right OR
%right AND
%left EQ NE LT GT RLT RGT
%left PLUS MINUS RPLUS RMINUS
%left MULT DIV RMULT RDIV
%nonassoc NOT NEG RNEG

%start <program> program
%%

program:
  | FUN; name = ID; LPAREN; params = params; RPAREN; LBRACE; body = exp; RBRACE; rest = program
    { let { funs; exp } = rest in { funs = { name; params; body } :: funs; exp } }
  | exp = exp; EOF
    { { funs = []; exp } }
  ;

exp:
  | LPAREN; e = exp; RPAREN { e }
	| i = INT { Int i }
	| r = REAL { Real r }
	| b = BOOL { Bool b }
	| x = ID { Var x }
  | f = ID; LPAREN; es = args; RPAREN { Call (f, es) }
  | IF; e_pred = exp; THEN; e_con = exp; ELSE; e_alt = exp { If (e_pred, e_con, e_alt) }
  | LET; x = ID; EQ; e = exp; IN; body = exp { Assign (x, e, body) }
  | SAMPLE; LPAREN; e = exp; RPAREN { Sample e }
  | OBSERVE; LPAREN; e1 = exp; COMMA; e2 = exp; RPAREN { Observe (e1, e2) }
  | e1 = exp; PLUS; e2 = exp { Add (e1, e2) }
  | e1 = exp; RPLUS; e2 = exp { Radd (e1, e2) }
  | e1 = exp; MINUS; e2 = exp { Minus (e1, e2) }
  | e1 = exp; RMINUS; e2 = exp { Rminus (e1, e2) }
  | e1 = exp; MULT; e2 = exp { Mult (e1, e2) }
  | e1 = exp; RMULT; e2 = exp { Rmult (e1, e2) }
  | e1 = exp; DIV; e2 = exp { Div (e1, e2) }
  | e1 = exp; RDIV; e2 = exp { Rdiv (e1, e2) }
  | e1 = exp; EQ; e2 = exp { Eq (e1, e2) }
  | e1 = exp; NE; e2 = exp { Noteq (e1, e2) }
  | e1 = exp; LT; e2 = exp { Less (e1, e2) }
  | e1 = exp; GT; e2 = exp { Less (e2, e1) }
  | e1 = exp; RLT; e2 = exp { Rless (e1, e2) }
  | e1 = exp; RGT; e2 = exp { Rless (e2, e1) }
  | e1 = exp; AND; e2 = exp { And (e1, e2) }
  | e1 = exp; OR; e2 = exp { Or (e1, e2) }
  | e1 = exp; SEMICOLON; e2 = exp { Seq (e1, e2) }
  | NOT; e = exp { Not e }
  | LBRACK; es = list_fields; RBRACK { List es }
  | LBRACE; es = rec_fields; RBRACE { Record es }
  | NEG; e = exp { Neg e }
  | RNEG; e = exp { Rneg e }
	;

params:
    params = separated_list(COMMA, ID) { params } ;

args:
    args = separated_list(COMMA, exp) { args } ;

list_fields:
    lst = separated_list(COMMA, exp) { lst } ;

rec_fields:
    record = separated_list(COMMA, rec_field) { record } ;

rec_field:
    k = exp; COLON; v = exp { (k, v) } ;
