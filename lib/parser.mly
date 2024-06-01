%{
open Program
%}

%token <int> INT
%token <float> REAL
%token <string> ID
%token IF LET FUN IN SAMPLE OBSERVE PLUS MINUS NEG MULT DIV RPLUS RMINUS RNEG RMULT RDIV EQ NOTEQ LESS GREAT AND OR NOT
%token LSQUARE RSQUARE COMMA LBRACKET RBRACKET COLON SEMICOLON THEN ELSE
%token LPAREN RPAREN EOF

%nonassoc IN
%left SEMICOLON
%nonassoc ELSE EQ NOTEQ LESS GREAT
%left PLUS MINUS AND OR RPLUS RMINUS
%right MULT DIV RMULT RDIV NOT
%left NEG RNEG

%start program
%type <Program.program> program

%%

program:
  | FUN ID idlist EQ exp SEMICOLON program {
    let {funs; exp} = $7 in {funs = { name = $2; params = $3; body = $5 } :: funs; exp}
  }
  | exp EOF { { funs = []; exp = $1 } }
  ;

exp:
  | LPAREN exp RPAREN { $2 }
	| INT { Int $1 }
	| REAL { Real $1 }
	| ID { Var $1 }
	| ID LPAREN arglist RPAREN { Call ($1, $3) }
	| IF exp THEN exp ELSE exp { If ($2, $4, $6) }
	| LET ID EQ exp IN exp { Assign ($2, $4, $6) }
	| SAMPLE LPAREN exp RPAREN { Sample $3 }
	| OBSERVE LPAREN exp COMMA exp RPAREN { Observe ($3, $5) }
	| exp PLUS exp { Add ($1, $3) }
	| exp RPLUS exp { Radd ($1, $3) }
	| exp MINUS exp { Minus ($1, $3) }
	| exp RMINUS exp { Rminus ($1, $3) }
	| exp MULT exp { Mult ($1, $3) }
	| exp RMULT exp { Rmult ($1, $3) }
	| exp DIV exp { Div ($1, $3) }
	| exp RDIV exp { Rdiv ($1, $3) }
	| exp EQ exp { Eq ($1, $3) }
	| exp NOTEQ exp { Noteq ($1, $3) }
	| exp LESS exp { Less ($1, $3) }
	| exp GREAT exp { Less ($3, $1) }
	| exp AND exp { And ($1, $3) }
	| exp OR exp { Or ($1, $3) }
	| exp SEMICOLON exp { Seq ($1, $3) }
	| NOT exp { Not $2 }
	| LSQUARE explist RSQUARE { List $2 }
	| LBRACKET reclist RBRACKET { Record $2 }
	| NEG exp { Neg $2 }
  	| RNEG exp { Rneg $2 }
	;

idlist: { [] }
	| ID idlist { $1 :: $2 }
	;

arglist: { [] }
  | exp { [$1] }
	| exp COMMA arglist { $1 :: $3 }
	;

explist: { [] }
  | exp { [$1] }
	| exp COMMA explist { $1 :: $3 }
	;

reclist: { [] }
  | exp COLON exp { [($1, $3)] }
	| exp COLON exp COMMA reclist { ($1, $3) :: $5 }
	;
%%
