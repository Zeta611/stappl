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
  | FUN ID idlist EQ exp SEMICOLON program { let {funs; exp} = $7 in {funs = ($2, $3, $5) :: funs; exp} }
  | exp EOF { { funs = []; exp = $1 } }
  ;

exp:
  | LPAREN exp RPAREN { $2 }
	| INT { INT $1 }
	| REAL { REAL $1 }
	| ID { VAR $1 }
	| ID LPAREN arglist RPAREN { CALL ($1, $3) }
	| IF exp THEN exp ELSE exp { IF ($2, $4, $6) }
	| LET ID EQ exp IN exp { ASSIGN ($2, $4, $6) }
	| SAMPLE LPAREN exp RPAREN { SAMPLE $3 }
	| OBSERVE LPAREN exp COMMA exp RPAREN { OBSERVE ($3, $5) }
	| exp PLUS exp { ADD ($1, $3) }
	| exp RPLUS exp { RADD ($1, $3) }
	| exp MINUS exp { MINUS ($1, $3) }
	| exp RMINUS exp { RMINUS ($1, $3) }
	| exp MULT exp { MULT ($1, $3) }
	| exp RMULT exp { RMULT ($1, $3) }
	| exp DIV exp { DIV ($1, $3) }
	| exp RDIV exp { RDIV ($1, $3) }
	| exp EQ exp { EQ ($1, $3) }
	| exp NOTEQ exp { NOTEQ ($1, $3) }
	| exp LESS exp { LESS ($1, $3) }
	| exp GREAT exp { LESS ($3, $1) }
	| exp AND exp { AND ($1, $3) }
	| exp OR exp { OR ($1, $3) }
	| exp SEMICOLON exp { SEQ ($1, $3) }
	| NOT exp { NOT $2 }
	| LSQUARE explist RSQUARE { LIST $2 }
	| LBRACKET reclist RBRACKET { RECORD $2 }
	| NEG exp { NEG $2 }
  	| RNEG exp { RNEG $2 }
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
