%{
open Program
%}

%token <int> NUM
%token <string> ID
%token IF LET FUN IN SAMPLE OBSERVE PLUS MINUS MULT DIV EQ NOTEQ LESS GREAT AND OR NOT
%token LSQUARE RSQUARE COMMA LBRACKET RBRACKET COLON SEMICOLON THEN ELSE 
%token LPAREN RPAREN EOF

%nonassoc IN
%nonassoc ELSE EQ NOTEQ LESS GREAT
%left PLUS MINUS AND OR
%right MULT DIV NOT
%nonassoc SAMPLE OBSERVE

%start program
%type <Program.program> program

%%

program:
  | FUN ID idlist EQ exp SEMICOLON program { let {funs; exp} = $7 in {funs = ($2, $3, $5) :: funs; exp} }
  | exp EOF { { funs = []; exp = $1 } }
  ;

exp:
	| NUM { CONST $1 }
	| ID { VAR $1 }
	| ID LPAREN arglist RPAREN { CALL ($1, $3) }
	| IF exp THEN exp ELSE exp { IF ($2, $4, $6) }
	| LET ID EQ exp IN exp { ASSIGN ($2, $4, $6) }
	| SAMPLE exp { SAMPLE $2 }
	| OBSERVE exp exp { OBSERVE ($2, $3) }
	| exp PLUS exp { ADD ($1, $3) }
	| exp MINUS exp { MINUS ($1, $3) }
	| exp MULT exp { MULT ($1, $3) }
	| exp DIV exp { DIV ($1, $3) }
	| exp EQ exp { EQ ($1, $3) }
	| exp NOTEQ exp { NOTEQ ($1, $3) }
	| exp LESS exp { LESS ($1, $3) }
	| exp GREAT exp { LESS ($3, $1) }
	| exp AND exp { AND ($1, $3) }
	| exp OR exp { OR ($1, $3) }
	| NOT exp { NOT $2 }
	| LSQUARE explist RSQUARE { LIST $2 }
	| LBRACKET reclist RBRACKET { RECORD $2 }
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
