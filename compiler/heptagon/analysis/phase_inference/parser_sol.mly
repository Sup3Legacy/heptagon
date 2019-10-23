%{

%}

%token ARROW
%token EOF

%token <string> IDENT
%token <int> INT

%start solution
%type <(string * int) list> solution

%%

lelement:
  | IDENT ARROW INT           { [($1,$3)] }
  | IDENT ARROW INT lelement  { ($1,$3)::$4 }
;

solution: lelement EOF { $1 }
;

