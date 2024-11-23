%{
open Expr
%}

%token IMP AND OR TRUE FALSE NOT
%token FUN TO CASE OF
%token LPAR RPAR COLON COMMA BAR
%token FST SND LEFT RIGHT ABSURD
%token <string> IDENT
%token EOF

%right IMP
%right OR
%right AND
%nonassoc NOT

%start typ
%start term
%type <Expr.typ> typ
%type <Expr.term> term
%%

/* A typpe */
typ:
  | IDENT     { TVar $1 }
  (*| typ IMP typ { Imp ($1, $3) }*)
  | typ AND typ { Conj ($1, $3) }
  | typ OR typ  { Disj ($1, $3) }
  (*| NOT typ    { Imp ($2, False) }*)
  | TRUE      { True }
  | FALSE     { Empty }

/* A term */
term:
  | aterm                                    { $1 }
  | FUN LPAR IDENT COLON typ RPAR TO term     { Abs ($3, $5, $8) }
  | CASE term OF IDENT TO term BAR IDENT TO term { Case ($2, $4, $6, $8, $10) }

/* An application */
aterm:
  | sterm     { $1 }
  | aterm sterm { App ($1, $2) }

/* A simple term */
sterm:
  | IDENT                        { Var $1 }
  | LPAR term RPAR                 { $2 }
  | FST sterm                      { Fst $2 }
  | SND sterm                      { Snd $2 }
  | LPAR RPAR                    { Unit }
  | LPAR term COMMA term RPAR        { Pair ($2, $4) }
  | LEFT LPAR term COMMA typ RPAR   { Left ($3, $5) }
  | RIGHT LPAR typ COMMA term RPAR  { Right ($3, $5) }
  | ABSURD LPAR term COMMA typ RPAR { Absurd ($3, $5) }
