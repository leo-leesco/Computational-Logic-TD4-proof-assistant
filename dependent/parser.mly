%{
open Expr
%}

%token IMP PI TYPE N NAT Z S IND EQ REFL J
%token FUN TO
%token LPAR RPAR COLON COMMA
%token <string> IDENT
%token EOF

%right TO IMP

%start expr
%type <Expr.expr> expr
%%

/* An expression */
expr:
  | aexpr { $1 }
  | PI LPAR IDENT COLON expr RPAR TO expr               { Pi ($3, $5, $8) }
  | LPAR IDENT COLON expr RPAR TO expr                  { Pi ($2, $4, $7) }
  | FUN LPAR IDENT COLON expr RPAR TO expr              { Abs ($3, $5, $8) }
  | expr IMP expr                                       { Pi ("_", $1, $3) }
  | expr TO expr                                        { Pi ("_", $1, $3) }
  | IND IDENT IDENT IDENT                               { Abs ("n", Nat, Ind (Var $2, Var $3, Var $4, Var "n")) }
  | IND IDENT IDENT IDENT IDENT                         { Ind (Var $2, Var $3, Var $4, Var $5) }
  | IND LPAR expr COMMA expr COMMA expr COMMA expr RPAR { Ind ($3, $5, $7, $9) }

/* An application */
aexpr:
  | sexpr       { $1 }
  | aexpr sexpr { App ($1, $2) }

/* A simple expression */
sexpr:
  | LPAR expr RPAR                  { $2 }
  | IDENT                           { Var $1 }
  | TYPE                            { Type }
  | NAT                             { Nat }
  | N                               { Nat }
  | Z                               { Z }
  | S expr                          { S $2 }
