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
  | PI LPAR IDENT COLON expr RPAR TO expr                        { Pi ($3, $5, $8) }
  | LPAR IDENT COLON expr RPAR TO expr                           { Pi ($2, $4, $7) }
  | FUN LPAR IDENT COLON expr RPAR TO expr                       { Abs ($3, $5, $8) }
  | expr IMP expr                                                { Pi ("_", $1, $3) }
  | expr TO expr                                                 { Pi ("_", $1, $3) }
  | IND IDENT IDENT IDENT                                        { let x = fresh_var () in
    Abs (x, Nat, Ind (Var $2, Var $3, Var $4, Var x)) }
  | IND IDENT IDENT IDENT IDENT                                  { Ind (Var $2, Var $3, Var $4, Var $5) }
  | IND sexpr sexpr sexpr                                        { let x = fresh_var () in
    Abs (x, Nat, Ind ($2, $3, $4, Var x)) }
  | IND sexpr sexpr sexpr sexpr                                  { Ind ($2, $3, $4, $5) }
  | IND LPAR expr COMMA expr COMMA expr COMMA expr RPAR          { Ind ($3, $5, $7, $9) }
  | J sexpr sexpr sexpr sexpr sexpr                              { J ($2, $3, $4, $5, $6) }
  | J LPAR expr COMMA expr COMMA expr COMMA expr COMMA expr RPAR { J ($3, $5, $7, $9, $11) }

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
  | S sexpr                         { S $2 }
  | sexpr EQ sexpr                  { Eq ($1, $3)}
  | REFL sexpr                      { Refl $2 }
