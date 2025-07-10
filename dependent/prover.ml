let () = Printexc.record_backtrace true
let log = true
let debug = false && log

open Expr
module Expr = Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(** [subst x u e] is [e[u/x]], meaning [x] is replaced by [u] in [e] *)
let rec subst x u = function
  | Type -> Type
  | Var y -> if x = y then u else Var y
  | App (t, t') -> App (subst x u t, subst x u t')
  | Abs (y, a, t) ->
      if debug then
        print_endline
          (to_string (Abs (y, a, t)) ^ "[" ^ x ^ "↦" ^ to_string u ^ "]");
      if y <> x then Abs (y, subst x u a, subst x u t)
      else
        let y' = fresh_var () in
        subst x u (Abs (y', subst y (Var y') a, subst y (Var y') t))
  | Pi (y, a, t) ->
      if y <> x then Pi (y, subst x u a, subst x u t)
      else
        let y' = fresh_var () in
        subst x u (Pi (y', subst y (Var y') a, subst y (Var y') t))

let%test_unit "subst" =
  [%test_eq: expr] (subst "x" (Var "y") (Var "x")) (Var "y");
  [%test_eq: expr] (subst "x" (Var "y") (Var "z")) (Var "z");

  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("t", Var "A", Var "x")))
    (Abs ("t", Var "A", Var "y"));
  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("x", Var "A", Var "x")))
    (Abs ("x1", Var "A", Var "x1"))




