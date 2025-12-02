let () = Printexc.record_backtrace true
let log = false
let debug = true

open Expr
module Expr = Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(** [subst x u e] is [e[u/x]], meaning [x] is replaced by [u] in [e] *)
let rec subst x u = function
  | Type -> Type
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x u n)
  | Var y -> if x = y then u else Var y
  | App (t, t') -> App (subst x u t, subst x u t')
  | Abs (y, a, t) ->
      if debug then
        print_endline
          (to_string (Abs (y, a, t))
          ^ if log then "[" ^ x ^ "↦" ^ to_string u ^ "]" else "");
      if y <> x then Abs (y, subst x u a, subst x u t)
      else
        let y' = fresh_var () in
        subst x u (Abs (y', subst y (Var y') a, subst y (Var y') t))
  | Pi (y, a, t) ->
      if y <> x then Pi (y, subst x u a, subst x u t)
      else
        let y' = fresh_var () in
        subst x u (Pi (y', subst y (Var y') a, subst y (Var y') t))
  | Ind (p, z, s, n) -> Ind (subst x u p, subst x u z, subst x u s, subst x u n)

let%test_unit "subst" =
  [%test_eq: expr] (subst "x" (Var "y") (Var "x")) (Var "y");
  [%test_eq: expr] (subst "x" (Var "y") (Var "z")) (Var "z");

  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("t", Var "A", Var "x")))
    (Abs ("t", Var "A", Var "y"));
  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("x", Var "A", Var "x")))
    (Abs ("x1", Var "A", Var "x1"))

let rec alpha t u =
  if debug then
    print_endline
      ((if log then "α-comparison:" else "")
      ^ to_string t ^ " =? " ^ to_string u);
  match (t, u) with
  | Var x, Var y -> x = y
  | Abs (x, a, t), Abs (y, b, u) | Pi (x, a, t), Pi (y, b, u) ->
      if x = y then alpha a b && alpha t u
      else
        let x' = fresh_var () in
        alpha (subst x (Var x') a) (subst y (Var x') b)
        && alpha (subst x (Var x') t) (subst y (Var x') u)
  | Ind (p, z, s, n), Ind (q, z', s', m) ->
      alpha p q && alpha n m && alpha z z' && alpha s s'
  | App (t, u), App (t', u') -> alpha t t' && alpha u u'
  | S n, S m -> alpha n m
  | Type, Type | Nat, Nat | Z, Z -> true
  | _, _ -> false

let%test "var1 α-equiv" = alpha (Var "x") (Var "x")
let%test "var2 α-equiv" = not (alpha (Var "x") (Var "y"))

let%test "abs α-equiv" =
  alpha (Abs ("y", Var "A", Var "y")) (Abs ("x", Var "A", Var "x"))

let%test "abs α-equiv" =
  alpha
    (Abs
       ("x", Var "A", App (Var "x", Abs ("x", Var "A", App (Var "x", Var "y")))))
    (Abs
       ("z", Var "A", App (Var "z", Abs ("x", Var "A", App (Var "x", Var "y")))))

let%test "abs α-equiv" =
  not
    (alpha
       (Abs
          ( "x",
            Var "A",
            App (Var "x", Abs ("x", Var "A", App (Var "x", Var "y"))) ))
       (Abs
          ( "y",
            Var "A",
            App (Var "y", Abs ("x", Var "A", App (Var "x", Var "y"))) )))

let%test "subst α-equiv" =
  alpha
    (subst "x" (Var "y") (Abs ("x", Var "A", Var "x")))
    (Abs ("x", Var "A", Var "x"))

let%test "subst in Nat α-equiv" =
  alpha (S (S (S Z))) (subst "x" (S (S Z)) (S (Var "x")))

let%test "subst in Nat α-equiv" =
  not (alpha (S (S (S Z))) (subst "x" Z (S (Var "x"))))

type context = (string * (expr * expr option)) list
(** each element of the context has a [string] identifier, an [expr] type and an
    [expr option] value *)

let string_of_context ctx =
  List.map
    (fun (x, (a, t)) ->
      x ^ " : " ^ to_string a
      ^ match t with Some t -> " = " ^ to_string t | None -> "")
    ctx
  |> String.concat "\n"

let%expect_test "Contexts" =
  let ctx = [ ("x", (Var "A", None)); ("x", (Var "A", Some (Var "t"))) ] in
  print_endline (string_of_context ctx);
  [%expect {|
    x : A
    x : A = t
  |}]

exception Type_error of string

let rec normalize ctx = function
  | Type -> Type
  | Nat -> Nat
  | Z -> Z
  | S n -> S (normalize ctx n)
  | Var x -> ( try Option.get (snd (List.assoc x ctx)) with _ -> Var x)
  | Abs (x, a, t) ->
      Abs (x, normalize ctx a, normalize ((x, (a, None)) :: ctx) t)
  | Pi (x, a, t) -> Pi (x, normalize ctx a, normalize ((x, (a, None)) :: ctx) t)
  | App (Abs (x, _a, t), u) ->
      subst x (normalize ctx u) (normalize ctx t)
      (* [normalize] should only be called in this case when [u:_a] *)
  | App (t, u) -> (
      let t' = normalize ctx t in
      match t' with
      | Abs (_, _, _) -> normalize ctx (App (t', normalize ctx u))
      | _ -> App (t', normalize ctx u))
  | Ind (p, z, s, n) -> (
      match normalize ctx n with
      | Z ->
          if debug then print_endline "base case";
          normalize ctx z
      | S m ->
          if debug then print_endline "induction case";
          let s = normalize ctx s in
          let p = normalize ctx p in
          let z = normalize ctx z in
          normalize ctx (App (App (s, m), Ind (p, z, s, m)))
      | _ ->
          if debug then print_endline "normalizing case";
          let s = normalize ctx s in
          let p = normalize ctx p in
          let z = normalize ctx z in
          let n = normalize ctx n in
          Ind (p, z, s, n))

let conv ctx t u = alpha (normalize ctx t) (normalize ctx u)

let rec infer ctx = function
  | Type | Nat -> Type
  | Z -> Nat
  | S n ->
      if infer ctx n = Nat then Nat
      else
        raise
          (Type_error
             (to_string n
            ^ " is not a natural number, but tried to take its successor"))
  | Var x -> fst (List.assoc x ctx)
  | Abs (x, a, t) -> Pi (x, a, infer ((x, (a, None)) :: ctx) t)
  | Pi (_, _, _) -> Type
  | App (t, u) -> (
      let ttype = infer ctx t in
      match ttype with
      | Pi (x, a, b)
        when check ctx u a;
             true ->
          subst x u b
      | _ ->
          raise
            (Type_error
               ("Mismatch in application : (" ^ to_string t ^ ":"
              ^ to_string ttype ^ ") (" ^ to_string u ^ ":"
               ^ to_string (infer ctx u)
               ^ ")")))
  | Ind (p, z, s, n) ->
      check ctx p (Pi ("x", Nat, Type));
      check ctx z (App (p, Z));
      check ctx s
        (Pi ("n", Nat, Pi ("pn", App (p, Var "n"), App (p, S (Var "n")))));
      check ctx n Nat;
      App (p, Var "n")

and check ctx term typ =
  let b = infer ctx term in
  if not (conv ctx typ b) then
    raise
      (Type_error
         (to_string term ^ " is of type " ^ to_string b ^ ", expected "
        ^ to_string typ))

let%test_unit "type inference" =
  let ctx =
    [
      ("Bool", (Type, None));
      ("true", (Var "Bool", None));
      ("false", (Var "Bool", None));
    ]
  in
  check ctx (Var "false") (Var "Bool")

let%test_unit "type inference - Nat" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, S (Var "n")))));
      ("z", (App (Var "p", Z), Some (S Z)));
      ( "s",
        ( Pi
            ( "n",
              Nat,
              Pi ("pn", App (Var "p", Var "n"), App (Var "p", S (Var "n"))) ),
          Some
            (Abs ("n", Nat, Abs ("pn", App (Var "p", Var "n"), S (Var "pn"))))
        ) );
      ("n", (Nat, Some (S (S Z))));
    ]
  in
  check ctx (Ind (Var "p", Var "z", Var "s", Var "n")) (App (Var "p", Var "n"))

(** tests for 𝝰𝝱-equivalence *)
let ( =? ) = conv []

let%test "αβ-equivalence_basic" =
  let idfun = Abs ("A", Type, Abs ("x", Var "A", Var "x")) in
  let idfun1 = Abs ("B", Type, Abs ("y", Var "B", Var "y")) in
  idfun =? idfun1

let%test "αβ-equivalence_example" =
  let ctx =
    [
      ("Bool", (Type, None));
      ("true", (Var "Bool", None));
      ("false", (Var "Bool", None));
    ]
  in
  let idbool = Abs ("b", Var "Bool", Var "b") in
  conv ctx (App (idbool, Var "true")) (Var "true")

let%test "αβ-equivalence_dependent" =
  let idsimple = Abs ("x", Var "A", Var "x") in
  let iddependent = Abs ("A", Type, idsimple) in
  let ctx = [ ("A", (Type, None)); ("x", (Var "A", None)) ] in

  if debug then (
    print_endline ("reducing: " ^ to_string iddependent);
    print_endline ("context:\r" ^ string_of_context ctx));

  conv ctx (App (idsimple, Var "x")) (Var "x")
  && conv ctx (Var "x") (App (App (iddependent, Var "A"), Var "x"))

let%test "αβ-equivalence_natural" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, S (Var "n")))));
      ("z", (App (Var "p", Z), Some (S Z)));
      ( "s",
        ( Pi
            ( "n",
              Nat,
              Pi ("pn", App (Var "p", Var "n"), App (Var "p", S (Var "n"))) ),
          Some
            (Abs ("n", Nat, Abs ("pn", App (Var "p", Var "n"), S (Var "pn"))))
        ) );
      ("n", (Nat, Some (S (S Z))));
    ]
  in
  conv ctx (Ind (Var "p", Var "z", Var "s", Var "n")) (S (S (S Z)))
