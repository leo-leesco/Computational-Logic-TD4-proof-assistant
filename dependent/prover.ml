let () = Printexc.record_backtrace true
(* let log = false *)
(* let debug = true *)

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
      (* print_endline *)
      (*   (to_string (Abs (y, a, t)) ^ "[" ^ x ^ "↦" ^ to_string u ^ "]"); *)
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
  | Eq (t, t') -> Eq (subst x u t, subst x u t')
  | Refl t -> Refl (subst x u t)
  | J (p, r, x', y, e) ->
      J (subst x u p, subst x u r, subst x u x', subst x u y, subst x u e)

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
  (* print_string "α-comparison:"; *)
  (* print_endline (to_string t ^ " =? " ^ to_string u); *)
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
  | J (p, r, x, y, e), J (q, s, x', y', e') ->
      alpha p q && alpha r s && alpha x x' && alpha y y' && alpha e e'
  | App (t, u), App (t', u') | Eq (t, u), Eq (t', u') ->
      alpha t t' && alpha u u'
  | S n, S m | Refl n, Refl m -> alpha n m
  | Type, Type | Nat, Nat | Z, Z -> true
  | _, _ -> false

let%test "var1 α-equiv" = alpha (Var "x") (Var "x")
let%test "var2 α-equiv" = not (alpha (Var "x") (Var "y"))

let%test "abs1 α-equiv" =
  alpha (Abs ("y", Var "A", Var "y")) (Abs ("x", Var "A", Var "x"))

let%test "abs2 α-equiv" =
  alpha
    (Abs
       ("x", Var "A", App (Var "x", Abs ("x", Var "A", App (Var "x", Var "y")))))
    (Abs
       ("z", Var "A", App (Var "z", Abs ("x", Var "A", App (Var "x", Var "y")))))

let%test "abs3 α-equiv" =
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

let%test "subst1 in Nat α-equiv" =
  alpha (S (S (S Z))) (subst "x" (S (S Z)) (S (Var "x")))

let%test "subst2 in Nat α-equiv" =
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

let%expect_test "context" =
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
  | Var x -> (
      (* print_endline ("trying to normalize " ^ x); *)
      try normalize ctx (Option.get (snd (List.assoc x ctx))) with _ -> Var x)
  | Abs (x, a, t) ->
      Abs (x, normalize ctx a, normalize ((x, (a, None)) :: ctx) t)
  | Pi (x, a, t) -> Pi (x, normalize ctx a, normalize ((x, (a, None)) :: ctx) t)
  | App (t, u) -> (
      (* print_endline ("application : " ^ to_string (App (t, u))); *)
      let u = normalize ctx u in
      match normalize ctx t with
      (* [normalize] should only be called in this case when [u:_a] *)
      | Abs (x, _a, t) -> normalize ctx (subst x u t)
      | t -> App (t, u))
  | Ind (p, z, s, n) -> (
      (* print_endline (to_string (Ind (p, z, s, n))); *)
      match normalize ctx n with
      | Z ->
          (* print_endline "base case"; *)
          normalize ctx z
      | S m ->
          (* print_endline "induction case"; *)
          let p = normalize ctx p in
          let z = normalize ctx z in
          let s = normalize ctx s in
          normalize ctx (App (App (s, m), Ind (p, z, s, m)))
      | _ ->
          (* print_endline "normalizing case"; *)
          let p = normalize ctx p in
          let z = normalize ctx z in
          let s = normalize ctx s in
          Ind (p, z, s, n))
  | J (p, r, x, y, e) -> (
      match normalize ctx e with
      | Refl z when z = x -> App (normalize ctx r, normalize ctx x)
      | e ->
          J
            ( normalize ctx p,
              normalize ctx r,
              normalize ctx x,
              normalize ctx y,
              e ))
  | Eq (x, y) -> Eq (normalize ctx x, normalize ctx y)
  | Refl x -> Refl (normalize ctx x)

let%test "normalize : explicit natural recursor" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, Nat))));
      ("z", (App (Var "p", Z), Some (S Z)));
      ( "s",
        ( Pi ("n", Nat, Pi ("pn", App (Var "p", Var "n"), App (Var "p", Nat))),
          Some
            (Abs ("n", Nat, Abs ("pn", App (Var "p", Var "n"), S (Var "pn"))))
        ) );
    ]
  in
  normalize ctx (Ind (Var "p", Var "z", Var "s", S (S Z))) = S (S (S Z))
  && normalize ctx (Ind (Var "p", Var "z", Var "s", S (S Z))) = S (S (S Z))

let%test_unit "normalize : implicit natural recursor ; identity" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, Nat))));
      ( "s",
        ( Pi ("n", Nat, Pi ("pn", Nat, Nat)),
          Some (Abs ("n", Nat, Abs ("pn", Nat, S (Var "n")))) ) );
      ( "pred",
        ( Pi ("n", Nat, Nat),
          Some (Abs ("n", Nat, Ind (Var "p", Z, Var "s", Var "n"))) ) );
    ]
  in
  [%test_eq: expr] (normalize ctx (App (Var "pred", Z))) Z;
  [%test_eq: expr] (normalize ctx (App (Var "pred", S Z))) (S Z);
  [%test_eq: expr] (normalize ctx (App (Var "pred", S (S Z)))) (S (S Z))

let%test_unit "normalize : implicit natural recursor ; predecessor" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, Nat))));
      ( "s",
        ( Pi ("n", Nat, Pi ("pn", Nat, Nat)),
          Some (Abs ("n", Nat, Abs ("pn", Nat, Var "n"))) ) );
      ( "pred",
        ( Pi ("n", Nat, Nat),
          Some (Abs ("n", Nat, Ind (Var "p", Z, Var "s", Var "n"))) ) );
    ]
  in
  [%test_eq: expr] (normalize ctx (App (Var "pred", Z))) Z;
  [%test_eq: expr] (normalize ctx (App (Var "pred", S Z))) Z;
  [%test_eq: expr] (normalize ctx (App (Var "pred", S (S Z)))) (S Z)

let%test_unit "normalize : implicit natural recursor ; addition" =
  let ctx =
    [
      ("p", (Pi ("n", Nat, Type), Some (Abs ("n", Nat, Nat))));
      ( "s",
        ( Pi ("n", Nat, Pi ("pn", Nat, Nat)),
          Some (Abs ("n", Nat, Abs ("pn", Nat, S (Var "pn")))) ) );
      ( "add",
        ( Pi ("n", Nat, Abs ("m", Nat, Nat)),
          Some
            (Abs
               ( "n",
                 Nat,
                 Abs ("m", Nat, Ind (Var "p", Var "m", Var "s", Var "n")) )) )
      );
    ]
  in
  [%test_eq: expr] (normalize ctx (App (App (Var "add", Z), Z))) Z;
  [%test_eq: expr] (normalize ctx (App (App (Var "add", Z), S Z))) (S Z);
  [%test_eq: expr] (normalize ctx (App (App (Var "add", S Z), S Z))) (S (S Z));
  [%test_eq: expr]
    (normalize ctx (App (App (Var "add", S (S Z)), S (S (S Z)))))
    (S (S (S (S (S Z)))));
  [%test_eq: expr]
    (normalize ctx (App (App (Var "add", S (S Z)), S Z)))
    (S (S (S Z)))

let conv ctx t u = alpha (normalize ctx t) (normalize ctx u)

let rec infer ctx = function
  | Type | Nat -> Type
  | Z -> Nat
  | S n ->
      if infer ctx (normalize ctx n) = Nat then Nat
      else
        raise
          (Type_error
             (to_string n
            ^ " is not a natural number, but tried to take its successor"))
  | Var x -> fst (List.assoc x ctx)
  | Abs (x, a, t) -> Pi (x, a, infer ((x, (a, None)) :: ctx) t)
  | Pi (_, _, _) -> Type
  | App (t, u) -> (
      match infer ctx t with
      | Pi (x, a, b)
        when check ctx u a;
             true ->
          subst x u b
      | typ ->
          raise
            (Type_error
               ("Mismatch in application : (" ^ to_string t ^ ":"
              ^ to_string typ ^ ") (" ^ to_string u ^ ":"
               ^ to_string (infer ctx u)
               ^ ")")))
  | Ind (p, z, s, n) ->
      check ctx p (Pi ("x", Nat, Type));
      check ctx z (normalize ctx (App (p, Z)));
      check ctx s
        (normalize ctx
           (Pi ("n", Nat, Pi ("pn", App (p, Var "n"), App (p, S (Var "n"))))));
      check ctx n Nat;
      normalize ctx (App (p, Var "n"))
  | Eq (t, u) ->
      if infer ctx t = infer ctx u then Type
      else
        raise
          (Type_error ("Tried to compare" ^ to_string t ^ " and " ^ to_string u))
  | Refl x -> Eq (x, x)
  | J (p, r, x, y, e) ->
      let a = infer ctx x in
      check ctx y a;
      check ctx p
        (Pi ("x", a, Pi ("y", a, Pi ("e", Eq (Var "x", Var "y"), Type))));
      check ctx r
        (Pi ("x", a, App (App (App (p, Var "x"), Var "x"), Refl (Var "x"))));
      check ctx e (Eq (x, y));
      App (App (App (p, x), y), e)
(* match p with *)
(*   | Pi (x',a,Pi (y',a',Pi(_,Eq(x'',y''),Type))) when a =? a' && x' =? x'' && y' =? y'' -> check ctx x a; check ctx y a; check e (Eq(x,y)); *)
(*   match  *)

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

let%test_unit "type inference : Nat" =
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

let%test_unit "type inference : Eq2" =
  let ctx =
    [
      ( "psucc",
        ( Pi ("x", Nat, Pi ("y", Nat, Pi ("e", Eq (Var "x", Var "y"), Type))),
          Some
            (Abs
               ( "x",
                 Nat,
                 Abs
                   ( "y",
                     Nat,
                     Abs
                       ( "e",
                         Eq (Var "x", Var "y"),
                         Eq (S (Var "x"), S (Var "y")) ) ) )) ) );
    ]
  in
  check ctx (Var "psucc")
    (Pi ("x", Nat, Pi ("y", Nat, Pi ("e", Eq (Var "x", Var "y"), Type))))

let%test "α-equivalence : polymorphic identity" =
  let idfun = Abs ("A", Type, Abs ("x", Var "A", Var "x")) in
  let idfun1 = Abs ("B", Type, Abs ("y", Var "B", Var "y")) in
  conv [] idfun idfun1

let%test "αβ-equivalence : (idbool true) -> true" =
  let ctx =
    [
      ("Bool", (Type, None));
      ("true", (Var "Bool", None));
      ("false", (Var "Bool", None));
    ]
  in
  let idbool = Abs ("b", Var "Bool", Var "b") in
  conv ctx (App (idbool, Var "true")) (Var "true")

let%test "α-equivalence : polymorphic identity" =
  let idsimple = Abs ("x", Var "A", Var "x") in
  let iddependent = Abs ("A", Type, idsimple) in
  let ctx = [ ("A", (Type, None)); ("x", (Var "A", None)) ] in

  conv ctx (App (idsimple, Var "x")) (Var "x")
  && conv ctx (App (App (iddependent, Var "A"), Var "x")) (Var "x")

let%test "αβ-equivalence : natural recursor" =
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

let%test "αβ-equivalence : Eq1" =
  let ctx = [ ("A", (Type, None)) ] in
  conv ctx
    (Abs ("x", Type, Eq (Var "x", Var "A")))
    (Abs ("y", Type, Eq (Var "y", Var "A")))

let%test "type inference : Eq2" =
  let ctx =
    [
      ( "psucc",
        ( Pi ("x", Nat, Pi ("y", Nat, Pi ("e", Eq (Var "x", Var "y"), Type))),
          Some
            (Abs
               ( "x",
                 Nat,
                 Abs
                   ( "y",
                     Nat,
                     Abs
                       ( "e",
                         Eq (Var "x", Var "y"),
                         Eq (S (Var "x"), S (Var "y")) ) ) )) ) );
    ]
  in
  conv ctx (Var "psucc")
    (Abs
       ( "x",
         Nat,
         Abs
           ( "y",
             Nat,
             Abs ("e", Eq (Var "x", Var "y"), Eq (S (Var "x"), S (Var "y"))) )
       ))
