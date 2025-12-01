let () = Printexc.record_backtrace true
let log = false
let debug = false

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

let rec alpha t u =
  if debug then
    print_endline
      ((if log then "𝝰:" else "") ^ to_string t ^ " =? " ^ to_string u);
  match (t, u) with
  | Var x, Var y -> x = y
  | Abs (x, a, t), Abs (y, b, u) | Pi (x, a, t), Pi (y, b, u) ->
      if x = y then alpha a b && alpha t u
      else
        let x' = fresh_var () in
        alpha (subst x (Var x') a) (subst y (Var x') b)
        && alpha (subst x (Var x') t) (subst y (Var x') u)
  | App (t, u), App (t', u') -> alpha t t' && alpha u u'
  | Type, Type -> true
  | _, _ -> false

let%test_unit "subst" =
  [%test_eq: expr] (subst "x" (Var "y") (Var "x")) (Var "y");
  [%test_eq: expr] (subst "x" (Var "y") (Var "z")) (Var "z");

  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("t", Var "A", Var "x")))
    (Abs ("t", Var "A", Var "y"));
  [%test_eq: expr]
    (subst "x" (Var "y") (Abs ("x", Var "A", Var "x")))
    (Abs ("x1", Var "A", Var "x1"))

let%test "var1 𝝰-equiv" = alpha (Var "x") (Var "x")
let%test "var2 𝝰-equiv" = not (alpha (Var "x") (Var "y"))

let%test "abs 𝝰-equiv" =
  alpha (Abs ("y", Var "A", Var "y")) (Abs ("x", Var "A", Var "x"))

let%test "abs 𝝰-equiv" =
  alpha
    (Abs
       ("x", Var "A", App (Var "x", Abs ("x", Var "A", App (Var "x", Var "y")))))
    (Abs
       ("z", Var "A", App (Var "z", Abs ("x", Var "A", App (Var "x", Var "y")))))

let%test "abs 𝝰-equiv" =
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

let%test "subst 𝝰-equiv" =
  alpha
    (subst "x" (Var "y") (Abs ("x", Var "A", Var "x")))
    (Abs ("x", Var "A", Var "x"))

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

let conv ctx t u = alpha (normalize ctx t) (normalize ctx u)

let rec infer ctx = function
  | Type -> Type
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

and check ctx t a =
  let b = infer ctx t in
  if not (conv ctx a b) then
    raise
      (Type_error
         (to_string t ^ " is of type " ^ to_string b ^ ", expected "
        ^ to_string a))

let%test_unit "type inference" =
  let ctx =
    [
      ("Bool", (Type, None));
      ("true", (Var "Bool", None));
      ("false", (Var "Bool", None));
    ]
  in
  check ctx (Var "false") (Var "Bool")

(** tests for 𝝰𝝱-equivalence *)
let ( =? ) = conv []

let%test "𝝰𝝱-equivalence_basic" =
  let idfun = Abs ("A", Type, Abs ("x", Var "A", Var "x")) in
  let idfun1 = Abs ("B", Type, Abs ("y", Var "B", Var "y")) in
  idfun =? idfun1

let%test "𝝰𝝱-equivalence_example" =
  let ctx =
    [
      ("Bool", (Type, None));
      ("true", (Var "Bool", None));
      ("false", (Var "Bool", None));
    ]
  in
  let idbool = Abs ("b", Var "Bool", Var "b") in
  conv ctx (App (idbool, Var "true")) (Var "true")

let%test "𝝰𝝱-equivalence_dependent" =
  let idsimple = Abs ("x", Var "A", Var "x") in
  let iddependent = Abs ("A", Type, idsimple) in
  let ctx = [ ("A", (Type, None)); ("x", (Var "A", None)) ] in

  if debug then (
    print_endline ("reducing: " ^ to_string iddependent);
    print_endline ("context:\r" ^ string_of_context ctx));

  conv ctx (App (idsimple, Var "x")) (Var "x")
  && conv ctx (Var "x") (App (App (iddependent, Var "A"), Var "x"))
