open Sexplib.Std

let compare_string = Stdlib.compare

(** Expressions. *)
type expr =
  | Type
  | Var of string
  | App of expr * expr
  | Abs of string * expr * expr
  | Pi of string * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
(* | Eq of expr * expr *)
(* | Refl of expr *)
(* | J of expr * expr * expr * expr * expr *)
[@@deriving sexp, compare]

let rec to_string = function
  | Type -> "Type"
  | Var x -> x
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, a, t) ->
      "(Λ (" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string t ^ ")"
  | Pi (x, a, b) ->
      "(Π (" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string b ^ ")"
  | Nat -> "ℕ"
  | Z -> "0"
  | S n -> (
      try string_of_int (Option.get (int_of_string_opt (to_string n)) + 1)
      with Invalid_argument _ -> "S (" ^ to_string n ^ ")")
  | Ind (p, base, inductive, n) ->
      "R (" ^ to_string p ^ ", " ^ to_string base ^ ", " ^ to_string inductive
      ^ ", " ^ to_string n ^ ")"

let%expect_test "Serialization of expressions" =
  let exp =
    [
      Type;
      Var "x";
      App (Var "t", Var "u");
      Abs ("a", Var "A", App (Var "b", Var "c"));
      Abs ("x", Var "A", App (Var "B", Var "x"));
      Pi ("A", Type, App (Var "A", Var "x"));
      Abs ("f", Pi ("x", Var "A", App (Var "B", Var "x")), Var "f");
      Nat;
      Z;
      S (S (S Z));
      S (S (S (Var "x")));
      Ind
        ( Var "P",
          App (Var "P", Z),
          Abs ("n", Nat, App (Var "P", Var "n")),
          Var "n" );
    ]
  in
  List.iter (fun x -> print_endline (to_string x)) exp;
  [%expect
    {|
    Type
    x
    (t u)
    (Λ (a : A) -> (b c))
    (Λ (x : A) -> (B x))
    (Π (A : Type) -> (A x))
    (Λ (f : (Π (x : A) -> (B x))) -> f)
    ℕ
    0
    3
    S (S (S (x)))
    R (P, (P 0), (Λ (n : ℕ) -> (P n)), n)
    |}]

let idx = ref 0

let fresh_var () =
  idx := !idx + 1;
  "x" ^ string_of_int !idx

let%expect_test "Fresh variables" =
  print_endline (fresh_var ());
  [%expect {| x1 |}];
  print_endline (fresh_var ());
  [%expect {| x2 |}];
  print_endline (fresh_var ());
  [%expect {| x3 |}]
