open Sexplib.Std

let compare_string = Stdlib.compare

(** Expressions. *)
type expr =
  | Type
  | Var of string
  | App of expr * expr
  | Abs of string * expr * expr
  | Pi of string * expr * expr
(* | Nat *)
(* | Z *)
(* | S of expr *)
(* | Ind of expr * expr * expr * expr *)
(* | Eq of expr * expr *)
(* | Refl of expr *)
(* | J of expr * expr * expr * expr * expr *)
[@@deriving sexp, compare]

let rec to_string = function
  | Type -> "Type"
  | Var x -> x
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, a, t) -> "󰘧 (" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string t
  | Pi (x, a, b) -> "𝚷 (" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string b

let%expect_test "Serialization of expressions" =
  let exp =
    [
      Type;
      Var "x";
      App (Var "t", Var "u");
      Abs ("a", Var "A", App (Var "b", Var "c"));
      Abs ("x", Var "A", App (Var "B", Var "x"));
    ]
  in
  List.iter (fun x -> print_endline (to_string x)) exp;
  [%expect
    {|
    Type
    x
    (t u)
    󰘧 (a : A) -> (b c)
    󰘧 (x : A) -> (B x)
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
