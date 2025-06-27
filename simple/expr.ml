open Sexplib.Std

let compare_string = Stdlib.compare
let log = true
let debug = false && log

(** Types. *)
type ty =
  | T of string
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
[@@deriving sexp, compare]

type tm =
  | Var of string
  | App of tm * tm
  | Fn of string * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Case of tm * tm * tm
  | Left of tm * ty
  | Right of ty * tm
  | Unit
  | Empty of tm * ty
[@@deriving sexp, compare]

let rec string_of_ty = function
  | T a -> a
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " => " ^ string_of_ty b ^ ")"
  | And (a, b) -> "(" ^ string_of_ty a ^ " ∧ " ^ string_of_ty b ^ ")"
  | Or (a, b) -> "(" ^ string_of_ty a ^ " ∨ " ^ string_of_ty b ^ ")"
  | True -> "⊤"
  | False -> "⊥"

let log_ty a = if log then print_endline (string_of_ty a)

let rec string_of_tm = function
  | Var x -> x
  | App (t, u) -> "(" ^ string_of_tm t ^ " " ^ string_of_tm u ^ ")"
  | Fn (x, a, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty a ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (t, u) -> "⟨" ^ string_of_tm t ^ ", " ^ string_of_tm u ^ "⟩"
  | Fst t -> "𝛑₁(" ^ string_of_tm t ^ ")"
  | Snd t -> "𝛑₂(" ^ string_of_tm t ^ ")"
  | Case (t, u, v) ->
      "case(" ^ string_of_tm t ^ " ? " ^ string_of_tm u ^ " : " ^ string_of_tm v
      ^ ")"
  | Left (t, b) -> "𝛊₁" ^ string_of_ty b ^ "(" ^ string_of_tm t ^ ")"
  | Right (a, t) -> "𝛊₂" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"
  | Unit -> "⟨⟩"
  | Empty (t, a) -> "case" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"

let log_tm t = if log then print_endline (string_of_tm t)

let () =
  let test_ty = Imp (Imp (T "A", T "B"), Imp (T "A", T "D")) in
  log_ty test_ty;

  let test_tm =
    Fn ("f", Imp (T "A", T "B"), Fn ("x", T "A", App (Var "f", Var "x")))
  in
  log_tm test_tm
