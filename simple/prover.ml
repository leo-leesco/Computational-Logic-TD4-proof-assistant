let () = Printexc.record_backtrace true
let debug = false

type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. *)
type ty =
  | T of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False

type tm =
  | Var of var
  | App of tm * tm
  | Fn of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Case of tm * tm * tm
  | Left of tm
  | Right of tm
  | Unit
  | Empty of tm

let rec string_of_ty = function
  | T a -> a
  | Imp (a, b) -> "(" ^ string_of_ty a ^ " => " ^ string_of_ty b ^ ")"
  | And (a, b) -> "(" ^ string_of_ty a ^ " ∧ " ^ string_of_ty b ^ ")"
  | Or (a, b) -> "(" ^ string_of_ty a ^ " ∨ " ^ string_of_ty b ^ ")"
  | True -> "⊤"
  | False -> "⊥"

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
  | Left t -> "𝛊₁(" ^ string_of_tm t ^ ")"
  | Right t -> "𝛊₂(" ^ string_of_tm t ^ ")"
  | Unit -> "⟨⟩"
  | Empty t -> "case(" ^ string_of_tm t ^ ")"

let () =
  let test_ty = Imp (Imp (T "A", T "B"), Imp (T "A", T "D")) in
  if debug then print_endline (string_of_ty test_ty);

  let test_tm =
    Fn ("f", Imp (T "A", T "B"), Fn ("x", T "A", App (Var "f", Var "x")))
  in
  if debug then print_endline (string_of_tm test_tm)

type context = (var * ty) list

let string_of_context ctx =
  List.map (fun (x, a) -> x ^ ": " ^ string_of_ty a) ctx |> String.concat ", "

exception Type_error

let rec infer_type ?(ctx : context = []) = function
  | Var x -> ( try List.assoc x ctx with Not_found -> raise Type_error)
  | App (t, u) -> (
      if debug then print_endline ("𝚪=" ^ string_of_context ctx);
      match infer_type ~ctx t with
      | Imp (a, b) ->
          check_type ~ctx u a;
          b
      | _ -> raise Type_error)
  | Fn (x, a, t) -> Imp (a, infer_type ~ctx:((x, a) :: ctx) t)
  | Fst t -> (
      match infer_type ~ctx t with And (a, b) -> a | _ -> raise Type_error)
  | Snd t -> (
      match infer_type ~ctx t with And (a, b) -> b | _ -> raise Type_error)
  | Pair (t, u) -> And (infer_type ~ctx t, infer_type ~ctx u)
  | Unit -> True
  | Case (t, u, v) -> failwith "TODO"

and check_type ?(ctx : context = []) t a : unit =
  if not (infer_type ~ctx t = a) then raise Type_error

let () =
  let test_infer =
    Fn
      ( "f",
        Imp (T "A", T "B"),
        Fn
          ( "g",
            Imp (T "B", T "C"),
            Fn ("x", T "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let test_infer_type =
    Imp (Imp (T "A", T "B"), Imp (Imp (T "B", T "C"), Imp (T "A", T "C")))
  in
  if debug then (
    print_endline (string_of_tm test_infer);
    print_endline (string_of_ty (infer_type test_infer));
    print_endline (string_of_ty test_infer_type));
  assert (infer_type test_infer = test_infer_type);

  let fail_outside_ctx = Fn ("f", T "A", Var "x") in
  (try
     print_endline (string_of_ty (infer_type fail_outside_ctx));
     failwith "This should not be typable"
   with Type_error -> ());

  let fail_apply_not_function =
    Fn ("f", T "A", Fn ("x", T "B", App (Var "f", Var "x")))
  in
  (try
     print_endline (string_of_ty (infer_type fail_apply_not_function));
     failwith "This should not be typable"
   with Type_error -> ());

  let fail_mistyped_argument =
    Fn ("f", Imp (T "A", T "B"), Fn ("x", T "B", App (Var "f", Var "x")))
  in
  try
    print_endline (string_of_ty (infer_type fail_mistyped_argument));
    failwith "This should not be typable"
  with Type_error -> ()

let () =
  let test_check = Fn ("x", T "A", Var "x") in
  let test_check_type = Imp (T "A", T "A") in
  check_type test_check test_check_type;

  let fail_check_type = Imp (T "B", T "B") in
  (try
     check_type test_check fail_check_type;
     failwith "󰘧x:A.x should not have type B -> B"
   with Type_error -> ());

  try
    check_type (Var "x") (T "A");
    failwith "x should not be typed, and not have type A"
  with Type_error -> ()
