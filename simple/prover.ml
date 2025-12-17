let () = Printexc.record_backtrace true
let log = false
let debug = false && log

open Expr
module Expr = Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

type context = (string * ty) list

let string_of_context ctx =
  List.map (fun (x, a) -> x ^ ": " ^ string_of_ty a) ctx |> String.concat ", "

let log_ctx ctx = if debug then print_endline ("𝚪=" ^ string_of_context ctx)

exception Type_error

let rec infer_type ?(ctx : context = []) = function
  | Var x -> ( try List.assoc x ctx with Not_found -> raise Type_error)
  | App (t, u) -> (
      match infer_type ~ctx t with
      | Imp (a, b) ->
          check_type ~ctx u a;
          b
      | _ ->
          log_ctx ctx;
          raise Type_error)
  | Fn (x, a, t) -> Imp (a, infer_type ~ctx:((x, a) :: ctx) t)
  | Pair (t, u) -> And (infer_type ~ctx t, infer_type ~ctx u)
  | Fst t -> (
      match infer_type ~ctx t with And (a, _) -> a | _ -> raise Type_error)
  | Snd t -> (
      match infer_type ~ctx t with And (_, b) -> b | _ -> raise Type_error)
  | Unit -> True
  | Case (t, u, v) -> (
      match (infer_type ~ctx t, infer_type ~ctx u, infer_type ~ctx v) with
      | Or (a, b), Imp (a', u), Imp (b', v) when a = a' && b = b' && u = v -> u
      | _ -> raise Type_error)
  | Left (t, b) -> Or (infer_type ~ctx t, b)
  | Right (a, t) -> Or (a, infer_type ~ctx t)
  | Empty (t, a) ->
      check_type ~ctx t False;
      a
  | Zero -> Nat
  | Succ n ->
      check_type ~ctx n Nat;
      Nat
  | Rec (sn, init, Fn (n, Nat, Fn (prev_value, a, t))) ->
      log_ctx ctx;
      check_type ~ctx (Var sn) Nat;
      check_type ~ctx:((n, Nat) :: (prev_value, a) :: ctx) t a;
      check_type ~ctx init a;
      a
  | _ ->
      log_ctx ctx;
      raise Type_error

and check_type ?(ctx : context = []) t a : unit =
  let typ = infer_type ~ctx t in
  if not (typ = a) then (
    log_ctx ctx;
    log_tm t;
    log_ty typ;
    raise Type_error)

let%test_unit "infer" =
  let test =
    Fn
      ( "f",
        Imp (T "A", T "B"),
        Fn
          ( "g",
            Imp (T "B", T "C"),
            Fn ("x", T "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let test_type =
    Imp (Imp (T "A", T "B"), Imp (Imp (T "B", T "C"), Imp (T "A", T "C")))
  in
  log_tm test;
  log_ty (infer_type test);
  log_ty test_type;
  [%test_eq: ty] (infer_type test) test_type

let%test_unit "outside_context" =
  let fail = Fn ("f", T "A", Var "x") in
  try
    log_ty (infer_type fail);
    failwith "This should not be typable"
  with Type_error -> ()

let%test_unit "apply_not_function" =
  let fail = Fn ("f", T "A", Fn ("x", T "B", App (Var "f", Var "x"))) in
  try
    log_ty (infer_type fail);
    failwith "This should not be typable"
  with Type_error -> ()

let%test_unit "mistyped_argument" =
  let fail =
    Fn ("f", Imp (T "A", T "B"), Fn ("x", T "B", App (Var "f", Var "x")))
  in
  try
    log_ty (infer_type fail);
    failwith "This should not be typable"
  with Type_error -> ()

let%test_unit "check" =
  let test_check = Fn ("x", T "A", Var "x") in
  let test_check_type = Imp (T "A", T "A") in
  check_type test_check test_check_type;

  let fail_check_type = Imp (T "B", T "B") in
  try
    check_type test_check fail_check_type;
    failwith "󰘧x:A.x should not have type B -> B"
  with Type_error -> ()

let%test_unit "no_type" =
  try
    check_type (Var "x") (T "A");
    failwith "x should not be typed, and not have type A"
  with Type_error -> ()

let%test_unit "and_comm" =
  let and_comm =
    Fn ("p", And (T "A", T "B"), Pair (Snd (Var "p"), Fst (Var "p")))
  in
  let and_comm_type = Imp (And (T "A", T "B"), And (T "B", T "A")) in
  log_ty (infer_type and_comm);
  check_type and_comm and_comm_type

let%test_unit "top_ex" =
  let top_ex = Fn ("f", Imp (True, T "A"), App (Var "f", Unit)) in
  let top_ex_type = Imp (Imp (True, T "A"), T "A") in
  log_ty (infer_type top_ex);
  check_type top_ex top_ex_type

let%test_unit "disj_comm" =
  let disj_comm =
    Fn
      ( "p",
        Or (T "A", T "B"),
        Case
          ( Var "p",
            Fn ("x", T "A", Right (T "B", Var "x")),
            Fn ("y", T "B", Left (Var "y", T "A")) ) )
  in
  let disj_comm_type = Imp (Or (T "A", T "B"), Or (T "B", T "A")) in
  log_ty (infer_type disj_comm);
  check_type disj_comm disj_comm_type

let%test_unit "incoh_elim" =
  let incoh_elim =
    Fn
      ( "p",
        And (T "A", Imp (T "A", False)),
        Empty (App (Snd (Var "p"), Fst (Var "p")), T "B") )
  in
  let incoh_elim_type = Imp (And (T "A", Imp (T "A", False)), T "B") in
  log_ty (infer_type incoh_elim);
  check_type incoh_elim incoh_elim_type

let%test_unit "Parsing types" =
  let l =
    [
      "A => B";
      "A ⇒ B";
      "A /\\ B";
      "A ∧ B";
      "T";
      "A \\/ B";
      "A ∨ B";
      "_";
      "not A";
      "¬ A";
    ]
  in
  if log then
    List.iter
      (fun s ->
        Printf.printf "the parsing of %S is %s\n%!" s
          (string_of_ty (ty_of_string s)))
      l

let%test_unit "Parsing terms" =
  let l =
    [
      "t u v";
      "fun (x : A) -> t";
      "λ (x : A) → t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of fun(x:A) -> u | fun(y:B) -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  if log then
    List.iter
      (fun s ->
        Printf.printf "the parsing of %S is %s\n%!" s
          (string_of_tm (tm_of_string s)))
      l

type sequent = context * ty

let string_of_sequent (seq : sequent) =
  let ctx, a = seq in
  string_of_context ctx ^ " ⊢ " ^ string_of_ty a

let log_seq seq = if log then print_endline (string_of_sequent seq)

let%test_unit "Recursor typing" =
  let idn = Rec ("x", Zero, Fn ("x1", Nat, Fn ("vx1", Nat, Var "vx1"))) in
  let ctx = [ ("x", Nat) ] in
  log_ty (infer_type ~ctx idn);
  check_type ~ctx idn Nat

let%test_unit "Parsing natural constructors" =
  let typ = [ "Nat"; "ℕ" ] in
  List.iter log_ty (List.map ty_of_string typ);

  let tms =
    [
      "Zero";
      "zero";
      "succ(Zero)";
      "rec(x,Zero,Zero)";
      "rec(x,Zero,(fun(x:Nat)->(fun(y:Nat) -> (x y))))";
    ]
  in
  List.iter log_tm (List.map tm_of_string tms)

let%test_unit "Parsing add" =
  let add =
    Fn
      ( "x",
        Nat,
        Fn
          ( "y",
            Nat,
            Rec
              ( "y",
                Var "x",
                Fn ("ym1", Nat, Fn ("xpym1", Nat, Succ (Var "xpym1"))) ) ) )
  in
  log_tm add;
  log_ty (infer_type add);
  check_type (App (App (add, Zero), Zero)) Nat
