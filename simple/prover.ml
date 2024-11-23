open Expr

let ty_of_string s = Parser.typ Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.term Lexer.token (Lexing.from_string s)

let rec string_of_ty ty =
  match ty with
  | TVar v -> v
  | Map (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"
  | Conj (t1, t2) -> "(" ^ string_of_ty t1 ^ " /\\ " ^ string_of_ty t2 ^ ")"
  | Disj (t1, t2) -> "(" ^ string_of_ty t1 ^ " \\/ " ^ string_of_ty t2 ^ ")"
  | True -> "\u{22a4}"
  | Empty -> "\u{22a5}"

let () =
  print_endline
    (string_of_ty (Map (Map (TVar "A", TVar "B"), Map (TVar "A", TVar "C"))));
  print_endline (string_of_ty (Conj (TVar "A", TVar "B")));
  print_endline (string_of_ty True)

let rec string_of_tm tm =
  match tm with
  | Var v -> v
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Abs (x, ty, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (t1, t2) ->
      "\u{27e8}" ^ string_of_tm t1 ^ "," ^ string_of_tm t2 ^ "\u{27e9}"
  | VarL (t, b) -> "\u{1d704}l" ^ string_of_ty b ^ "(" ^ string_of_tm t ^ ")"
  | VarR (t, a) -> "\u{1d704}r" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"
  | Case (t, u, v) ->
      "case(" ^ string_of_tm t ^ " , " ^ string_of_tm u ^ " , " ^ string_of_tm v
      ^ ")"
  | Fst t -> "\u{1D6D1}1(" ^ string_of_tm t ^ ")"
  | Snd t -> "\u{1D6D1}2(" ^ string_of_tm t ^ ")"
  | Unit -> "\u{27e8}\u{27e9}"
  | EmptyCase (t, a) -> "case" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"

let () =
  print_endline
    (string_of_tm
       (Abs
          ( "f",
            Map (TVar "A", TVar "B"),
            Abs ("x", TVar "A", App (Var "f", Var "x")) )));
  print_endline (string_of_tm (Pair (Var "x", Var "y")));
  print_endline (string_of_tm Unit)

type context = (var * typ) list

exception Type_error

let rec infer_type env t =
  match t with
  | Var x -> ( try List.assoc x env with Not_found -> raise Type_error)
  | Abs (x, a, t) -> Map (a, infer_type ((x, a) :: env) t)
  | App (t, u) -> (
      match infer_type env t with
      | Map (a, b) ->
          check_type env u a;
          b
      | _ -> raise Type_error)
  | Pair (t1, t2) -> Conj (infer_type env t1, infer_type env t2)
  | VarL (t, b) -> Disj (infer_type env t, b)
  | VarR (t, a) -> Disj (a, infer_type env t)
  | Case (t, u, v) -> (
      match (infer_type env t, infer_type env u, infer_type env v) with
      | Disj (a, b), Map (a', c1), Map (b', c2) when a = a' && b = b' && c1 = c2
        ->
          c1
      | _ -> raise Type_error)
  | Fst t -> (
      match infer_type env t with Conj (t1, _) -> t1 | _ -> raise Type_error)
  | Snd t -> (
      match infer_type env t with Conj (_, t2) -> t2 | _ -> raise Type_error)
  | Unit -> True
  | EmptyCase (t, a) -> (
      match infer_type env t with Empty -> a | _ -> raise Type_error)

and check_type env t a = if infer_type env t <> a then raise Type_error

let () =
  assert (
    infer_type []
      (Abs
         ( "f",
           Map (TVar "A", TVar "B"),
           Abs
             ( "g",
               Map (TVar "B", TVar "C"),
               Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) ))
    = Map
        ( Map (TVar "A", TVar "B"),
          Map (Map (TVar "B", TVar "C"), Map (TVar "A", TVar "C")) ));
  assert (
    try infer_type [] (Abs ("f", TVar "A", Var "x")) = TVar "s" with
    | Type_error -> true
    | _ -> false);

  assert (
    try
      infer_type []
        (Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))))
      = TVar "s"
    with
    | Type_error -> true
    | _ -> false);
  assert (
    try
      infer_type []
        (Abs
           ( "f",
             Map (TVar "A", TVar "B"),
             Abs ("x", TVar "B", App (Var "f", Var "x")) ))
      = TVar "s"
    with
    | Type_error -> true
    | _ -> false)

let () =
  let and_comm =
    Abs ("t", Conj (TVar "A", TVar "B"), Pair (Snd (Var "t"), Fst (Var "t")))
  in
  print_endline (string_of_tm and_comm);
  print_endline (string_of_ty (infer_type [] and_comm))

let () =
  let or_comm =
    Abs
      ( "c",
        Disj (TVar "A", TVar "B"),
        Case
          ( Var "c",
            Abs ("x", TVar "A", VarR (Var "x", TVar "B")),
            Abs ("y", TVar "B", VarL (Var "y", TVar "A")) ) )
  in
  print_endline (string_of_tm or_comm);
  print_endline (string_of_ty (infer_type [] or_comm))

let () =
  let truth = Abs ("f", Map (True, TVar "A"), App (Var "f", Unit)) in
  print_endline (string_of_tm truth);
  print_endline (string_of_ty (infer_type [] truth))

let () =
  let fals =
    Abs
      ( "t",
        Conj (TVar "A", Map (TVar "A", Empty)),
        EmptyCase (App (Snd (Var "t"), Fst (Var "t")), TVar "B") )
  in
  print_endline (string_of_tm fals);
  print_endline (string_of_ty (infer_type [] fals))

let () =
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
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_ty (ty_of_string s)))
    l

let () =
  let l =
    [
      "t u v";
      "fun (x : A) -> t";
      "λ (x : A) → t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_tm (tm_of_string s)))
    l
