open Expr

let debug = false
let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty ty =
  match ty with
  | TVar v -> v
  | Imp (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"
  | And (t1, t2) -> "(" ^ string_of_ty t1 ^ " /\\ " ^ string_of_ty t2 ^ ")"
  | Or (t1, t2) -> "(" ^ string_of_ty t1 ^ " \\/ " ^ string_of_ty t2 ^ ")"
  | True -> "\u{22a4}"
  | False -> "\u{22a5}"
  | Nat -> "\u{2115}"

let rec raw_of_ty ty =
  match ty with
  | TVar v -> v
  | Imp (t1, t2) -> "Imp(" ^ raw_of_ty t1 ^ "," ^ raw_of_ty t2 ^ ")"
  | And (t1, t2) -> "And(" ^ raw_of_ty t1 ^ "," ^ raw_of_ty t2 ^ ")"
  | Or (t1, t2) -> "Or(" ^ raw_of_ty t1 ^ "," ^ raw_of_ty t2 ^ ")"
  | True -> "True"
  | False -> "False"
  | Nat -> "Nat"

let string_of_ctx ctx =
  String.concat ", " (List.map (fun (x, t) -> x ^ " : " ^ string_of_ty t) ctx)

let () =
  if debug then (
    print_endline
      (string_of_ty (Imp (Imp (TVar "A", TVar "B"), Imp (TVar "A", TVar "C"))));
    print_endline (string_of_ty (And (TVar "A", TVar "B")));
    print_endline (string_of_ty True))

let rec string_of_tm tm =
  let extract_parts str =
    let rec index_of_last_number s ?(idx = String.length str) () =
      let is_digit c = c >= '0' && c <= '9' in
      if s = "" || not (is_digit s.[String.length s - 1]) then idx
      else
        let lm1 = String.length s - 1 in
        let s' = String.sub s 0 lm1 in
        index_of_last_number s' ~idx:lm1 ()
    in

    let idx_number = index_of_last_number str () in
    ( String.sub str 0 idx_number,
      String.sub str idx_number (String.length str - idx_number) )
  in

  match tm with
  | Var v -> v
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Abs (x, ty, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm t ^ ")"
  | Pair (t1, t2) ->
      "\u{27e8}" ^ string_of_tm t1 ^ "," ^ string_of_tm t2 ^ "\u{27e9}"
  | Left (t, b) -> "\u{1d704}l" ^ string_of_ty b ^ "(" ^ string_of_tm t ^ ")"
  | Right (a, t) -> "\u{1d704}r" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"
  | Case (t, x, u, y, v) ->
      "case(" ^ string_of_tm t ^ ", " ^ x ^ ", " ^ string_of_tm u ^ ", " ^ y
      ^ ", " ^ string_of_tm v ^ ")"
  | Fst t -> "\u{1D6D1}1(" ^ string_of_tm t ^ ")"
  | Snd t -> "\u{1D6D1}2(" ^ string_of_tm t ^ ")"
  | Unit -> "\u{27e8}\u{27e9}"
  | Absurd (t, a) -> "case" ^ string_of_ty a ^ "(" ^ string_of_tm t ^ ")"
  | Zero -> string_of_int 0
  | Succ x ->
      let prefix, n = extract_parts (string_of_tm x) in
      prefix ^ if n = "" then " + 1" else string_of_int (int_of_string n + 1)
  | Rec (n, init, here) ->
      "rec(" ^ string_of_tm n ^ ", " ^ string_of_tm init ^ ", "
      ^ string_of_tm here ^ ")"

let () =
  if debug then (
    print_endline
      (string_of_tm
         (Abs
            ( "f",
              Imp (TVar "A", TVar "B"),
              Abs ("x", TVar "A", App (Var "f", Var "x")) )));
    print_endline (string_of_tm (Pair (Var "x", Var "y")));
    print_endline (string_of_tm Unit);
    print_endline (string_of_tm Zero);
    print_endline (string_of_tm (Succ Zero));
    print_endline (string_of_tm (Succ (Succ Zero)));
    print_endline
      (string_of_tm
         (Rec
            ( Succ (Succ (Succ Zero)),
              Zero,
              Abs ("x", Nat, Abs ("y", Nat, Succ (Var "y"))) )));
    print_endline
      (string_of_tm
         (Rec
            ( Succ (Succ (Succ Zero)),
              Zero,
              Abs ("x", Nat, Abs ("y", Nat, Succ (Succ (Var "y")))) ))))

type context = (var * ty) list

exception Type_error

let rec infer_type env t =
  if debug then (
    print_string (string_of_tm t);
    print_endline (string_of_ctx env));
  match t with
  | Var x -> (
      try List.assoc x env
      with Not_found ->
        if debug then print_endline ("could not find variable" ^ x);
        raise Type_error)
  | Abs (x, a, t) -> Imp (a, infer_type ((x, a) :: env) t)
  | App (t, u) -> (
      match infer_type env t with
      | Imp (a, b) ->
          check_type env u a;
          b
      | terr ->
          if debug then print_endline (raw_of_ty terr);
          raise Type_error)
  | Pair (t1, t2) -> And (infer_type env t1, infer_type env t2)
  | Left (t, b) -> Or (infer_type env t, b)
  | Right (a, t) -> Or (a, infer_type env t)
  | Case (t, x, u, y, v) -> (
      match infer_type env t with
      | Or (a, b) ->
          let c1, c2 =
            (infer_type ((x, a) :: env) u, infer_type ((y, b) :: env) v)
          in
          if c1 = c2 then c1
          else (
            if debug then (
              print_endline (raw_of_ty c1);
              print_endline (raw_of_ty c2));
            raise Type_error)
      | terr ->
          if debug then print_endline (raw_of_ty terr);
          raise Type_error)
  | Fst t -> (
      match infer_type env t with
      | And (t1, _) -> t1
      | terr ->
          if debug then print_endline (raw_of_ty terr);
          raise Type_error)
  | Snd t -> (
      match infer_type env t with
      | And (_, t2) -> t2
      | terr ->
          if debug then print_endline (raw_of_ty terr);
          raise Type_error)
  | Unit -> True
  | Absurd (t, a) -> (
      match infer_type env t with
      | False -> a
      | terr ->
          if debug then print_endline (raw_of_ty terr);
          raise Type_error)
  | Zero -> Nat
  | Succ n -> if infer_type env n = Nat then Nat else raise Type_error
  | Rec (n, init, here) ->
      let tn = infer_type env n in
      let tinit = infer_type env init in
      if tn = Nat then (
        match here with
        | Abs (x, tx, Abs (y, ty, v)) ->
            let tv = infer_type ((x, tx) :: (y, ty) :: env) v in
            if tx = Nat && tv = ty && tinit = tv then tv
            else (
              if debug then (
                print_endline "tx != Nat or tv != ty";
                print_endline (raw_of_ty tv);
                print_endline (raw_of_ty ty));
              raise Type_error)
        | _ ->
            if debug then (
              print_endline "did not get good form of heredite";
              print_endline (string_of_tm here));
            raise Type_error)
      else (
        if debug then (
          print_endline "did not get tn=Nat or tinit=";
          print_endline (raw_of_ty tn);
          print_endline (raw_of_ty tinit));
        raise Type_error)

and check_type env t a =
  if infer_type env t <> a then (
    print_endline (string_of_ty (infer_type env t) ^ " " ^ string_of_ty a);
    raise Type_error)

let () =
  assert (
    infer_type []
      (Abs
         ( "f",
           Imp (TVar "A", TVar "B"),
           Abs
             ( "g",
               Imp (TVar "B", TVar "C"),
               Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) ))
    = Imp
        ( Imp (TVar "A", TVar "B"),
          Imp (Imp (TVar "B", TVar "C"), Imp (TVar "A", TVar "C")) ));
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
             Imp (TVar "A", TVar "B"),
             Abs ("x", TVar "B", App (Var "f", Var "x")) ))
      = TVar "s"
    with
    | Type_error -> true
    | _ -> false);
  assert (
    try
      infer_type
        [ ("t", Nat); ("v", TVar "A"); ("u", TVar "A") ]
        (Rec (Var "t", Var "u", Abs ("x", Nat, Abs ("y", TVar "A", Var "v"))))
      = TVar "A"
    with Type_error -> false);
  assert (
    try
      let t =
        infer_type
          [ ("v", TVar "A") ]
          (Abs
             ( "t",
               Nat,
               Abs
                 ( "u",
                   TVar "A",
                   Rec
                     ( Var "t",
                       Var "u",
                       Abs ("x", Nat, Abs ("y", TVar "A", Var "v")) ) ) ))
      in
      if debug then print_endline (string_of_ty t);
      t = Imp (Nat, Imp (TVar "A", TVar "A"))
    with Type_error ->
      print_endline "échec mission";
      false)
(*print_endline*)
(*  (string_of_ty*)
(*     (infer_type []*)
(*        (tm_of_string*)
(* "fun (n : Nat) -> (fun (m : Nat) -> rec(m, n, (fun (x : Nat) -> \*)
   (*            (fun (y : Nat) -> suc ( y )))))")))*)

let () =
  if debug then (
    let and_comm =
      Abs ("t", And (TVar "A", TVar "B"), Pair (Snd (Var "t"), Fst (Var "t")))
    in
    print_endline (string_of_tm and_comm);
    print_endline (string_of_ty (infer_type [] and_comm)))

let () =
  if debug then (
    let or_comm =
      Abs
        ( "t",
          Or (TVar "A", TVar "B"),
          Case
            ( Var "t",
              "x",
              Right (TVar "B", Var "x"),
              "y",
              Left (Var "y", TVar "A") ) )
    in
    print_endline (string_of_tm or_comm);
    print_endline (string_of_ty (infer_type [] or_comm)))

let () =
  if debug then (
    let truth = Abs ("f", Imp (True, TVar "A"), App (Var "f", Unit)) in
    print_endline (string_of_tm truth);
    print_endline (string_of_ty (infer_type [] truth)))

let () =
  if debug then (
    let fals =
      Abs
        ( "t",
          And (TVar "A", Imp (TVar "A", False)),
          Absurd (App (Snd (Var "t"), Fst (Var "t")), TVar "B") )
    in
    print_endline (string_of_tm fals);
    print_endline (string_of_ty (infer_type [] fals)))

let () =
  if debug then
    let l =
      [
        "A => B";
        (*"A ⇒ B"; OCaml LSP does not like unicode characters very much...*)
        "A /\\ B";
        (*"A ∧ B";*)
        "T";
        "A \\/ B";
        (*"A ∨ B";*)
        "_";
        "not A";
        (*"¬ A";*)
      ]
    in
    List.iter
      (fun s ->
        Printf.printf "the parsing of %S is %s\n%!" s
          (string_of_ty (ty_of_string s)))
      l

let () =
  if debug then
    let l =
      [
        "t u v";
        "fun (x : A) -> t";
        (*"λ (x : A) → t";*)
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

let string_of_ctx ctx =
  String.concat ", " (List.map (fun (x, t) -> x ^ " : " ^ string_of_ty t) ctx)

let () =
  if debug then
    let ctx =
      [
        ("x", Imp (TVar "A", TVar "B"));
        ("y", And (TVar "A", TVar "B"));
        ("Z", TVar "T");
      ]
    in
    print_endline (string_of_ctx ctx)

type sequent = context * ty

let string_of_seq (ctx, t) = string_of_ctx ctx ^ " |- " ^ string_of_ty t

let () =
  if debug then
    let seq =
      ([ ("x", Imp (TVar "A", TVar "B")); ("y", TVar "A") ], TVar "B")
    in
    print_endline (string_of_seq seq)

let rec prove env goal commands destination =
  let error e =
    print_endline e;
    prove env goal commands destination
  in

  print_endline (string_of_seq (env, goal));
  print_string "? ";
  flush_all ();
  let cmd, arg =
    let cmd = input_line commands in
    output_string destination (cmd ^ "\n");
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in

  match cmd with
  | "intro" -> (
      match goal with
      | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else if List.exists (fun (x, _) -> x = arg) env then
            error "This variable is already in the environment."
          else
            let x = arg in
            let t = prove ((x, a) :: env) b commands destination in
            Abs (x, a, t)
      | And (a, b) ->
          let x = prove env a commands destination in
          let y = prove env b commands destination in
          Pair (x, y)
      | True -> Unit
      | Nat ->
          if arg = "" then prove (("0", Nat) :: env) goal commands destination
          else if List.exists (fun (x, tx) -> x = arg && tx = Nat) env then
            prove (("suc ( " ^ arg ^ " )", Nat) :: env) Nat commands destination
          else
            error
              "Cannot introduce the successor of a variable that does not \
               exist."
      | _ -> error "Don't know how to introduce this.")
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else if String.contains arg '|' then
        match String.split_on_char '|' arg with
        | [ x; y ] ->
            let t = prove env Nat commands destination in
            let u = prove env goal commands destination in
            let v =
              prove
                ((String.trim x, Nat) :: (String.trim y, goal) :: env)
                goal commands destination
            in
            Rec (t, u, Abs (x, Nat, Abs (y, goal, v)))
        | _ -> error "Please provide exactly two arguments"
      else
        let x, tx = List.find (fun (y, _) -> y = arg) env in
        match tx with
        | Imp (a, b) ->
            if goal = b then
              let u = prove env a commands destination in
              App (Var x, u)
            else
              error
                "The specified function return type does not match the goal."
        | Or (a, b) ->
            let u =
              prove ((arg ^ raw_of_ty a, a) :: env) goal commands destination
            in
            let v =
              prove ((arg ^ raw_of_ty b, b) :: env) goal commands destination
            in
            Case (tm_of_string arg, arg ^ raw_of_ty a, u, arg ^ raw_of_ty b, v)
        | False -> Absurd (Var x, goal)
        (*      | Rec(n,init,here) ->*)
        (*      let t = prove env Nat commands destination in*)
        (*let u = prove env goal commands destination in*)
        (*let Abs(x,tx,Abs(y,ty,res))=here in*)
        (*    if tx <> Nat then error x^" is not in \u{2115}"else*)
        (*let v = prove ((x,tx) :: (y,ty) :: env) goal commands destination in*)
        | _ -> error "Cannot eliminate.")
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else
        let arg = ty_of_string arg in
        let t = prove env (Imp (arg, goal)) commands destination in
        let u = prove env arg commands destination in
        App (t, u)
  | "fst" ->
      if arg = "" then error "Please provide an argument for fst."
      else
        let t = tm_of_string arg in
        let intended = infer_type env (Fst t) in
        if intended <> goal then
          error
            ("Not the correct type.\nType provided : " ^ string_of_ty intended
           ^ " ; Goal : " ^ string_of_ty goal)
        else Fst t
  | "snd" ->
      if arg = "" then error "Please provide an argument for fst."
      else
        let t = tm_of_string arg in
        let intended = infer_type env (Snd t) in
        if intended <> goal then
          error
            ("Not the correct type.\nType provided : " ^ string_of_ty intended
           ^ " ; Goal : " ^ string_of_ty goal)
        else Snd t
  (*| "tintro" ->*)
  (*    if arg = "" then error "Please provide an argument for tintro."*)
  (*    else*)
  (*      let _ = prove ((arg, True) :: env) goal commands destination in*)
  (*      Unit*)
  | "left" -> (
      match goal with
      | Or (a, b) ->
          let t = prove env a commands destination in
          Left (t, b)
      | _ -> error "Cannot introduce this.")
  | "right" -> (
      match goal with
      | Or (a, b) ->
          let t = prove env b commands destination in
          Right (a, t)
      | _ -> error "Cannot introduce this.")
  | "exact" ->
      let t = tm_of_string arg in
      let intended = infer_type env t in
      if intended <> goal then
        error
          ("Not the correct type.\nType provided : " ^ string_of_ty intended
         ^ " ; Goal : " ^ string_of_ty goal)
      else t
  | "type" ->
      if arg = "" then
        error "Please provide the name of the variable you are looking for."
      else
        let t = tm_of_string arg in
        let intended = infer_type env t in
        error
          ("Variable " ^ arg ^ " : " ^ raw_of_ty intended ^ " ; Goal : "
         ^ raw_of_ty goal)
  | "show" -> error (string_of_tm (prove env goal commands destination))
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  let commands, destination =
    print_endline "Would you like to load the proof from a file? [y/n]";
    match input_line stdin with
    | "y" ->
        print_endline
          "Please specify the name of the file that contains the proof:";
        let name = input_line stdin in
        (open_in ("proof/" ^ name ^ ".proof"), stdout)
    | "n" ->
        print_endline
          "Please specify the name of the file that will store the proof:";
        let name = input_line stdin in
        (stdin, open_out ("proof/" ^ name ^ ".proof"))
    | _ -> raise (Invalid_argument "Invalid argument")
  in

  let a =
    if commands = stdin then (
      print_endline "Please enter the formula to prove:";
      let goal = input_line commands in
      output_string destination (goal ^ "\n");
      print_endline goal;
      goal)
    else (
      print_endline "Goal:";
      let goal = input_line commands in
      print_endline goal;
      goal)
  in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a commands destination in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."
