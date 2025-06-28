open Prover
open Expr

let commands = ref []

let rec prove ctx goal =
  print_endline (string_of_sequent (ctx, goal));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove ctx goal
  in
  let cmd, arg =
    let cmd = input_line stdin in
    commands := cmd :: !commands;
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
          else
            let x = arg in
            let t = prove ((x, a) :: ctx) b in
            Fn (x, a, t)
      | And (a, b) -> Pair (prove ctx a, prove ctx b)
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      if goal = True then Unit
      else
        let t = tm_of_string arg in
        if infer_type ~ctx t <> goal then error "Not the right type." else t
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        match List.assoc arg ctx with
        | Imp (a, b) ->
            if b <> goal then
              error "This arrow codomain does not match the current goal"
            else
              let t = Var arg in
              let u = prove ctx a in
              App (t, u)
        | Or (a, b) ->
            (* print_endline "Provide two new identifiers for the subcases"; *)
            (* let x = input_line stdin in *)
            (* let y = input_line stdin in *)
            Case
              ( Var arg,
                Fn (arg, a, prove ((arg, a) :: ctx) goal),
                Fn (arg, b, prove ((arg, b) :: ctx) goal) )
        | False -> Empty (Var arg, goal)
        | _ -> error "Don't know how to eliminate this.")
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else
        let subgoal = ty_of_string arg in
        App (prove ctx (Imp (subgoal, goal)), prove ctx subgoal)
  | "fst" -> (
      if arg = "" then error "Please provide an argument for fst."
      else
        match List.assoc arg ctx with
        | And (a, _) when a = goal -> Fst (Var arg)
        | _ -> error "This identifier is not a conjunction in the context.")
  | "snd" -> (
      if arg = "" then error "Please provide an argument for snd."
      else
        match List.assoc arg ctx with
        | And (_, b) when b = goal -> Snd (Var arg)
        | _ -> error "This identifier is not a conjunction in the context.")
  | "left" -> (
      match goal with
      | Or (a, b) -> Left (prove ctx a, b)
      | _ -> error "The goal is not a disjunction.")
  | "right" -> (
      match goal with
      | Or (a, b) -> Right (a, prove ctx b)
      | _ -> error "The goal is not a disjunction.")
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  commands := a :: !commands;
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type t = a);
  print_endline "ok.";
  print_endline "Commands :";
  print_endline (String.concat "\n" (List.rev !commands))
