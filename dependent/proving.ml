open Dependent_prover
open Expr
open Prover

let debug = false
let loop = ref true
let print = ref true

let split c s =
  try
    let n = String.index s c in
    ( String.trim (String.sub s 0 n),
      String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
  with Not_found -> (s, "")

exception Break

(** @raise Break *)
let rec prove ctx goal =
  print_endline ("⊢ " ^ to_string goal);
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove ctx goal
  in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in
  match cmd with
  | "intro" -> (
      match goal with
      | Pi (x, a, b) ->
          let t = prove ((x, (a, None)) :: ctx) b in
          Abs (x, a, t)
      | Nat ->
          if arg = "" then error "Please provide an argument for intro."
          else S (prove ((arg, (Nat, None)) :: ctx) Nat)
      | _ -> error "Don't know how to introduce this.")
  | "exact" -> (
      match goal with
      | Nat when arg = "" -> Z
      | _ ->
          let t = of_string arg in
          if infer ctx t <> goal then error "Not the right type." else t)
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        match fst (List.assoc arg ctx) with
        | Pi (_x, a, b) ->
            if b <> goal then
              error "This arrow codomain does not match the current goal"
            else
              let u = prove ctx a in
              App (Var arg, u)
        | Nat ->
            print_endline "name the predicate p : Π(n : Nat) -> Type\n";
            let pname = input_line stdin in
            let ptype = Pi (arg, Nat, Type) in
            let p = prove ctx ptype in
            let ctxp = (pname, (ptype, Some p)) :: ctx in
            Ind
              ( p,
                prove ctxp (App (p, Z)),
                prove ctxp
                  (Pi
                     ( arg,
                       Nat,
                       Pi
                         ( (print_endline "name the value of the previous case";
                            input_line stdin),
                           App (p, Var arg),
                           App (p, S (Var arg)) ) )),
                Var arg )
        | Eq (t, u) ->
            let a = infer ctx t in
            let a' = infer ctx u in
            if not (conv ctx a a') then
              error
                ("Trying to eliminate a non-homogeneous equation, between \
                  types " ^ to_string a ^ " and " ^ to_string a')
            else (
              print_endline
                "name the predicate p : Π(x y : A, e : x = y) -> Type\n";
              let pname = input_line stdin in
              print_endline "name x : ";
              let xname = input_line stdin in
              print_endline "name y : ";
              let yname = input_line stdin in
              let ptype =
                Pi
                  ( xname,
                    a,
                    Pi (yname, a', Pi (arg, Eq (Var xname, Var yname), Type)) )
              in
              let p = prove ctx ptype in
              let ctxp = (pname, (ptype, Some p)) :: ctx in
              let rtype =
                Pi
                  ( xname,
                    a,
                    App (App (App (p, Var xname), Var xname), Refl (Var xname))
                  )
              in
              J (p, prove ctxp rtype, t, u, prove ctx (Eq (t, u))))
        | _ -> error "Don't know how to eliminate this.")
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else (
        print_endline "Please provide a name for your lemma";
        let lemma_name = input_line stdin in
        let subgoal = of_string arg in
        App (prove ctx (Pi (lemma_name, subgoal, goal)), prove ctx subgoal))
  | "abort" -> raise Break
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  let env = ref [] in

  let file =
    open_out
      (try Array.get Sys.argv 1
       with Invalid_argument _ -> "proofs/interactive")
  in
  while !loop do
    try
      if !print then print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd ^ "\n");
        if debug then print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          if !print then print_endline (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
          if !print then
            print_endline
              (x ^ " defined to " ^ to_string t ^ " of type " ^ to_string a)
      | "context" -> print_endline (string_of_context !env)
      | "type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_endline (to_string t ^ " is of type " ^ to_string a)
      | "check" ->
          let t, a = split '=' arg in
          let t = of_string t in
          let a = of_string a in
          check !env t a;
          print_endline "Ok."
      | "eval" ->
          let t = of_string arg in
          let _ = infer !env t in
          print_endline (to_string (normalize !env t))
      | "prove" -> (
          let x, sa = split '=' arg in
          let a = of_string sa in
          try
            let def = prove !env a in
            check !env def a;
            env := (x, (a, Some def)) :: !env
          with Break -> ())
      | "hide" -> print := false
      | "show" -> print := true
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: " ^ cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> if !print then print_endline ("Error: " ^ err ^ ".")
    | Type_error err ->
        if !print then print_endline ("Typing error :" ^ err ^ ".")
    | Parsing.Parse_error -> print_endline "Parsing error."
  done;
  print_endline "Bye."
