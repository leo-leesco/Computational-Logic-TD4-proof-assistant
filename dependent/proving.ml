open Dependent_prover
open Expr
open Prover

let env = ref []
let debug = false
let loop = ref true
let print = ref true

let file =
  open_out
    (try Array.get Sys.argv 1 with Invalid_argument _ -> "proofs/interactive")

let split c s =
  try
    let n = String.index s c in
    ( String.trim (String.sub s 0 n),
      String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
  with Not_found -> (s, "")

exception Break

type local_context = (string * expr) list

let to_env = List.map (fun (x, a) -> (x, (a, None)))

let string_of_context ctx =
  List.map (fun (x, a) -> x ^ ": " ^ to_string a) ctx |> String.concat ", "

(** @raise Break *)
let rec prove (ctx : local_context) goal =
  let goal = normalize (to_env ctx) goal in

  let error e =
    print_endline e;
    prove ctx goal
  in

  print_endline (string_of_context ctx ^ " ⊢ " ^ to_string goal);
  print_string "? ";
  flush_all ();

  let cmd, arg =
    let cmd = input_line stdin in
    output_string file (cmd ^ "\n");
    split ' ' cmd
  in

  match cmd with
  | "intro" -> (
      match goal with
      | Pi (x, a, b) ->
          let x = if arg <> "" then arg else x in
          Abs (x, a, prove ((x, a) :: ctx) b)
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      let t = of_string arg in
      if infer (!env @ to_env ctx) t <> goal then error "Not the right type."
      else t
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        let arg, params = split ' ' arg in
        match List.assoc arg ctx with
        | Pi (_x, a, b) ->
            if b <> goal then
              error "This arrow codomain does not match the current goal"
            else App (Var arg, prove ctx a)
        | Nat ->
            (*
                récurrence sur `arg` 
                p : la propriété à montrer est celle par récurrence (qui contient `arg`)
                z : il faut donner la preuve de l'initialisation
              *)
            let p = Abs (arg, Nat, goal) in
            Ind
              ( p,
                prove ctx
                  (print_endline ("Base case on " ^ arg ^ " :");
                   App (p, Z)),
                prove ctx
                  (print_endline ("Induction case on " ^ arg ^ " :");
                   Pi
                     ( arg,
                       Nat,
                       Pi
                         ( (print_endline "name the value of the previous case";
                            let pn = input_line stdin in
                            output_string file (pn ^ "\n");
                            pn),
                           App (p, Var arg),
                           App (p, S (Var arg)) ) )),
                Var arg )
        | Eq (t, u) as etype ->
            (*
               récurrence sur `arg` (c'est-à-dire en supposant que )
               p : la propriété à montrer 
             *)
            let t = normalize (to_env ctx) t in
            let u = normalize (to_env ctx) u in
            let a = infer (to_env ctx) t in
            let a' = infer (to_env ctx) u in
            if not (conv (to_env ctx) a a') then
              error
                ("Trying to eliminate a non-homogeneous equation, between \
                  types " ^ to_string a ^ " and " ^ to_string a')
            else
              let x, y =
                let x, y = split ' ' params in

                ( (if x = "" then (
                     print_endline "name x :";
                     input_line stdin)
                   else x),
                  if y = "" then (
                    print_endline "name y :";
                    input_line stdin)
                  else y )
              in

              let p = Abs (x, a, Abs (y, a, Abs (arg, etype, goal))) in

              let rtype =
                Pi (x, a, App (App (App (p, Var x), Var x), Refl (Var x)))
              in
              J (p, prove ctx rtype, t, u, etype)
        | _ -> error "Don't know how to eliminate this.")
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else (
        print_endline "Please provide a name for your lemma";
        let lemma_name = input_line stdin in
        let subgoal = of_string arg in
        App (prove ctx (Pi (lemma_name, subgoal, goal)), prove ctx subgoal))
  | "context" -> error (string_of_context ctx)
  | "abort" -> raise Break
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
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
      | "context" -> print_endline (Prover.string_of_context !env)
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
            let def = prove [] a in
            if !print then
              print_endline
                (x ^ " defined to " ^ to_string def ^ " of type " ^ to_string a);
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
