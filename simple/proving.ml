open Prover
open Expr

let rec prove ctx a =
  print_endline (string_of_sequent (ctx, a));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove ctx a
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
      match a with
      | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else
            let x = arg in
            let t = prove ((x, a) :: ctx) b in
            Fn (x, a, t)
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      let t = tm_of_string arg in
      if infer_type ~ctx t <> a then error "Not the right type." else t
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type t = a);
  print_endline "ok."
