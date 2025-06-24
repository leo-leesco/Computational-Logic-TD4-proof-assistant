open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)
let debug = false

let rec to_string ex =
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
  match ex with
  | Type -> "Type"
  | Var v -> v
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, tx, t) ->
      "(fun (" ^ x ^ " : " ^ to_string tx ^ ") -> " ^ to_string t ^ ")"
  | Pi (x, a, b) ->
      "\u{03A0} (" ^ x ^ " : " ^ to_string a ^ ", " ^ to_string b ^ ")"
  | _ -> failwith "TODO"

let () =
  if debug then (
    print_endline "---- Test to_string ----";
    print_endline (to_string (Var "x"));
    print_endline
      (to_string (Abs ("f", Pi ("x", Type, Type), App (Var "f", Var "x")))))

let idx = ref 0

let fresh_var () =
  idx := !idx + 1;
  "x" ^ string_of_int !idx

let () =
  if debug then (
    print_endline "---- Test fresh_var ----";
    print_endline (fresh_var ());
    print_endline (fresh_var ());
    print_endline (fresh_var ());
    print_endline (fresh_var ()))

let rec subst x t u =
  match u with
  | Type -> Type
  | Var v -> if x = v then t else Var v
  | App (f, y) -> App (subst x t f, subst x t y)
  | Abs (y, ty, z) ->
      let y' = fresh_var () in
      Abs (y', subst x t ty, subst x t (subst y (Var y') z))
  | Pi (y, ty, z) ->
      let y' = fresh_var () in
      Pi (y', subst x t ty, subst x t (subst y (Var y') z))
  | _ -> failwith "TODO"

let () =
  let t = App (Var "x", Abs ("y", Type, Var "x")) in
  let i = Abs ("x", Type, Var "x") in
  let ti =
    App (Abs ("x", Type, Var "x"), Abs ("y", Type, Abs ("x", Type, Var "x")))
  in
  if debug then (
    print_endline "---- Test subst ----";
    print_endline (to_string (subst "x" i t));
    print_endline (to_string ti));
  let id = Abs ("A", Type, Abs ("x", Var "A", Var "x")) in
  if debug then (
    print_endline (to_string id);
    print_endline (to_string (subst "A" (Var "Bool") id)))

type context = (var * (expr * expr option)) list

let string_of_context ctx =
  String.concat ", "
    (List.map
       (fun (v, (tv, opt_val)) ->
         v ^ " : " ^ to_string tv
         ^
         match opt_val with Some value -> " = " ^ to_string value | None -> "")
       ctx)

let () =
  if debug then (
    print_endline "---- Test string_of_context ----";
    print_endline (string_of_context [ ("x", (Var "A", None)) ]);
    print_endline (string_of_context [ ("x", (Var "A", Some (Var "t"))) ]))

let rec red ctx t =
  match t with
  | Var x when List.exists (fun (v, _) -> v = x) ctx -> (
      match snd (List.assoc x ctx) with Some y -> Some y | None -> None)
  | App (Abs (x, _, t), u) -> Some (subst x t u)
  | App (e1, e2) -> (
      match red ctx e1 with
      | Some r1 -> Some (App (r1, e2))
      | None -> (
          match red ctx e2 with Some r2 -> Some (App (e1, r2)) | None -> None))
  | Abs (x, tx, e) -> (
      match (red ctx e, red ctx tx) with
      | Some r, Some tx' -> Some (Abs (x, tx', r))
      | Some r, None -> Some (Abs (x, tx, r))
      | None, Some tx' -> Some (Abs (x, tx', e))
      | None, None -> None)
  | Pi (x, tx, e) -> (
      match (red ctx e, red ctx tx) with
      | Some r, Some tx' -> Some (Pi (x, tx', r))
      | Some r, None -> Some (Pi (x, tx, r))
      | None, Some tx' -> Some (Pi (x, tx', e))
      | None, None -> None)
  | _ -> None

let rec normalize ctx t =
  match red ctx t with Some r -> normalize ctx r | None -> t

let () =
  let id = Abs ("x", Type, Var "x") in
  let id2 = App (id, id) in
  let x = Var "x" in
  if debug then (
    print_endline "---- Test beta conversion ----";
    print_endline ("id : " ^ to_string id);
    print_endline ("id2 : " ^ to_string (normalize [] id2));
    print_endline (to_string (normalize [] x)));
  let id = Abs ("A", Type, Abs ("x", Var "A", Var "x")) in
  if debug then (
    print_endline (to_string id);
    print_endline
      (to_string
         (normalize
            [ ("Bool", (Type, None)) ]
            (App
               (App (id, Pi ("_", Var "Bool", Var "Bool")), App (id, Var "Bool"))))))

let eq ctx t1 t2 = normalize ctx t1 = normalize ctx t2

let rec alpha t1 t2 =
  match (t1, t2) with
  | Type, Type -> true
  | Var v, Var w -> v = w
  | App (e1, e2), App (f1, f2) -> alpha e1 f1 && alpha e2 f2
  | Abs (v, tv, e), Abs (w, tw, f) ->
      (if v = w then alpha e f else alpha e (subst w (Var v) f)) && alpha tv tw
  | Pi (v, tv, e), Pi (w, tw, f) ->
      (if v = w then alpha e f else alpha e (subst w (Var v) f)) && alpha tv tw
  | _ -> false

let () =
  let id = Abs ("x", Type, Var "x") in
  let id' = Abs ("y", Type, Var "y") in
  let id2 = App (id, id) in
  let x = Var "x" in
  let x' = Var "x" in
  let y = Var "y" in
  if debug then print_endline "---- Test alpha conversion ----";
  assert (alpha id id');
  assert (alpha id (normalize [] id2));
  assert (alpha x x');
  assert (not (alpha x y))

let conv t1 t2 = alpha (normalize [] t1) (normalize [] t2)

let () =
  let id = Abs ("x", Type, Var "x") in
  let id' = Abs ("y", Type, Var "y") in
  let id2 = App (id, id) in
  if debug then print_endline "---- Test alpha/beta conversion ----";
  assert (conv id id');
  assert (conv id id2);
  assert (conv Type Type)

exception Type_error of string

let rec infer env t =
  if debug then print_endline (to_string t ^ " [" ^ string_of_context env ^ "]");
  match t with
  | Type -> Type
  | Var x -> (
      try fst (List.assoc x env)
      with Not_found ->
        raise (Type_error ("Variable " ^ x ^ " is not in the context")))
  | Abs (x, a, t) ->
      let a = normalize env a in
      Pi (x, a, infer ((x, (a, None)) :: env) t)
  | App (t, u) -> (
      let t = infer env t in
      match t with
      | Pi (x, a, b) ->
          check env u a;
          subst x u b
      | _ ->
          raise
            (Type_error ("First argument is not a function : " ^ to_string t)))
  | Pi (_, _, _) -> Type
  | _ -> failwith "TODO"

and check env t a =
  let t = infer env t in
  if not (conv t a) then
    raise
      (Type_error
         ("Not \u{03b1}\u{03b2}-convertible : " ^ to_string t ^ " != "
        ^ to_string a))

let () =
  let id = Abs ("x", Type, Var "x") in
  if debug then (
    print_endline "---- Test infer_type ----";
    (*print_string (to_string id ^ " : ");*)
    print_endline "\u{2228}\u{2228}\u{2228}\u{2228}";
    print_endline (to_string (infer [] id));
    print_endline "^^^^";
    print_endline "\u{2228}\u{2228}\u{2228}\u{2228}";
    print_endline
      (to_string (infer [ ("y", (Var "A", None)) ] (Abs ("x", Type, Var "y"))));
    print_endline "^^^^";
    print_endline "\u{2228}\u{2228}\u{2228}\u{2228}";
    print_endline
      (to_string
         (infer [ ("Bool", (Type, None)) ] (Abs ("b", Var "Bool", Var "b"))));
    print_endline "^^^^")

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      ( String.trim (String.sub s 0 n),
        String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
    with Not_found -> (s, "")
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd ^ "\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          print_endline (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
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
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: " ^ cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: " ^ err ^ ".")
    | Type_error err -> print_endline ("Typing error :" ^ err ^ ".")
    | Parsing.Parse_error -> print_endline "Parsing error."
  done;
  print_endline "Bye."
