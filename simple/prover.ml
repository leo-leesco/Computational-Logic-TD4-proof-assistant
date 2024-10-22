type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. *)
type typ = TVar of var | Arr of typ * typ

type term = Var of var | App of term * term | Abs of var * typ * term

let rec string_of_ty ty =
  match ty with
  | TVar v -> v
  | Arr (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"

let () =
  print_endline
    (string_of_ty (Arr (Arr (TVar "A", TVar "B"), Arr (TVar "A", TVar "C"))))

let rec string_of_tm tm =
  match tm with
  | Var v -> v
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Abs (x, ty, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm t ^ ")"

let () =
  print_endline
    (string_of_tm
       (Abs
          ( "f",
            Arr (TVar "A", TVar "B"),
            Abs ("x", TVar "A", App (Var "f", Var "x")) )))

type context = (var * typ) list

exception Type_error

let rec infer_type env t =
  match t with
  | Var x -> ( try List.assoc x env with Not_found -> raise Type_error)
  | Abs (x, a, t) -> Arr (a, infer_type ((x, a) :: env) t)
  | App (t, u) -> (
      match infer_type env t with
      | Arr (a, b) ->
          check_type env u a;
          b
      | _ -> raise Type_error)

and check_type env t a = if infer_type env t <> a then raise Type_error

let () =
  assert (
    infer_type []
      (Abs
         ( "f",
           Arr (TVar "A", TVar "B"),
           Abs
             ( "g",
               Arr (TVar "B", TVar "C"),
               Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) ))
    = Arr
        ( Arr (TVar "A", TVar "B"),
          Arr (Arr (TVar "B", TVar "C"), Arr (TVar "A", TVar "C")) ));
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
             Arr (TVar "A", TVar "B"),
             Abs ("x", TVar "B", App (Var "f", Var "x")) ))
      = TVar "s"
    with
    | Type_error -> true
    | _ -> false)
