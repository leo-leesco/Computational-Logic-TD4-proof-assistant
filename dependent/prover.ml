type var = string
(** Variables. *)

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string ex =
  match ex with
  | Type -> "Type"
  | Var v -> v
  | App (t, u) -> "(" ^ to_string t ^ " " ^ to_string u ^ ")"
  | Abs (x, tx, t) ->
      "(fun (" ^ x ^ " : " ^ to_string tx ^ ") -> " ^ to_string t ^ ")"
  | Pi (x, a, b) ->
      "\u{03A0} (" ^ x ^ " : " ^ to_string a ^ ", " ^ to_string b ^ ")"
  | _ -> raise (Invalid_argument "Not implemented")

let idx = ref 0

let fresh_var () =
  idx := !idx + 1;
  "x" ^ string_of_int !idx

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
  | _ -> raise (Invalid_argument "Not implemented")

type context = (var * (expr * expr option)) list

let string_of_context ctx =
  String.concat ", "
    (List.map
       (fun (v, (tv, opt_val)) ->
         v ^ " : " ^ to_string tv
         ^ match opt_val with Some value -> to_string value | None -> "")
       ctx)
