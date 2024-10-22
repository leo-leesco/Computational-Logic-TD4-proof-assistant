type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. *)
type ty = TVar of var | Arr of ty * ty

type tm = Var of var | App of tm * tm | Abs of var * ty * tm

let rec string_of_ty ty =
  match ty with
  | TVar v -> v
  | Arr (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"

let rec string_of_tm tm =
  match tm with
  | Var v -> v
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Abs (x, ty, t) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm t ^ ")"

type context = (var * ty) list

exception Type_error

(*let rec infer_type env t =*)
(*  match t with *)
(*    | *)
