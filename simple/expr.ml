type tvar = string
type var = string

(** Types. *)
type ty =
  | TVar of var
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | VarL of tm * ty
  | VarR of tm * ty
  | Case of tm * tm * tm
  | Unit
  | EmptyCase of tm * ty
