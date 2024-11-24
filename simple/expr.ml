type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

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
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * ty * tm * ty * tm
  | Unit
  | Absurd of tm * ty
