type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** Types. *)
type typ =
  | TVar of var
  | Map of typ * typ
  | Conj of typ * typ
  | Disj of typ * typ
  | True
  | Empty

type term =
  | Var of var
  | App of term * term
  | Abs of var * typ * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | VarL of term * typ
  | VarR of term * typ
  | Case of term * term * term
  | Unit
  | EmptyCase of term * typ
