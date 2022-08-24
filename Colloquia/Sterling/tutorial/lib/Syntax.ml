


(** De Bruijn indices *)
type var = Ix of int
(* x : A, y : B, z : C |- <<<you are here>>> *)

(* Binder(A) type
   B : A ---> Binder(A)  *)
type 'a binder = B of 'a

type term =
  | Var of var
  | Pi of term * term binder
  (* Pi (x:A). Bx
     A; x.B *)
  | Sg of term * term binder
  | Lam of term binder (* \x. Mx *)
  | Pair of term * term
  | App of term * term
  | Fst of term
  | Snd of term
  | Bool
  | True
  | False
  | BoolInd of {motive : term binder; tcase : term; fcase : term; scrut : term }
