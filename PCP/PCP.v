Require Import List.
Import ListNotations.

(** ** Traditional Definition *)

Definition symbol := nat.
Definition string X := list X.
Definition card X : Type := string X * string X.
Definition stack X := list (card X).
Definition SRS := stack nat.
Definition BSRS := stack bool.

Notation "x / y" := (x,y).

Fixpoint tau1 {X : Type} (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => x ++ (tau1 A)
  end.

Fixpoint tau2 {X : Type} (A : stack X) : string X :=
  match A with
  | [] => []
  | (x / y) :: A => y ++ tau2 A
  end.

(* Post correspondence problem *)
Definition PCP P := exists A : SRS, incl A P /\ A <> [] /\ tau1 A = tau2 A.

(* Modified Post correspondence problem *)
Definition MPCP '((x,y), P) := exists A : SRS, incl A (x/y :: P) /\ x ++ tau1 A = y ++ tau2 A.


(*
  Problem:
    Binary modified Post correspondence problem (BMPCP)

  BMPCP:
    Given a pair (x, y) of binary strings and 
    a list P of pairs of binary strings,
    is there a list A = [(x₁, y₁),...,(xₙ, yₙ)] of pairs of binary strings such that
    x ++ x₁ ++ ... ++ xₙ = y ++ y₁ ++ ... yₙ?
    
*)
Definition BMPCP '((x,y), P) := exists A : BSRS, incl A (x/y :: P) /\ x ++ tau1 A = y ++ tau2 A.
