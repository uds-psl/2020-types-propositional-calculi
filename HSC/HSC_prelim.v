(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Preliminaries for Provability in Hilbert-style calculi
*)

Require Import List.

(* propositional formulae s, t ::= a | s → t *)
Inductive formula : Set :=
  | var : nat -> formula
  | arr : formula -> formula -> formula.

(* substitute ζ t replaces each variable n in t by ζ n *)
Fixpoint substitute (ζ: nat -> formula) (t: formula) : formula :=
  match t with
  | var n => ζ n
  | arr s t => arr (substitute ζ s) (substitute ζ t)
  end.

(* Hilbert-style calculus *)
Inductive hsc (Gamma: list formula) : formula -> Prop :=
  | hsc_var : forall (ζ: nat -> formula) (t: formula), In t Gamma -> hsc Gamma (substitute ζ t)
  | hsc_arr : forall (s t : formula), hsc Gamma (arr s t) -> hsc Gamma s -> hsc Gamma t.
