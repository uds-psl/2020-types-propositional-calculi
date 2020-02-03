(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Provability in Hilbert-style calculi (HSC_PRV)

  HSC_PRV:
    Fix a list s₁,...,sₙ of formulae.
    Given a formula s, is [s₁,...,sₙ] ⊢ s derivable?
*)

Require Import List.

From Undecidability.HSC Require Import HSC_prelim.

(* is the formula s derivable from the fixed list of formulae Gamma? *)
Definition HSC_PRV (Gamma: list formula) (s: formula) := hsc Gamma s.
