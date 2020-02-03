(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Recognizing axiomatizations of Hilbert-style calculi (HSC_AX)
    (Linial-Post theorem, strengthened by Bokov [1,2])

  HSC_AX:
    Given a list s₁,...,sₙ of formulae such that 
    [a → b → a] ⊢ sᵢ is derivable for i = 1...n,
    is [s₁,...,sₙ] ⊢ a → b → a derivable?
  
  References:
    [1] Grigoriy V. Bokov: Undecidable problems for propositional calculi with implication. 
      Logic Journal of the IGPL, 24(5):792–806, 2016. doi:10.1093/jigpal/jzw013
    [2] Andrej Dudenhefner, Jakob Rehof: Lower End of the Linial-Post Spectrum. 
      TYPES 2017: 2:1-2:15. doi: 10.4230/LIPIcs.TYPES.2017.2
*)

Require Import PeanoNat.
Require Import List.
Import ListNotations.

From Undecidability.HSC Require Import HSC_prelim.

(* the formula a → b → a *)
Definition a_b_a : formula := arr (var 0) (arr (var 1) (var 0)).

(* list of formulae derivable from a → b → a *)
Definition HSC_AX_PROBLEM := { Gamma: list formula | forall s, In s Gamma -> hsc [a_b_a] s}.

(* is the formula a → b → a derivable? *)
Definition HSC_AX (l: HSC_AX_PROBLEM) := hsc (proj1_sig l) a_b_a.
