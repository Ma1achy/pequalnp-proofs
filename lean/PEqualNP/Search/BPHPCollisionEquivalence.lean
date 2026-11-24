import PEqualNP.Search.BPHPCollisionTautology
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- On every Boolean input at least one pair of pigeons has the same binary label. -/
theorem collisionLine_holds (l : ℕ) (a : Fin (2^l+1) × Fin l → Bool) :
    QLine.Holds a (collisionLine (2^l+1) l) := by
  by_contra none
  have inj : Function.Injective (fun (i : Fin (2^l+1)) (b : Fin l) => a (i,b)) := by
    intro i j rows
    by_contra ne
    exact none ⟨binaryRowEq i j, mem_collisionLine.mpr ⟨i, j, ne, rfl⟩,
      (binaryRowEq_holds a i j).mpr (congrFun rows)⟩
  have h := Fintype.card_le_of_injective _ inj
  simp at h

private theorem zero_bit_refutation :
    IsResLinQSynRefutation (BPHP (2^0+1) 0) [[]] := by
  have input : (∅ : ProofComplexity.Clause (Fin (2^0+1) × Fin 0)) ∈ BPHP (2^0+1) 0 :=
    ⟨0, 1, fun _ => false, by decide, by simp⟩
  exact ⟨IsResLinQSynDerivation.ax ∅ .nil input (by simp), List.mem_cons_self⟩

/-- The exact unrestricted question is equivalent to a size lower bound on
proofs from Boolean axioms alone of a single disjunction of integer equalities.
At bit width zero an input clause is already empty. -/
theorem BPHPCollisionEquivalence :
    (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (QLine (Fin (2^l+1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2^l+1) l) π → p.eval (2^l) < resLinQSize π) ↔
    (∀ p : Polynomial ℕ, ∃ l : ℕ, 0 < l ∧ ∀ ρ : List (QLine (Fin (2^l+1) × Fin l)),
      IsResLinQSynDerivation ∅ ρ → collisionLine (2^l+1) l ∈ ρ → p.eval (2^l) < resLinQSize ρ) := by
  constructor
  · intro hard p
    obtain ⟨l, lower⟩ := hard (p + 500*(Polynomial.X+1)^10 + 1)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one] at lower
    have hl : 0 < l := by
      by_contra! hz
      obtain rfl : l = 0 := by omega
      have h := lower _ zero_bit_refutation
      change _ < 1 at h
      omega
    refine ⟨l, hl, ?_⟩
    intro ρ d hm
    obtain ⟨π, ref, cost⟩ := bphp_collision_tautology_to_refutation d hm
    have h := lower π ref
    omega
  · intro hard p
    obtain ⟨l, hl, lower⟩ := hard (1000*(Polynomial.X+1)^5*p)
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one] at lower
    refine ⟨l, ?_⟩
    intro π ref
    obtain ⟨ρ, d, hm, cost⟩ := bphp_refutation_to_collision_tautology hl ref
    have h := lower ρ d hm
    by_contra! small
    have := Nat.mul_le_mul_left (1000*(2^l+1)^5) small
    omega

end PEqualNP.Search
