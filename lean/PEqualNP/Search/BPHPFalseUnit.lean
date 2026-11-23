import PEqualNP.Search.BPHPFinalSimplification
import PEqualNP.Search.Helpers.QConstantUnit

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- It suffices to bound simplification-free derivations of one nonzero constant
equation. The forward implication adds one step and the reverse one uses the
quadratic-cost normalization with the same bit-size measure as L-alg-006. -/
theorem BPHPFalseUnit :
    (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < resLinQSize π) ↔
    (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ (ρ : List (QLine (Fin (2 ^ l + 1) × Fin l))) (D : ℤ),
      NoSimpDerivation (BPHP (2 ^ l + 1) l) ρ → D ≠ 0 → [(0,D)] ∈ ρ →
      p.eval (2 ^ l) < resLinQSize ρ) := by
  constructor
  · intro full p
    obtain ⟨l, lower⟩ := BPHPFinalSimplification.mp full p
    refine ⟨l, ?_⟩
    intro ρ D hd hD hm
    apply lower ρ [(0,D)] hm hd
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨rfl, hD⟩
  · intro unit p
    obtain ⟨l, lower⟩ := unit (20 * (p + 1) ^ 2)
    refine ⟨l, ?_⟩
    intro π hπ
    obtain ⟨D, ρ, hD, hd, hm, _, cost⟩ := normalized_constant_unit hπ
    have big := lower ρ D hd hD hm
    by_contra! short
    have bound := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (Nat.add_le_add_right short 1) 2)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_ofNat] at big
    omega

end PEqualNP.Search
