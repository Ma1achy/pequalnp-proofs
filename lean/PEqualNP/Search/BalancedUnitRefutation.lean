import PEqualNP.Search.BPHPBalancedUnit

namespace PEqualNP.Search

/-- An arbitrary nontrivial singleton on balanced pigeonhole produces a short
refutation on one additional pigeon. Costs use the project's binary encoding. -/
theorem BalancedUnitRefutation :
    ∀ (l : ℕ) (π : List (QLine (Fin (2^l) × Fin l))) (e : QEq (Fin (2^l) × Fin l)),
      IsResLinQSynDerivation (PEqualNP.ProofComplexity.BPHP (2^l) l) π →
      [e] ∈ π → e.1 ≠ 0 →
      ∃ ρ, IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2^l+1) l) ρ ∧
        resLinQSize ρ ≤ 42*(2^l)^2*resLinQSize π + 1200*(2^l+1)^5 := by
  intro l π e d unit coeff
  exact bphp_refutation_of_balanced_unit d unit coeff

end PEqualNP.Search
