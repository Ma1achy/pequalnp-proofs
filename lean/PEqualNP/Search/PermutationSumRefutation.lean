import PEqualNP.Search.BPHPBalancedTotal
import PEqualNP.Search.BPHPPermutationReduction

namespace PEqualNP.Search

/-- The balanced inputs force the sum of the labels. A derivation of this
singleton yields a refutation of the instance with one extra pigeon. -/
theorem PermutationSumRefutation :
  ∀ l : ℕ,
    let n := 2 ^ l
    let total : PEqualNP.Search.QEq (Fin n × Fin l) :=
      (fun v => (2 : ℤ) ^ v.2.val, (n : ℤ) * (n - 1) / 2)
    (∀ a, PEqualNP.ProofComplexity.Satisfies a (PEqualNP.ProofComplexity.BPHP n l) →
      PEqualNP.Search.QEq.Holds a total) ∧
    ∀ π : List (PEqualNP.Search.QLine (Fin n × Fin l)),
      PEqualNP.Search.IsResLinQSynDerivation (PEqualNP.ProofComplexity.BPHP n l) π →
      [total] ∈ π → ∃ ρ, PEqualNP.Search.IsResLinQSynRefutation
        (PEqualNP.ProofComplexity.BPHP (n + 1) l) ρ ∧
        PEqualNP.Search.resLinQSize ρ ≤ 2 * PEqualNP.Search.resLinQSize π + 403 * (n+1)^6 := by
  intro l n total
  refine ⟨?_, ?_⟩
  · intro a sat
    simpa [total, n, Helpers.binaryTotal] using BPHPBalancedTotal l a sat
  · intro π d hm
    exact BPHPPermutationReduction l _ d hm

end PEqualNP.Search
