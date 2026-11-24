import PEqualNP.Search.BPHPBlockUpper

namespace PEqualNP.Search

/-- Every fixed positive exponential rate in the number of holes eventually
exceeds the cost of the constructed refutations. -/
theorem BPHPSubexponential :
    ∀ k l : ℕ, 8*(512*k+1) ≤ l →
      ∃ π : List (QLine (Fin (2^l+1) × Fin l)),
        IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2^l+1) l) π ∧
        resLinQSize π ^ k ≤ 2^(2^l) := by
  intro k l width
  obtain ⟨π,ref,cost⟩ := BPHPBlockUpper l
  refine ⟨π,ref,(Nat.pow_le_pow_left cost k).trans ?_⟩
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  rw [Nat.mul_comm _ k]
  apply Helpers.bphp_block_exponent_rate
  simpa only [Nat.mul_comm 512 k] using width

end PEqualNP.Search
