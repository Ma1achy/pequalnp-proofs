import PEqualNP.Search.BPHPParityBarrier

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- An odd false unit stays false after reduction modulo two. The projected
trace therefore needs just one more weakening to the empty parity clause. -/
theorem parity_refutation_of_odd_unit {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty) {π : List (QLine V)} {D : ℤ}
    (der : NoSimpDerivation F π) (unit : [(0, D)] ∈ π) (odd : Odd D) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ 4 * π.length + 2 := by
  obtain ⟨τ, d, rep, len⟩ := parity_derivation_no_simp seed der
  refine ⟨∅ :: τ, ⟨d.weak (rep _ unit) ?_, List.mem_cons_self⟩, ?_⟩
  · rintro a ⟨q, hq, hs⟩
    have eq : q = qParity ((0, D) : QEq V) := by simpa [qLineParity] using hq
    exact (qParity_false a ((0, D) : QEq V) rfl odd (eq ▸ hs)).elim
  · simp only [List.length_cons]
    omega

/-- Below the parity length bound, a simplification-free derivation of a
constant unit must have even right-hand side. -/
theorem BPHPFalseUnitParity {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))} {D : ℤ}
    (der : NoSimpDerivation (BPHP (2 ^ l + 1) l) π) (unit : [(0, D)] ∈ π)
    (short : 4 * (π.length : ℝ) + 2 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    Even D := by
  apply Int.not_odd_iff_even.mp
  intro odd
  obtain ⟨ρ, ref, len⟩ := parity_refutation_of_odd_unit (collision_formula_nonempty l) der unit odd
  have lower := L036 l ρ hl ref
  have upper : (ρ.length : ℝ) ≤ 4 * (π.length : ℝ) + 2 := by exact_mod_cast len
  linarith

end PEqualNP.Search
