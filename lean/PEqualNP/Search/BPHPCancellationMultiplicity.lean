import PEqualNP.Search.BPHPCancellationPigeons
import PEqualNP.Search.Helpers.ParityQueryExceptions

/-! Counting locally injective assignments in a hard cancellation region. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- Falsifiers of the repair clause on which the named pigeons have distinct holes. -/
noncomputable def injectiveFalsifiers {m l : ℕ} (R : ProofComplexity.LinClause (Fin m × Fin l))
    (U : Finset (Fin m)) : Finset (Fin m × Fin l → Bool) := by
  classical
  exact (parityFalsifiers R).filter (fun a =>
    Set.InjOn (fun (i : Fin m) (b : Fin l) => a (i,b)) (↑U : Set _))

/-- Querying the bits of U either exhibits a collision or leaves an exceptional
assignment that is injective on U. Distinguishing those exceptional assignments
costs at most one additional leaf per assignment across the entire tree. -/
theorem BPHPCancellationMultiplicity {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) (r : ℕ)
    (short : (3 * (r : ℝ) + 10) * π.length + 1 ≤
      Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ step : ResolutionSite π, PrimitiveRankPair step.firstHead step.secondHead ∧
      r < (parityFalsifiers step.repair).card ∧
      (∀ t : ParityTree _, LeafFindsViolation (BPHP (2 ^ l + 1) l) step.repair t → r < t.leaves) ∧
      ∀ U : Finset (Fin (2 ^ l + 1)),
        r < 2 ^ (l * U.card) + (injectiveFalsifiers step.repair U).card := by
  classical
  obtain ⟨step, rank, many, hard⟩ := BPHPCancellationSearch hl hπ r short
  refine ⟨step, rank, many, hard, ?_⟩
  intro U
  let W := U ×ˢ (Finset.univ : Finset (Fin l))
  have hw : W.card = l * U.card := by simp [W, Nat.mul_comm]
  have unsat := L021 (2^l+1) l (by omega)
  obtain ⟨tree, small, solves⟩ := supported_violation_except_tree (BPHP (2^l+1) l)
    step.repair W (injectiveFalsifiers step.repair U) (collision_formula_nonempty l) (by
      intro a ha hn
      apply collision_clause_on_rows a U
      intro hinj
      exact hn (Finset.mem_filter.mpr ⟨(mem_parityFalsifiers _ _).mpr ha, hinj⟩)) (by
      intro a _
      by_contra! h
      exact unsat ⟨a, h⟩)
  exact (hard tree solves).trans_le (by simpa only [hw] using small)

end PEqualNP.Search
