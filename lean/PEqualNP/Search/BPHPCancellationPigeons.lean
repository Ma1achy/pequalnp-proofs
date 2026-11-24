import PEqualNP.Search.BPHPCancellationSearch
import PEqualNP.Search.Helpers.ParityQuerySupport

/-! No small group of pigeon rows can contain a collision on every falsifier of
the hard repair clause. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- A collision within the chosen rows falsifies an input clause using only their bits. -/
theorem collision_clause_on_rows {m l : ℕ} (a : Fin m × Fin l → Bool)
    (U : Finset (Fin m))
    (hn : ¬ Set.InjOn (fun (i : Fin m) (b : Fin l) => a (i, b)) (↑U : Set (Fin m))) :
    ∃ C ∈ BPHP m l,
      (∀ lit ∈ C, lit.1 ∈ U ×ˢ (Finset.univ : Finset (Fin l))) ∧ ¬ ClauseSat a C := by
  classical
  unfold Set.InjOn at hn
  push Not at hn
  obtain ⟨i, hi, j, hj, heq, hne⟩ := hn
  refine ⟨_, ⟨i, j, fun b => a (i, b), hne, rfl⟩, ?_, ?_⟩
  · intro lit h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩
  · rintro ⟨lit, h, hsat⟩
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      simp at hsat
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      have same : a (i,b) = a (j,b) := congrFun heq b
      dsimp only at hsat
      rw [← same] at hsat
      simp at hsat

/-- A single resolution site with hard parity search has, for every small set of
pigeons, a cancellation witness assigning all pigeons in that set distinct holes.
The choice of witness can depend on the set of pigeons. -/
theorem BPHPCancellationPigeons {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) (r : ℕ)
    (short : (3 * (r : ℝ) + 10) * π.length + 1 ≤
      Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ step : ResolutionSite π, PrimitiveRankPair step.firstHead step.secondHead ∧
      r < (parityFalsifiers step.repair).card ∧
      (∀ t : ParityTree _, LeafFindsViolation (BPHP (2 ^ l + 1) l) step.repair t → r < t.leaves) ∧
      ∀ U : Finset (Fin (2 ^ l + 1)), 2 ^ (l * U.card) ≤ r →
        ∃ a ∈ parityFalsifiers step.repair,
          Set.InjOn (fun (i : Fin (2 ^ l + 1)) (b : Fin l) => a (i, b)) (↑U : Set _) := by
  classical
  obtain ⟨step, rank, many, hard⟩ := BPHPCancellationSearch hl hπ r short
  refine ⟨step, rank, many, hard, ?_⟩
  intro U hU
  by_contra! hn
  let W := U ×ˢ (Finset.univ : Finset (Fin l))
  have hw : W.card = l * U.card := by simp [W, Nat.mul_comm]
  obtain ⟨tree, small, solves⟩ := supported_violation_tree (BPHP (2^l+1) l) step.repair W
    (collision_formula_nonempty l) (fun a ha =>
      collision_clause_on_rows a U (hn a ((mem_parityFalsifiers _ _).mpr ha)))
  exact (hard tree solves).not_ge (small.trans (by simpa only [hw] using hU))

end PEqualNP.Search
