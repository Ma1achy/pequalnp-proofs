import PEqualNP.Search.Helpers.ParityTreeSimulation
import PEqualNP.ProofComplexity.L036

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- A sufficiently short integer refutation contains a line whose Boolean truth
function requires more than r leaves in every decision tree with parity queries.
The tree can choose a different parity on every path and for every proof line. -/
theorem BPHPParityTree {l r : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (hs : ((π.length * (r * (4 * (r + 1) * (r + 1))) + 1 : ℕ) : ℝ) ≤
      Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ L ∈ π, ∀ t : ParityTree (Fin (2 ^ l + 1) × Fin l),
      (∀ a, t.eval a = true ↔ QLine.Holds a L) → r < t.leaves := by
  classical
  by_contra! h
  have small (L) (hL : L ∈ π) : ∃ t : ParityTree (Fin (2 ^ l + 1) × Fin l),
      t.leaves ≤ r ∧ ∀ a, t.eval a = true ↔ QLine.Holds a L := by
    obtain ⟨t, ht, hb⟩ := h L hL
    exact ⟨t, hb, ht⟩
  have hn : 0 < 2 ^ l := by positivity
  have seed : (BPHP (2 ^ l + 1) l).Nonempty := by
    let i : Fin (2 ^ l + 1) := ⟨0, by omega⟩
    let j : Fin (2 ^ l + 1) := ⟨1, by omega⟩
    exact ⟨_, i, j, fun _ => false, by simp [i, j], rfl⟩
  obtain ⟨ρ, hρ, hsize⟩ := parity_refutation_of_small_trees seed hπ r small
  exact (L036 l ρ hl hρ).not_ge ((Nat.cast_le.mpr hsize).trans hs)

end PEqualNP.Search
