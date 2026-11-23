import PEqualNP.ProofComplexity.L036
import PEqualNP.Search.Helpers.QParitySimulation

/-! A small integer proof must cross a step that fails after reduction modulo two. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

theorem collision_formula_nonempty (l : ℕ) : (BPHP (2 ^ l + 1) l).Nonempty := by
  have hn : 0 < 2 ^ l := by positivity
  let i : Fin (2 ^ l + 1) := ⟨0, by omega⟩
  let j : Fin (2 ^ l + 1) := ⟨1, by omega⟩
  exact ⟨_, i, j, fun _ => false, by simp [i, j], rfl⟩

/-- Every refutation below the parity lower bound (after accounting for the
four-line simulation) has a simplification pair distinguishable on a Boolean
assignment after projection. -/
theorem bphp_parity_obstruction {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (hshort : 4 * (π.length : ℝ) + 1 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    Helpers.ParityObstruction π := by
  by_contra h
  obtain ⟨ρ, hρ, hlen⟩ := Helpers.parity_refutation_of_safe (collision_formula_nonempty l) hπ h
  have hbound := L036 l ρ hl hρ
  have hu : (ρ.length : ℝ) ≤ 4 * (π.length : ℝ) + 1 := by exact_mod_cast hlen
  linarith

/-- In particular such a proof contains an integer contradiction with nonzero even
right-hand side, and also contains the line after false constants are removed. -/
theorem BPHPParityBarrier {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (hshort : 4 * (π.length : ℝ) + 1 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ K ∈ π, K.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) ∈ π ∧
      ∃ e ∈ K, e.1 = 0 ∧ e.2 ≠ 0 ∧ Even e.2 :=
  Helpers.even_constant_of_parityObstruction (bphp_parity_obstruction hl hπ hshort)

end PEqualNP.Search
