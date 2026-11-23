import PEqualNP.ProofComplexity.L036
import PEqualNP.Search.Helpers.QSemanticDag
import PEqualNP.Search.Helpers.ParityCaseSplit

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- Split on the same `k` parity forms throughout an integer proof. If every line
has a one-clause parity representation in every cell, the resulting parity proof
costs at most four lines per original line per cell, plus setup and recombination. -/
theorem parity_refutation_of_common_cover {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}
    (hπ : IsResLinQSynRefutation F π) {k : ℕ} (forms : Fin k → Finset V)
    (cover : ∀ b L, L ∈ π → ∃ T : PEqualNP.ProofComplexity.LinClause V,
      ∀ a, ¬ LinClauseSat a (Helpers.parityBlock forms b) → (LinClauseSat a T ↔ QLine.Holds a L)) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ 2 ^ k * (4 * π.length + 3) := by
  classical
  have seed : F.Nonempty := by
    by_contra hF
    have hd := Helpers.syn_lines_hold_of_used_axioms hπ.1 (fun _ => false)
      (fun C hC _ => False.elim (hF ⟨C, hC⟩))
    obtain ⟨_, he, _⟩ := hd [] hπ.2
    simp at he
  choose leaf hd hm hc using fun b =>
    Helpers.guard_derivation_of_representation seed hπ (Helpers.parityBlock forms b) (cover b)
  obtain ⟨ρ, d, hlen⟩ := Helpers.parity_cases_refutation forms leaf hd hm
  have hu : (∑ b, (leaf b).length) ≤ 2 ^ k * (4 * π.length + 2) := by
    calc
      _ ≤ ∑ _ : Fin k → Bool, (4 * π.length + 2) := Finset.sum_le_sum (fun b _ => hc b)
      _ = _ := by simp
  refine ⟨ρ, d, hlen.trans ?_⟩
  have heq : 2 ^ k * (4 * π.length + 3) = 2 ^ k * (4 * π.length + 2) + 2 ^ k := by ring
  rw [heq]
  exact Nat.add_le_add hu (Nat.sub_le _ _)

/-- A shared partition into parity cells which makes every proof line a single
parity clause trades its number of cells against the length of the integer proof. -/
theorem BPHPParityCover {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) {k : ℕ}
    (forms : Fin k → Finset (Fin (2 ^ l + 1) × Fin l))
    (cover : ∀ b L, L ∈ π →
      ∃ T : PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l),
      ∀ a, ¬ LinClauseSat a (Helpers.parityBlock forms b) → (LinClauseSat a T ↔ QLine.Holds a L)) :
    Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) <
      (2 : ℝ) ^ k * (4 * (π.length : ℝ) + 3) := by
  obtain ⟨ρ, hρ, hlen⟩ := parity_refutation_of_common_cover hπ forms cover
  exact (L036 l ρ hl hρ).trans_le (by exact_mod_cast hlen)

end PEqualNP.Search
