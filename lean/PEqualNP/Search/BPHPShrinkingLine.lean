import PEqualNP.Search.Helpers.BPHPEssential
import PEqualNP.Search.Helpers.DagCopies
import PEqualNP.Search.Helpers.QContraction
import PEqualNP.Search.Helpers.QPaddingCost
import PEqualNP.Search.Helpers.QWidthUnfold

/-! Locate a unary inference with many actual occurrences in the tree unfolded
from the empty line. Zero-cost operations make no contribution to the bound. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private theorem loss_le_proof_size {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (ProofComplexity.Clause V)} {π : List (QLine V)}
    (g : QWidthUnfolding F π) (i : Fin π.length) : g.loss i ≤ resLinQSize π := by
  by_cases h : 0 < g.loss i
  · obtain ⟨j, _, hj⟩ := g.loss_spec i h
    rw [hj]
    have cost : (π.get j).length ≤ qCost (π.get j) :=
      (qLength_le_weight _).trans (Nat.le_add_left _ 1)
    exact (Nat.sub_le ..).trans (cost.trans (qCost_le_of_mem (List.get_mem π j)))
  · omega

private theorem repeated_loss {l N : ℕ} {π : List (QLine (Fin N × Fin l))}
    (g : QWidthUnfolding (BPHP N l) π) (root : Fin π.length) (M T : ℕ)
    (rate : T ≤ 4 * g.totalLoss root) (budget : 4 * (M * (π.length * resLinQSize π)) < T) :
    ∃ i, 0 < g.loss i ∧ M < dagCopies g.parents g.later root i := by
  have sumBound : (∑ i, g.loss i) ≤ π.length * resLinQSize π := by
    calc
      _ ≤ ∑ _ : Fin π.length, resLinQSize π := Finset.sum_le_sum
        (fun i _ => loss_le_proof_size g i)
      _ = _ := by simp
  have hM := Nat.mul_le_mul_left M sumBound
  exact exists_many_copies_of_positive_cost g.parents g.later g.loss
    g.totalLoss g.total_rec root M (by omega)

private theorem bphp_seed (l : ℕ) : (BPHP (2^l+1) l).Nonempty := by
  have hn : 0 < 2 ^ l := by positivity
  let i : Fin (2 ^ l + 1) := ⟨0, by omega⟩
  let j : Fin (2 ^ l + 1) := ⟨1, by omega⟩
  exact ⟨_, i, j, fun _ => false, by simp [i, j], rfl⟩

/-- For every indexed width accounting of a bit-PHP refutation, any bound on
the copies of each width-decreasing unary step must pay for the tree lower
bound. The threshold uses the original integer proof's encoded bit size. -/
theorem shrinking_step_copies {l N : ℕ} (hl : 17 ≤ l) {π : List (QLine (Fin N × Fin l))}
    (g : QWidthUnfolding (BPHP N l) π) (root : Fin π.length) (hempty : π.get root = [])
    (M : ℕ) (budget : 4 * (M * (π.length * resLinQSize π)) <
      2 ^ (2 ^ ((l-17)/6)) + 2) :
    ∃ i j, g.parents i = [j] ∧ UnaryWidthRule (π.get j) (π.get i) ∧
      (π.get i).length < (π.get j).length ∧
      M < dagCopies g.parents g.later root i := by
  have leaves := bphp_false_line_leaf_rate hl (g.tree root) (by rw [hempty]; simp)
  have loss := g.potential root
  have rootWidth : (π.get root).length = 0 := congrArg List.length hempty
  rw [rootWidth, Nat.add_zero] at loss
  obtain ⟨i, hi, many⟩ := repeated_loss g root M _ (by omega) budget
  obtain ⟨j, hj, eq⟩ := g.loss_spec i hi
  obtain ⟨j', hj', rule⟩ := g.loss_rule i hi
  have same : j' = j := by simpa using hj'.symm.trans hj
  subst j'
  exact ⟨i, j, hj, rule, by omega, many⟩

/-- A syntactic refutation provides such an indexed width accounting, including
when it uses Boolean axioms or uses the same premise twice. -/
theorem BPHPShrinkingLine {l : ℕ} (hl : 17 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) :
    ∃ (g : QWidthUnfolding (BPHP (2 ^ l + 1) l) π) (root : Fin π.length),
      π.get root = [] ∧ ∀ M : ℕ, 4 * (M * (π.length * resLinQSize π)) <
        2 ^ (2 ^ ((l-17)/6)) + 2 →
        ∃ i j, g.parents i = [j] ∧ UnaryWidthRule (π.get j) (π.get i) ∧
          (π.get i).length < (π.get j).length ∧
          M < dagCopies g.parents g.later root i := by
  obtain ⟨g⟩ := exists_width_unfolding (bphp_seed l) (fun _ hC _ rep =>
    (show 2 ≤ 2*l by omega).trans (bphp_axiom_length hC rep)) hπ.1
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp hπ.2
  exact ⟨g, r, hr, shrinking_step_copies hl g r hr⟩

/-- In a simplification-free prefix deriving a false unit, every equation of the
premise survives a width drop. Some duplicate-removing weakening is therefore
copied many times in the tree unfolded from that unit. -/
theorem BPHPRepeatedContraction {l : ℕ} (hl : 17 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hd : NoSimpDerivation (BPHP (2 ^ l + 1) l) π)
    {D : ℤ} (hn : D ≠ 0) (root : Fin π.length) (hu : π.get root = [(0,D)]) :
    ∃ g : QWidthUnfolding (BPHP (2 ^ l + 1) l) π, ∀ M : ℕ,
      4 * (M * (π.length * resLinQSize π)) < 2 ^ (2 ^ ((l-17)/6)) + 2 →
      ∃ i j, g.parents i = [j] ∧ (∀ e ∈ π.get j, e ∈ π.get i) ∧
        (π.get i).length < (π.get j).length ∧ ¬ (π.get j).Nodup ∧
        M < dagCopies g.parents g.later root i := by
  obtain ⟨g, keep⟩ := exists_nosimp_width_unfolding (bphp_seed l) (fun _ hC _ rep =>
    (show 2 ≤ 2*l by omega).trans (bphp_axiom_length hC rep)) hd
  refine ⟨g, fun M budget => ?_⟩
  have bad : ∀ e ∈ π.get root, e.1 = 0 ∧ e.2 ≠ 0 := by
    rw [hu]
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨rfl, hn⟩
  have leaves := bphp_false_line_leaf_rate hl (g.tree root) bad
  have loss := g.potential root
  have rootWidth : (π.get root).length = 1 := congrArg List.length hu
  rw [rootWidth] at loss
  obtain ⟨i, hi, many⟩ := repeated_loss g root M _ (by omega) budget
  obtain ⟨j, hj, eq⟩ := g.loss_spec i hi
  have short : (π.get i).length < (π.get j).length := by omega
  have sub := keep i j hi hj
  exact ⟨i, j, hj, sub, short, not_nodup_of_shorter_superlist sub short, many⟩

end PEqualNP.Search
