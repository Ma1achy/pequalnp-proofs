import PEqualNP.Search.Helpers.BinaryBalanceCut
import PEqualNP.Defs.ProofComplexityBit
import Mathlib.Algebra.BigOperators.Fin

/-! The balanced bit pigeonhole formula forces its binary row labels to sum to
the triangular number. This is a statement about satisfying assignments. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private def binaryLabel {l : ℕ} (x : Fin l → Bool) : ℤ :=
  ∑ j, (2 : ℤ)^j.val * (if x j then 1 else 0)

private theorem sum_digit_weights (l : ℕ) : (∑ j : Fin l, (2 : ℤ)^j.val) = 2^l - 1 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, ih, Fin.val_last, pow_succ]; ring

private theorem sum_binary_labels (l : ℕ) :
    (∑ x : Fin l → Bool, binaryLabel x) = (2^l * (2^l - 1) : ℤ) / 2 := by
  classical
  let flip : (Fin l → Bool) ≃ (Fin l → Bool) :=
    ⟨fun x i => !x i, fun x i => !x i, fun x => by funext i; simp,
      fun x => by funext i; simp⟩
  have pair (x : Fin l → Bool) : binaryLabel x + binaryLabel (flip x) = 2^l-1 := by
    rw [binaryLabel, binaryLabel, ← Finset.sum_add_distrib, ← sum_digit_weights]
    apply Finset.sum_congr rfl
    intro j _
    cases h : x j <;> simp [flip, h]
  have double : (∑ x : Fin l → Bool, binaryLabel x) + (∑ x : Fin l → Bool, binaryLabel x) =
      2^l * (2^l-1) := by
    calc
      _ = (∑ x, binaryLabel x) + ∑ x, binaryLabel (flip x) := by rw [flip.sum_comp binaryLabel]
      _ = ∑ x : Fin l → Bool, (2^l - 1 : ℤ) := by rw [← Finset.sum_add_distrib]; simp_rw [pair]
      _ = _ := by simp; ring
  omega

private theorem rows_injective_of_balanced_sat {l : ℕ}
    (a : Fin (2 ^ l) × Fin l → Bool) (sat : Satisfies a (BPHP (2 ^ l) l)) :
    Function.Injective (fun (i : Fin (2 ^ l)) (b : Fin l) => a (i,b)) := by
  intro i j same
  by_contra diff
  obtain ⟨lit, hlit, holds⟩ := sat _ ⟨i, j, fun b => a (i,b), diff, rfl⟩
  rcases Finset.mem_union.mp hlit with h | h
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
    simp at holds
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
    have hbit : a (i,b) = a (j,b) := congrFun same b
    dsimp at holds
    simp [← hbit] at holds

/-- Every satisfying assignment with equally many pigeons and holes lists each
binary label once, so its total equals n(n−1)/2 for n=2^l. -/
theorem BPHPBalancedTotal (l : ℕ) (a : Fin (2 ^ l) × Fin l → Bool)
    (sat : Satisfies a (BPHP (2 ^ l) l)) :
    QEq.Holds a (binaryTotal ((2^l * (2^l - 1) : ℤ) / 2)) := by
  classical
  let row (i : Fin (2^l)) (b : Fin l) := a (i,b)
  have bij : Function.Bijective row := Fintype.bijective_iff_injective_and_card row |>.mpr
    ⟨rows_injective_of_balanced_sat a sat, by simp⟩
  let e := Equiv.ofBijective row bij
  change (∑ v : Fin (2^l) × Fin l, (2 : ℤ)^v.2.val * (if a v then 1 else 0)) = _
  rw [Fintype.sum_prod_type]
  change (∑ i, binaryLabel (e i)) = _
  rw [e.sum_comp binaryLabel]
  exact sum_binary_labels l

end PEqualNP.Search
