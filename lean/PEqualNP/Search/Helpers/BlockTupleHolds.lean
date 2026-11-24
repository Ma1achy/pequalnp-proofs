import PEqualNP.Search.Helpers.BlockTupleEq
import Mathlib.Algebra.BigOperators.Fin

namespace PEqualNP.Search.Helpers

/-- A tuple's signed bit sum is maximal exactly when every specified row has
the prescribed prefix. -/
theorem blockTupleEq_holds {m u : ℕ} (v : ℕ) (a : Fin m × Fin (u+v) → Bool)
    (S : Finset (Fin m)) (h : Fin u → Bool) :
    QEq.Holds a (blockTupleEq v S h) ↔ ∀ i ∈ S, ∀ b : Fin u, a (i,b.castAdd v) = h b := by
  classical
  let bit (z : Bool) : ℤ := if z then 1 else 0
  let w (b : Fin u) : ℤ := if h b then 1 else -1
  let val (i : Fin m) (b : Fin u) := w b * bit (a (i,b.castAdd v))
  let err (i : Fin m) (b : Fin u) := bit (h b) - val i b
  have positive (i b) : 0 ≤ err i b := by
    cases hb : h b <;> cases ha : a (i,b.castAdd v) <;> simp [err,val,w,bit,hb,ha]
  have zero (i b) : err i b = 0 ↔ a (i,b.castAdd v) = h b := by
    cases hb : h b <;> cases ha : a (i,b.castAdd v) <;> simp [err,val,w,bit,hb,ha]
  have total : (∑ x : Fin m × Fin (u+v), (blockTupleEq v S h).1 x * bit (a x)) =
      ∑ i ∈ S, ∑ b, val i b := by
    rw [Fintype.sum_prod_type, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have absent (i : Fin m) (hi : i ∉ S) :
        (∑ j, (blockTupleEq v S h).1 (i,j) * bit (a (i,j))) = 0 := by
      simp [blockTupleEq,hi]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun i => i ∉ S))
      (fun i hi => absent i (Finset.mem_filter.mp hi).2), add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Fin.sum_univ_add]
    simp [blockTupleEq,hi,val,w,Fin.isLt]
  have margin : (∑ i ∈ S, ∑ b, err i b) =
      (S.card : ℤ)*(∑ b, bit (h b)) - ∑ i ∈ S, ∑ b, val i b := by
    simp [err,Finset.sum_sub_distrib]
  change (∑ x, (blockTupleEq v S h).1 x * bit (a x)) = (S.card : ℤ)*(∑ b, bit (h b)) ↔ _
  rw [total, ← sub_eq_zero, ← neg_sub, neg_eq_zero, ← margin]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun b _ => positive i b))]
  constructor
  · intro H i hi b
    exact (zero i b).mp ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => positive i b)).mp
      (H i hi) b (Finset.mem_univ _))
  · intro H i hi
    exact Finset.sum_eq_zero (fun b _ => (zero i b).mpr (H i hi b))

end PEqualNP.Search.Helpers
