import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Bound the cost of unfolding ordered proof DAGs. Vertices list their dependencies;
parallel edges represent distinct uses of the same premise. -/

namespace PEqualNP.Search.Helpers

/-- Number of references to a vertex, counted with multiplicity. -/
def dagUses {n : ℕ} (parents : Fin n → List (Fin n)) (i : Fin n) : ℕ :=
  ∑ j, (parents j).count i

/-- References in excess of one per vertex. -/
def dagExcess {n : ℕ} (parents : Fin n → List (Fin n)) : ℕ :=
  ∑ i, (dagUses parents i - 1)

private theorem sum_map_eq_uses {n : ℕ} (xs : List (Fin n)) (f : Fin n → ℕ) :
    (xs.map f).sum = ∑ i, xs.count i * f i := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    simp_rw [Nat.add_mul, Finset.sum_add_distrib]
    simp [ite_mul, add_comm]

/-- A nonnegative multiplicity bound at each vertex pays for the root and the
demands made on that vertex by its users. Summing cancels the internal edge costs. -/
theorem dag_unfold_cost_le_of_weights {n : ℕ} (parents : Fin n → List (Fin n))
    (cost : Fin n → ℕ) (c : ℕ)
    (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum) (root : Fin n)
    (w : Fin n → ℕ)
    (balance : ∀ i, (if i = root then 1 else 0) +
      (∑ j, w j * (parents j).count i) ≤ w i) :
    cost root ≤ c * ∑ i, w i := by
  let edgeCost := ∑ i, ∑ j, w i * (parents i).count j * cost j
  have advance : (∑ i, w i * cost i) ≤ c * (∑ i, w i) + edgeCost := by
    calc
      _ ≤ ∑ i, w i * (c + ((parents i).map cost).sum) :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (rec i))
      _ = _ := by
        simp_rw [sum_map_eq_uses, Nat.mul_add, Finset.mul_sum, ← Nat.mul_assoc]
        simp [edgeCost, Finset.sum_add_distrib, Finset.sum_mul, mul_comm c]
  have consume : cost root + edgeCost ≤ ∑ i, w i * cost i := by
    calc
      _ = ∑ i, ((if i = root then 1 else 0) +
            (∑ j, w j * (parents j).count i)) * cost i := by
        simp_rw [Nat.add_mul, Finset.sum_mul]
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => w j * (parents j).count i * cost i)]
        simp [edgeCost, ite_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (balance i))
  omega

private theorem uses_le_pow (d : ℕ) : d ≤ 2 ^ (d - 1) := by
  cases d with
  | zero => simp
  | succ d => simpa using d.lt_two_pow_self

/-- Unfolding a DAG with local cost at most c into a tree costs at most c times
the vertex count times two to the number of excess references. A vertex listed
twice as a premise consumes two incoming references. -/
theorem dag_unfold_cost_le {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (cost : Fin n → ℕ) (c : ℕ)
    (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum) (root : Fin n) :
    cost root ≤ c * n * 2 ^ dagExcess parents := by
  classical
  let extra := fun i => dagUses parents i - 1
  let bound := fun i => 2 ^ (∑ j ∈ Finset.Iic i, extra j)
  let w := fun i => if i < root then 0 else bound i
  have support (i j : Fin n) (h : ¬ j < i) : (parents j).count i = 0 :=
    List.count_eq_zero.mpr (fun hi => h (order j i hi))
  have balance (i : Fin n) :
      (if i = root then 1 else 0) + (∑ j, w j * (parents j).count i) ≤ w i := by
    by_cases hir : i ≤ root
    · have zero_in : (∑ j, w j * (parents j).count i) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hji : j < i
        · simp [w, hji.trans_le hir]
        · simp [support i j hji]
      rw [zero_in]
      by_cases h : i = root
      · subst i
        simp [w, bound, Nat.one_le_two_pow]
      · simp [w, lt_of_le_of_ne hir h, h]
    · have hr : root < i := lt_of_not_ge hir
      simp only [ite_eq_right hr.ne', Nat.zero_add]
      rw [show w i = bound i from ite_eq_right (not_lt_of_ge hr.le)]
      let B := 2 ^ (∑ j ∈ Finset.Iio i, extra j)
      have demand (j : Fin n) : w j * (parents j).count i ≤ B * (parents j).count i := by
        by_cases hji : j < i
        · apply Nat.mul_le_mul_right
          have sub : Finset.Iic j ⊆ Finset.Iio i :=
            fun h hx => Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hx) hji)
          have le : bound j ≤ B := Nat.pow_le_pow_right (by decide)
            (Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega))
          by_cases h : j < root <;> simp [w, h, le]
        · simp [support i j hji]
      calc
        _ ≤ ∑ j, B * (parents j).count i := Finset.sum_le_sum (fun j _ => demand j)
        _ = B * dagUses parents i := (Finset.mul_sum ..).symm
        _ ≤ B * 2 ^ extra i := Nat.mul_le_mul_left B (uses_le_pow _)
        _ = bound i := by
          dsimp only [B, bound]
          rw [Finset.Iic_eq_cons_Iio i, Finset.sum_cons, pow_add, Nat.mul_comm]
  have each (i : Fin n) : w i ≤ 2 ^ dagExcess parents := by
    have le : bound i ≤ 2 ^ dagExcess parents := Nat.pow_le_pow_right (by decide)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega))
    by_cases h : i < root <;> simp [w, h, le]
  calc
    cost root ≤ c * ∑ i, w i := dag_unfold_cost_le_of_weights parents cost c rec root w balance
    _ ≤ c * ∑ _ : Fin n, 2 ^ dagExcess parents :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum fun i _ => each i)
    _ = _ := by simp [Nat.mul_assoc]

end PEqualNP.Search.Helpers
