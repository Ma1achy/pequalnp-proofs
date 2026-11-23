import PEqualNP.Search.Helpers.DagUnfoldBound

/-! Unfold an additive cost into the copy count of each vertex times its local cost. -/

namespace PEqualNP.Search.Helpers

/-- Number of occurrences of vertex j in the tree obtained by following the parent
references from i. Repetition in a parent list creates separate copies. -/
def dagCopies {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (i j : Fin n) : ℕ :=
  (if i = j then 1 else 0) +
    ((parents i).attach.map (fun k => dagCopies parents order k.1 j)).sum
termination_by n - i.val
decreasing_by
  have h := order i k.1 k.2
  omega

theorem dagCopies_step {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (i j : Fin n) :
    dagCopies parents order i j = (if i = j then 1 else 0) +
      ((parents i).map (fun k => dagCopies parents order k j)).sum := by
  rw [dagCopies]
  simp

private theorem sum_parent_costs {n : ℕ} (parents : List (Fin n)) (c : Fin n → ℕ)
    (f : Fin n → Fin n → ℕ) (cost : Fin n → ℕ)
    (h : ∀ i ∈ parents, cost i = ∑ j, f i j * c j) :
    (parents.map cost).sum = ∑ j, ((parents.map (fun i => f i j)).sum) * c j := by
  induction parents with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul, Finset.sum_add_distrib]
    rw [h i List.mem_cons_self, ih (fun k hk => h k (List.mem_cons_of_mem i hk))]

/-- Exact vertex-by-vertex decomposition of any additive unfolded cost. -/
theorem dag_cost_eq_sum_copies {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (localCost cost : Fin n → ℕ)
    (rec : ∀ i, cost i = localCost i + ((parents i).map cost).sum) (root : Fin n) :
    cost root = ∑ j, dagCopies parents order root j * localCost j := by
  have hp := sum_parent_costs (parents root) localCost (dagCopies parents order) cost
    (fun i hi => dag_cost_eq_sum_copies parents order localCost cost rec i)
  rw [rec root, hp]
  simp_rw [dagCopies_step parents order root, Nat.add_mul, Finset.sum_add_distrib]
  simp [ite_mul]
termination_by n - root.val
decreasing_by
  have h := order root i hi
  omega

/-- When the cumulative cost exceeds the local cost budget times M, some vertex
with positive local cost occurs more than M times in the unfolded tree. -/
theorem exists_many_copies_of_positive_cost {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (localCost cost : Fin n → ℕ)
    (rec : ∀ i, cost i = localCost i + ((parents i).map cost).sum) (root : Fin n) (M : ℕ)
    (big : M * (∑ j, localCost j) < cost root) :
    ∃ j, 0 < localCost j ∧ M < dagCopies parents order root j := by
  by_contra! h
  have upper : cost root ≤ M * ∑ j, localCost j := by
    rw [dag_cost_eq_sum_copies parents order localCost cost rec root, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : localCost j = 0
    · simp [hz]
    · exact Nat.mul_le_mul_right _ (h j (Nat.pos_of_ne_zero hz))
  omega

end PEqualNP.Search.Helpers
