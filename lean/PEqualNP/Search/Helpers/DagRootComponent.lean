import PEqualNP.Search.Helpers.DagReuseDepth

namespace PEqualNP.Search.Helpers

variable {n : ℕ}

/-- Keep exactly the dependency lists belonging to the designated root's
component. Removing an unused line removes all its references to active lines. -/
noncomputable def rootParents (parents : Fin n → List (Fin n)) (root i : Fin n) : List (Fin n) := by
  classical
  exact if dagReachable parents (· = root) i then parents i else []

/-- Assign zero cost to vertices whose proof is unused by the root. -/
noncomputable def rootCost (parents : Fin n → List (Fin n)) (root : Fin n)
    (cost : Fin n → ℕ) (i : Fin n) : ℕ := by
  classical
  exact if dagReachable parents (· = root) i then cost i else 0

theorem mem_rootParents {parents : Fin n → List (Fin n)} {root i j : Fin n} :
    j ∈ rootParents parents root i ↔ dagReachable parents (· = root) i ∧ j ∈ parents i := by
  classical
  by_cases h : dagReachable parents (· = root) i <;> simp [rootParents, h]

theorem rootParents_later {parents : Fin n → List (Fin n)}
    (order : ∀ i j, j ∈ parents i → i < j) (root : Fin n) :
    ∀ i j, j ∈ rootParents parents root i → i < j :=
  fun i j h => order i j (mem_rootParents.mp h).2

theorem rootParents_arity {parents : Fin n → List (Fin n)} {d : ℕ}
    (arity : ∀ i, (parents i).length ≤ d) (root : Fin n) :
    ∀ i, (rootParents parents root i).length ≤ d := by
  classical
  intro i
  by_cases h : dagReachable parents (· = root) i <;> simp [rootParents, h, arity]

theorem rootCost_root (parents : Fin n → List (Fin n)) (root : Fin n) (cost : Fin n → ℕ) :
    rootCost parents root cost root = cost root := by
  have h : dagReachable parents (· = root) root := .single rfl
  simp [rootCost, h]

/-- Every parent of an active vertex is active, preserving its unfolding
recurrence even when dependencies occur more than once in a list. -/
theorem rootCost_rec (parents : Fin n → List (Fin n)) (root : Fin n) (cost : Fin n → ℕ)
    (c : ℕ) (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum) :
    ∀ i, rootCost parents root cost i ≤ c +
      ((rootParents parents root i).map (rootCost parents root cost)).sum := by
  classical
  intro i
  by_cases h : dagReachable parents (· = root) i
  · have eq : (parents i).map (rootCost parents root cost) = (parents i).map cost := by
      apply List.map_congr_left
      intro j hj
      simp [rootCost, h.step hj]
    simpa [rootParents, h, eq, rootCost] using rec i
  · simp [rootCost, h]

/-- The global factor `2^dagExcess` may be computed using only references from
the designated root's component. -/
theorem dag_unfold_cost_le_root_component (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (cost : Fin n → ℕ) (c : ℕ)
    (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum) (root : Fin n) :
    cost root ≤ c * n * 2 ^ dagExcess (rootParents parents root) := by
  rw [← rootCost_root parents root cost]
  exact dag_unfold_cost_le _ (rootParents_later order root) _ c
    (rootCost_rec parents root cost c rec) root

end PEqualNP.Search.Helpers
