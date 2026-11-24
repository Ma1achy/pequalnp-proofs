import PEqualNP.Defs.SearchQ
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace PEqualNP.Search.Helpers

/-- The equation `x + y = 1` on Boolean coordinates. -/
def twoBitMismatch {V : Type} [DecidableEq V] (x y : V) : QEq V :=
  (fun v => (if v = x then 1 else 0) + (if v = y then 1 else 0), 1)

theorem twoBitMismatch_holds {V : Type} [DecidableEq V] [Fintype V]
    (a : V → Bool) (x y : V) : QEq.Holds a (twoBitMismatch x y) ↔ a x ≠ a y := by
  unfold QEq.Holds twoBitMismatch
  simp only [Int.add_mul, Finset.sum_add_distrib, ite_mul, Int.one_mul, Int.zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases a x <;> cases a y <;> decide

theorem twoBitMismatch_size {V : Type} [DecidableEq V] [Fintype V]
    (x y : V) (ne : x ≠ y) : (twoBitMismatch x y).size = 4 := by
  have size (v : V) : ((twoBitMismatch x y).1 v).natAbs.size =
      (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
    by_cases hx : v = x
    · subst v
      simp [twoBitMismatch, ne]
    · by_cases hy : v = y
      · subst v
        simp [twoBitMismatch, hx]
      · simp [twoBitMismatch, hx, hy]
  unfold QEq.size
  simp only [size, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [twoBitMismatch]

end PEqualNP.Search.Helpers
