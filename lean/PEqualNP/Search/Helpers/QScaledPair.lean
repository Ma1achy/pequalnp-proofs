import PEqualNP.Defs.SearchQ
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Search.Helpers

variable {V : Type} [DecidableEq V]

/-- The singleton equation c(x-y)=0 in coordinates. -/
def scaledEqPair (c : ℤ) (x y : V) : QEq V :=
  (fun v => (if v = x then c else 0) - (if v = y then c else 0), 0)

theorem scaledEqPair_size [Fintype V] (c : ℤ) (x y : V) :
    (scaledEqPair c x y).size ≤ 1+2*c.natAbs.size := by
  have coef (v : V) : ((scaledEqPair c x y).1 v).natAbs.size ≤
      (if v=x then c.natAbs.size else 0) + (if v=y then c.natAbs.size else 0) := by
    dsimp only [scaledEqPair]
    split_ifs <;> simp
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => coef v)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at total
  change 1 + _ + (0:ℤ).natAbs.size ≤ _
  rw [show (0:ℤ).natAbs.size = 0 from rfl, Nat.add_zero, Nat.two_mul]
  exact Nat.add_le_add_left total 1

end PEqualNP.Search.Helpers
