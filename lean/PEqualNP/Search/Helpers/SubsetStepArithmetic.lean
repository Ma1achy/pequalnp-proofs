import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

/-- Maximum encoded cost of a row-pattern equation. -/
def subsetEquationCap (n t : ℕ) : ℕ := 2+((n+1)*t+1)*n

/-- Maximum weight of the equations recording one subset state. -/
def subsetStateCap (n t : ℕ) : ℕ := (n+1)*n*subsetEquationCap n t

/-- Maximum context weight when extending one subset state. -/
def subsetContextCap (n t : ℕ) : ℕ := (n+1)*subsetEquationCap n t + 4*t + subsetStateCap n t

/-- Encoded cost at each leaf of the bit queries in one subset transition. -/
def subsetLeafBudget (n t : ℕ) : ℕ :=
  (n+1)*(n*((4*t+3)*(10+(n+1)*t*n+(n+t*n)+(4*t+subsetContextCap n t)) +
    10*(subsetContextCap n t+4*t+1))) +
    (4*t+4)*(10+(n+1)*t*n+(n+t*n)+4*t) + 2*(1+subsetContextCap n t)

/-- The extension of one state, including the full case split, costs at most
a polynomial of degree ten in the number of holes. -/
theorem subset_arithmetic_cap {n t : ℕ} (ht : t ≤ n) :
    n*(subsetLeafBudget n t+10*(subsetStateCap n t+4*t+1)) ≤ 1000*(n+1)^10 := by
  calc
    _ ≤ n*(subsetLeafBudget n n+10*(subsetStateCap n n+4*n+1)) := by
      unfold subsetLeafBudget subsetContextCap subsetStateCap subsetEquationCap
      gcongr
    _ ≤ _ := by
      unfold subsetLeafBudget subsetContextCap subsetStateCap subsetEquationCap
      ring_nf
      omega

end PEqualNP.Search.Helpers
