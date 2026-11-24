import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

namespace PEqualNP.Search.Petersen2541

private theorem tripleSum (x y z : ℕ) (h : 4 ≤ (2^x-1)*(2^y-1)*(2^z-1)) :
    5 ≤ x + y + z := by
  by_contra! hn
  have test : ∀ x y z : Fin 5, 4 ≤ (2^x.val-1)*(2^y.val-1)*(2^z.val-1) →
      5 ≤ x.val+y.val+z.val := by decide +kernel
  exact (by omega : ¬5 ≤ x+y+z) (test ⟨x,by omega⟩ ⟨y,by omega⟩ ⟨z,by omega⟩ h)

private theorem pairSum (x y : ℕ) (h : 2 ≤ (2^x-1)*(2^y-1)) : 3 ≤ x+y := by
  by_contra! hn
  have test : ∀ x y : Fin 3, 2 ≤ (2^x.val-1)*(2^y.val-1) → 3 ≤ x.val+y.val := by decide +kernel
  exact (by omega : ¬3 ≤ x+y) (test ⟨x,by omega⟩ ⟨y,by omega⟩ h)

/-- The four cofactor constraints force sixteen variable occurrences. -/
theorem sum_occurrences_ge16 (r : Fin 9 → ℕ) (r0 : r 0 ≤ 1)
    (a : 4 ≤ (2^r 0-1)*(2^r 5-1)*(2^r 8-1))
    (b : 4 ≤ (2^r 0-1)*(2^r 1-1)*(2^r 6-1))
    (c : 4 ≤ (2^r 2-1)*(2^r 3-1)*(2^r 7-1))
    (d : 2 ≤ (2^r 0-1)*(2^r 4-1)) : 16 ≤ ∑ i,r i := by
  have ha := tripleSum _ _ _ a
  have hb := tripleSum _ _ _ b
  have hc := tripleSum _ _ _ c
  have hd := pairSum _ _ d
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  change 16 ≤ r 0 + (r 1 + (r 2 + (r 3 + (r 4 + (r 5 + (r 6 + (r 7 + (r 8 + 0))))))))
  omega

end PEqualNP.Search.Petersen2541
