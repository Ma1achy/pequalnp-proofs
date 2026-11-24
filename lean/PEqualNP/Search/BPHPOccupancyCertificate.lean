import PEqualNP.Search.BPHPOccupancyInterpolation
import PEqualNP.Search.Helpers.OccupancyWeights

/-! For holes `0,…,n`, clearing the interpolation denominators gives signed
binomial coefficients and `n+1` products with `n+1` linear factors each. -/

namespace PEqualNP.Search

/-- The numbered occupancy certificate with factorial scaling and integral weights. -/
theorem occupancy_certificate_scaled {n : ℕ} (y : Fin (n+1) → ℚ) :
    (n.factorial : ℚ) * ((∑ i, y i) - ((n:ℚ)+1)*n/2) =
      -∑ h : Fin (n+1), ((-1:ℚ)^(n-h.val) * (n.choose h.val : ℚ)) *
        ∏ i, ((h.val:ℚ) - y i) := by
  have cert := numbered_occupancy_certificate y
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at cert
  rw [cert, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [← Helpers.occupancyWeight_scaled h]
  ring

/-- A polynomial identity for the balanced occupancy assertions in which each
coefficient on the product side is an explicitly signed binomial integer. -/
theorem occupancy_polynomial_certificate_scaled (n : ℕ) :
    MvPolynomial.C (n.factorial : ℚ) *
      ((∑ i, (MvPolynomial.X i : MvPolynomial (Fin (n+1)) ℚ)) -
        MvPolynomial.C (((n:ℚ)+1)*n/2)) =
      -∑ h : Fin (n+1), MvPolynomial.C ((-1:ℚ)^(n-h.val) * (n.choose h.val : ℚ)) *
        ∏ i, (MvPolynomial.C (h.val:ℚ) - MvPolynomial.X i) := by
  apply MvPolynomial.funext
  intro y
  simpa using occupancy_certificate_scaled y

end PEqualNP.Search
