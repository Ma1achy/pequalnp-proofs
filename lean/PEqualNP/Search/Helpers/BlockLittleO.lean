import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

open Asymptotics Filter

/-- A geometric upper bound that absorbs the rounding in the exponent. -/
theorem block_geometric_le (l : ℕ) (hl : 1 ≤ l) :
    ((l : ℝ) + 2) * (2 : ℝ)^((l+1)/2) ≤ 5 * ((l : ℝ) * (3/2 : ℝ)^l) := by
  have half : (2 : ℝ)^((l+1)/2) ≤ (3/2 : ℝ)^(l+1) := calc
    _ ≤ ((3/2 : ℝ)^2)^((l+1)/2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (3/2 : ℝ)^(2*((l+1)/2)) := (pow_mul _ _ _).symm
    _ ≤ (3/2 : ℝ)^(l+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  calc
    _ ≤ ((l : ℝ)+2) * (3/2 : ℝ)^(l+1) := mul_le_mul_of_nonneg_left half (by positivity)
    _ = (((l : ℝ)+2)*(3/2)) * (3/2 : ℝ)^l := by rw [pow_succ]; ring
    _ ≤ (5*(l : ℝ)) * (3/2 : ℝ)^l := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The linear factor and the rounding in the half exponent are absorbed by `2^l`. -/
theorem block_little_o :
    (fun l : ℕ => ((l : ℝ) + 2) * (2 : ℝ)^((l + 1)/2)) =o[atTop]
      fun l : ℕ => (2 : ℝ)^l := by
  have exponential : (fun l : ℕ => (l : ℝ) * (3/2 : ℝ)^l) =o[atTop]
      fun l : ℕ => (2 : ℝ)^l := by
    simpa only [pow_one] using isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 1
      (r₁ := (3/2 : ℝ)) (r₂ := 2) (by norm_num)
  apply IsBigO.trans_isLittleO _ exponential
  apply IsBigO.of_bound 5
  filter_upwards [eventually_ge_atTop 1] with l hl
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact block_geometric_le l hl

end PEqualNP.Search.Helpers
