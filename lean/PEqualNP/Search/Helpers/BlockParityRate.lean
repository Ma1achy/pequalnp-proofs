import PEqualNP.Search.Helpers.BlockLittleO
import Mathlib.Analysis.Complex.Exponential

namespace PEqualNP.Search.Helpers

open Asymptotics Filter

/-- Every fixed power of the block upper bound eventually lies below the parity lower bound. -/
theorem block_parity_rate (k : ℕ) : ∃ L : ℕ, ∀ l ≥ L,
    (2 : ℝ)^(k*(512*(l+2)*2^((l+1)/2))) ≤ Real.exp ((2 : ℝ)^l/(32768*(l : ℝ)^2)) := by
  let c : ℝ := 32768 * (k : ℝ) * 512 * 5
  have small := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 3
    (r₁ := (3/2 : ℝ)) (r₂ := 2) (by norm_num)).const_mul_left c
  obtain ⟨N, hN⟩ := eventually_atTop.mp (small.bound (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 1 N, fun l hl => ?_⟩
  obtain ⟨hl₁, hlN⟩ := max_le_iff.mp hl
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have cap := hN l hlN
  change ‖c * ((l : ℝ)^3 * (3/2 : ℝ)^l)‖ ≤ 1 * ‖(2 : ℝ)^l‖ at cap
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at cap
  let n := k*(512*(l+2)*2^((l+1)/2))
  have hn : (n : ℝ) = (k : ℝ)*512*(((l : ℝ)+2)*(2 : ℝ)^((l+1)/2)) := by
    dsimp [n]
    push_cast
    ring
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have exponent : (n : ℝ) ≤ (2 : ℝ)^l / (32768*(l : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hn]
    calc
      _ ≤ ((k : ℝ)*512*(5*((l : ℝ)*(3/2 : ℝ)^l))) * (32768*(l : ℝ)^2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (block_geometric_le l hl₁) (by positivity)) (by positivity)
      _ = c * ((l : ℝ)^3 * (3/2 : ℝ)^l) := by dsimp [c]; ring
      _ ≤ _ := cap
  have base : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  calc
    (2 : ℝ)^n ≤ (Real.exp 1)^n := pow_le_pow_left₀ (by norm_num) base _
    _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := Real.exp_le_exp.mpr exponent

end PEqualNP.Search.Helpers
