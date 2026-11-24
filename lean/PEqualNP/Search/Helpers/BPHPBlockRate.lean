import Mathlib.Tactic

/-! Arithmetic bounds for a balanced split of the bits of a binary label.
The block construction uses `2^(l/2)` blocks and `2^(l-l/2)` holes per block. -/

namespace PEqualNP.Search.Helpers

/-- Convert the construction's power-of-the-hole-count envelope to an explicit
base-two bound, valid also for the zero-bit instance. -/
theorem bphp_block_envelope (l : ℕ) :
    (2^l+2)^(128*(2^(l-l/2) + 2^(l/2) + 2)) ≤
      2^(512*(l+2)*2^((l+1)/2)) := by
  have split : l-l/2 = (l+1)/2 := by omega
  have g_le : 2^(l/2) ≤ 2^((l+1)/2) := Nat.pow_le_pow_right (by decide) (by omega)
  have b_pos := Nat.one_le_two_pow (n := (l+1)/2)
  have base : 2^l+2 ≤ 2^(l+2) := by
    rw [pow_add]
    have := Nat.one_le_two_pow (n := l)
    omega
  have scale : 128*(2^(l-l/2) + 2^(l/2) + 2) ≤ 512*2^((l+1)/2) := by
    rw [split]; omega
  calc
    _ ≤ (2^(l+2))^(128*(2^(l-l/2) + 2^(l/2) + 2)) := Nat.pow_le_pow_left base _
    _ = 2^((l+2)*(128*(2^(l-l/2) + 2^(l/2) + 2))) := (pow_mul ..).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      calc
        _ ≤ (l+2)*(512*2^((l+1)/2)) := Nat.mul_le_mul_left _ scale
        _ = _ := by ring

private theorem square_le_two_pow (x : ℕ) (hx : 4 ≤ x) : x*x ≤ 2^x := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    rw [pow_succ]
    have m : 0 ≤ (x:ℤ) - 4 := by omega
    have sq := mul_nonneg m m
    nlinarith

/-- Explicit little-o bound for the exponent relative to the number of holes.
Beyond the displayed threshold the exponent is at most `2^l / k` for every
positive `k`. -/
theorem bphp_block_exponent_rate (C k l : ℕ) (width : 8*(k*C+1) ≤ l) :
    k * (C*(l+2)*2^((l+1)/2)) ≤ 2^l := by
  let t := l/2
  have large : 4*(k*C+1) ≤ t := by dsimp [t]; omega
  have up : l+2 ≤ 4*t := by dsimp [t] at *; omega
  have prod : (k*C)*(l+2) ≤ t*t := by
    calc
      _ ≤ (k*C)*(4*t) := Nat.mul_le_mul_left _ up
      _ = (4*(k*C))*t := by ring
      _ ≤ t*t := Nat.mul_le_mul_right _ (by omega)
  have split : t + (l+1)/2 = l := by dsimp [t]; omega
  calc
    _ = ((k*C)*(l+2))*2^((l+1)/2) := by ring
    _ ≤ (2^t)*2^((l+1)/2) :=
      Nat.mul_le_mul_right _ (prod.trans (square_le_two_pow t (by omega)))
    _ = _ := by rw [← pow_add, split]

end PEqualNP.Search.Helpers
