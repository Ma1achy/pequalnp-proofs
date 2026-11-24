import PEqualNP.Search.Helpers.BlockBudget
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace PEqualNP.Search.Helpers

/-- The exhaustive test of a terminal tuple only reads its b+1 rows. Its
2^((b+1)l) leaves and every copy of the remaining line fit this budget. -/
theorem block_terminal_budget (u v w len : ℕ) (hlen : len ≤ w) (hw : w ≤ blockStateWeightCap u v) :
    let l := u+v
    let n := 2^l
    let b := 2^v
    len * (2^((b+1)*l) * ((4*((b+1)*l)+3)*(10 + (n+1)*l + 6*((b+1)*l) + 8*l + w) +
      10*(w+4*((b+1)*l)+1))) ≤ (n+2)^(64*(b+1)) := by
  intro l n b
  let d := n+2
  let X := d^(b+6)
  have hn : 1 ≤ n := Nat.one_le_two_pow
  have hb : 1 ≤ b := Nat.one_le_two_pow
  have hb' : b ≤ n := Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have hl : l ≤ n := Nat.lt_two_pow_self.le
  have hd : 3 ≤ d := by dsimp [d]; omega
  have pos : 0 < d := by omega
  have cap : blockStateWeightCap u v ≤ X := blockStateWeightCap_le u v
  have dx : d ≤ X := by simpa using Nat.pow_le_pow_right pos (by omega : 1 ≤ b+6)
  have big : 128 ≤ X := calc
    128 ≤ 3^7 := by decide
    _ ≤ d^7 := Nat.pow_le_pow_left hd _
    _ ≤ X := Nat.pow_le_pow_right pos (by omega)
  have rows : b+1 ≤ X := (show b+1 ≤ d by dsimp [d]; omega).trans dx
  have m : n+1 ≤ X := (show n+1 ≤ d by dsimp [d]; omega).trans dx
  have lx : l ≤ X := by omega
  have wx := hw.trans cap
  have sz := hlen.trans wx
  have paths : 2^((b+1)*l) ≤ X := calc
    _ = n^(b+1) := by rw [Nat.mul_comm (b+1),pow_mul]
    _ ≤ d^(b+1) := Nat.pow_le_pow_left (by dsimp [d]; omega) _
    _ ≤ X := Nat.pow_le_pow_right pos (by omega)
  calc
    _ ≤ X * (X*((4*(X*X)+3)*(10+X*X+6*(X*X)+8*X+X)+10*(X+4*(X*X)+1))) := by gcongr
    _ ≤ X^10 := by
      obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le big
      rw [hz]
      ring_nf
      omega
    _ = d^((b+6)*10) := (pow_mul d (b+6) 10).symm
    _ ≤ _ := Nat.pow_le_pow_right pos (by omega)

end PEqualNP.Search.Helpers
