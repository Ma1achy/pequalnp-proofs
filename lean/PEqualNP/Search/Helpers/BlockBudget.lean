import PEqualNP.Search.Helpers.BlockTransitionCost
import Mathlib.Tactic

/-! Uniform encoded-cost estimates for count-vector states and their transitions. -/

namespace PEqualNP.Search.Helpers

/-- The number of groups and the bit cost of one state equation are absorbed by
five additional powers of the hole count plus two. -/
theorem blockStateWeightCap_le (u v : ℕ) :
    blockStateWeightCap u v ≤ (2^(u+v)+2)^(2^v+6) := by
  let n := 2^(u+v)
  let b := 2^v
  let d := n+2
  have hl : u+v ≤ n := (Nat.lt_two_pow_self (n := u+v)).le
  have hu : u ≤ n := (Nat.le_add_right u v).trans hl
  have hg : 2^u ≤ n := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  have budget : 1 + (n+1)*(u+v) + (n+1)*u ≤ d^3 := by
    calc
      _ ≤ 1 + (n+1)*n + (n+1)*n := by gcongr
      _ ≤ d^3 := by dsimp [d]; ring_nf; omega
  change 2^u * d^(b+1) * (1 + (n+1)*(u+v) + (n+1)*u) ≤ d^(b+6)
  calc
    _ ≤ d * d^(b+1) * d^3 := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by dsimp [d]; omega)) budget
    _ = d^(b+5) := by ring
    _ ≤ d^(b+6) := Nat.pow_le_pow_right (by dsimp [d]; omega) (by omega)

/-- A transition of the count-vector DAG fits in an explicit power whose
exponent is linear in the number of suffix values per group. -/
theorem blockTransitionCost_le (u v : ℕ) :
    blockTransitionCost u v ≤ (2^(u+v)+2)^(64*(2^v+1)) := by
  let l := u+v
  let n := 2^l
  let b := 2^v
  let d := n+2
  let X := d^(b+6)
  let C := blockStateWeightCap u v
  have hl : l ≤ n := (Nat.lt_two_pow_self (n := l)).le
  have hu : u ≤ l := by dsimp [l]; omega
  have hb : 1 ≤ b := Nat.one_le_two_pow
  have hn : 1 ≤ n := Nat.one_le_two_pow
  have dpos : 0 < d := by dsimp [d]; omega
  have dx : d ≤ X := by
    rw [show d = d^1 from (pow_one _).symm]
    exact Nat.pow_le_pow_right dpos (by omega : 1 ≤ b+6)
  have xbig : 10 ≤ X := calc
    10 ≤ 3^3 := by decide
    _ ≤ d^3 := Nat.pow_le_pow_left (by dsimp [d]; omega) _
    _ ≤ X := Nat.pow_le_pow_right dpos (by omega : 3 ≤ b+6)
  have nx : n ≤ X := (show n ≤ d by dsimp [d]; omega).trans dx
  have lx : l ≤ X := hl.trans nx
  have ux : u ≤ X := hu.trans lx
  have cx : C ≤ X := blockStateWeightCap_le u v
  change n * ((C+2)*(2+2*C+4*(4*l+C)) + (4*l+4)*(10+(n+1)*l+(u+l)+4*l) +
    (1+(4*l+C)) + 10*(C+4*l+1)) ≤ d^(64*(b+1))
  calc
    _ ≤ X * ((X+2)*(2+2*X+4*(4*X+X)) + (4*X+4)*(10+(X+1)*X+(X+X)+4*X) +
        (1+(4*X+X)) + 10*(X+4*X+1)) := by gcongr
    _ ≤ X^8 := by
      obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le xbig
      rw [hz]; ring_nf; omega
    _ = d^((b+6)*8) := (pow_mul d _ _).symm
    _ ≤ d^(64*(b+1)) := Nat.pow_le_pow_right dpos (by omega)

end PEqualNP.Search.Helpers
