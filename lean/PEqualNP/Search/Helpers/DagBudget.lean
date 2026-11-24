import PEqualNP.Library.Helpers.BGSDiagonal

/-! The binary-PHP unfolded-tree lower bound dominates simultaneous polynomial
budgets for proof size in the number of holes and for reuse depth in the bit width. -/

namespace PEqualNP.Search.Helpers

open Polynomial PEqualNP.Library.Helpers

/-- At arbitrarily large widths, the unfolded-tree lower bound exceeds the bound from
a proof of size at most p(2^l) and reuse depth at most q(l). -/
theorem exists_width_beating_dag_budgets (p q : Polynomial ℕ) (N : ℕ) :
    ∃ l : ℕ, N ≤ l ∧ 17 ≤ l ∧
      2 * p.eval (2 ^ l) * (2 * p.eval (2 ^ l) + 1) ^ q.eval l <
        2 ^ (2 ^ ((l - 17) / 6)) := by
  obtain ⟨a, d, hp⟩ := poly_le_monomial p
  let width : Polynomial ℕ := 6 * X + 17
  let expo : Polynomial ℕ := (C (a + 2) + C d * width) * (q.comp width + 1)
  obtain ⟨m, hm, hsmall⟩ := BGS.exists_stage_len expo N
  let l := 6 * m + 17
  let e := a + d * l
  have hsmall' : (e + 2) * (q.eval l + 1) < 2 ^ m := by
    simpa [expo, width, l, e, eval_comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsmall
  have hs : p.eval (2 ^ l) ≤ 2 ^ e := by
    calc
      _ ≤ a * (2 ^ l) ^ d := hp _ Nat.one_le_two_pow
      _ ≤ 2 ^ a * (2 ^ l) ^ d := Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ e := by rw [← pow_mul, ← pow_add]; simp [e, Nat.mul_comm]
  have hbase : 2 * p.eval (2 ^ l) + 1 ≤ 2 ^ (e + 2) := by
    have hpos : 0 < 2 ^ e := by positivity
    have h4 : 2 ^ (e + 2) = 2 ^ e * 4 := pow_add (2 : ℕ) e 2
    omega
  refine ⟨l, by dsimp [l]; omega, by dsimp [l]; omega, ?_⟩
  have index : (l - 17) / 6 = m := by dsimp [l]; omega
  rw [index]
  calc
    _ ≤ 2 ^ (e + 2) * (2 ^ (e + 2)) ^ q.eval l :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ ((e + 2) * (q.eval l + 1)) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ < 2 ^ (2 ^ m) := Nat.pow_lt_pow_right (by decide) hsmall'

end PEqualNP.Search.Helpers
