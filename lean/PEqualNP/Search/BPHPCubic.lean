import PEqualNP.Search.Helpers.BPHPEssential
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-! A degree-three restriction of L-alg-006 for the posted syntactic integer proof system. -/

namespace PEqualNP.Search

private theorem cubic_eval_le (p : Polynomial ℕ) (hp : p.natDegree ≤ 3)
    {n : ℕ} (hn : 0 < n) : p.eval n ≤ p.eval 1 * n ^ 3 := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range (p := p) 1]
  simp only [one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiDegree := Finset.mem_range.mp hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by omega))

private theorem cubic_lt_axiom_cost (p : Polynomial ℕ) (hp : p.natDegree ≤ 3)
    {l n : ℕ} (hl : p.eval 1 < l) (hn : 0 < n) :
    p.eval n < (2 * l + 1) * (n * (n + 1).choose 2) := by
  have pairs : (n + 1).choose 2 * 2 = (n + 1) * n := by
    simpa using Nat.choose_succ_right_eq (n + 1) 1
  calc
    p.eval n ≤ p.eval 1 * n ^ 3 := cubic_eval_le p hp hn
    _ < l * n ^ 3 := Nat.mul_lt_mul_of_pos_right hl (Nat.pow_pos hn)
    _ ≤ l * (n * ((n + 1) * n)) := by
      apply Nat.mul_le_mul_left
      calc
        n ^ 3 = n * (n * n) := by ring
        _ ≤ n * ((n + 1) * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
    _ = (2 * l) * (n * (n + 1).choose 2) := by rw [← pairs]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- Every polynomial of degree at most three is eventually smaller than every
syntactic integer R(lin) refutation of binary PHP, measured in the posted bit size.
An explicit sufficient threshold for the bit width is the sum of the coefficients plus one. -/
theorem BPHPCubic (p : Polynomial ℕ) (hp : p.natDegree ≤ 3)
    {l : ℕ} (hl : p.eval 1 < l) {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π) :
    p.eval (2 ^ l) < resLinQSize π := by
  have hcost := Helpers.bphp_syn_size_lower_bound (l := l) (by omega) hπ
  apply (cubic_lt_axiom_cost p hp hl (n := 2 ^ l) (by positivity)).trans_le
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcost

end PEqualNP.Search
