import PEqualNP.Search.Helpers.BPHPCollisionTree
import PEqualNP.Search.Helpers.QAdaptiveRefutation

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- A coordinate search successively retains a majority class of pigeons.
Compiling this search gives a syntactic integer refutation at every width. -/
theorem BPHPTreeUpper :
  ∀ l : ℕ,
  let n := 2 ^ l
  let d := 2 * (n - 1) + l
  ∃ π : List (PEqualNP.Search.QLine (Fin (n + 1) × Fin l)),
    PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (n + 1) l) π ∧
    PEqualNP.Search.resLinQSize π ≤ 12 * (4*d + 1) * 2^d ∧
    PEqualNP.Search.resLinQSize π ≤ 36 * n^2 * 4^n := by
  intro l n d
  have positive : 0 < n := Nat.two_pow_pos l
  obtain ⟨t, height, correct⟩ := bphp_collision_tree l
  obtain ⟨π, ref, budget⟩ := qRefuteOfCoordSearch t correct
  have height' : t.depth ≤ d := height
  have cost : resLinQSize π ≤ 12 * (4*d + 1) * 2^d := budget.trans (by gcongr)
  refine ⟨π,ref,cost,cost.trans ?_⟩
  have logarithm : l ≤ n := Nat.lt_two_pow_self.le
  have factor : 12 * (4*d+1) ≤ 144*n := by dsimp [d]; omega
  have exponential : 2^d = 4^(n-1) * n := by
    change 2^(2*(n-1)+l) = _
    rw [pow_add,pow_mul]
    rfl
  have prev : 4^n = 4^(n-1)*4 := by
    rw [← pow_succ]; congr 1; omega
  rw [exponential,prev]
  calc
    _ ≤ (144*n)*(4^(n-1)*n) := Nat.mul_le_mul_right _ factor
    _ = _ := by ring

end PEqualNP.Search
