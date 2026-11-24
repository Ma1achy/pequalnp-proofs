import PEqualNP.Defs.ProofComplexityBit
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Search.Helpers

/-- Allowed counts for each prefix of length u. Each prefix has 2^v suffixes. -/
abbrev BlockCounts (u v : ℕ) := (Fin u → Bool) → Fin (2^v+1)

/-- The capacity specified by a vector, summed across all prefixes. -/
def blockRank {u v : ℕ} (t : BlockCounts u v) : ℕ := ∑ h, (t h).val

/-- Decrease the allowance of one prefix by one. -/
def blockPred {u v : ℕ} (t : BlockCounts u v) (h : Fin u → Bool) : BlockCounts u v :=
  Function.update t h ⟨(t h).val - 1, by have := (t h).isLt; omega⟩

@[simp] theorem blockPred_same {u v : ℕ} (t : BlockCounts u v) (h : Fin u → Bool) :
    (blockPred t h h).val = (t h).val - 1 := by simp [blockPred]

theorem blockPred_other {u v : ℕ} (t : BlockCounts u v) (h k : Fin u → Bool) (ne : k ≠ h) :
    blockPred t h k = t k := Function.update_of_ne ne _ _

theorem blockRank_pred {u v : ℕ} (t : BlockCounts u v) (h : Fin u → Bool) (pos : 0 < (t h).val) :
    blockRank (blockPred t h) + 1 = blockRank t := by
  classical
  unfold blockRank
  have atH : (blockPred t h h).val + 1 = (t h).val := by rw [blockPred_same]; omega
  calc
    _ = (∑ k, ((blockPred t h k).val + (if k = h then 1 else 0))) := by simp [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases eq : k = h
      · subst k; simpa using atH
      · simp [eq,blockPred_other t h k eq]

theorem blockRank_le {u v : ℕ} (t : BlockCounts u v) : blockRank t ≤ 2^(u+v) := by
  have b := Finset.sum_le_sum (s := Finset.univ) (fun h _ => Nat.le_of_lt_succ (t h).isLt)
  simpa [blockRank,pow_add] using b

/-- The terminal state allows every block its full capacity. -/
def blockFull (u v : ℕ) : BlockCounts u v := fun _ => Fin.last (2^v)

@[simp] theorem blockRank_full (u v : ℕ) : blockRank (blockFull u v) = 2^(u+v) := by
  simp [blockRank,blockFull,pow_add]

theorem blockCounts_card (u v : ℕ) : Fintype.card (BlockCounts u v) = (2^v+1)^(2^u) := by
  simp [BlockCounts]

end PEqualNP.Search.Helpers
