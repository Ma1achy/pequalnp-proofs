import PEqualNP.Search.Helpers.BlockTupleEq
import PEqualNP.Search.Helpers.QPaddingCost
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Sigma

namespace PEqualNP.Search.Helpers

/-- Among the first k pigeons, some prefix group h has at least t(h)+1
members. One affine equation encodes each possible witnessing set of rows. -/
noncomputable def blockCapacityLine {m u : ℕ} (v k : ℕ) (t : (Fin u → Bool) → ℕ) :
    QLine (Fin m × Fin (u+v)) :=
  let rows := (Finset.univ : Finset (Fin m)).filter (fun i => i.val < k)
  (Finset.univ.sigma (fun h => rows.powersetCard (t h+1))).toList.map
    (fun z => blockTupleEq v z.2 z.1)

theorem mem_blockCapacityLine {m u : ℕ} (v k : ℕ) (t : (Fin u → Bool) → ℕ)
    (e : QEq (Fin m × Fin (u+v))) :
    e ∈ blockCapacityLine v k t ↔ ∃ (h : Fin u → Bool) (S : Finset (Fin m)),
      (∀ i ∈ S, i.val < k) ∧ S.card = t h+1 ∧ e = blockTupleEq v S h := by
  classical
  simp only [blockCapacityLine,List.mem_map,Finset.mem_toList,Finset.mem_sigma,Sigma.exists,
    Finset.mem_univ,true_and,Finset.mem_powersetCard,Finset.subset_iff,Finset.mem_filter]
  aesop

theorem blockCapacityLine_length {m u : ℕ} (v k : ℕ) (t : (Fin u → Bool) → ℕ) (b : ℕ)
    (cap : ∀ h, t h ≤ b) :
    (blockCapacityLine (m := m) v k t).length ≤ 2^u*(m+1)^(b+1) := by
  classical
  let rows := (Finset.univ : Finset (Fin m)).filter (fun i => i.val < k)
  have nr : rows.card ≤ m+1 := (Finset.card_le_univ rows).trans (by simp)
  have per (h : Fin u → Bool) : (rows.powersetCard (t h+1)).card ≤ (m+1)^(b+1) := by
    rw [Finset.card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left nr _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.succ_le_succ (cap h))))
  have total := Finset.sum_le_sum (s := Finset.univ) (fun h _ => per h)
  simpa only [blockCapacityLine,List.length_map,Finset.length_toList,Finset.card_sigma,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,rows] using total

theorem blockCapacityLine_weight {m u : ℕ} (v k : ℕ) (t : (Fin u → Bool) → ℕ) (b : ℕ)
    (cap : ∀ h, t h ≤ b) :
    qWeight (blockCapacityLine (m := m) v k t) ≤ 2^u*(m+1)^(b+1)*(1+m*(u+v)+m*u) := by
  let L := blockCapacityLine (m := m) v k t
  have costs := List.sum_le_length_nsmul (L.map QEq.size) (1+m*(u+v)+m*u) (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨h,S,_,_,rfl⟩ := (mem_blockCapacityLine v k t e).mp he
    exact blockTupleEq_size v S h)
  exact (show qWeight L ≤ L.length*(1+m*(u+v)+m*u) by simpa [qWeight] using costs).trans
    (Nat.mul_le_mul_right _ (blockCapacityLine_length v k t b cap))

end PEqualNP.Search.Helpers
