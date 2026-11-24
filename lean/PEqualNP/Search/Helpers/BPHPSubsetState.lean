import PEqualNP.Search.Helpers.RowPatternEq
import PEqualNP.Search.Helpers.QPaddingCost

namespace PEqualNP.Search

open Helpers

/-- One of the first |H|+1 pigeons lies outside H. Each allowed pair of a pigeon
index and a label contributes a single integer equation. -/
noncomputable def subsetState {l : ℕ} (H : Finset (Fin l → Bool)) :
    QLine (Fin (2^l+1) × Fin l) :=
  (((Finset.univ : Finset (Fin (2^l+1))).filter (fun i => i.val ≤ H.card)) ×ˢ Hᶜ).toList.map
    (fun z => rowPatternEq z.1 z.2)

@[simp] theorem subsetState_univ (l : ℕ) :
    subsetState (Finset.univ : Finset (Fin l → Bool)) = [] := by simp [subsetState]

theorem mem_subsetState {l : ℕ} (H : Finset (Fin l → Bool)) (e : QEq (Fin (2^l+1) × Fin l)) :
    e ∈ subsetState H ↔ ∃ (i : Fin (2^l+1)) (h : Fin l → Bool),
      i.val ≤ H.card ∧ h ∉ H ∧ rowPatternEq i h = e := by
  simp only [subsetState,List.mem_map,Finset.mem_toList,Finset.mem_product,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_compl,Prod.exists]
  aesop

theorem subsetState_weight {l : ℕ} (H : Finset (Fin l → Bool)) :
    qWeight (subsetState H) ≤ (2^l+1)*2^l*(2+((2^l+1)*l+1)*2^l) := by
  have len : (subsetState H).length ≤ (2^l+1)*2^l := by
    simp only [subsetState,List.length_map,Finset.length_toList,Finset.card_product]
    apply Nat.mul_le_mul
    · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    · simpa using Finset.card_le_univ Hᶜ
  have bound := List.sum_le_length_nsmul ((subsetState H).map QEq.size) (2+((2^l+1)*l+1)*2^l)
    (by
      intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,h,_,_,rfl⟩ := (mem_subsetState H _).mp he
      exact rowPatternEq_size i h)
  exact (by simpa [qWeight] using bound : qWeight (subsetState H) ≤ (subsetState H).length * _).trans
    (Nat.mul_le_mul_right _ len)

end PEqualNP.Search
