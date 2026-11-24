import PEqualNP.Search.Helpers.BinaryRowEquation

namespace PEqualNP.Search.Helpers

/-- The signed sum of a row equals its maximum exactly when it matches the
prescribed bits. A prescribed true bit contributes coefficient 1 and a false
bit contributes coefficient −1. -/
def rowPatternEq {m l : ℕ} (i : Fin m) (α : Fin l → Bool) : QEq (Fin m × Fin l) :=
  (fun v => if v.1 = i then (if α v.2 then 1 else -1) else 0,
   ∑ b, if α b then 1 else 0)

theorem rowPatternEq_holds {m l : ℕ} (a : Fin m × Fin l → Bool) (i : Fin m) (α : Fin l → Bool) :
    QEq.Holds a (rowPatternEq i α) ↔ ∀ b, a (i,b) = α b := by
  classical
  let w (b : Fin l) : ℤ := if α b then 1 else -1
  let bit (b : Bool) : ℤ := if b then 1 else 0
  let err (b : Fin l) := bit (α b) - w b * bit (a (i,b))
  have pos (b : Fin l) : 0 ≤ err b := by
    cases h : α b <;> cases k : a (i,b) <;> simp [err,bit,w,h,k]
  have zero (b : Fin l) : err b = 0 ↔ a (i,b) = α b := by
    cases h : α b <;> cases k : a (i,b) <;> simp [err,bit,w,h,k]
  have integral : (∑ v : Fin m × Fin l, (rowPatternEq i α).1 v * bit (a v)) =
      ∑ b, w b * bit (a (i,b)) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single i]
    · simp [rowPatternEq,w]
    · intro j _ hji
      simp [rowPatternEq,hji]
    · simp
  change (∑ v : Fin m × Fin l, (rowPatternEq i α).1 v * bit (a v)) = (∑ b, bit (α b)) ↔ _
  rw [integral]
  have gap : (∑ b, err b) = (∑ b, bit (α b)) - ∑ b, w b * bit (a (i,b)) := Finset.sum_sub_distrib ..
  constructor
  · intro H b
    have total : ∑ b, err b = 0 := by rw [gap,H,sub_self]
    exact (zero b).mp ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => pos b)).mp total b (Finset.mem_univ b))
  · intro H
    have total : ∑ b, err b = 0 := Finset.sum_eq_zero (fun b _ => (zero b).mpr (H b))
    exact (sub_eq_zero.mp (gap.symm.trans total)).symm

theorem rowPatternEq_off {m l : ℕ} (i : Fin m) (α : Fin l → Bool) (v : Fin m × Fin l) (ne : v.1 ≠ i) :
    (rowPatternEq i α).1 v = 0 := by simp [rowPatternEq,ne]

theorem rowPatternEq_coeff {m l : ℕ} (i : Fin m) (α : Fin l → Bool) (v : Fin m × Fin l) :
    ((rowPatternEq i α).1 v).natAbs ≤ 2^l := by
  have h := Nat.two_pow_pos l
  by_cases hv : v.1 = i <;> cases k : α v.2 <;> simp [rowPatternEq,hv,k] <;> omega

theorem rowPatternEq_rhs {m l : ℕ} (i : Fin m) (α : Fin l → Bool) : (rowPatternEq i α).2.natAbs ≤ 2^l := by
  let S := Finset.univ.filter (fun b : Fin l => α b = true)
  have sum : (rowPatternEq i α).2 = (S.card : ℤ) := by
    simp [rowPatternEq,S]
  rw [sum,Int.natAbs_natCast]
  exact (Finset.card_le_univ S).trans (by simpa using (Nat.lt_two_pow_self (n := l)).le)

theorem rowPatternEq_size {m l : ℕ} (i : Fin m) (α : Fin l → Bool) :
    (rowPatternEq i α).size ≤ 2+(m*l+1)*2^l := by
  have cost (v : Fin m × Fin l) : ((rowPatternEq i α).1 v).natAbs.size ≤ 2^l :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (rowPatternEq_coeff i α v)
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => cost v)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul] at sum
  have rhs : (rowPatternEq i α).2.natAbs.size ≤ 2^l :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (rowPatternEq_rhs i α)
  unfold QEq.size
  rw [Nat.add_mul,Nat.one_mul]
  calc
    _ ≤ 1 + (m*l * 2^l) + 2^l := Nat.add_le_add (Nat.add_le_add_left sum 1) rhs
    _ ≤ _ := by omega

end PEqualNP.Search.Helpers
