import PEqualNP.Search.Helpers.RowPatternEq

namespace PEqualNP.Search.Helpers

/-- The equation whose maximum is attained exactly when all selected rows have
the prescribed prefix. The last v coordinates of each row have coefficient zero. -/
def blockTupleEq {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool) :
    QEq (Fin m × Fin (u+v)) :=
  (fun x => if x.1 ∈ S then
    if g : x.2.val < u then (if h ⟨x.2.val,g⟩ then 1 else -1) else 0
    else 0, (S.card : ℤ) * ∑ b, if h b then 1 else 0)

theorem blockTupleEq_insert {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool) (j : Fin m)
    (fresh : j ∉ S) :
    blockTupleEq v (insert j S) h = blockTupleEq v S h + blockTupleEq v {j} h := by
  apply Prod.ext
  · funext x
    by_cases isJ : x.1=j
    · simp [blockTupleEq,isJ,fresh]
    · simp [blockTupleEq,isJ]
  · simp [blockTupleEq,Finset.card_insert_of_notMem fresh,add_mul]

theorem blockTupleEq_off {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool)
    (x : Fin m × Fin (u+v)) (hne : x.1 ∉ S) : (blockTupleEq v S h).1 x = 0 := by
  simp [blockTupleEq,hne]

theorem blockTupleEq_off_bit {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool)
    (x : Fin m × Fin (u+v)) (hne : u ≤ x.2.val) : (blockTupleEq v S h).1 x = 0 := by
  simp [blockTupleEq,Nat.not_lt.mpr hne]

theorem blockTupleEq_coeff {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool)
    (x : Fin m × Fin (u+v)) : ((blockTupleEq v S h).1 x).natAbs ≤ 1 := by
  dsimp [blockTupleEq]
  split_ifs <;> decide

theorem blockTupleEq_rhs {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool) :
    (blockTupleEq v S h).2.natAbs ≤ S.card*u := by
  let H := Finset.univ.filter (fun b : Fin u => h b = true)
  have num : (∑ b : Fin u, if h b then (1:ℤ) else 0) = H.card := by simp [H]
  rw [show (blockTupleEq v S h).2 = (S.card:ℤ) * (H.card:ℤ) by simp [blockTupleEq,num],
    Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ ((Finset.card_le_univ H).trans (by simp))

theorem blockTupleEq_size {m u : ℕ} (v : ℕ) (S : Finset (Fin m)) (h : Fin u → Bool) :
    (blockTupleEq v S h).size ≤ 1+m*(u+v)+m*u := by
  have coeff (x : Fin m × Fin (u+v)) : ((blockTupleEq v S h).1 x).natAbs.size ≤ 1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (blockTupleEq_coeff v S h x)
  have costs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => coeff x)
  have length : S.card ≤ m := (Finset.card_le_univ _).trans (by simp)
  have rhs := (Nat.size_le.mpr Nat.lt_two_pow_self).trans ((blockTupleEq_rhs v S h).trans
    (Nat.mul_le_mul_right _ length))
  apply Nat.add_le_add _ rhs
  exact Nat.add_le_add_left (by simpa using costs) 1

end PEqualNP.Search.Helpers
