import PEqualNP.Search.BPHPOccupancyGuard

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

private theorem occupancy_bool {m l : ℕ} (hm : 0 < m) (hl : 0 < l) (v : Fin (m+1) × Fin l) :
    QCanAdd (BPHP m l) ∅ ([qZeroRestrict (keepRows m l) (litQEq (v,false)),
      qZeroRestrict (keepRows m l) (litQEq (v,true))] ++ zeroOccupancyLine m l)
      (occupancyGuardCost m l) := by
  rcases v with ⟨i,b⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩|rfl
  · simp only [keepRows_lit]
    let K := [litQEq ((i,b),false), litQEq ((i,b),true)]
    have h : QCanAdd (BPHP m l) ∅ K 9 := by
      intro ρ d _
      refine ⟨[K], .bool (i,b) d, List.mem_cons_self, ?_⟩
      have hf := qLit_size_le (i,b) false
      have ht := qLit_size_le (i,b) true
      change 1 + ((litQEq ((i,b),false)).size + ((litQEq ((i,b),true)).size + 0)) + 0 ≤ 9
      omega
    apply h.weakenTo (fun _ he => List.mem_append_left _ he)
    rw [qCost_append]
    have hf := qLit_size_le (i,b) false
    have ht := qLit_size_le (i,b) true
    change 9 + ((1 + ((litQEq ((i,b),false)).size + ((litQEq ((i,b),true)).size+0)))+_) ≤ _
    unfold occupancyGuardCost
    omega
  · simp only [keepRows_lit_last, Bool.false_eq_true, ite_false, ite_true]
    apply (qZeroUnit (F := BPHP m l) (⟨0,hm⟩,⟨0,hl⟩)).weakenTo
    · intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact List.mem_cons_self
    · have one : QEq.size ((0,1) : QEq (Fin m × Fin l)) = 2 := by simp [QEq.size]
      rw [qCost_append]
      change 380 + ((1 + ((0 : QEq (Fin m × Fin l)).size + (QEq.size ((0,1) : QEq (Fin m × Fin l))+0)))+_) ≤ _
      rw [qZero_size,one]
      unfold occupancyGuardCost
      omega

/-- A short refutation on n+1 pigeons yields a short proof on n pigeons that
hole zero is occupied, by fixing the last row to zero throughout the refutation. -/
theorem BPHPBalancedOccupancy {l : ℕ} (hl : 0 < l)
    {π : List (QLine (Fin (2^l+1) × Fin l))}
    (ref : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    ∃ ρ, IsResLinQSynDerivation (BPHP (2^l) l) ρ ∧ zeroOccupancyLine (2^l) l ∈ ρ ∧
      resLinQSize ρ ≤ (1000*(2^l+1)^4 + 2*resLinQSize π)*resLinQSize π := by
  let n := 2^l
  have hn : 0 < n := Nat.two_pow_pos l
  have hln : l ≤ n := Nat.lt_two_pow_self.le
  obtain ⟨ρ,d,h,cost⟩ := qZeroRestrictionDeduction (keepRows n l) (zeroOccupancyLine n l)
    (occupancyGuardCost n l) ref (fun _ hc => bphp_occupancy_guard hn hl hc) (occupancy_bool hn hl)
  refine ⟨ρ,d,h,cost.trans (Nat.mul_le_mul ?_ (qlength_le_size π))⟩
  have hw : qWeight (zeroOccupancyLine n l) ≤ n*(1+n*n*(n+1)) :=
    (zeroOccupancyLine_weight n l).trans (by gcongr)
  have rate : occupancyGuardCost n l + 4*qWeight (zeroOccupancyLine n l) ≤ 1000*(n+1)^4 := by
    unfold occupancyGuardCost
    change 400+(4*l+4)*(10+n*l*n+l*n+8*l)+2*(1+8*l)+qWeight _+4*qWeight _ ≤ _
    calc
      _ ≤ 400+(4*n+4)*(10+n*n*n+n*n+8*n)+2*(1+8*n)+n*(1+n*n*(n+1))+
          4*(n*(1+n*n*(n+1))) := by gcongr
      _ ≤ _ := by ring_nf; omega
  change occupancyGuardCost n l + 2*resLinQSize π + 4*qWeight (zeroOccupancyLine n l) ≤ 1000*(n+1)^4 + 2*resLinQSize π
  omega

end PEqualNP.Search
