import PEqualNP.Search.Helpers.BPHPZeroOccupancy
import PEqualNP.Search.Helpers.QBuildAtPoint

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- After fixing the last row to zero, each input axiom follows from the surviving
collision axioms when padded by the disjunction that some surviving row is zero. -/
theorem bphp_occupancy_guard {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {C : ProofComplexity.Clause (Fin (m+1) × Fin l)} (hc : C ∈ BPHP (m+1) l) :
    QCanAdd (BPHP m l) ∅
      (((C.toList.map litQEq).map (qZeroRestrict (keepRows m l))) ++ zeroOccupancyLine m l)
      (occupancyGuardCost m l) := by
  classical
  let emb := keepRows m l
  let A := (C.toList.map litQEq).map (qZeroRestrict emb)
  let G := zeroOccupancyLine m l
  let T := A ++ G
  let work := (4*l+4)*(10+m*l*2^l + l*2^l + 8*l)
  have wA : qWeight A ≤ 8*l := restricted_bphp_axiom_weight hc
  have finish {K : QLine (Fin m × Fin l)} {B : ℕ} (start : QCanAdd (BPHP m l) ∅ K B)
      (sub : ∀ e ∈ K, e ∈ T) (small : B ≤ 400+work+(1+8*l)) :
      QCanAdd (BPHP m l) ∅ T (occupancyGuardCost m l) := by
    apply start.weakenTo sub
    rw [show qCost T = (1+qWeight A)+qWeight G from qCost_append A G]
    change _ ≤ 400+work+2*(1+8*l)+qWeight G
    omega
  obtain ⟨i,j,α,hij,hC⟩ := hc
  have entry (r : Fin (m+1)) (hr : r = i ∨ r = j) (b : Fin l) :
      qZeroRestrict emb (litQEq ((r,b), !α b)) ∈ A := by
    apply List.mem_map_of_mem
    apply List.mem_map_of_mem
    apply Finset.mem_toList.mpr
    rw [hC]
    rcases hr with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have kept (r : Fin m) (hr : r.castSucc = i ∨ r.castSucc = j) (b : Fin l) :
      litQEq ((r,b), !α b) ∈ A := by
    simpa only [emb,keepRows_lit] using entry _ hr b
  have withLast (r : Fin m) (hr : r.castSucc = i ∨ r.castSucc = j)
      (hLast : Fin.last m = i ∨ Fin.last m = j) :
      QCanAdd (BPHP m l) ∅ T (occupancyGuardCost m l) := by
    by_cases allZero : ∀ b, α b = false
    · let vs := (Finset.univ : Finset (Fin l)).toList.map (fun b => (r,b))
      let e : QEq (Fin m × Fin l) := (binaryRowCoeff r,0)
      have len : vs.length = l := by simp [vs]
      have ne : vs ≠ [] := by intro h; rw [h] at len; simp at len; omega
      have bound (u : Fin m × Fin l) : (e.1 u).natAbs ≤ 2^l := by
        have power := Nat.pow_le_pow_right (by decide : 0 < 2) u.2.isLt.le
        by_cases h : u.1 = r <;> simp [e,binaryRowCoeff,h,power]
      have off (u : Fin m × Fin l) (hu : u ∉ vs) : e.1 u = 0 := by
        have neRow : u.1 ≠ r := by
          intro h
          exact hu (List.mem_map.mpr ⟨u.2,by simp,Prod.ext h.symm rfl⟩)
        simp [e,binaryRowCoeff,neRow]
      have guard (u : Fin m × Fin l) (hu : u ∈ vs) : litQEq (u,!false) ∈ A := by
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp hu
        simpa [allZero] using kept r hr b
      have start : QCanAdd (BPHP m l) ∅ (e :: A) work := by
        intro ρ d _
        obtain ⟨s,ds,hs,cost⟩ := qBuildAtPoint vs (fun _ => false) A (2^l) e ne bound off
          (by simp [QEq.Holds,e]) guard d
        refine ⟨s,ds,hs,cost.trans ?_⟩
        simp only [len,Fintype.card_prod,Fintype.card_fin]
        change (4*l+4)*(10+m*l*2^l+(0+l*2^l)+qWeight A) ≤ _
        simp only [Nat.zero_add]
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left wA _)
      apply finish start _ (by omega)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact List.mem_append_right _ (mem_zeroOccupancyLine r)
      · exact List.mem_append_left _ h
    · obtain ⟨b,hb⟩ := not_forall.mp allZero
      have yes : α b = true := by cases h : α b <;> simp_all
      have zero : (0 : QEq (Fin m × Fin l)) ∈ A := by
        change ((0, (0 : ℤ)) : QEq (Fin m × Fin l)) ∈ A
        simpa only [emb,keepRows_lit_last,yes,Bool.not_true,Bool.false_eq_true,ite_false] using entry _ hLast b
      let v : Fin m × Fin l := (⟨0,hm⟩,⟨0,hl⟩)
      apply finish (qZeroUnit v) _ (by omega)
      intro z hz
      obtain rfl := List.mem_singleton.mp hz
      exact List.mem_append_left _ zero
  rcases Fin.eq_castSucc_or_eq_last i with ⟨r,rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨s,rfl⟩ | rfl
    · let D := Finset.univ.image (fun b : Fin l => ((r,b), !α b)) ∪
          Finset.univ.image (fun b : Fin l => ((s,b), !α b))
      have hD : D ∈ BPHP m l := ⟨r,s,α,fun h => hij (congrArg Fin.castSucc h),rfl⟩
      let K := D.toList.map litQEq
      have start : QCanAdd (BPHP m l) ∅ K (1+8*l) := by
        intro ρ d _
        refine ⟨[K], .ax D d hD (by intro z; simp [K,eq_comm]),List.mem_cons_self,?_⟩
        change 1 + qWeight K + 0 ≤ _
        simpa using Nat.add_le_add_left (bphp_axiom_weight hD) 1
      apply finish start _ (by omega)
      intro z hz
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
      rcases Finset.mem_union.mp (Finset.mem_toList.mp ht) with h | h
      · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp h
        exact List.mem_append_left _ (kept r (Or.inl rfl) b)
      · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp h
        exact List.mem_append_left _ (kept s (Or.inr rfl) b)
    · exact withLast r (Or.inl rfl) (Or.inr rfl)
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨s,rfl⟩ | rfl
    · exact withLast s (Or.inr rfl) (Or.inl rfl)
    · exact False.elim (hij rfl)

end PEqualNP.Search
