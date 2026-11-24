import PEqualNP.Search.Helpers.BPHPCollisionLine
import PEqualNP.Search.Helpers.QZeroRestriction
import PEqualNP.Search.Helpers.QZeroUnit

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}
  {Γ : Set (QLine V)} {L T : QLine V} {B B' : ℕ}

theorem QCanAdd.weakenTo (fromL : QCanAdd F Γ L B) (sub : ∀ e ∈ L, e ∈ T)
    (cap : B + qCost T ≤ B') : QCanAdd F Γ T B' := by
  intro ρ d hs
  obtain ⟨σ,ds,hm,cost⟩ := fromL ρ d hs
  refine ⟨T::σ, .weaken ds (List.mem_append_left _ hm) sub,List.mem_cons_self,?_⟩
  rw [qSize_cons]
  omega

end PEqualNP.Search.Helpers

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- Include the first m pigeon rows, so that restriction sets the last row to zero. -/
def keepRows (m l : ℕ) : (Fin m × Fin l) ↪ (Fin (m+1) × Fin l) :=
  rowEmbedding (Fin.castSuccEmb : Fin m ↪ Fin (m+1)) l

@[simp] theorem keepRows_lit {m l : ℕ} (i : Fin m) (b : Fin l) (s : Bool) :
    qZeroRestrict (keepRows m l) (litQEq ((i.castSucc,b),s)) = litQEq ((i,b),s) :=
  qZeroRestrict_lit (keepRows m l) (i,b) s

@[simp] theorem keepRows_lit_last {m l : ℕ} (b : Fin l) (s : Bool) :
    qZeroRestrict (keepRows m l) (litQEq ((Fin.last m,b),s)) = (0,if s then 1 else 0) := by
  apply qZeroRestrict_lit_off
  rintro ⟨⟨i,c⟩,he⟩
  exact Fin.castSucc_ne_last i (congrArg Prod.fst he)

/-- At least one pigeon occupies hole zero. Each disjunct equates the binary
value of one row to zero. -/
def zeroOccupancyLine (m l : ℕ) : QLine (Fin m × Fin l) :=
  List.ofFn (fun i : Fin m => ((binaryRowCoeff i,0) : QEq (Fin m × Fin l)))

theorem mem_zeroOccupancyLine {m l : ℕ} (i : Fin m) :
    (binaryRowCoeff i,0) ∈ zeroOccupancyLine m l := List.mem_ofFn.mpr ⟨i,rfl⟩

theorem zeroOccupancyLine_weight (m l : ℕ) :
    qWeight (zeroOccupancyLine m l) ≤ m*(1+m*l*(l+1)) := by
  have size (i : Fin m) : QEq.size ((binaryRowCoeff i,0) : QEq (Fin m × Fin l)) ≤ 1+m*l*(l+1) := by
    have bound (v : Fin m × Fin l) : (binaryRowCoeff i v).natAbs.size ≤ l+1 := by
      apply Nat.size_le.mpr
      by_cases h : v.1 = i
      · simpa [binaryRowCoeff,h] using (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_of_lt v.2.isLt))
      · simp [binaryRowCoeff,h]
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m × Fin l))) (fun v _ => bound v)
    simpa [QEq.size] using Nat.add_le_add_left total 1
  have h := List.sum_le_length_nsmul (l := (zeroOccupancyLine m l).map QEq.size) (1+m*l*(l+1))
    (by intro x hx; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
        exact size i)
  simpa [qWeight,zeroOccupancyLine] using h

def occupancyGuardCost (m l : ℕ) : ℕ :=
  400 + (4*l+4)*(10+m*l*2^l + l*2^l+8*l) + 2*(1+8*l) + qWeight (zeroOccupancyLine m l)

theorem restricted_bphp_axiom_weight {m l : ℕ} {C : PEqualNP.ProofComplexity.Clause (Fin (m+1) × Fin l)}
    (hC : C ∈ BPHP (m+1) l) :
    qWeight ((C.toList.map litQEq).map (qZeroRestrict (keepRows m l))) ≤ 8*l := by
  have h := qZeroRestrict_cost (keepRows m l) (C.toList.map litQEq)
  have bound := bphp_axiom_weight hC
  simp only [qCost] at h
  omega

end PEqualNP.Search
