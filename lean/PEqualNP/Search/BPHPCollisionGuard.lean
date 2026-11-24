import PEqualNP.Search.Helpers.BPHPCollisionLine
import PEqualNP.Search.Helpers.QBuildAtPoint
import PEqualNP.Search.Helpers.QCoordinateCases

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- Encoded cost of deriving one guarded collision clause from the Boolean axioms. -/
def collisionGuardCost (m l : ℕ) : ℕ :=
  (8*l+4)*(10 + m*l*2^l + 2*l*2^l + 8*l) + (1 + 8*l + m^2*(1+m*l*(l+1)))

/-- When the two rows match the forbidden hole, their binary row numbers agree.
The Boolean axioms derive this row equality disjoined with the input clause. A
final weakening includes all the other row equalities in the collision line. -/
theorem bphp_collision_guard {m l : ℕ} (hl : 0 < l)
    {C : PEqualNP.ProofComplexity.Clause (Fin m × Fin l)} (hC : C ∈ BPHP m l) :
    QCanAdd ∅ ∅ ((C.toList.map litQEq) ++ collisionLine m l) (collisionGuardCost m l) := by
  classical
  let G := C.toList.map litQEq
  have wG : qWeight G ≤ 8*l := bphp_axiom_weight hC
  obtain ⟨i,j,α,hij,hCv⟩ := hC
  let S := ({i,j} : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin l))
  let vs := S.toList
  let a := fun v : Fin m × Fin l => α v.2
  have len : vs.length = 2*l := by simp [vs,S,hij,Finset.card_product]
  have ne : vs ≠ [] := by
    intro h
    rw [h] at len
    simp at len
    omega
  have off (v : Fin m × Fin l) (hv : v ∉ vs) : (binaryRowEq i j).1 v = 0 := by
    apply binaryRowEq_off
    · intro h
      exact hv (by simp [vs,S,h])
    · intro h
      exact hv (by simp [vs,S,h])
  have guard (v : Fin m × Fin l) (hv : v ∈ vs) : litQEq (v, !a v) ∈ G := by
    apply List.mem_map.mpr
    refine ⟨(v,!a v), Finset.mem_toList.mpr ?_, rfl⟩
    rcases v with ⟨u,b⟩
    have hu : u = i ∨ u = j := by simpa [vs,S] using hv
    rw [hCv]
    rcases hu with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  have good : QEq.Holds a (binaryRowEq i j) := (binaryRowEq_holds a i j).mpr (fun _ => rfl)
  intro ρ d _
  obtain ⟨σ,ds,he,cost⟩ := qBuildAtPoint vs a G (2^l) (binaryRowEq i j) ne
    (binaryRowEq_abs_bound i j) off good guard d
  let T := G ++ collisionLine m l
  have sub (x : QEq (Fin m × Fin l)) (hx : x ∈ binaryRowEq i j :: G) : x ∈ T := by
    rcases List.mem_cons.mp hx with rfl | h
    · exact List.mem_append_right _ (mem_collisionLine.mpr ⟨i,j,hij,rfl⟩)
    · exact List.mem_append_left _ h
  refine ⟨T :: σ, .weaken ds (List.mem_append_left ρ he) sub, List.mem_cons_self, ?_⟩
  have work : resLinQSize σ ≤ (8*l+4)*(10 + m*l*2^l + 2*l*2^l + 8*l) := by
    apply cost.trans
    rw [len, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    change (4*(2*l)+4)*(10 + m*l*2^l + (0+2*l*2^l) + qWeight G) ≤ _
    simp only [Nat.zero_add, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left wG _)
  have last : qCost T ≤ 1 + 8*l + m^2*(1+m*l*(l+1)) := by
    rw [show qCost T = 1 + qWeight G + qWeight (collisionLine m l) by simp [T,qCost,Nat.add_assoc]]
    exact Nat.add_le_add (Nat.add_le_add_left wG _) (collisionLine_weight m l)
  simpa [qSize_cons, collisionGuardCost, Nat.add_comm] using Nat.add_le_add last work

end PEqualNP.Search
