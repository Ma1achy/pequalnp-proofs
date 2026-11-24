import PEqualNP.Search.Helpers.BinaryRowEquation
import PEqualNP.Search.Helpers.QCoordinateCut
import PEqualNP.Defs.ProofComplexityBit

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- The disjunction of row equalities, with one occurrence for each ordered pair
of distinct pigeons. -/
noncomputable def collisionLine (m l : ℕ) : QLine (Fin m × Fin l) :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2)).toList.map
    (fun z => binaryRowEq z.1 z.2)

theorem mem_collisionLine {m l : ℕ} {e : QEq (Fin m × Fin l)} :
    e ∈ collisionLine m l ↔ ∃ i j : Fin m, i ≠ j ∧ e = binaryRowEq i j := by
  simp only [collisionLine, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists]
  constructor <;> rintro ⟨i,j,h,eq⟩ <;> exact ⟨i,j,h,eq.symm⟩

theorem collisionLine_length (m l : ℕ) : (collisionLine m l).length ≤ m^2 := by
  simp only [collisionLine, List.length_map, Finset.length_toList]
  simpa [pow_two] using Finset.card_le_card (Finset.filter_subset
    (fun z : Fin m × Fin m => z.1 ≠ z.2) Finset.univ)

theorem collisionLine_weight (m l : ℕ) :
    qWeight (collisionLine m l) ≤ m^2 * (1 + m*l*(l+1)) := by
  have eqSize (i j : Fin m) : (binaryRowEq (l := l) i j).size ≤ 1 + m*l*(l+1) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m × Fin l)))
      (fun v _ => Nat.size_le.mpr ((binaryRowEq_abs_bound i j v).trans_lt
        (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self l))))
    change 1 + (∑ v, ((binaryRowEq i j).1 v).natAbs.size) + (0 : ℤ).natAbs.size ≤ _
    simpa using Nat.add_le_add_left h 1
  have bound := List.sum_le_length_nsmul (l := (collisionLine m l).map QEq.size) (1 + m*l*(l+1))
    (by
      intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,j,_,rfl⟩ := mem_collisionLine.mp he
      exact eqSize i j)
  exact (by simpa [qWeight] using bound :
    qWeight (collisionLine m l) ≤ (collisionLine m l).length * (1+m*l*(l+1))).trans
    (Nat.mul_le_mul_right _ (collisionLine_length m l))

theorem bphp_axiom_weight {m l : ℕ} {C : PEqualNP.ProofComplexity.Clause (Fin m × Fin l)} (hC : C ∈ BPHP m l) :
    qWeight (C.toList.map litQEq) ≤ 8*l := by
  have width : C.card ≤ 2*l := by
    obtain ⟨i,j,a,_,rfl⟩ := hC
    exact (Finset.card_union_le ..).trans (by
      have bd (k : Fin m) := Finset.card_image_le (s := Finset.univ)
        (f := fun b : Fin l => ((k,b), !a b))
      simpa [two_mul] using Nat.add_le_add (bd i) (bd j))
  have h := List.sum_le_length_nsmul (l := (C.toList.map litQEq).map QEq.size) 4 (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
    exact qLit_size_le t.1 t.2)
  change ((C.toList.map litQEq).map QEq.size).sum ≤ _
  simp at h ⊢
  omega

end PEqualNP.Search
