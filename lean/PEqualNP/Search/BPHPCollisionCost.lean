import PEqualNP.Search.BPHPCollisionTautology

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- The canonical line lists each ordered pair of distinct rows once. -/
theorem collisionLine_length_eq (m l : ℕ) :
    (collisionLine m l).length = m*(m-1) := by
  classical
  have pairs : (Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1 ≠ z.2) =
      (Finset.univ : Finset (Fin m)).offDiag := by ext; simp
  simp only [collisionLine, List.length_map, Finset.length_toList, pairs, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin, Nat.mul_sub_left_distrib, Nat.mul_one]

/-- A Boolean derivation of the canonical disjunction of collisions yields a
bit pigeonhole refutation of encoded size at most quartic in its own input size. -/
theorem bphp_collision_refutation_quartic {l : ℕ}
    {ρ : List (QLine (Fin (2^l+1) × Fin l))} (d : IsResLinQSynDerivation ∅ ρ)
    (mem : collisionLine (2^l+1) l ∈ ρ) :
    ∃ π, IsResLinQSynRefutation (BPHP (2^l+1) l) π ∧
      resLinQSize π ≤ 3300*(resLinQSize ρ)^4 := by
  let n := 2^l
  let m := n+1
  let S := resLinQSize ρ
  have hn : 0 < n := Nat.two_pow_pos l
  have d' : IsResLinQSynDerivation (BPHP m l) ρ := by
    clear mem S
    induction d with
    | nil => exact .nil
    | ax _ _ h _ _ => exact False.elim h
    | bool v _ ih => exact .bool v ih
    | res α β _ h₁ h₂ ih => exact .res α β ih h₁ h₂
    | weaken _ h sub ih => exact .weaken ih h sub
    | simp _ h ih => exact .simp ih h
  obtain ⟨π,ref,cost⟩ := bphp_collisionLine_to_refutation d' mem (fun _ he => mem_collisionLine.mp he)
  refine ⟨π,ref,cost.trans ?_⟩
  have len : m*n ≤ S := by
    have w := (qLength_le_weight (collisionLine m l)).trans
      ((Nat.le_add_left _ 1).trans (qCost_le_of_mem mem))
    simpa [m, collisionLine_length_eq] using w
  have sq : m^2 ≤ 2*S := calc
    m^2 = m*m := by ring
    _ ≤ m*(2*n) := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
    _ = 2*(m*n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 len
  have lm : m ≤ S := (Nat.le_mul_of_pos_right m hn).trans len
  have sixth : m^6 ≤ (2*S)^3 := by
    simpa [←pow_mul] using Nat.pow_le_pow_left sq 3
  have cube : m^3 ≤ (2*S)*S := by
    simpa [pow_succ] using Nat.mul_le_mul sq lm
  have pos : 0 < S := lt_of_lt_of_le (Nat.succ_pos _) lm
  have small : S ≤ S^4 := by simpa using Nat.pow_le_pow_right pos (by decide : 1 ≤ 4)
  change S + S * (400*m^6 + 21*m^3*S) ≤ 3300*S^4
  calc
    _ ≤ S^4 + S*(400*(2*S)^3 + 21*((2*S)*S)*S) := by gcongr
    _ ≤ _ := by ring_nf; omega

end PEqualNP.Search
