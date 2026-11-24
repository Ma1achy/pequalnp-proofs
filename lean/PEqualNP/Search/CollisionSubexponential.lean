import PEqualNP.Search.BPHPBlockUpper
import PEqualNP.Search.BPHPCollisionTautology

namespace PEqualNP.Search

/-- The disjunction of all collisions itself has a subexponential syntactic
derivation from Boolean axioms alone at each positive width. -/
theorem CollisionSubexponential :
    ∀ l : ℕ, 0 < l →
      let G := ((Finset.univ : Finset (Fin (2^l+1) × Fin (2^l+1))).filter (fun z => z.1 ≠ z.2)).toList.map
        (fun z => ((fun v : Fin (2^l+1) × Fin l =>
          (if v.1 = z.1 then (2 : ℤ)^v.2.val else 0) -
          (if v.1 = z.2 then (2 : ℤ)^v.2.val else 0)), (0 : ℤ)))
      ∃ ρ : List (QLine (Fin (2^l+1) × Fin l)), IsResLinQSynDerivation ∅ ρ ∧ G ∈ ρ ∧
        resLinQSize ρ ≤ 2^(522*(l+2)*2^((l+1)/2)) := by
  intro l hl G
  obtain ⟨π,ref,size⟩ := BPHPBlockUpper l
  obtain ⟨ρ,d,mem,cost⟩ := bphp_refutation_to_collision_tautology hl ref
  refine ⟨ρ,d,mem,cost.trans ?_⟩
  let s := 2^((l+1)/2)
  have add : 2^l+1 ≤ 2^(l+1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := l)
    omega
  have pre : 1000*(2^l+1)^5 ≤ 2^(10 + (l+1)*5) := by
    rw [pow_add,pow_mul]
    exact Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left add _)
  have loss : 10+(l+1)*5 ≤ 10*(l+2)*s :=
    (show 10+(l+1)*5 ≤ 10*(l+2) by omega).trans
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  calc
    _ ≤ 2^(10+(l+1)*5) * 2^(512*(l+2)*s) := Nat.mul_le_mul pre size
    _ = 2^((10+(l+1)*5) + 512*(l+2)*s) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
      _ ≤ 10*(l+2)*s + 512*(l+2)*s := Nat.add_le_add_right loss _
      _ = 522*(l+2)*s := by ring)

end PEqualNP.Search
