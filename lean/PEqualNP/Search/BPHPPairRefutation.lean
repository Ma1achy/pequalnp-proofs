import PEqualNP.Search.BPHPPermutationReduction

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- To refute a binary pigeonhole instance it suffices to refute each local
assignment on two fixed unequal rows. At a point where they differ we use a
previously derived unit with small coefficients on these rows. -/
theorem bphp_refute_from_local_units {m l : ℕ} (i j : Fin m) (hne : i ≠ j) (P : ℕ)
    (units : ∀ a : Fin m × Fin l → Bool, (∃ k, a (i,k) ≠ a (j,k)) →
      ∃ (e : QEq (Fin m × Fin l)) (π : List (QLine (Fin m × Fin l))),
        IsResLinQSynDerivation (BPHP m l) π ∧ [e] ∈ π ∧ resLinQSize π ≤ P ∧
        (∀ v, (e.1 v).natAbs ≤ 1) ∧ e.2 = 0 ∧
        (∀ v, v.1 ≠ i → v.1 ≠ j → e.1 v = 0) ∧ ¬QEq.Holds a e) :
    ∃ ρ, IsResLinQSynRefutation (BPHP m l) ρ ∧
      resLinQSize ρ ≤ 2^(2*l) * (P + (8*l+3)*(10+m*l+10*l) + 10*(8*l+1)) := by
  classical
  let S := ({i,j} : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin l))
  let vs := S.toList
  let cap := P + (8*l+3)*(10+m*l+10*l)
  have len : vs.length = 2*l := by simp [vs,S,hne,Finset.card_product]
  have leaves (a : Fin m × Fin l → Bool) :
      QCanAdd (BPHP m l) ∅ ((vs.map (fun v => litQEq (v,a v))).reverse ++ []) cap := by
    let G := (vs.map (fun v => litQEq (v,a v))).reverse
    simp only [List.append_nil]
    intro ρ d _
    change ∃ σ, IsResLinQSynDerivation _ (σ ++ ρ) ∧ G ∈ σ ∧ resLinQSize σ ≤ cap
    have memG (e : QEq (Fin m × Fin l)) :
        e ∈ G ↔ ∃ v ∈ S, litQEq (v,a v) = e := by simp [G,vs]
    have weight : qWeight G ≤ 8*l := by
      unfold qWeight
      apply le_trans (List.sum_le_length_nsmul (G.map QEq.size) 4 ?_)
      · simp [G,len]
        omega
      · intro w hw
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
        obtain ⟨v, _, rfl⟩ := (memG e).mp he
        exact qLit_size_le v _
    by_cases same : ∀ k, a (i,k) = a (j,k)
    · let C := S.image (fun v => (v,a v))
      have ax : C ∈ BPHP m l := bphp_same_row_axiom i j hne a same
      have rep (e) : e ∈ G ↔ ∃ t ∈ C, e = litQEq t := by
        rw [memG]
        constructor
        · rintro ⟨v,hv,rfl⟩
          exact ⟨_,Finset.mem_image_of_mem _ hv,rfl⟩
        · rintro ⟨t,ht,rfl⟩
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
          exact ⟨v,hv,rfl⟩
      refine ⟨[G],d.ax C ax rep,List.mem_cons_self,?_⟩
      change 1 + qWeight G + 0 ≤ _
      have factor : 1 ≤ 8*l+3 := by omega
      have bound := Nat.mul_le_mul_right (10+m*l+10*l) factor
      dsimp [cap]
      omega
    · let point := fun v => !(a v)
      have diff : ∃ k, point (i,k) ≠ point (j,k) := by
        by_contra! eqs
        exact same (fun k => by simpa [point] using eqs k)
      obtain ⟨e,π,dπ,used,small,hc,rhs,off,bad⟩ := units point diff
      have guard (v) (hv : v ∈ vs) : litQEq (v,!(point v)) ∈ G :=
        (memG _).mpr ⟨v,by simpa [vs] using hv,by simp [point]⟩
      have outside (v) (hv : v ∉ vs) : e.1 v = 0 :=
        off v (fun hi => hv (by simp [vs,S,hi])) (fun hj => hv (by simp [vs,S,hj]))
      have combined := qAppendDerivations dπ d
      obtain ⟨τ,dτ,mem,cost⟩ := qEvaluatePointFromContext vs point G 1 e hc outside bad guard
        combined (List.mem_append_left _ used) (by simp)
      refine ⟨τ ++ π,by simpa only [List.append_assoc] using dτ,List.mem_append_left _ mem,?_⟩
      have hcost : resLinQSize τ ≤ (8*l+3)*(10 + m*l + 10*l) := by
        simp only [len,Fintype.card_prod,Fintype.card_fin,mul_one,rhs,Int.natAbs_zero,zero_add] at cost
        apply cost.trans
        have eq : 4*(2*l) = 8*l := by omega
        rw [eq]
        exact Nat.mul_le_mul_left _ (by omega)
      have add : resLinQSize (τ ++ π) = resLinQSize τ + resLinQSize π := by simp [resLinQSize]
      dsimp [cap]
      omega
  obtain ⟨ρ,d,empty,cost⟩ := qCoordinateCases vs S.nodup_toList [] cap leaves [] .nil (by simp)
  refine ⟨ρ,⟨by simpa using d,empty⟩,?_⟩
  simpa only [qWeight_nil,zero_add,len,show 4*(2*l) = 8*l by omega,cap] using cost

end PEqualNP.Search
