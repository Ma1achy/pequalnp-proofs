import PEqualNP.Search.BPHPBalancedTotal

/-! Integer affine equations valid on the balanced bit pigeonhole instance. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- Satisfying the collision clauses means precisely that different rows have different labels. -/
theorem bphp_sat_iff_rows_injective {m l : ℕ} (a : Fin m × Fin l → Bool) :
    Satisfies a (BPHP m l) ↔ Function.Injective (fun (i : Fin m) (b : Fin l) => a (i,b)) := by
  classical
  constructor
  · intro sat i j same
    by_contra diff
    obtain ⟨lit, hm, val⟩ := sat _ ⟨i,j,fun b => a (i,b),diff,rfl⟩
    rcases Finset.mem_union.mp hm with h | h
    · obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp h
      simp at val
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp h
      have hbit : a (i,b) = a (j,b) := congrFun same b
      simp [← hbit] at val
  · rintro inj C ⟨i,j,α,hij,rfl⟩
    by_contra none
    have entry (k : Fin m)
        (inc : ∀ b, ((k,b), !α b) ∈
          Finset.univ.image (fun b => ((i,b), !α b)) ∪
          Finset.univ.image (fun b => ((j,b), !α b))) (b : Fin l) : a (k,b) = α b := by
      by_contra h
      exact none ⟨_,inc b,by cases h₁ : a (k,b) <;> cases h₂ : α b <;> simp_all⟩
    apply hij (inj (funext (fun b => ?_)))
    exact (entry i (fun t => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))) b).trans
      (entry j (fun t => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))) b).symm

private def bitValue (x : Bool) : ℤ := if x then 1 else 0

/-- In a balanced solution each bit column contains exactly half of the rows. -/
theorem bphp_column_sum {l : ℕ} (hl : 0 < l) (a : Fin (2^l) × Fin l → Bool)
    (sat : Satisfies a (BPHP (2^l) l)) (b : Fin l) :
    (∑ i : Fin (2^l), (if a (i,b) then (1 : ℤ) else 0)) = 2^(l-1) := by
  classical
  let row (i : Fin (2^l)) (t : Fin l) := a (i,t)
  let perm := Equiv.ofBijective row (Fintype.bijective_iff_injective_and_card row |>.mpr
    ⟨(bphp_sat_iff_rows_injective a).mp sat, by simp⟩)
  let neg : (Fin l → Bool) ≃ (Fin l → Bool) :=
    ⟨fun x t => !x t, fun x t => !x t, fun x => by funext t; simp, fun x => by funext t; simp⟩
  let val (x : Fin l → Bool) := bitValue (x b)
  have pair (x : Fin l → Bool) : val x + val (neg x) = 1 := by
    cases h : x b <;> simp [val,bitValue,neg,h]
  change (∑ i, val (perm i)) = _
  rw [perm.sum_comp val]
  have twice : (∑ x, val x) + (∑ x, val x) = (2:ℤ)^l := calc
    _ = (∑ x, val x) + ∑ x, val (neg x) := by rw [neg.sum_comp val]
    _ = (∑ x : Fin l → Bool, (1:ℤ)) := by rw [← Finset.sum_add_distrib]; simp_rw [pair]
    _ = _ := by simp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  rw [pow_succ] at twice
  change (∑ x, val x) = (2:ℤ)^k
  omega

private theorem two_rows {α β : Type*} [DecidableEq α] (f : α ≃ β) {i j : α} {x y : β}
    (hij : i ≠ j) (hxy : x ≠ y) : ∃ P : α ≃ β, P i = x ∧ P j = y := by
  let g := f.setValue i x
  have gi : g i = x := Equiv.setValue_eq ..
  have other : i ≠ g.symm y := by
    intro h
    exact hxy (gi.symm.trans ((congrArg g h).trans (g.apply_symm_apply y)))
  refine ⟨g.setValue j y, ?_, Equiv.setValue_eq ..⟩
  simpa only [Equiv.setValue, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hij other] using gi

private theorem row_coeff_same {l : ℕ} {e : QEq (Fin (2^l) × Fin l)}
    (valid : ∀ a, Satisfies a (BPHP (2^l) l) → QEq.Holds a e) (i j : Fin (2^l)) (b : Fin l) :
    e.1 (i,b) = e.1 (j,b) := by
  classical
  by_cases hij : i = j
  · rw [hij]
  let base : Fin (2^l) ≃ (Fin l → Bool) := Fintype.equivOfCardEq (by simp)
  let zero := fun _ : Fin l => false
  let one := fun t : Fin l => decide (t = b)
  have diff : zero ≠ one := by
    intro h
    have ht := congrFun h b
    simp [zero,one] at ht
  obtain ⟨P,hi,hj⟩ := two_rows base hij diff
  let P' := (Equiv.swap i j).trans P
  let a := fun v : Fin (2^l) × Fin l => P v.1 v.2
  let a' := fun v : Fin (2^l) × Fin l => P' v.1 v.2
  have h₀ := valid a ((bphp_sat_iff_rows_injective a).mpr P.injective)
  have h₁ := valid a' ((bphp_sat_iff_rows_injective a').mpr P'.injective)
  let z := e.1
  have delta (v : Fin (2^l) × Fin l) : z v*bitValue (a' v) - z v*bitValue (a v) =
      (if (i,b) = v then z (i,b) else 0) - (if (j,b) = v then z (j,b) else 0) := by
    rcases v with ⟨r,t⟩
    by_cases ri : r = i
    · subst r
      by_cases tb : t = b
      · subst t
        simp [a',a,P',hi,hj,zero,one,bitValue,Ne.symm hij]
      · simp [a',a,P',hi,hj,zero,one,bitValue,Ne.symm hij,tb,Ne.symm tb]
    · by_cases rj : r = j
      · subst r
        by_cases tb : t = b
        · subst t
          simp [a',a,P',hi,hj,zero,one,bitValue,hij]
        · simp [a',a,P',hi,hj,zero,one,bitValue,hij,tb,Ne.symm tb]
      · simp [a',a,P',Equiv.swap_apply_of_ne_of_ne ri rj, Ne.symm ri,Ne.symm rj]
  have total : (∑ v, (z v*bitValue (a' v) - z v*bitValue (a v))) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h₁.trans h₀.symm)
  simp_rw [delta] at total
  rw [Finset.sum_sub_distrib] at total
  simpa using sub_eq_zero.mp total

private theorem eval_column_coeff {l : ℕ} (hl : 0 < l) (a : Fin (2^l) × Fin l → Bool)
    (sat : Satisfies a (BPHP (2^l) l)) (c : Fin l → ℤ) :
    (∑ v : Fin (2^l) × Fin l, c v.2 * bitValue (a v)) = (2:ℤ)^(l-1) * ∑ b, c b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ i, c b * bitValue (a (i,b))) = _
  rw [← Finset.mul_sum]
  change c b * (∑ i, if a (i,b) then (1:ℤ) else 0) = _
  rw [bphp_column_sum hl a sat b, mul_comm]

/-- Every valid integer affine equation on permutations of the binary labels is an
integer linear combination of the column balances. -/
theorem bphp_affine_hull {l : ℕ} (hl : 0 < l) (e : QEq (Fin (2^l) × Fin l)) :
    (∀ a, Satisfies a (BPHP (2^l) l) → QEq.Holds a e) ↔
      ∃ c : Fin l → ℤ, (∀ i b, e.1 (i,b) = c b) ∧ e.2 = (2:ℤ)^(l-1) * ∑ b, c b := by
  classical
  constructor
  · intro valid
    let i₀ : Fin (2^l) := ⟨0,Nat.two_pow_pos l⟩
    let c := fun b => e.1 (i₀,b)
    have hc (v : Fin (2^l) × Fin l) : e.1 v = c v.2 := row_coeff_same valid v.1 i₀ v.2
    let P : Fin (2^l) ≃ (Fin l → Bool) := Fintype.equivOfCardEq (by simp)
    let a := fun v : Fin (2^l) × Fin l => P v.1 v.2
    have sat := (bphp_sat_iff_rows_injective a).mpr P.injective
    refine ⟨c, fun i b => hc (i,b), (valid a sat).symm.trans ?_⟩
    simp_rw [hc]
    exact eval_column_coeff hl a sat c
  · rintro ⟨c,coef,rhs⟩ a sat
    have hc (v : Fin (2^l) × Fin l) : e.1 v = c v.2 := coef v.1 v.2
    unfold QEq.Holds
    simp_rw [hc,rhs]
    exact eval_column_coeff hl a sat c

end PEqualNP.Search
