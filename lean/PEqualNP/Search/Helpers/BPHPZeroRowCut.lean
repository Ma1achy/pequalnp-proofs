import PEqualNP.Search.Helpers.BPHPZeroOccupancy

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

def rowVars {m l : ℕ} (i : Fin m) : List (Fin m × Fin l) := List.ofFn (fun b => (i,b))

def rowBlock {m l : ℕ} (i : Fin m) (a : Fin m × Fin l → Bool) : QLine (Fin m × Fin l) :=
  ((rowVars i).map (fun v => litQEq (v,a v))).reverse

theorem mem_rowBlock {m l : ℕ} (i : Fin m) (a : Fin m × Fin l → Bool) (e : QEq _) :
    e ∈ rowBlock i a ↔ ∃ b : Fin l, litQEq ((i,b),a (i,b)) = e := by
  simp [rowBlock,rowVars,List.map_ofFn,Function.comp_def]

theorem rowBlock_weight {m l : ℕ} (i : Fin m) (a : Fin m × Fin l → Bool) :
    qWeight (rowBlock i a) ≤ 4*l := by
  have h := List.sum_le_length_nsmul ((rowBlock i a).map QEq.size) 4 (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,rfl⟩ := (mem_rowBlock i a _).mp he
    exact qLit_size_le _ _)
  simpa [qWeight,rowBlock,rowVars,Nat.mul_comm] using h

private theorem binaryZeroRow_fails {m l : ℕ} (i : Fin m) (a : Fin m × Fin l → Bool)
    (b : Fin l) (hb : a (i,b) = true) : ¬ QEq.Holds a (binaryRowCoeff i,0) := by
  intro h
  have hnonneg (v : Fin m × Fin l) (_ : v ∈ Finset.univ) :
      0 ≤ binaryRowCoeff i v * (if a v then 1 else 0) := by
    unfold binaryRowCoeff
    split_ifs <;> positivity
  have one := Finset.single_le_sum hnonneg (Finset.mem_univ (i,b))
  change (∑ v, binaryRowCoeff i v * (if a v then 1 else 0)) = 0 at h
  rw [h] at one
  simp [binaryRowCoeff,hb] at one
  exact (not_lt_of_ge one) (by positivity)

def zeroRowCutCost (m l w : ℕ) : ℕ :=
  2^l * ((4*l+3)*(10+m*l*2^l+l*2^l+4*l+w) + 10*(w+4*l+1))

/-- Remove a disjunct saying row i is zero while retaining a clause that says
row j is nonzero. The Boolean coordinate case tree queries row i only. -/
theorem bphp_drop_zero_row {m l : ℕ} (i j : Fin m) (hne : i ≠ j) (D : QLine (Fin m × Fin l))
    (block : ∀ e ∈ rowBlock j (fun _ => true), e ∈ D) :
    QCanAdd (BPHP m l) {((binaryRowCoeff i,0) : QEq _) :: D} D (zeroRowCutCost m l (qWeight D)) := by
  classical
  let vs := rowVars (l := l) i
  have len : vs.length = l := by simp [vs,rowVars]
  have nod : vs.Nodup := List.nodup_ofFn.mpr (fun b c h => congrArg Prod.snd h)
  let cap := (4*l+3)*(10+m*l*2^l+l*2^l+4*l+qWeight D)
  have step := qCoordinateCases (F := BPHP m l)
    (Γ := ({((binaryRowCoeff i,0) : QEq _) :: D} : Set (QLine _))) vs nod D cap
  apply (by simpa [zeroRowCutCost,cap,len] using step)
  intro a ρ d base
  let G := rowBlock i a
  change ∃ σ, IsResLinQSynDerivation _ (σ++ρ) ∧ G++D ∈ σ ∧ resLinQSize σ ≤ cap
  have wG : qWeight G ≤ 4*l := rowBlock_weight i a
  by_cases all : ∀ b, a (i,b) = true
  · let C := Finset.univ.image (fun b : Fin l => ((i,b),true)) ∪ Finset.univ.image (fun b : Fin l => ((j,b),true))
    have input : C ∈ BPHP m l := ⟨i,j,fun _ => false,hne,rfl⟩
    let A := G ++ rowBlock j (fun _ => true)
    have rep (e : QEq (Fin m × Fin l)) : e ∈ A ↔ ∃ t ∈ C, e = litQEq t := by
      simp [A,G,C,mem_rowBlock,all,eq_comm]
    have ds := IsResLinQSynDerivation.ax C d input rep
    have sub : ∀ e ∈ A, e ∈ G++D := fun x hx =>
      List.mem_append.mpr ((List.mem_append.mp hx).imp id (block x))
    refine ⟨[G++D,A], .weaken ds List.mem_cons_self sub, List.mem_cons_self,?_⟩
    have wj := rowBlock_weight (l := l) j (fun _ => true)
    have inD : qWeight D ≥ 0 := Nat.zero_le _
    change qCost (G++D)+(qCost A+0) ≤ cap
    simp only [A,qCost,qWeight_append]
    dsimp [cap]
    nlinarith [Nat.zero_le (m*l*2^l),Nat.zero_le (l*2^l),Nat.zero_le (4*l*qWeight D)]
  · obtain ⟨b,hb⟩ := Classical.not_forall.mp all
    let p := fun v => !(a v)
    have bad := binaryZeroRow_fails i p b (by simpa [p] using hb)
    have coeff (u : Fin m × Fin l) : (binaryRowCoeff i u).natAbs ≤ 2^l := by
      by_cases h : u.1=i
      · simpa [binaryRowCoeff,h] using Nat.pow_le_pow_right (by decide : 0 < 2) u.2.isLt.le
      · simp [binaryRowCoeff,h]
    have off (u : Fin m × Fin l) (hu : u ∉ vs) : binaryRowCoeff i u = 0 := by
      rcases u with ⟨z,c⟩
      have h : z ≠ i := fun eq => hu (List.mem_ofFn.mpr ⟨c, by simpa [eq]⟩)
      simp [binaryRowCoeff,h]
    have blocked (u : Fin m × Fin l) (hu : u ∈ vs) : litQEq (u,!p u) ∈ G++D := by
      obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hu
      exact List.mem_append_left _ ((mem_rowBlock i a _).mpr ⟨c,by simp [p]⟩)
    obtain ⟨σ,ds,hm,cost⟩ := qEvaluatePointFromContext vs p (G++D) (2^l)
      (binaryRowCoeff i,0) coeff off bad blocked d (base _ rfl) (fun _ => List.mem_append_right G)
    refine ⟨σ,ds,hm,cost.trans ?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,len,qWeight_append]
    change (4*l+3)*(10+m*l*2^l+(0+l*2^l)+(qWeight G+qWeight D)) ≤ cap
    exact Nat.mul_le_mul_left _ (by omega)

/-- Eliminate the rows of an occupancy line, with copies of the final blocker
charged only at the current step. -/
theorem bphp_drop_zero_rows {m l : ℕ} (j : Fin m) (L : QLine (Fin m × Fin l))
    (rows : ∀ e ∈ L, ∃ i : Fin m, i ≠ j ∧ e = (binaryRowCoeff i,0))
    {ρ : List (QLine (Fin m × Fin l))} (d : IsResLinQSynDerivation (BPHP m l) ρ)
    (start : L ++ rowBlock j (fun _ => true) ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation (BPHP m l) (σ ++ ρ) ∧ rowBlock j (fun _ => true) ∈ σ ++ ρ ∧
      resLinQSize σ ≤ L.length * zeroRowCutCost m l (qWeight L + 4*l) := by
  let G := rowBlock (l := l) j (fun _ => true)
  change L++G ∈ ρ at start
  have gen (M : ℕ) (cap : qWeight L + 4*l ≤ M) :
      ∃ σ, IsResLinQSynDerivation (BPHP m l) (σ ++ ρ) ∧ G ∈ σ ++ ρ ∧
        resLinQSize σ ≤ L.length * zeroRowCutCost m l M := by
    induction L generalizing ρ with
    | nil => exact ⟨[],d,start,by simp [resLinQSize]⟩
    | cons e L ih =>
      obtain ⟨i,ne,rfl⟩ := rows e List.mem_cons_self
      let D := L++G
      obtain ⟨s,ds,mem,cost⟩ := bphp_drop_zero_row i j ne D (fun _ => List.mem_append_right L) ρ d
        (fun _ hm => Set.mem_singleton_iff.mp hm ▸ start)
      change QEq.size ((binaryRowCoeff i,0) : QEq (Fin m × Fin l)) + qWeight L + 4*l ≤ M at cap
      have tailCap : qWeight L + 4*l ≤ M := by omega
      obtain ⟨t,dt,h,b⟩ := ih (fun e he => rows e (List.mem_cons_of_mem _ he)) ds
        (List.mem_append_left _ mem) tailCap
      refine ⟨t++s,by simpa only [List.append_assoc] using dt,
        by simpa only [List.append_assoc] using h,?_⟩
      have dw : qWeight D ≤ M := (qWeight_append L G) ▸ (Nat.add_le_add_left (rowBlock_weight j _) _).trans tailCap
      have bc : zeroRowCutCost m l (qWeight D) ≤ zeroRowCutCost m l M := by unfold zeroRowCutCost; gcongr
      rw [show resLinQSize (t++s) = resLinQSize t + resLinQSize s by simp only [resLinQSize,List.map_append,List.sum_append],List.length_cons,Nat.succ_mul]
      exact Nat.add_le_add b (cost.trans bc)
  exact gen _ (Nat.le_refl _)

end PEqualNP.Search.Helpers
