import PEqualNP.Search.Helpers.BPHPZeroRowCut
import PEqualNP.Search.Helpers.RowPatternEq

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

def patternCutCost (m l w : ℕ) : ℕ :=
  2^l * ((4*l+3)*(10 + m*l*2^l + (2^l + l*2^l) + (4*l+w)) + 10*(w+4*l+1))

/-- Under a blocker fixing row j to h, collision axioms allow every old row i's
equation asserting label h to be dropped from the head of a disjunction. -/
theorem drop_pattern_head {m l : ℕ} (i j : Fin m) (hne : i ≠ j) (h : Fin l → Bool)
    (D : QLine (Fin m × Fin l))
    (block : ∀ e ∈ rowBlock j (fun v => !(h v.2)), e ∈ D) :
    QCanAdd (BPHP m l) {rowPatternEq i h :: D} D (patternCutCost m l (qWeight D)) := by
  classical
  let vs := rowVars (l := l) i
  have len : vs.length = l := by simp [vs,rowVars]
  have nod : vs.Nodup := List.nodup_ofFn.mpr (fun b c h => congrArg Prod.snd h)
  let cap := (4*l+3)*(10+m*l*2^l+(2^l+l*2^l)+(4*l+qWeight D))
  have step := qCoordinateCases (F := BPHP m l) (Γ := ({rowPatternEq i h :: D} : Set (QLine _))) vs nod D cap
  apply (by simpa [patternCutCost,cap,len] using step)
  intro a ρ d base
  let G := rowBlock i a
  change ∃ σ, IsResLinQSynDerivation _ (σ++ρ) ∧ G++D ∈ σ ∧ resLinQSize σ ≤ cap
  have wG : qWeight G ≤ 4*l := rowBlock_weight i a
  by_cases all : ∀ b, a (i,b) = !(h b)
  · let C := Finset.univ.image (fun b : Fin l => ((i,b),!(h b))) ∪ Finset.univ.image (fun b : Fin l => ((j,b),!(h b)))
    have input : C ∈ BPHP m l := ⟨i,j,h,hne,rfl⟩
    let A := G ++ rowBlock j (fun v => !(h v.2))
    have rep (e : QEq (Fin m × Fin l)) : e ∈ A ↔ ∃ t ∈ C, e = litQEq t := by
      constructor
      · intro he
        rcases List.mem_append.mp he with hG | hj
        · obtain ⟨b,rfl⟩ := (mem_rowBlock i a e).mp hG
          exact ⟨_,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩),by rw [all b]⟩
        · obtain ⟨b,rfl⟩ := (mem_rowBlock j _ e).mp hj
          exact ⟨_,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩),rfl⟩
      · rintro ⟨t,ht,rfl⟩
        rcases Finset.mem_union.mp ht with hi|hj
        · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
          exact List.mem_append_left _ ((mem_rowBlock i a _).mpr ⟨b,by rw [all b]⟩)
        · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
          exact List.mem_append_right _ ((mem_rowBlock j _ _).mpr ⟨b,rfl⟩)
    have ds := IsResLinQSynDerivation.ax C d input rep
    have sub : ∀ e ∈ A, e ∈ G++D := fun x hx =>
      List.mem_append.mpr ((List.mem_append.mp hx).imp id (block x))
    refine ⟨[G++D,A], .weaken ds List.mem_cons_self sub, List.mem_cons_self,?_⟩
    have wj := rowBlock_weight (l := l) j (fun v => !(h v.2))
    change qCost (G++D)+(qCost A+0) ≤ cap
    simp only [A,qCost,qWeight_append]
    dsimp [cap]
    calc
      _ ≤ 3*(10+(4*l+qWeight D)) := by omega
      _ ≤ 3*(10+m*l*2^l+(2^l+l*2^l)+(4*l+qWeight D)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) _)
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · let p := fun v => !(a v)
    have bad : ¬ QEq.Holds p (rowPatternEq i h) := by
      intro good
      apply all
      intro b
      simpa [p] using congrArg Bool.not ((rowPatternEq_holds p i h).mp good b)
    have off (u : Fin m × Fin l) (hu : u ∉ vs) : (rowPatternEq i h).1 u = 0 := by
      rcases u with ⟨z,c⟩
      apply rowPatternEq_off
      exact fun eq => hu (List.mem_ofFn.mpr ⟨c,Prod.ext eq.symm rfl⟩)
    have blocked (u : Fin m × Fin l) (hu : u ∈ vs) : litQEq (u,!p u) ∈ G++D := by
      obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hu
      exact List.mem_append_left _ ((mem_rowBlock i a _).mpr ⟨c,by simp [p]⟩)
    obtain ⟨σ,ds,hm,cost⟩ := qEvaluatePointFromContext vs p (G++D) (2^l)
      (rowPatternEq i h) (rowPatternEq_coeff i h) off bad blocked d
      (base _ rfl) (fun _ => List.mem_append_right G)
    refine ⟨σ,ds,hm,cost.trans ?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,len,qWeight_append]
    exact Nat.mul_le_mul_left _ (by have := rowPatternEq_rhs i h; omega)

theorem drop_pattern_heads {m l : ℕ} (j : Fin m) (h : Fin l → Bool) (L D : QLine (Fin m × Fin l))
    (rows : ∀ e ∈ L, ∃ i, i ≠ j ∧ e = rowPatternEq i h)
    (block : ∀ e ∈ rowBlock j (fun v => !(h v.2)), e ∈ D)
    {ρ : List (QLine (Fin m × Fin l))} (d : IsResLinQSynDerivation (BPHP m l) ρ)
    (start : L ++ D ∈ ρ) (W : ℕ) (cap : qWeight L + qWeight D ≤ W) :
    ∃ σ, IsResLinQSynDerivation (BPHP m l) (σ ++ ρ) ∧ D ∈ σ ++ ρ ∧
      resLinQSize σ ≤ L.length * patternCutCost m l W := by
  induction L generalizing ρ with
  | nil => exact ⟨[],d,start,by simp [resLinQSize]⟩
  | cons e L ih =>
    obtain ⟨i,ne,rfl⟩ := rows e List.mem_cons_self
    obtain ⟨s,ds,mem,cost⟩ := drop_pattern_head i j ne h (L++D)
      (fun e hm => List.mem_append_right _ (block e hm)) ρ d
      (fun _ hm => Set.mem_singleton_iff.mp hm ▸ start)
    change (rowPatternEq i h).size + qWeight L + qWeight D ≤ W at cap
    have tailCap : qWeight L + qWeight D ≤ W := by omega
    obtain ⟨t,dt,hm,b⟩ := ih (fun e he => rows e (List.mem_cons_of_mem _ he)) ds
      (List.mem_append_left _ mem) tailCap
    refine ⟨t++s,by simpa only [List.append_assoc] using dt,by simpa only [List.append_assoc] using hm,?_⟩
    have weak : qWeight (L++D) ≤ W := by simpa using tailCap
    have bc : patternCutCost m l (qWeight (L++D)) ≤ patternCutCost m l W := by unfold patternCutCost; gcongr
    rw [show resLinQSize (t++s) = resLinQSize t + resLinQSize s by simp only [resLinQSize,List.map_append,List.sum_append],List.length_cons,Nat.succ_mul]
    exact Nat.add_le_add b (cost.trans bc)

end PEqualNP.Search.Helpers
