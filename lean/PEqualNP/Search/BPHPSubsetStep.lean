import PEqualNP.Search.Helpers.BPHPSubsetState
import PEqualNP.Search.Helpers.BPHPSubsetCut
import PEqualNP.Search.Helpers.SubsetStepArithmetic

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- Derive one subset state from its immediate predecessors. The new pigeon's
label is read once on each branch. If that label lies in H, collision clauses
remove it as a possibility for any pigeon in the predecessor state. -/
theorem subsetState_step {l : ℕ} (hl : 0 < l) (H : Finset (Fin l → Bool)) :
    QCanAdd (BPHP (2^l+1) l) {L | ∃ h ∈ H, L = subsetState (H.erase h)}
      (subsetState H) (1000*(2^l+1)^10) := by
  classical
  let n := 2^l
  have cardH : H.card ≤ n := by simpa [n] using Finset.card_le_univ H
  let j : Fin (n+1) := ⟨H.card,by omega⟩
  let vs := rowVars (l := l) j
  let Γ : Set (QLine (Fin (n+1) × Fin l)) := {L | ∃ h ∈ H, L = subsetState (H.erase h)}
  let T := subsetState H
  have wT : qWeight T ≤ subsetStateCap n l := subsetState_weight H
  have len : vs.length = l := by simp [vs,rowVars]
  have nod : vs.Nodup := List.nodup_ofFn.mpr (fun _ _ h => congrArg Prod.snd h)
  have branches (a : Fin (n+1) × Fin l → Bool) :
      QCanAdd (BPHP (n+1) l) Γ (rowBlock j a ++ T) (subsetLeafBudget n l) := by
    let G := rowBlock j a
    let D := G ++ T
    let h := fun b => !(a (j,b))
    let W := subsetContextCap n l
    let E := subsetEquationCap n l
    have wG : qWeight G ≤ 4*l := rowBlock_weight j a
    have wD : qWeight D ≤ 4*l+subsetStateCap n l := by
      rw [show qWeight D = qWeight G + qWeight T from qWeight_append ..]
      exact Nat.add_le_add wG wT
    have wDW : qWeight D ≤ W := wD.trans (by dsimp [W,subsetContextCap]; omega)
    have cDW : qCost D ≤ 1+W := Nat.add_le_add_left wDW 1
    by_cases hin : h ∈ H
    · let I := (Finset.univ : Finset (Fin (n+1))).filter (fun i => i.val < j.val)
      let X := I.toList.map (fun i => rowPatternEq i h)
      have xmem (e) : e ∈ X ↔ ∃ i : Fin (n+1), i.val < j.val ∧ rowPatternEq i h = e := by
        simp [X,I]
      have xlen : X.length ≤ n+1 := by simpa only [X,List.length_map,Finset.length_toList,Fintype.card_fin] using Finset.card_le_univ I
      have wX : qWeight X ≤ (n+1)*E := by
        have b := List.sum_le_length_nsmul (X.map QEq.size) E (by
          intro y hy
          obtain ⟨e,he,rfl⟩ := List.mem_map.mp hy
          obtain ⟨i,_,rfl⟩ := (xmem e).mp he
          exact rowPatternEq_size i h)
        exact (by simpa [qWeight] using b : qWeight X ≤ X.length*E).trans (Nat.mul_le_mul_right _ xlen)
      have wxd : qWeight X + qWeight D ≤ W := by
        change _ ≤ (n+1)*E + 4*l + subsetStateCap n l
        omega
      have incl : ∀ e ∈ subsetState (H.erase h), e ∈ X ++ D := by
        intro e he
        obtain ⟨i,u,hi,hu,rfl⟩ := (mem_subsetState _ _).mp he
        have old : i.val < j.val := by
          have card := Finset.card_erase_add_one hin
          change _ < H.card
          omega
        by_cases uh : u = h
        · exact List.mem_append_left _ ((xmem _).mpr ⟨i,old,by rw [uh]⟩)
        · exact List.mem_append_right _ (List.mem_append_right G ((mem_subsetState H _).mpr
            ⟨i,u,old.le,fun hh => hu (Finset.mem_erase.mpr ⟨uh,hh⟩),rfl⟩))
      have guard : ∀ e ∈ rowBlock j (fun v => !(h v.2)), e ∈ D := by
        intro e he
        obtain ⟨b,rfl⟩ := (mem_rowBlock j _ e).mp he
        exact List.mem_append_left _ ((mem_rowBlock j a _).mpr ⟨b,by simp [h]⟩)
      intro ρ der prior
      have prev := prior (subsetState (H.erase h)) ⟨h,hin,rfl⟩
      have raw := IsResLinQSynDerivation.weaken der prev incl
      obtain ⟨σ,ds,hm,cost⟩ := drop_pattern_heads j h X D (fun e he => by
        obtain ⟨i,lt,rfl⟩ := (xmem e).mp he
        exact ⟨i,fun eq => (ne_of_lt lt) (congrArg Fin.val eq),rfl⟩)
        guard raw List.mem_cons_self W wxd
      let δ := D :: (σ ++ [X ++ D])
      refine ⟨δ,?_,List.mem_cons_self,?_⟩
      · simpa only [δ,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
          IsResLinQSynDerivation.weaken ds hm (fun _ he => he)
      · have xs : qCost (X++D) ≤ 1+W := by simpa only [qCost,qWeight_append] using Nat.add_le_add_left wxd 1
        have sc := cost.trans (Nat.mul_le_mul_right _ xlen)
        have ss : resLinQSize δ = qCost D + (resLinQSize σ + (qCost (X++D)+0)) := by
          change qCost D + resLinQSize (σ ++ [X++D]) = _
          rw [show resLinQSize (σ ++ [X++D]) = resLinQSize σ + resLinQSize [X++D] by
            simp only [resLinQSize,List.map_append,List.sum_append]]
          rfl
        rw [ss]
        change _ ≤ (n+1)*patternCutCost (n+1) l W +
          (4*l+4)*(10+(n+1)*l*n+(n+l*n)+4*l)+2*(1+W)
        omega
    · intro ρ der _
      let p := fun v => !(a v)
      have ne : vs ≠ [] := fun hv => by rw [hv] at len; simp at len; omega
      have support (u : Fin (n+1) × Fin l) (hu : u ∉ vs) : (rowPatternEq j h).1 u = 0 := by
        rcases u with ⟨i,b⟩
        exact rowPatternEq_off j h (i,b) (fun eq => hu (List.mem_ofFn.mpr ⟨b,Prod.ext eq.symm rfl⟩))
      have good : QEq.Holds p (rowPatternEq j h) := (rowPatternEq_holds p j h).mpr (fun _ => rfl)
      have blocked (u : Fin (n+1) × Fin l) (hu : u ∈ vs) : litQEq (u,!p u) ∈ G := by
        obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hu
        exact (mem_rowBlock j a _).mpr ⟨b,by simp [p]⟩
      obtain ⟨σ,ds,mem,cost⟩ := qBuildAtPoint vs p G n (rowPatternEq j h) ne
        (rowPatternEq_coeff j h) support good blocked der
      have sub : ∀ e ∈ rowPatternEq j h :: G, e ∈ D := by
        intro e he
        rcases List.mem_cons.mp he with rfl|he
        · exact List.mem_append_right G ((mem_subsetState H _).mpr ⟨j,h,by rfl,hin,rfl⟩)
        · exact List.mem_append_left _ he
      refine ⟨D :: σ,.weaken ds (List.mem_append_left _ mem) sub,List.mem_cons_self,?_⟩
      have cost' : resLinQSize σ ≤ (4*l+4)*(10+(n+1)*l*n+(n+l*n)+4*l) := by
        apply cost.trans
        simp only [len,Fintype.card_prod,Fintype.card_fin]
        have rhs : (rowPatternEq j h).2.natAbs ≤ n := rowPatternEq_rhs j h
        gcongr
      rw [qSize_cons]
      change _ ≤ (n+1)*patternCutCost (n+1) l W +
        (4*l+4)*(10+(n+1)*l*n+(n+l*n)+4*l)+2*(1+W)
      omega
  intro ρ d prev
  obtain ⟨σ,ds,hm,cost⟩ := qCoordinateCases vs nod T (subsetLeafBudget n l) branches ρ d prev
  refine ⟨σ,ds,hm,cost.trans ?_⟩
  rw [len]
  exact (Nat.mul_le_mul_left n (Nat.add_le_add_left
    (Nat.mul_le_mul_left 10 (Nat.add_le_add_right (Nat.add_le_add_right wT _) _)) _)).trans
      (subset_arithmetic_cap (n := n) Nat.lt_two_pow_self.le)

end PEqualNP.Search
