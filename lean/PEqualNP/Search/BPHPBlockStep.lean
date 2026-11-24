import PEqualNP.Search.Helpers.BlockCounts
import PEqualNP.Search.Helpers.BlockCapacityState
import PEqualNP.Search.Helpers.BlockTupleHolds
import PEqualNP.Search.Helpers.BlockTransitionCost
import PEqualNP.Search.Helpers.QPromoteHeads
import PEqualNP.Search.Helpers.BPHPZeroRowCut

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- Some block's count among the first one-plus-rank rows exceeds its allowance. -/
noncomputable def blockState {u v : ℕ} (t : BlockCounts u v) : QLine (Fin (2^(u+v)+1) × Fin (u+v)) :=
  blockCapacityLine v (blockRank t+1) (fun h => (t h).val)

/-- A unit change to one count either leaves a previous witness valid or appends
the currently queried pigeon to its witness tuple by a single integer sum. -/
theorem blockState_step {u v : ℕ} (hu : 0 < u) (t : BlockCounts u v) :
    QCanAdd (BPHP (2^(u+v)+1) (u+v))
      {L | ∃ h, 0<(t h).val ∧ L=blockState (blockPred t h)} (blockState t)
      (blockTransitionCost u v) := by
  classical
  let l := u+v
  let n := 2^l
  let C := blockStateWeightCap u v
  let T := blockState t
  let j : Fin (n+1) := ⟨blockRank t,Nat.lt_succ_of_le (blockRank_le t)⟩
  let vs := rowVars (l := u+v) j
  let Γ : Set (QLine (Fin (n+1) × Fin l)) := {L | ∃ h, 0<(t h).val ∧ L=blockState (blockPred t h)}
  have wc (s : BlockCounts u v) : qWeight (blockState s) ≤ C := by
    simpa only [blockState,C,blockStateWeightCap,Nat.add_assoc] using
      blockCapacityLine_weight (m := n+1) v (blockRank s+1) (fun h => (s h).val) (2^v)
        (fun h => Nat.le_of_lt_succ (s h).isLt)
  have wt : qWeight T ≤ C := wc t
  have len : vs.length = l := by simp [vs,rowVars,l]
  have nod : vs.Nodup := List.nodup_ofFn.mpr (fun _ _ h => congrArg Prod.snd h)
  have branches (a : Fin (n+1) × Fin (u+v) → Bool) :
      QCanAdd (BPHP (n+1) l) Γ (rowBlock j a ++ T) (blockBranchCap u v) := by
    let G := rowBlock j a
    let D := G++T
    let p := fun x => !(a x)
    let h : Fin u → Bool := fun b => p (j,b.castAdd v)
    let f := blockTupleEq v {j} h
    have wG : qWeight G ≤ 4*l := rowBlock_weight j a
    have wD : qWeight D ≤ 4*l+C := by
      rw [show qWeight D = qWeight G+qWeight T from qWeight_append G T]
      exact Nat.add_le_add wG wt
    have wg : qWeight G ≤ qWeight D := by rw [show qWeight D = qWeight G+qWeight T from qWeight_append ..]; omega
    have ne : vs ≠ [] := fun hx => by rw [hx] at len; simp [l] at len; omega
    have support (x : Fin (n+1) × Fin (u+v)) (hx : x ∉ vs) : f.1 x = 0 := by
      rcases x with ⟨r,b⟩
      apply blockTupleEq_off
      intro hm
      obtain rfl : r = j := Finset.mem_singleton.mp hm
      exact hx (List.mem_ofFn.mpr ⟨b,rfl⟩)
    have good : QEq.Holds p f := (blockTupleEq_holds v p {j} h).mpr (by
      intro i hi b
      obtain rfl := Finset.mem_singleton.mp hi
      rfl)
    have blocked (x : Fin (n+1) × Fin (u+v)) (hx : x ∈ vs) : litQEq (x,!p x) ∈ G := by
      obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hx
      exact (mem_rowBlock j a _).mpr ⟨b,by simp [p]⟩
    intro ρ der hist
    obtain ⟨σ,ds,mem,cost⟩ := qBuildAtPoint vs p G 1 f ne (blockTupleEq_coeff v {j} h)
      support good blocked der
    have costσ : resLinQSize σ ≤ (4*l+4)*(10+(n+1)*l+(u+l)+4*l) := by
      apply cost.trans
      have rhs : f.2.natAbs ≤ u := by simpa [f] using blockTupleEq_rhs v {j} h
      simp only [len,Fintype.card_prod,Fintype.card_fin,Nat.mul_one]
      exact Nat.mul_le_mul_left _ (by change 10 + (n+1)*l + (f.2.natAbs+l) + qWeight G ≤ _; omega)
    by_cases pos : 0 < (t h).val
    · let s := blockPred t h
      let P := blockState s
      have rank : blockRank s + 1 = j.val := blockRank_pred t h pos
      have wP : qWeight P ≤ C := wc s
      have plen : P.length ≤ C := (qLength_le_weight P).trans wP
      have prior : P ∈ ρ := hist P ⟨h,pos,rfl⟩
      have heads (e : QEq (Fin (n+1) × Fin (u+v))) (he : e ∈ P) :
          e ∈ D ∨ (e.1+f.1,e.2+f.2) ∈ D := by
        obtain ⟨z,S,old,num,rfl⟩ := (mem_blockCapacityLine v _ _ _).mp he
        have small (i : Fin (n+1)) (hi : i ∈ S) : i.val < j.val := rank ▸ old i hi
        by_cases eq : z = h
        · subst z
          have fresh : j ∉ S := fun hj => (Nat.lt_irrefl _ (small j hj))
          apply Or.inr
          apply List.mem_append_right
          apply (mem_blockCapacityLine v _ _ _).mpr
          refine ⟨h,insert j S,?_,?_,?_⟩
          · intro r hr
            rcases Finset.mem_insert.mp hr with rfl|hr
            · exact Nat.lt_succ_self _
            · exact (small r hr).trans (Nat.lt_succ_self _)
          · rw [Finset.card_insert_of_notMem fresh,num]
            change ((blockPred t h h).val + 1)+1 = (t h).val+1
            rw [blockPred_same]
            omega
          · exact (blockTupleEq_insert v S h j fresh).symm
        · apply Or.inl
          apply List.mem_append_right
          apply (mem_blockCapacityLine v _ _ _).mpr
          exact ⟨z,S,fun i hi => (small i hi).trans (Nat.lt_succ_self _), by
            simpa only [s,blockPred_other t h z eq] using num,rfl⟩
      obtain ⟨τ,dt,hm,price⟩ := qPromoteHeads P D G f (fun _ he => List.mem_append_left _ he)
        wg heads ds (List.mem_append_right _ prior) (List.mem_append_left _ mem)
      refine ⟨τ++σ,by simpa only [List.append_assoc] using dt,List.mem_append_left _ hm,?_⟩
      have packed : resLinQSize τ ≤ (C+2)*(2+2*C+4*(4*l+C)) := price.trans (by gcongr)
      rw [show resLinQSize (τ++σ) = resLinQSize τ + resLinQSize σ by simp only [resLinQSize,List.map_append,List.sum_append]; rfl]
      change _ ≤ (C+2)*(2+2*C+4*(4*l+C))+(4*l+4)*(10+(n+1)*l+(u+l)+4*l)+(1+(4*l+C))
      omega
    · have keep : f ∈ T := by
        apply (mem_blockCapacityLine v _ _ _).mpr
        refine ⟨h,{j},?_,?_,rfl⟩
        · intro i hi
          obtain rfl := Finset.mem_singleton.mp hi
          exact Nat.lt_succ_self _
        · rw [Finset.card_singleton]
          omega
      have sub : ∀ e ∈ f :: G, e ∈ D := by
        intro e he
        rcases List.mem_cons.mp he with rfl|he
        · exact List.mem_append_right _ keep
        · exact List.mem_append_left _ he
      refine ⟨D::σ,.weaken ds (List.mem_append_left _ mem) sub,List.mem_cons_self,?_⟩
      rw [qSize_cons]
      change 1+qWeight D + _ ≤ (C+2)*(2+2*C+4*(4*l+C))+(4*l+4)*(10+(n+1)*l+(u+l)+4*l)+(1+(4*l+C))
      omega
  intro ρ d prev
  obtain ⟨σ,ds,hm,cost⟩ := qCoordinateCases vs nod T (blockBranchCap u v) branches ρ d prev
  refine ⟨σ,ds,hm,cost.trans ?_⟩
  rw [len]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_left 10 (Nat.add_le_add_right (Nat.add_le_add_right wt _) _)) _)

end PEqualNP.Search
