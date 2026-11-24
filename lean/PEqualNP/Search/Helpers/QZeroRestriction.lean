import PEqualNP.Search.Helpers.QPaddedDeduction
import PEqualNP.Search.Helpers.QSynRename

namespace PEqualNP.Search.Helpers

variable {V W : Type}

/-- Set every variable outside the image of the embedding to zero. -/
def qZeroRestrict (ι : W ↪ V) (e : QEq V) : QEq W := (fun w => e.1 (ι w), e.2)

@[simp] theorem qZeroRestrict_at (ι : W ↪ V) (e : QEq V) (w : W) :
    (qZeroRestrict ι e).1 w = e.1 (ι w) := rfl

@[simp] theorem qZeroRestrict_rhs (ι : W ↪ V) (e : QEq V) :
    (qZeroRestrict ι e).2 = e.2 := rfl

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem qZeroRestrict_lit (ι : W ↪ V) (w : W) (b : Bool) :
    qZeroRestrict ι (litQEq (ι w,b)) = litQEq (w,b) := by
  refine Prod.ext ?_ (by rfl)
  funext u
  simp [qZeroRestrict,litQEq]

theorem qZeroRestrict_lit_off (ι : W ↪ V) (v : V) (hv : v ∉ Set.range ι) (b : Bool) :
    qZeroRestrict ι (litQEq (v,b)) = (0,if b then 1 else 0) := by
  refine Prod.ext ?_ (by rfl)
  funext w
  exact if_neg (fun eq => hv ⟨w,eq⟩)

theorem qZeroRestrict_size (ι : W ↪ V) (e : QEq V) :
    (qZeroRestrict ι e).size ≤ e.size := by
  classical
  let f (v : V) := (e.1 v).natAbs.size
  have s : (∑ w, f (ι w)) ≤ ∑ v, f v := by
    rw [← Finset.sum_map (Finset.univ : Finset W) ι f]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact Nat.add_le_add_right (Nat.add_le_add_left s 1) _

theorem qZeroRestrict_cost (ι : W ↪ V) (L : QLine V) : qCost (L.map (qZeroRestrict ι)) ≤ qCost L := by
  apply Nat.add_le_add_left
  induction L with
  | nil => rfl
  | cons e L ih => exact Nat.add_le_add (qZeroRestrict_size ι e) ih

private theorem filter_cost {Z : Type} [Fintype Z] (p : QEq Z → Bool) (L : QLine Z) :
    qCost (L.filter p) ≤ qCost L :=
  Nat.add_le_add_left (((List.filter_sublist).map QEq.size).sum_le_sum (fun _ _ => Nat.zero_le _)) 1

/-- Transport an integer refutation by setting variables to zero and padding its
lines by a guard. The two input hypotheses supply the restricted axioms. -/
theorem qZeroRestrictionDeduction (ι : W ↪ V) (G : QLine W) (B : ℕ)
    {F : Set (PEqualNP.ProofComplexity.Clause V)} {F' : Set (PEqualNP.ProofComplexity.Clause W)}
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (axioms : ∀ C ∈ F, QCanAdd F' ∅ (((C.toList.map litQEq).map (qZeroRestrict ι)) ++ G) B)
    (bools : ∀ v : V, QCanAdd F' ∅ ([qZeroRestrict ι (litQEq (v,false)),
      qZeroRestrict ι (litQEq (v,true))] ++ G) B) :
    ∃ ρ, IsResLinQSynDerivation F' ρ ∧ G ∈ ρ ∧
      resLinQSize ρ ≤ (B + 2*resLinQSize π + 4*qWeight G)*π.length := by
  let M := resLinQSize π
  let pL (K : QLine V) := K.map (qZeroRestrict ι) ++ G
  let K := B + 2*M + 4*qWeight G
  have go {τ : List (QLine V)} (d : IsResLinQSynDerivation F τ)
      (cap : ∀ L ∈ τ, qCost L ≤ M) :
      ∃ ρ, IsResLinQSynDerivation F' ρ ∧ (∀ L ∈ τ, pL L ∈ ρ) ∧ resLinQSize ρ ≤ K*τ.length := by
    have one (T : QLine V) (h : qCost T ≤ M) : qCost (pL T) ≤ M + qWeight G := by
      rw [show qCost (pL T) = qCost (T.map (qZeroRestrict ι)) + qWeight G from qCost_append ..]
      exact Nat.add_le_add_right ((qZeroRestrict_cost ι T).trans h) _
    have add {T : QLine V} {τ : List (QLine V)} {ρ : List (QLine W)} (prev : resLinQSize ρ ≤ K*τ.length)
        (old : ∀ L ∈ τ, pL L ∈ ρ) {σ : List (QLine W)} (dσ : IsResLinQSynDerivation F' (σ++ρ))
        (mem : pL T ∈ σ) (size : resLinQSize σ ≤ K) :
        ∃ δ, IsResLinQSynDerivation F' δ ∧ (∀ L ∈ T::τ, pL L ∈ δ) ∧ resLinQSize δ ≤ K*(T::τ).length := by
      refine ⟨σ++ρ,dσ,?_,?_⟩
      · intro L h
        rcases List.mem_cons.mp h with rfl| h
        · exact List.mem_append_left _ mem
        · exact List.mem_append_right _ (old L h)
      · rw [List.length_cons,Nat.mul_succ,Nat.add_comm (K*τ.length)]
        simpa only [resLinQSize,List.map_append,List.sum_append] using Nat.add_le_add size prev
    induction d with
    | nil => exact ⟨[],.nil,by simp,by simp [resLinQSize]⟩
    | @ax τ L C _ hC rep ih =>
      obtain ⟨ρ,dr,old,prev⟩ := ih (fun L h => cap L (.tail _ h))
      obtain ⟨σ,dσ,mem,cost⟩ := axioms C hC ρ dr (by simp)
      have sub : ∀ x ∈ ((C.toList.map litQEq).map (qZeroRestrict ι)) ++ G, x ∈ pL L := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
          obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
          exact List.mem_append_left _ (List.mem_map_of_mem ((rep _).mpr ⟨t,Finset.mem_toList.mp ht,rfl⟩))
        · exact List.mem_append_right _ hx
      apply add prev old (σ := pL L :: σ) (.weaken dσ (List.mem_append_left _ mem) sub) List.mem_cons_self
      have := one L (cap L List.mem_cons_self)
      rw [qSize_cons]
      dsimp [K]; omega
    | @bool τ v _ ih =>
      obtain ⟨ρ,dr,old,prev⟩ := ih (fun L h => cap L (.tail _ h))
      obtain ⟨σ,dσ,mem,cost⟩ := bools v ρ dr (by simp)
      exact add prev old dσ mem (cost.trans (by dsimp [K]; omega))
    | @res τ e f C D α β _ hC hD ih =>
      obtain ⟨ρ,dr,old,prev⟩ := ih (fun L h => cap L (.tail _ h))
      let u : QEq V := (α • e.1 + β • f.1, α*e.2+β*f.2)
      let T := u :: (C++D)
      let S := qZeroRestrict ι u :: (pL C ++ pL D)
      have raw : IsResLinQSynDerivation F' (S::ρ) :=
        .res α β dr (old _ hC) (old _ hD)
      have eq : pL T = qZeroRestrict ι u :: ((C.map (qZeroRestrict ι) ++ D.map (qZeroRestrict ι)) ++ G) := by
        simp [T,pL]
      have sub : ∀ x ∈ S, x ∈ pL T := by simp only [S,eq,pL,List.mem_cons,List.mem_append]; tauto
      apply add prev old (σ := [pL T,S]) (.weaken raw List.mem_cons_self sub) List.mem_cons_self
      have hT := one T (cap T List.mem_cons_self)
      have hS : qCost S ≤ M + 2*qWeight G := by
        rw [show qCost S = qCost (T.map (qZeroRestrict ι)) + 2*qWeight G by
          simpa [T,pL,S,List.map_append] using qCost_padded_res (qZeroRestrict ι u) (C.map _) (D.map _) G]
        exact Nat.add_le_add_right ((qZeroRestrict_cost ι T).trans (cap T List.mem_cons_self)) _
      change qCost (pL T) + (qCost S + 0) ≤ K
      dsimp [K]; omega
    | @weaken τ C D _ hC sub ih =>
      obtain ⟨ρ,dr,old,prev⟩ := ih (fun L h => cap L (.tail _ h))
      have keep : ∀ x ∈ pL C, x ∈ pL D := by
        intro x hx
        rcases List.mem_append.mp hx with hm|hm
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
          exact List.mem_append_left _ (List.mem_map_of_mem (sub _ he))
        · exact List.mem_append_right _ hm
      apply add prev old (σ := [pL D]) (.weaken dr (old _ hC) keep) List.mem_cons_self
      have := one D (cap D List.mem_cons_self)
      change qCost (pL D)+0 ≤ K
      dsimp [K]; omega
    | @simp τ C _ hC ih =>
      obtain ⟨ρ,dr,old,prev⟩ := ih (fun L h => cap L (.tail _ h))
      let T := C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))
      let S := (pL C).filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))
      have sub : ∀ x ∈ S, x ∈ pL T := by
        intro x hx
        obtain ⟨hm,keep⟩ := List.mem_filter.mp hx
        rcases List.mem_append.mp hm with hm|hm
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
          apply List.mem_append_left
          apply List.mem_map_of_mem
          apply List.mem_filter.mpr
          refine ⟨he,decide_eq_true (fun ⟨hz,hn⟩ => ?_)⟩
          exact (of_decide_eq_true keep) ⟨funext (fun w => congrFun hz (ι w)),hn⟩
        · exact List.mem_append_right _ hm
      apply add prev old (σ := [pL T,S]) (.weaken (.simp dr (old _ hC)) List.mem_cons_self sub) List.mem_cons_self
      have ht := one T (cap T List.mem_cons_self)
      have hs : qCost S ≤ M + qWeight G := (filter_cost _ _).trans (one C (cap C (.tail _ hC)))
      change qCost (pL T)+(qCost S+0) ≤ K
      dsimp [K]; omega
  obtain ⟨ρ,d,h,cost⟩ := go ref.1 (fun _ hm => qCost_le_of_mem hm)
  exact ⟨ρ,d,h [] ref.2,cost⟩

end PEqualNP.Search.Helpers
