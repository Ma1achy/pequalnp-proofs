import PEqualNP.Search.Helpers.QPaddedDeduction

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

/-- Replace disjuncts by sums with a previously established equation, retaining
a common disjunctive context. Both premises remain available at every step. -/
theorem qPromoteHeads (P D G : QLine V) (f : QEq V)
    (guard : ∀ e ∈ G, e ∈ D) (wg : qWeight G ≤ qWeight D)
    (heads : ∀ e ∈ P, e ∈ D ∨ (e.1 + f.1,e.2+f.2) ∈ D)
    {ρ : List (QLine V)} (der : IsResLinQSynDerivation F ρ) (start : P ∈ ρ) (add : f :: G ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ++ρ) ∧ D ∈ σ ∧
      resLinQSize σ ≤ (P.length+2) * (2 + 2*qWeight P + 4*qWeight D) := by
  let W := qWeight P
  let T := 2+2*W+4*qWeight D
  have gen (L : QLine V) (old : ∀ e ∈ L, e ∈ P) (wL : qWeight L ≤ W)
      {τ : List (QLine V)} (dt : IsResLinQSynDerivation F τ) (s : L++D ∈ τ) (a : f::G ∈ τ) :
      ∃ δ, IsResLinQSynDerivation F (δ++τ) ∧ D ∈ δ++τ ∧ resLinQSize δ ≤ L.length*T := by
    induction L generalizing τ with
    | nil => exact ⟨[],dt,s,by simp [resLinQSize]⟩
    | cons e L ih =>
      let C := L++D
      change e.size+qWeight L ≤ W at wL
      have w : qWeight L ≤ W := by omega
      have cq : qCost C ≤ 1+W+qWeight D := by
        simp only [C,qCost,qWeight_append]; omega
      have step : ∃ σ, IsResLinQSynDerivation F (σ++τ) ∧ C ∈ σ ∧ resLinQSize σ ≤ T := by
        rcases heads e (old _ List.mem_cons_self) with he|comb
        · have sub : ∀ x ∈ (e::L)++D, x ∈ C := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | ht
            · exact List.mem_append_right _ he
            · exact ht
          refine ⟨[C], .weaken dt s sub, List.mem_cons_self,?_⟩
          change qCost C + 0 ≤ T
          dsimp [T]; omega
        · let r : QEq V := (e.1+f.1,e.2+f.2)
          let R := r :: (C ++ G)
          have base : IsResLinQSynDerivation F (R::τ) := by
            simpa only [one_zsmul,one_mul] using
              IsResLinQSynDerivation.res (1:ℤ) 1 dt (show e::C ∈ τ from s) a
          have sub : ∀ x ∈ R, x ∈ C := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl|hx
            · exact List.mem_append_right L comb
            · rcases List.mem_append.mp hx with hc|hg
              · exact hc
              · exact List.mem_append_right L (guard _ hg)
          have wr : r.size ≤ qWeight D := List.le_sum_of_mem (List.mem_map_of_mem comb)
          refine ⟨[C,R], .weaken base List.mem_cons_self sub, List.mem_cons_self,?_⟩
          change qCost C + (1 + (r.size + qWeight (C++G)) + 0) ≤ T
          have cwt : qWeight C = qWeight L+qWeight D := qWeight_append ..
          rw [qWeight_append,cwt]; dsimp [T]; omega
      obtain ⟨s',ds,hm,cost⟩ := step
      obtain ⟨u,du,hu,cu⟩ := ih (fun z hz => old _ (List.mem_cons_of_mem _ hz)) w
        ds (List.mem_append_left _ hm) (List.mem_append_right _ a)
      refine ⟨u++s',by simpa only [List.append_assoc] using du,by simpa only [List.append_assoc] using hu,?_⟩
      rw [show resLinQSize (u++s') = resLinQSize u + resLinQSize s' by simp [resLinQSize],List.length_cons,Nat.succ_mul]
      exact Nat.add_le_add cu cost
  let A := P++D
  have da : IsResLinQSynDerivation F (A::ρ) := .weaken der start (fun _ he => List.mem_append_left _ he)
  obtain ⟨s,ds,hm,cost⟩ := gen P (fun _ he => he) (Nat.le_refl _) da List.mem_cons_self (List.mem_cons_of_mem _ add)
  refine ⟨D :: (s ++ [A]),?_,List.mem_cons_self,?_⟩
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      IsResLinQSynDerivation.weaken ds hm (fun _ he => he)
  · have size : resLinQSize (D::(s++[A])) = qCost D + (resLinQSize s + (qCost A+0)) := by
      change qCost D + resLinQSize (s++[A]) = _
      rw [show resLinQSize (s++[A]) = resLinQSize s + resLinQSize [A] by simp [resLinQSize]]; rfl
    rw [size, Nat.add_mul]
    change qCost D + (resLinQSize s + (qCost A+0)) ≤ P.length*T + 2*T
    have ca : qCost A = 1+qWeight P+qWeight D := by simp [A,qCost,Nat.add_assoc]
    change 1+qWeight D+_ ≤ _
    rw [ca]
    dsimp [T,W] at cost ⊢
    omega

end PEqualNP.Search.Helpers
