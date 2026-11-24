import PEqualNP.Search.Helpers.QCoordinateCases

/-! Derive a fixed disjunction from padded input axioms by carrying it through a
syntactic integer refutation. Simplification may delete contradictory constants
from the disjunction; syntactic weakening puts those entries back. -/

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F F' : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}

/-- A stand-alone derivation of a line can be run unchanged after any history. -/
theorem QCanAdd.of_derivation {G : QLine V} {B : ℕ} (d : IsResLinQSynDerivation F π)
    (mem : G ∈ π) (cost : resLinQSize π ≤ B) : QCanAdd F ∅ G B := by
  intro ρ hρ _
  refine ⟨π, ?_, mem, cost⟩
  clear mem cost
  induction d with
  | nil => exact hρ
  | ax C _ hC encoding ih => exact .ax C ih hC encoding
  | bool v _ ih => exact .bool v ih
  | res α β _ left right ih =>
    exact .res α β ih (List.mem_append_left _ left) (List.mem_append_left _ right)
  | weaken _ hC sub ih => exact .weaken ih (List.mem_append_left _ hC) sub
  | simp _ hC ih => exact .simp ih (List.mem_append_left _ hC)

private def PaddedDerivation (F' : Set (PEqualNP.ProofComplexity.Clause V))
    (G : QLine V) (B : ℕ) (π : List (QLine V)) : Prop :=
  ∃ ρ, IsResLinQSynDerivation F' ρ ∧ (∀ L ∈ π, L ++ G ∈ ρ) ∧
    resLinQSize ρ ≤ 2*resLinQSize π + (B+3*qWeight G)*π.length

private theorem padded_cons {T G : QLine V} {B : ℕ} (prev : PaddedDerivation F' G B π)
    (step : ∀ ρ, IsResLinQSynDerivation F' ρ → (∀ L ∈ π, L ++ G ∈ ρ) →
      ∃ σ, IsResLinQSynDerivation F' (σ ++ ρ) ∧ T ++ G ∈ σ ∧
        resLinQSize σ ≤ 2*qCost T + B + 3*qWeight G) : PaddedDerivation F' G B (T :: π) := by
  obtain ⟨ρ,d,rep,n⟩ := prev
  obtain ⟨s,ds,hs,b⟩ := step ρ d rep
  refine ⟨s ++ ρ, ds, ?_, ?_⟩
  · intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ (rep _ hL)
  · have size : resLinQSize (s ++ ρ) = resLinQSize s + resLinQSize ρ := by simp [resLinQSize]
    rw [size, qSize_cons, List.length_cons, Nat.mul_succ]
    omega

private theorem pad_all (G : QLine V) (B : ℕ) (d : IsResLinQSynDerivation F π)
    (inputs : ∀ L ∈ π, ∀ C ∈ F, (∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) →
      QCanAdd F' ∅ (L ++ G) (2*qCost L + B + 3*qWeight G)) :
    PaddedDerivation F' G B π := by
  have nil_size : resLinQSize ([] : List (QLine V)) = 0 := rfl
  induction d with
  | nil => exact ⟨[], .nil, by simp, by simp [nil_size]⟩
  | ax C _ hC ax ih =>
    apply padded_cons (ih (fun L hL => inputs L (.tail _ hL)))
    intro ρ d _
    exact inputs _ List.mem_cons_self C hC ax ρ d (by simp)
  | bool v _ ih =>
    apply padded_cons (ih (fun L hL => inputs L (.tail _ hL)))
    intro ρ d _
    let T := [litQEq (v,false), litQEq (v,true)]
    refine ⟨[T ++ G,T], .weaken (.bool v d) List.mem_cons_self (fun _ hm => List.mem_append_left _ hm),
      List.mem_cons_self, ?_⟩
    change resLinQSize [T ++ G,T] ≤ 2*qCost T + B + 3*qWeight G
    simp only [qSize_cons, qCost_append, nil_size]
    omega
  | @res tail e f C D α β _ hC hD ih =>
    apply padded_cons (ih (fun L hL => inputs L (.tail _ hL)))
    intro ρ d rep
    let u : QEq V := (α • e.1 + β • f.1, α*e.2 + β*f.2)
    let T := u :: (C ++ D)
    let S := u :: ((C ++ G) ++ (D ++ G))
    have raw : IsResLinQSynDerivation F' (S :: ρ) :=
      .res α β d (show e :: (C ++ G) ∈ ρ from rep _ hC) (show f :: (D ++ G) ∈ ρ from rep _ hD)
    have sub : ∀ x ∈ S, x ∈ T ++ G := by
      simp only [S, T, List.mem_cons, List.mem_append]
      tauto
    refine ⟨[T ++ G,S], .weaken raw List.mem_cons_self sub, List.mem_cons_self, ?_⟩
    change resLinQSize [T ++ G,S] ≤ 2*qCost T + B + 3*qWeight G
    have shifted : qCost S = qCost T + 2*qWeight G := qCost_padded_res u C D G
    simp only [qSize_cons, qCost_append, shifted, nil_size]
    omega
  | @weaken tail C D _ hC sub ih =>
    apply padded_cons (ih (fun L hL => inputs L (.tail _ hL)))
    intro ρ d rep
    have keep : ∀ x ∈ C ++ G, x ∈ D ++ G := fun _ hx =>
      List.mem_append.mpr ((List.mem_append.mp hx).imp (sub _) id)
    refine ⟨[D ++ G], .weaken d (rep _ hC) keep, List.mem_cons_self, ?_⟩
    simp only [qSize_cons, qCost_append, nil_size]
    omega
  | @simp tail C _ hC ih =>
    apply padded_cons (ih (fun L hL => inputs L (.tail _ hL)))
    intro ρ d rep
    let p (e : QEq V) := decide (¬ (e.1 = 0 ∧ e.2 ≠ 0))
    let T := C.filter p
    let S := T ++ G.filter p
    have raw : IsResLinQSynDerivation F' (S :: ρ) := by
      simpa only [S, T, List.filter_append] using IsResLinQSynDerivation.simp d (rep _ hC)
    have sub : ∀ x ∈ S, x ∈ T ++ G := fun _ hx =>
      List.mem_append.mpr ((List.mem_append.mp hx).imp id (fun h => (List.mem_filter.mp h).1))
    refine ⟨[T ++ G,S], .weaken raw List.mem_cons_self sub, List.mem_cons_self, ?_⟩
    change resLinQSize [T ++ G,S] ≤ 2*qCost T + B + 3*qWeight G
    have filt : qWeight (G.filter p) ≤ qWeight G :=
      ((List.filter_sublist (p := p) (l := G)).map QEq.size).sum_le_sum (fun _ _ => Nat.zero_le _)
    simp only [S, qSize_cons, qCost_append, nil_size]
    omega

/-- If each padded input representation can be derived with encoded cost B,
an integer refutation yields a derivation of the guard. -/
theorem qPaddedDeduction (G : QLine V) (B : ℕ) (ref : IsResLinQSynRefutation F π)
    (inputs : ∀ L ∈ π, ∀ C ∈ F, (∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) →
      QCanAdd F' ∅ (L ++ G) B) :
    ∃ ρ, IsResLinQSynDerivation F' ρ ∧ G ∈ ρ ∧
      resLinQSize ρ ≤ 2*resLinQSize π + (B+3*qWeight G)*π.length := by
  obtain ⟨ρ,d,rep,n⟩ := pad_all (F' := F') G B ref.1 (by
    intro L hL C hC ax δ dd base
    obtain ⟨s,ds,m,b⟩ := inputs L hL C hC ax δ dd base
    exact ⟨s,ds,m,by omega⟩)
  exact ⟨ρ,d,by simpa using rep [] ref.2,n⟩

/-- One canonical padded input suffices per clause. A weakening step supplies all
reordered or duplicated representations used by the original refutation. -/
theorem qPaddedDeductionCanonical (G : QLine V) (B : ℕ) (ref : IsResLinQSynRefutation F π)
    (inputs : ∀ C ∈ F, QCanAdd F' ∅ ((C.toList.map litQEq) ++ G) B) :
    ∃ ρ, IsResLinQSynDerivation F' ρ ∧ G ∈ ρ ∧
      resLinQSize ρ ≤ 2*resLinQSize π + (B+3*qWeight G)*π.length := by
  obtain ⟨ρ,d,rep,n⟩ := pad_all (F' := F') G B ref.1 (by
    intro L _ C hC ax δ dd base
    obtain ⟨s,ds,m,b⟩ := inputs C hC δ dd base
    have sub : ∀ x ∈ C.toList.map litQEq ++ G, x ∈ L ++ G := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
        exact List.mem_append_left _ ((ax _).mpr ⟨_, Finset.mem_toList.mp ht, rfl⟩)
      · exact List.mem_append_right _ hx
    exact ⟨(L ++ G) :: s, .weaken ds (List.mem_append_left _ m) sub, List.mem_cons_self, by
      rw [qSize_cons, qCost_append]
      omega⟩)
  exact ⟨ρ,d,by simpa using rep [] ref.2,n⟩

end PEqualNP.Search.Helpers
