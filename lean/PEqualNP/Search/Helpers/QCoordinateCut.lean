import PEqualNP.Search.Helpers.QPaddingCost
import PEqualNP.Search.Helpers.SemanticWeakening

/-! Eliminate one Boolean coordinate by combining its opposite literal equations. -/
namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

theorem qLit_size_le (v : V) (b : Bool) : (litQEq (v, b)).size ≤ 4 :=
  (litQEq_size (v, b)).trans (by decide)

/-- From the two values of a coordinate with a common disjunctive context, derive
the context. Subtraction produces the false constant `0 = 1`; simplification
removes it and weakening contracts the duplicated context. -/
theorem qCoordinateCut (v : V) (G : QLine V) {ρ : List (QLine V)}
    (hρ : IsResLinQSynDerivation F ρ) (lo : litQEq (v, false) :: G ∈ ρ)
    (hi : litQEq (v, true) :: G ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧ resLinQSize σ ≤ 10 * (qWeight G + 1) := by
  classical
  let u : QEq V := (0, 1)
  let R := u :: (G ++ G)
  have hr : IsResLinQSynDerivation F (R :: ρ) := by
    have eqn : ((-1 : ℤ) • (litQEq (v, false)).1 + (1 : ℤ) • (litQEq (v, true)).1,
        (-1 : ℤ) * (litQEq (v, false)).2 + 1 * (litQEq (v, true)).2) = u := by
      simp [litQEq, u]
    simpa only [R, eqn] using IsResLinQSynDerivation.res (-1) 1 hρ lo hi
  let p (e : QEq V) := decide (¬ (e.1 = 0 ∧ e.2 ≠ 0))
  let K := (G ++ G).filter p
  have hK : IsResLinQSynDerivation F (K :: R :: ρ) := by
    simpa [R, u, p, K] using IsResLinQSynDerivation.simp hr (C := R) List.mem_cons_self
  have finish : IsResLinQSynDerivation F (G :: K :: R :: ρ) := by
    apply IsResLinQSynDerivation.weaken hK List.mem_cons_self
    intro e he
    have h := (List.mem_filter.mp he).1
    simpa using h
  refine ⟨[G, K, R], finish, List.mem_cons_self, ?_⟩
  have filt : qWeight K ≤ qWeight (G ++ G) :=
    ((List.filter_sublist (p := p) (l := G ++ G)).map QEq.size).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hu : u.size = 2 := by simp [QEq.size, u]
  have qR : qWeight R = 2 + qWeight (G ++ G) := by
    change u.size + qWeight (G ++ G) = _
    rw [hu]
  simp only [qSize_cons, qCost, qR, qWeight_append] at filt ⊢
  have hnil : resLinQSize ([] : List (QLine V)) = 0 := rfl
  omega

end PEqualNP.Search.Helpers
