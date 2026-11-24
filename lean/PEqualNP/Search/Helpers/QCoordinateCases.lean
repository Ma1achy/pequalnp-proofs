import PEqualNP.Search.Helpers.QCoordinateCut

/-! Eliminate a full set of Boolean coordinate cases in syntactic integer resolution.
The size bound counts all copied context equations at each internal node. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)} {Γ : Set (QLine V)}

/-- A bounded extension of any derivation containing the assumptions. -/
def QCanAdd (F : Set (PEqualNP.ProofComplexity.Clause V)) (Γ : Set (QLine V)) (L : QLine V) (B : ℕ) : Prop :=
  ∀ ρ, IsResLinQSynDerivation F ρ → (∀ K ∈ Γ, K ∈ ρ) →
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ L ∈ σ ∧ resLinQSize σ ≤ B

private theorem coordinate_cases_aux (vs : List V) (distinct : vs.Nodup) (G : QLine V)
    (B M : ℕ) (cap : qWeight G + 4*vs.length + 1 ≤ M)
    (leaves : ∀ a : V → Bool, QCanAdd F Γ ((vs.map (fun v => litQEq (v,a v))).reverse ++ G) B)
    (ρ : List (QLine V)) (hρ : IsResLinQSynDerivation F ρ) (base : ∀ K ∈ Γ, K ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧
      resLinQSize σ + 10*M ≤ 2^vs.length * (B + 10*M) := by
  induction vs generalizing G ρ with
  | nil =>
    obtain ⟨s, d, m, bound⟩ := leaves (fun _ => false) ρ hρ base
    exact ⟨s, d, by simpa using m, by simpa using Nat.add_le_add_right bound (10*M)⟩
  | cons v vs ih =>
    obtain ⟨fresh, tailDistinct⟩ := List.nodup_cons.mp distinct
    have sub (b : Bool) (π : List (QLine V)) (valid : IsResLinQSynDerivation F π)
        (all : ∀ K ∈ Γ, K ∈ π) :
        ∃ s, IsResLinQSynDerivation F (s ++ π) ∧ litQEq (v,b) :: G ∈ s ∧
          resLinQSize s + 10*M ≤ 2^vs.length * (B + 10*M) := by
      apply ih tailDistinct (litQEq (v,b) :: G) ?_ ?_ π valid all
      · change (litQEq (v,b)).size + qWeight G + 4*vs.length + 1 ≤ M
        have := qLit_size_le v b
        simp only [List.length_cons] at cap
        omega
      · intro a
        let a' (x : V) := if x = v then b else a x
        have agree : vs.map (fun x => litQEq (x,a' x)) = vs.map (fun x => litQEq (x,a x)) := by
          apply List.map_congr_left
          intro x hx
          have ne : x ≠ v := fun eq => fresh (eq ▸ hx)
          simp [a',ne]
        simpa [List.reverse_cons, agree, a'] using leaves a'
    obtain ⟨s, ds, hs, bs⟩ := sub false ρ hρ base
    obtain ⟨t, dt, ht, bt⟩ := sub true (s ++ ρ) ds (fun K hK => List.mem_append_right _ (base K hK))
    obtain ⟨u, du, hu, bu⟩ := qCoordinateCut v G dt
      (List.mem_append_right _ (List.mem_append_left _ hs)) (List.mem_append_left _ ht)
    refine ⟨u ++ (t ++ s), by simpa [List.append_assoc] using du, List.mem_append_left _ hu, ?_⟩
    have size : resLinQSize (u ++ (t ++ s)) = resLinQSize u + (resLinQSize t + resLinQSize s) := by
      simp [resLinQSize]
    have cut : resLinQSize u ≤ 10*M := bu.trans (by omega)
    rw [size, List.length_cons, pow_succ, mul_comm _ 2, Nat.mul_assoc, two_mul]
    omega

/-- From the full coordinate blockers derive the root context. A variable occurs at
most once, so each path extends to a total Boolean assignment. -/
theorem qCoordinateCases (vs : List V) (distinct : vs.Nodup) (G : QLine V) (B : ℕ)
    (leaves : ∀ a : V → Bool, QCanAdd F Γ ((vs.map (fun v => litQEq (v,a v))).reverse ++ G) B) :
    QCanAdd F Γ G (2^vs.length * (B + 10*(qWeight G + 4*vs.length + 1))) := by
  intro ρ hρ base
  obtain ⟨s,d,m,h⟩ := coordinate_cases_aux vs distinct G B _ (Nat.le_refl _) leaves ρ hρ base
  exact ⟨s,d,m,by omega⟩

end PEqualNP.Search.Helpers
