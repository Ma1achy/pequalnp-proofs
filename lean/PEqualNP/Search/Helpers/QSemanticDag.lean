import PEqualNP.Search.Helpers.QSynMerges
import PEqualNP.Search.Helpers.ParitySemanticStep
import PEqualNP.ProofComplexity.Helpers.Lin

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}

/-- Compile represented lines under a common guard. Every guarded line is true
outside the branch, so the original semantic implications apply on all assignments. -/
private theorem compile_trace (seed : F.Nonempty) {k : ℕ} (t : QSynMergeTrace F π k)
    (G : PEqualNP.ProofComplexity.LinClause V) (f : QLine V → PEqualNP.ProofComplexity.LinClause V)
    (rep : ∀ L ∈ π, ∀ a, LinClauseSat a (f L) ↔ LinClauseSat a G ∨ QLine.Holds a L) :
    ∃ ρ, IsLinDerivation (linOfClause '' F) ρ ∧ (∃ A, A ∈ ρ) ∧
      (∀ L ∈ π, f L ∈ ρ) ∧ ρ.length ≤ 4 * π.length + 1 := by
  induction t with
  | nil =>
    obtain ⟨C, hC⟩ := seed
    exact ⟨[linOfClause C], .ax .nil ⟨C, hC, rfl⟩, ⟨_, List.mem_cons_self⟩, by simp, by simp⟩
  | @input π k L C _ hC sound ih =>
    obtain ⟨ρ, d, _, prev, cost⟩ := ih (fun K hK => rep K (List.mem_cons_of_mem _ hK))
    have dC : IsLinDerivation (linOfClause '' F) (linOfClause C :: ρ) := .ax d ⟨C, hC, rfl⟩
    have dL : IsLinDerivation (linOfClause '' F) (f L :: linOfClause C :: ρ) := by
      apply dC.weak List.mem_cons_self
      intro a ha
      exact (rep L List.mem_cons_self a).mpr (Or.inr (sound a
        ((PEqualNP.ProofComplexity.Helpers.linOfClause_sat a C).mp ha)))
    refine ⟨_, dL, ⟨_, List.mem_cons_self⟩, ?_, ?_⟩
    · intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (prev _ hK))
    · simp only [List.length_cons]
      omega
  | @step π k L parents _ hlen hpar sound ih =>
    obtain ⟨ρ, d, ⟨A₀,h₀⟩, prev, cost⟩ := ih (fun K hK => rep K (List.mem_cons_of_mem _ hK))
    have implication (a : V → Bool) (hp : ∀ K ∈ parents, LinClauseSat a (f K)) :
        LinClauseSat a (f L) := by
      apply (rep L List.mem_cons_self a).mpr
      by_cases hg : LinClauseSat a G
      · exact Or.inl hg
      · exact Or.inr (sound a (fun K hK =>
          ((rep K (List.mem_cons_of_mem _ (hpar K hK)) a).mp (hp K hK)).resolve_left hg))
    have hpair : ∃ A ∈ ρ, ∃ B ∈ ρ, ∀ a, LinClauseSat a A → LinClauseSat a B →
        LinClauseSat a (f L) := by
      cases parents with
      | nil => exact ⟨A₀, h₀, A₀, h₀, fun a _ _ => implication a (by simp)⟩
      | cons P tail =>
        have hm := prev P (hpar P List.mem_cons_self)
        cases tail with
        | nil => exact ⟨f P, hm, f P, hm, fun a ha _ => implication a (by simpa using ha)⟩
        | cons Q rest =>
          have hrest : rest = [] := by
            cases rest with
            | nil => rfl
            | cons R more => simp at hlen
          subst rest
          refine ⟨f P, hm, f Q, prev Q (hpar Q (by simp)), fun a hp hq => ?_⟩
          exact implication a (by simpa using And.intro hp hq)
    obtain ⟨A, hA, B, hB, h⟩ := hpair
    obtain ⟨σ, dσ, hσ, hc⟩ := paritySemanticStep d hA hB h
    refine ⟨σ ++ ρ, dσ, ⟨_, List.mem_append_left _ hσ⟩, ?_, ?_⟩
    · intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact List.mem_append_left _ hσ
      · exact List.mem_append_right _ (prev K hK)
    · simp only [List.length_cons, List.length_append]
      omega

/-- If every integer line admits a parity-clause representation under the
assignments falsifying `G`, the integer refutation derives `G` in Res(⊕). -/
theorem guard_derivation_of_representation (seed : F.Nonempty)
    (hπ : IsResLinQSynRefutation F π) (G : PEqualNP.ProofComplexity.LinClause V)
    (repr : ∀ L ∈ π, ∃ T : PEqualNP.ProofComplexity.LinClause V,
      ∀ a, ¬ LinClauseSat a G → (LinClauseSat a T ↔ QLine.Holds a L)) :
    ∃ ρ, IsLinDerivation (linOfClause '' F) ρ ∧ G ∈ ρ ∧ ρ.length ≤ 4 * π.length + 2 := by
  classical
  let f : QLine V → PEqualNP.ProofComplexity.LinClause V := fun L =>
    if h : L ∈ π then G ∪ (repr L h).choose else G
  have rep (L) (hL : L ∈ π) (a) :
      LinClauseSat a (f L) ↔ LinClauseSat a G ∨ QLine.Holds a L := by
    have hu (T : PEqualNP.ProofComplexity.LinClause V) : LinClauseSat a (G ∪ T) ↔ LinClauseSat a G ∨ LinClauseSat a T := by
      simp only [LinClauseSat, Finset.mem_union]
      grind
    rw [show f L = G ∪ (repr L hL).choose by simp [f, hL], hu]
    by_cases hg : LinClauseSat a G
    · simp [hg]
    · simp [hg, (repr L hL).choose_spec a hg]
  obtain ⟨k, t⟩ := exists_merge_trace hπ.1
  obtain ⟨ρ, d, _, prev, cost⟩ := compile_trace seed t G f rep
  refine ⟨G :: ρ, d.weak (prev [] hπ.2) ?_, List.mem_cons_self, ?_⟩
  · intro a ha
    rcases (rep [] hπ.2 a).mp ha with h | ⟨_, he, _⟩
    · exact h
    · simp at he
  · simp only [List.length_cons]
    omega

end PEqualNP.Search.Helpers
