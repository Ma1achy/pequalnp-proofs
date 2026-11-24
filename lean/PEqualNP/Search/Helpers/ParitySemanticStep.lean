import PEqualNP.Search.Helpers.ParityCut
import PEqualNP.Search.Helpers.ParitySeparator

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- A unary semantic inference is one weakening in Res(⊕). -/
theorem paritySemanticUnary {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {ρ : List (LinClause V)} {A T : LinClause V} (hd : IsLinDerivation F ρ) (hA : A ∈ ρ)
    (h : ∀ a, LinClauseSat a A → LinClauseSat a T) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ T ∈ σ ∧ σ.length ≤ 1 :=
  ⟨[T], hd.weak hA h, List.mem_cons_self, Nat.le_refl 1⟩

/-- Every sound binary inference between parity clauses costs at most four lines
in Res(⊕), including the case where one premise already implies the conclusion. -/
theorem paritySemanticStep {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {ρ : List (LinClause V)} {A B T : LinClause V} (hd : IsLinDerivation F ρ)
    (hA : A ∈ ρ) (hB : B ∈ ρ)
    (h : ∀ a, LinClauseSat a A → LinClauseSat a B → LinClauseSat a T) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ T ∈ σ ∧ σ.length ≤ 4 := by
  rcases paritySeparator h with hAT | hBT | ⟨q, hqA, hqB⟩
  · exact ⟨[T], hd.weak hA hAT, List.mem_cons_self, by simp⟩
  · exact ⟨[T], hd.weak hB hBT, List.mem_cons_self, by simp⟩
  · exact parityCut q hd hA hB hqA hqB

end PEqualNP.Search.Helpers
