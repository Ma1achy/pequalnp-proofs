import PEqualNP.Defs.ProofComplexityLin

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

private theorem weakenToPivot {V : Type} [DecidableEq V] {C T : LinClause V} (q : LinEq V)
    (hw : ∀ a, LinClauseSat a C → LinClauseSat a T ∨ LinEqSat a q) :
    ∀ a, LinClauseSat a C → LinClauseSat a (insert q T) := by
  intro a ha
  rcases hw a ha with ⟨e, he, hs⟩ | hs
  · exact ⟨e, Finset.mem_insert_of_mem he, hs⟩
  · exact ⟨q, Finset.mem_insert_self _ _, hs⟩

private theorem parityCutFalseTrue {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {ρ : List (LinClause V)} {A B T : LinClause V} (f : Finset V)
    (hd : IsLinDerivation F ρ) (hA : A ∈ ρ) (hB : B ∈ ρ)
    (hwA : ∀ a, LinClauseSat a A → LinClauseSat a T ∨ LinEqSat a (f, false))
    (hwB : ∀ a, LinClauseSat a B → LinClauseSat a T ∨ LinEqSat a (f, true)) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ T ∈ σ ∧ σ.length ≤ 4 := by
  let C := insert (f, false) T
  let D := insert (f, true) T
  let R := C.erase (f, false) ∪ D.erase (f, true)
  have hC : IsLinDerivation F (C :: ρ) := hd.weak hA (weakenToPivot _ hwA)
  have hD : IsLinDerivation F (D :: C :: ρ) :=
    hC.weak (List.mem_cons_of_mem _ hB) (weakenToPivot _ hwB)
  have hR : IsLinDerivation F (R :: D :: C :: ρ) :=
    hD.res (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
      ⟨f, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, rfl⟩
  have hsub : R ⊆ T := Finset.union_subset (Finset.erase_insert_subset _ _)
    (Finset.erase_insert_subset _ _)
  refine ⟨[T, R, D, C], hR.weak List.mem_cons_self ?_, by simp, by simp⟩
  rintro a ⟨e, he, hs⟩
  exact ⟨e, hsub he, hs⟩

/-- Resolve two semantic weakenings on opposite values of the same parity form.
The last weakening restores any occurrence of the pivot erased from the target. -/
theorem parityCut {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {ρ : List (LinClause V)} {A B T : LinClause V} (q : LinEq V)
    (hd : IsLinDerivation F ρ) (hA : A ∈ ρ) (hB : B ∈ ρ)
    (hwA : ∀ a, LinClauseSat a A → LinClauseSat a T ∨ LinEqSat a (q.1, !q.2))
    (hwB : ∀ a, LinClauseSat a B → LinClauseSat a T ∨ LinEqSat a q) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ T ∈ σ ∧ σ.length ≤ 4 := by
  obtain ⟨f, b⟩ := q
  cases b with
  | false => exact parityCutFalseTrue f hd hB hA hwB hwA
  | true => exact parityCutFalseTrue f hd hA hB hwA hwB

end PEqualNP.Search.Helpers
