import PEqualNP.Search.BPHPFinalSimplification

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private def AllowedBeforeFinal {V : Type} [DecidableEq V] (F : Set (Clause V))
    (L : QLine V) (tail : List (QLine V)) : Prop :=
  (∃ C ∈ F, ∀ e, e ∈ L ↔ ∃ l ∈ C, e = PEqualNP.Search.litQEq l) ∨
      (∃ v : V, L = [PEqualNP.Search.litQEq (v, false), PEqualNP.Search.litQEq (v, true)]) ∨
      (∃ (e e' : PEqualNP.Search.QEq V) (C D : PEqualNP.Search.QLine V) (α β : ℤ),
        (e :: C) ∈ tail ∧ (e' :: D) ∈ tail ∧
        L = (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) ∨
      (∃ C ∈ tail, ∀ e ∈ C, e ∈ L)

private def ValidBeforeFinal {V : Type} [DecidableEq V] (F : Set (Clause V))
    (ρ : List (QLine V)) : Prop :=
  ∀ front L tail, ρ = front ++ (L :: tail) → AllowedBeforeFinal F L tail

private theorem valid_cons {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {T : QLine V} {ρ : List (QLine V)} (head : AllowedBeforeFinal F T ρ)
    (rest : ValidBeforeFinal F ρ) : ValidBeforeFinal F (T :: ρ) := by
  intro front L tail eq
  cases front with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj eq
    exact head
  | cons K front => exact rest front L tail (List.cons.inj eq).2

/-- Expand a simplification-free derivation into an explicit justification for every line. -/
theorem explicitNoSimpSuffixes {V : Type} [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {ρ : List (QLine V)} (d : NoSimpDerivation F ρ) : ValidBeforeFinal F ρ := by
  induction d with
  | nil =>
    intro front L tail eq
    simp at eq
  | ax C _ hC rep ih => exact valid_cons (Or.inl ⟨C, hC, rep⟩) ih
  | bool v _ ih => exact valid_cons (Or.inr (Or.inl ⟨v, rfl⟩)) ih
  | @res π e e' C D α β _ hC hD ih =>
    exact valid_cons (Or.inr (Or.inr (Or.inl ⟨e, e', C, D, α, β, hC, hD, rfl⟩))) ih
  | weaken _ hC sub ih => exact valid_cons (Or.inr (Or.inr (Or.inr ⟨_, hC, sub⟩))) ih

/-- Any syntactic integer refutation admits a quadratic-size prefix with explicit
justifications at every position. Applying one simplification to its disjunction
of false constants derives the empty line. -/
theorem DeferredSimplification :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V))
    (π : List (PEqualNP.Search.QLine V)), PEqualNP.Search.IsResLinQSynRefutation F π →
  ∃ (ρ : List (PEqualNP.Search.QLine V)) (G : PEqualNP.Search.QLine V),
    PEqualNP.Search.resLinQSize ρ ≤ 6 * (PEqualNP.Search.resLinQSize π) ^ 2 ∧
    G ∈ ρ ∧ (∀ e ∈ G, e.1 = 0 ∧ e.2 ≠ 0) ∧
    PEqualNP.Search.IsResLinQSynRefutation F ([] :: ρ) ∧
    ∀ (front : List (PEqualNP.Search.QLine V)) (L : PEqualNP.Search.QLine V)
      (tail : List (PEqualNP.Search.QLine V)), ρ = front ++ (L :: tail) →
      (∃ C ∈ F, ∀ e, e ∈ L ↔ ∃ l ∈ C, e = PEqualNP.Search.litQEq l) ∨
      (∃ v : V, L = [PEqualNP.Search.litQEq (v, false), PEqualNP.Search.litQEq (v, true)]) ∨
      (∃ (e e' : PEqualNP.Search.QEq V) (C D : PEqualNP.Search.QLine V) (α β : ℤ),
        (e :: C) ∈ tail ∧ (e' :: D) ∈ tail ∧
        L = (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) ∨
      (∃ C ∈ tail, ∀ e ∈ C, e ∈ L) := by
  intro V _ _ F π h
  obtain ⟨ρ, d, hG, size⟩ := defer_simp_quadratic h
  have bad : ∀ e ∈ falseConstants π, e.1 = 0 ∧ e.2 ≠ 0 :=
    fun _ he => (mem_falseConstants.mp he).2
  exact ⟨ρ, falseConstants π, size, hG, bad, refute_at_end d hG bad, explicitNoSimpSuffixes d⟩

end PEqualNP.Search
