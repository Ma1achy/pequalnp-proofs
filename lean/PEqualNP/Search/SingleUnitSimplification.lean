import PEqualNP.Search.DeferredSimplification
import PEqualNP.Search.Helpers.QConstantUnit

namespace PEqualNP.Search

/-- Normalize any syntactic integer refutation to a quadratic-size proof with a
simplification-free prefix and a final simplification of one contradictory equation. -/
theorem SingleUnitSimplification :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V))
    (π : List (PEqualNP.Search.QLine V)), PEqualNP.Search.IsResLinQSynRefutation F π →
  ∃ (D : ℤ) (ρ : List (PEqualNP.Search.QLine V)),
    D ≠ 0 ∧ [(0, D)] ∈ ρ ∧
    PEqualNP.Search.IsResLinQSynRefutation F ([] :: ρ) ∧
    Nat.size D.natAbs ≤ 1 + PEqualNP.Search.resLinQSize π ∧
    PEqualNP.Search.resLinQSize ([] :: ρ) ≤ 20 * (PEqualNP.Search.resLinQSize π + 1) ^ 2 + 1 ∧
    ∀ (front : List (PEqualNP.Search.QLine V)) (L : PEqualNP.Search.QLine V)
      (tail : List (PEqualNP.Search.QLine V)), ρ = front ++ (L :: tail) →
      (∃ C ∈ F, ∀ e, e ∈ L ↔ ∃ l ∈ C, e = PEqualNP.Search.litQEq l) ∨
      (∃ v : V, L = [PEqualNP.Search.litQEq (v, false), PEqualNP.Search.litQEq (v, true)]) ∨
      (∃ (e e' : PEqualNP.Search.QEq V) (C D : PEqualNP.Search.QLine V) (α β : ℤ),
        (e :: C) ∈ tail ∧ (e' :: D) ∈ tail ∧
        L = (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) ∨
      (∃ C ∈ tail, ∀ e ∈ C, e ∈ L) := by
  intro V _ _ F π hπ
  obtain ⟨D, ρ, hD, d, unit, finalStep, bits, size⟩ := Helpers.single_simp_unit_refutation hπ
  exact ⟨D, ρ, hD, unit, finalStep, bits, size, explicitNoSimpSuffixes d⟩

end PEqualNP.Search
