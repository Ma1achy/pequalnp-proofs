import PEqualNP.Search.Helpers.QCoordinateCases
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Assemble one syntactic proof per subset. An inference for H can reuse all
states obtained by deleting an element of H. Every subset is charged only once. -/
theorem qSubsetAssembly {V X : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    {F : Set (ProofComplexity.Clause V)} (state : Finset X → QLine V) (B : ℕ)
    (step : ∀ H : Finset X, QCanAdd F {L | ∃ x ∈ H, L = state (H.erase x)} (state H) B) :
    ∃ π, IsResLinQSynDerivation F π ∧ (∀ H, state H ∈ π) ∧
      resLinQSize π ≤ 2 ^ Fintype.card X * B := by
  classical
  let rec assemble (U : Finset (Finset X))
      (closed : ∀ H ∈ U, ∀ x ∈ H, H.erase x ∈ U) :
      ∃ π, IsResLinQSynDerivation F π ∧ (∀ H ∈ U, state H ∈ π) ∧ resLinQSize π ≤ U.card * B := by
    by_cases empty : U = ∅
    · subst U
      exact ⟨[],.nil,by simp,by simp [resLinQSize]⟩
    obtain ⟨H,memH,maxH⟩ := U.exists_max_image Finset.card (Finset.nonempty_iff_ne_empty.mpr empty)
    have prev (J) (memJ : J ∈ U) (x) (hx : x ∈ J) : J.erase x ∈ U.erase H := by
      refine Finset.mem_erase.mpr ⟨?_,closed J memJ x hx⟩
      intro eq
      have smaller := Finset.card_erase_lt_of_mem hx
      rw [eq] at smaller
      exact (maxH J memJ).not_gt smaller
    obtain ⟨π,d,hit,cost⟩ := assemble (U.erase H)
      (fun J memJ x hx => prev J (Finset.mem_of_mem_erase memJ) x hx)
    obtain ⟨σ,dσ,hσ,bσ⟩ := step H π d (by
      rintro L ⟨x,hx,rfl⟩
      exact hit _ (prev H memH x hx))
    refine ⟨σ ++ π,dσ,?_,?_⟩
    · intro J memJ
      by_cases e : J = H
      · exact e ▸ List.mem_append_left _ hσ
      · exact List.mem_append_right _ (hit J (Finset.mem_erase.mpr ⟨e,memJ⟩))
    · have card : (U.erase H).card + 1 = U.card := Finset.card_erase_add_one memH
      have sz : resLinQSize (σ ++ π) = resLinQSize σ + resLinQSize π := by simp [resLinQSize]
      rw [sz,← card,Nat.succ_mul]
      omega
  termination_by U.card
  decreasing_by exact Finset.card_erase_lt_of_mem memH
  obtain ⟨π,d,hit,price⟩ := assemble Finset.univ (by simp)
  exact ⟨π,d,fun H => hit H (Finset.mem_univ _),by simpa using price⟩

end PEqualNP.Search.Helpers
