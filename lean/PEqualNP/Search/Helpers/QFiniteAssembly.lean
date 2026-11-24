import PEqualNP.Search.Helpers.QCoordinateCases
import Mathlib.Data.Finset.Max

/-! A finite family of proof states can share every premise already derived at
a lower rank. The assembly charges the local derivation of each state once. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V X : Type} [Fintype V] [DecidableEq V] [Fintype X]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)}

/-- Assemble a DAG of lower-ranked premises with a separate cost per state. -/
theorem qFiniteAssemblyWeighted (state : X → QLine V) (rank : X → ℕ) (pred : X → X → Prop)
    (lower : ∀ i j, pred i j → rank i < rank j) (cost : X → ℕ)
    (step : ∀ j, QCanAdd F {L | ∃ i, pred i j ∧ L = state i} (state j) (cost j)) :
    ∃ π, IsResLinQSynDerivation F π ∧ (∀ j, state j ∈ π) ∧
      resLinQSize π ≤ ∑ j, cost j := by
  classical
  let rec assemble (U : Finset X) (closed : ∀ j ∈ U, ∀ i, pred i j → i ∈ U) :
      ∃ π, IsResLinQSynDerivation F π ∧ (∀ j ∈ U, state j ∈ π) ∧
        resLinQSize π ≤ ∑ j ∈ U, cost j := by
    by_cases empty : U = ∅
    · subst U
      exact ⟨[],.nil,by simp,by simp [resLinQSize]⟩
    obtain ⟨j,hj,top⟩ := U.exists_max_image rank (Finset.nonempty_iff_ne_empty.mpr empty)
    have previous (z) (hz : z ∈ U) (i) (hp : pred i z) : i ∈ U.erase j := by
      refine Finset.mem_erase.mpr ⟨?_,closed z hz i hp⟩
      intro eq
      subst i
      exact (top z hz).not_gt (lower j z hp)
    obtain ⟨π,d,hit,n⟩ := assemble (U.erase j) (fun z hz => previous z (Finset.mem_of_mem_erase hz))
    obtain ⟨s,der,mem,localCost⟩ := step j π d (by
      rintro L ⟨i,hp,rfl⟩
      exact hit i (previous j hj i hp))
    refine ⟨s ++ π,der,?_,?_⟩
    · intro z hz
      by_cases eq : z=j
      · exact eq ▸ List.mem_append_left _ mem
      · exact List.mem_append_right _ (hit z (Finset.mem_erase.mpr ⟨eq,hz⟩))
    · have sz : resLinQSize (s ++ π) = resLinQSize s + resLinQSize π := by simp [resLinQSize]
      rw [sz, ← Finset.add_sum_erase U cost hj]
      exact Nat.add_le_add localCost n
  termination_by U.card
  decreasing_by classical exact Finset.card_erase_lt_of_mem hj
  obtain ⟨π,d,hit,n⟩ := assemble Finset.univ (by simp)
  exact ⟨π,d,fun j => hit j (Finset.mem_univ _),n⟩

/-- With a uniform cost B, the encoded size is at most the number of states times B. -/
theorem qFiniteAssembly (state : X → QLine V) (rank : X → ℕ) (pred : X → X → Prop)
    (lower : ∀ i j, pred i j → rank i < rank j) (B : ℕ)
    (step : ∀ j, QCanAdd F {L | ∃ i, pred i j ∧ L = state i} (state j) B) :
    ∃ π, IsResLinQSynDerivation F π ∧ (∀ j, state j ∈ π) ∧
      resLinQSize π ≤ Fintype.card X * B := by
  simpa using qFiniteAssemblyWeighted state rank pred lower (fun _ => B) step

end PEqualNP.Search.Helpers
