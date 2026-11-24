import PEqualNP.Search.Helpers.ParityTreeProof

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Append a list of local parity goals to a single DAG derivation. Each local
construction may reuse the starting lines and all the lines produced so far. -/
theorem canAdd_many {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)}
    (goals : List (LinClause V)) (m : ℕ) (hgoals : ∀ G ∈ goals, CanAdd F Γ G m)
    (ρ : List (LinClause V)) (hd : IsLinDerivation F ρ) (hΓ : ∀ C ∈ Γ, C ∈ ρ) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧
      (∀ G ∈ goals, G ∈ σ ++ ρ) ∧ σ.length ≤ goals.length * m := by
  induction goals with
  | nil => exact ⟨[], hd, by simp, by simp⟩
  | cons G goals ih =>
    obtain ⟨τ, dτ, hτ, nτ⟩ := ih (fun C hC => hgoals C (List.mem_cons_of_mem G hC))
    obtain ⟨υ, dυ, hυ, nυ⟩ := hgoals G List.mem_cons_self (τ ++ ρ) dτ
      (fun C hC => List.mem_append_right _ (hΓ C hC))
    refine ⟨υ ++ τ, by simpa only [List.append_assoc] using dυ, ?_, ?_⟩
    · intro C hC
      rw [List.append_assoc]
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hυ
      · exact List.mem_append_right _ (hτ C hC)
    · rw [List.length_append, List.length_cons, Nat.succ_mul]
      omega

end PEqualNP.Search.Helpers
