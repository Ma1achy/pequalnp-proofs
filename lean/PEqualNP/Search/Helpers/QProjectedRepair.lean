import PEqualNP.Search.Helpers.QProjectedSimulation
import PEqualNP.Search.Helpers.ParityRepairCut
import PEqualNP.ProofComplexity.Helpers.Recomb

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- For each resolution with a falsifying assignment after projection, the clause
expressing its missing implication has a short parity derivation from the inputs. -/
def BoundedProjectionRepairs (φ : QEq V → LinEq V) (F : Set (Clause V))
    (π : List (QLine V)) (B : ℕ) : Prop :=
  ∀ (front tail : List (QLine V)) (e e' : QEq V) (C D : QLine V) (α β : ℤ),
    let R : QLine V := (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)
    π = front ++ (R :: tail) → (e :: C) ∈ tail → (e' :: D) ∈ tail →
    (∃ a : V → Bool, LinEqSat a (φ e) ∧ LinEqSat a (φ e') ∧ ¬ LinClauseSat a (projectLine φ R)) →
    ∃ δ : List (LinClause V), IsLinDerivation (linOfClause '' F) δ ∧
      repairClause (projectLine φ R) (φ e) (φ e') ∈ δ ∧ δ.length ≤ B

/-- A failed inference costs its repair proof and at most two binary parity
inferences. Each binary inference takes at most four ordinary lines. -/
theorem projected_refutation_with_repairs [Fintype V] (φ : QEq V → LinEq V)
    (lit : ∀ t : V × Bool, φ (litQEq t) = ({t.1}, t.2))
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinEqSat a (φ e))
    {F : Set (Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π) (B : ℕ) (repairs : BoundedProjectionRepairs φ F π B) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ (B + 8) * π.length + 1 := by
  classical
  apply projected_refutation_of_steps φ lit dead seed ref (by omega : 1 ≤ B + 8)
  intro front tail e e' C D α β R eq hC hD ρ d hA hB
  have left := projected_head_or_target (R := R) φ e
    (fun u hu => List.mem_cons_of_mem _ (List.mem_append_left D hu))
  have right := projected_head_or_target (R := R) φ e'
    (fun u hu => List.mem_cons_of_mem _ (List.mem_append_right C hu))
  by_cases bad : ∃ a : V → Bool, LinEqSat a (φ e) ∧ LinEqSat a (φ e') ∧
      ¬ LinClauseSat a (projectLine φ R)
  · obtain ⟨δ, dδ, hm, cost⟩ := repairs front tail e e' C D α β eq hC hD bad
    have appended := Recomb.deriv_append d dδ (fun _ h => Or.inl h)
    obtain ⟨s, ds, hs, small⟩ := applyRepair (φ e) (φ e') appended
      (List.mem_append_right δ hA) (List.mem_append_right δ hB)
      (List.mem_append_left ρ hm) left right
    refine ⟨s ++ δ, by simpa only [List.append_assoc] using ds,
      List.mem_append_left δ hs, ?_⟩
    simp only [List.length_append]
    omega
  · have sound (a : V → Bool) (sa : LinClauseSat a (projectLine φ (e :: C)))
        (sb : LinClauseSat a (projectLine φ (e' :: D))) : LinClauseSat a (projectLine φ R) := by
      by_contra no
      exact bad ⟨a, (left a sa).resolve_left no, (right a sb).resolve_left no, no⟩
    obtain ⟨s, ds, hs, small⟩ := paritySemanticStep d hA hB sound
    exact ⟨s, ds, hs, by omega⟩

end PEqualNP.Search.Helpers
