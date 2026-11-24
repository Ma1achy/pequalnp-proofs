import PEqualNP.Search.Helpers.ParityTreeProof
import PEqualNP.ProofComplexity.Helpers.Lin

/-! Derive a parity repair clause from a decision tree that finds an input
violation on assignments falsifying the repair. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- At each leaf, all assignments falsifying both the repair and the path's
blocking clause violate one input clause. Add that input, weaken to the union
of the repair and the path clause, and resolve the leaf conclusions up the tree. -/
theorem repair_from_parity_tree {V : Type} [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}
    (R : PEqualNP.ProofComplexity.LinClause V) (t : ParityTree V)
    (search : ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F,
      ∀ a, ¬ LinClauseSat a R → ¬ LinClauseSat a B → ¬ ClauseSat a C) :
    ∃ ρ, IsLinDerivation (linOfClause '' F) ρ ∧ R ∈ ρ ∧ ρ.length ≤ 3 * t.leaves - 1 := by
  classical
  have add : CanAdd (linOfClause '' F) ∅ R (t.leaves * (2 + 1) - 1) := by
    apply split_tree t R 2
    intro b B hb ρ hd _
    obtain ⟨C, hC, hbad⟩ := search b B hb
    have input : IsLinDerivation (linOfClause '' F) (linOfClause C :: ρ) :=
      hd.ax ⟨C, hC, rfl⟩
    refine ⟨[R ∪ B, linOfClause C], input.weak List.mem_cons_self ?_, List.mem_cons_self, by simp⟩
    intro a hinput
    by_contra h
    have hr : ¬ LinClauseSat a R := by
      rintro ⟨e, he, hs⟩
      exact h ⟨e, Finset.mem_union_left _ he, hs⟩
    have hb' : ¬ LinClauseSat a B := by
      rintro ⟨e, he, hs⟩
      exact h ⟨e, Finset.mem_union_right _ he, hs⟩
    exact hbad a hr hb' ((PEqualNP.ProofComplexity.Helpers.linOfClause_sat a C).mp hinput)
  obtain ⟨ρ, d, hR, hs⟩ := add [] .nil (by simp)
  exact ⟨ρ, by simpa using d, by simpa using hR, by simpa [Nat.mul_comm] using hs⟩

end PEqualNP.Search.Helpers
