import PEqualNP.Search.Helpers.ParityPointCover

/-! Querying every bit in a finite set W determines the truth of any input
clause supported on those bits. This yields a parity decision tree for
finding a violated clause wherever a chosen parity repair fails. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- Query each coordinate of W once. Two points in the same leaf cell agree
on every queried coordinate. -/
theorem query_support_tree (W : Finset V) :
    ∃ t : ParityTree V, t.leaves = 2 ^ W.card ∧
      ∀ b B, (b, B) ∈ t.cells → ∀ a z, ¬ LinClauseSat a B → ¬ LinClauseSat z B →
        ∀ v ∈ W, a v = z v := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨.leaf false, by simp [ParityTree.leaves], by simp⟩
  | @insert i W hi ih =>
    obtain ⟨t, count, agree⟩ := ih
    refine ⟨.node {i} t t, ?_, ?_⟩
    · simp [ParityTree.leaves, hi, count, pow_succ, Nat.mul_two]
    · intro b B hm a z ha hz v hv
      have branch (B' : PEqualNP.ProofComplexity.LinClause V) (hb : (b, B') ∈ t.cells) (bit : Bool)
          (part : ∀ x, ¬ LinClauseSat x B → x i = bit ∧ ¬ LinClauseSat x B') :
          a v = z v := by
        obtain ⟨ahi, haf⟩ := part a ha
        obtain ⟨zhi, hzf⟩ := part z hz
        rcases Finset.mem_insert.mp hv with rfl | hW
        · exact ahi.trans zhi.symm
        · exact agree b B' hb a z haf hzf v hW
      rcases singleton_node_cell i t t hm with ⟨B', hb, h⟩ | ⟨B', hb, h⟩
      · exact branch B' hb false h
      · exact branch B' hb true h

/-- If each counterexample to R violates an input supported on W, querying W
suffices to name an input violated throughout each counterexample cell. -/
theorem supported_violation_tree (F : Set (PEqualNP.ProofComplexity.Clause V))
    (R : PEqualNP.ProofComplexity.LinClause V) (W : Finset V) (hne : F.Nonempty)
    (hlocal : ∀ a, ¬ LinClauseSat a R → ∃ C ∈ F, (∀ lit ∈ C, lit.1 ∈ W) ∧ ¬ ClauseSat a C) :
    ∃ t : ParityTree V, t.leaves ≤ 2 ^ W.card ∧
      ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F,
        ∀ a, ¬ LinClauseSat a R → ¬ LinClauseSat a B → ¬ ClauseSat a C := by
  classical
  obtain ⟨t, size, same⟩ := query_support_tree W
  refine ⟨t, size.le, ?_⟩
  intro b B hm
  by_cases h : ∃ x, ¬ LinClauseSat x R ∧ ¬ LinClauseSat x B
  · obtain ⟨x, hxR, hxB⟩ := h
    obtain ⟨C, hC, supp, bad⟩ := hlocal x hxR
    refine ⟨C, hC, ?_⟩
    rintro a _ ha ⟨lit, hlit, val⟩
    exact bad ⟨lit, hlit, (same b B hm x a hxB ha lit.1 (supp lit hlit)).trans val⟩
  · obtain ⟨C, hc⟩ := hne
    exact ⟨C, hc, fun a ar ab => False.elim (h ⟨a, ar, ab⟩)⟩

end PEqualNP.Search.Helpers
