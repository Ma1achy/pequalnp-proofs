import PEqualNP.Search.Helpers.ParityTreeProof

/-! Simulate an inference by resolving over the leaf pairs of parity decision
trees for its premises. A false leaf provides an earlier clause. Under two
true leaves the implication to the target makes the combined guard valid. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)}

/-- Semantic implication between two tree outputs and a parity clause gives
a derivation of the target of size proportional to the product of leaf counts. -/
theorem trees_imply_clause (tA tB : ParityTree V) (G : LinClause V) (hΓ : Γ.Nonempty)
    (hA : ∀ C, (false, C) ∈ tA.cells → C ∈ Γ)
    (hB : ∀ C, (false, C) ∈ tB.cells → C ∈ Γ)
    (rule : ∀ a, tA.eval a = true → tB.eval a = true → LinClauseSat a G) :
    CanAdd F Γ G (4 * (tA.leaves + 1) * (tB.leaves + 1)) := by
  classical
  have leaf (a b : Bool) (A B : LinClause V) (ha : (a, A) ∈ tA.cells) (hb : (b, B) ∈ tB.cells) :
      CanAdd F Γ (G ∪ A ∪ B) 1 := by
    cases a with
    | false =>
      apply CanAdd.of_imp (hA A ha)
      rintro _ ⟨e, he, hs⟩
      exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he), hs⟩
    | true =>
      cases b with
      | false =>
        apply CanAdd.of_imp (hB B hb)
        rintro _ ⟨e, he, hs⟩
        exact ⟨e, Finset.mem_union_right _ he, hs⟩
      | true =>
        apply CanAdd.of_tautology hΓ
        intro x
        by_cases sa : LinClauseSat x A
        · obtain ⟨e, he, hs⟩ := sa
          exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _ he), hs⟩
        by_cases sb : LinClauseSat x B
        · obtain ⟨e, he, hs⟩ := sb
          exact ⟨e, Finset.mem_union_right _ he, hs⟩
        obtain ⟨e, he, hs⟩ := rule x (tA.eval_of_mem_cells x ha sa) (tB.eval_of_mem_cells x hb sb)
        exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _ he), hs⟩
  have inner (a : Bool) (A : LinClause V) (ha : (a, A) ∈ tA.cells) :=
    split_tree tB (G ∪ A) 1 (fun b B hb => leaf a b A B ha hb)
  have outer := split_tree tA G _ inner
  intro ρ hd he
  obtain ⟨σ, hσ, hm, hlen⟩ := outer ρ hd he
  refine ⟨σ, hσ, hm, hlen.trans ?_⟩
  have hpos := tB.leaves_pos
  have eq : tB.leaves * (1 + 1) - 1 + 1 = 2 * tB.leaves := by omega
  rw [eq]
  have := Nat.sub_le (tA.leaves * (2 * tB.leaves)) 1
  nlinarith

/-- Unary inference using the same budget as a binary step on a repeated premise. -/
theorem tree_implies_clause (t : ParityTree V) (G : LinClause V) (hΓ : Γ.Nonempty)
    (h : ∀ C, (false, C) ∈ t.cells → C ∈ Γ)
    (rule : ∀ a, t.eval a = true → LinClauseSat a G) :
    CanAdd F Γ G (4 * (t.leaves + 1) * (t.leaves + 1)) :=
  trees_imply_clause t t G hΓ h h (fun a ha _ => rule a ha)

end PEqualNP.Search.Helpers
