import PEqualNP.Search.Helpers.BPHPTreeRate

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- A syntactic weakening to a shorter list must remove some duplicate from its
premise, since every distinct premise equation survives. -/
theorem not_nodup_of_shorter_superlist {α : Type*} {xs ys : List α}
    (sub : ∀ x ∈ xs, x ∈ ys) (short : ys.length < xs.length) : ¬ xs.Nodup := by
  classical
  intro h
  have inclusion : xs.toFinset ⊆ ys.toFinset :=
    fun x hx => List.mem_toFinset.mpr (sub x (List.mem_toFinset.mp hx))
  have bound := (Finset.card_le_card inclusion).trans (List.toFinset_card_le ys)
  rw [List.toFinset_card_of_nodup h] at bound
  omega

/-- Any line consisting entirely of false constants can be weakened to the empty
line. This adds no input leaves, so the bit-PHP leaf lower bound already holds
at that line, including when it is a single equation. -/
theorem bphp_false_line_leaf_rate {N l : ℕ} {L : QLine (Fin N × Fin l)} (hl : 17 ≤ l)
    (t : ResLinQTree (BPHP N l) L) (bad : ∀ e ∈ L, e.1 = 0 ∧ e.2 ≠ 0) :
    2 ^ (2 ^ ((l - 17) / 6)) + 2 ≤ 4 * (Tree.axiomUses t).length := by
  have empty : ∀ a, QLine.Holds a L → QLine.Holds a [] := by
    rintro a ⟨e, he, hs⟩
    obtain ⟨hz, hn⟩ := bad e he
    exact False.elim (hn (by simpa [QEq.Holds, hz] using hs.symm))
  exact Tree.bphp_leaf_rate hl (.weaken t empty)

end PEqualNP.Search.Helpers
