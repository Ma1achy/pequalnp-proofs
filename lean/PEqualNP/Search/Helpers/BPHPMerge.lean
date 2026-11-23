import PEqualNP.Search.Helpers.BPHPEssential
import PEqualNP.Search.Helpers.QSynMerges

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- To combine all the essential bit-pigeonhole inputs into a contradiction, a
dag-like syntactic R(lin) proof needs at least one fewer binary resolution
inference than there are collision clauses. This counts inference occurrences. -/
theorem bphp_binary_resolution_lower_bound {l k : ℕ}
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (trace : QSynMergeTrace (BPHP (2 ^ l + 1) l) π k) (hempty : [] ∈ π) :
    (2 ^ l + 1).choose 2 * 2 ^ l ≤ k + 1 := by
  by_cases hl : 0 < l
  · obtain ⟨S, hcard, _, hcrit⟩ := exists_bphp_critical_family hl
    rw [← hcard]
    exact critical_card_le_binary_add_one trace hempty S hcrit
  · have : l = 0 := by omega
    subst l
    simp

end PEqualNP.Search.Helpers
