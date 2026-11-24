import PEqualNP.Search.Helpers.SignedFormulaPruning
import PEqualNP.Search.Helpers.PetersenLeafSum

namespace PEqualNP.Search

open Petersen2541 PetersenGateWitness

/-- Every AND/OR/NOT formula computing the twelve-edge function with at most
one occurrence of input zero has at least sixteen variable leaves. Each
leaf can independently read its variable in either polarity. -/
theorem PetersenFormula2541
    (t : FormulaTree) (lab : t.Pos → Fin 9) (sign : t.Pos → Bool)
    (restrict0 : t.occurrences lab 0 ≤ 1)
    (computes : ∀ x, t.eval (fun p => x (lab p) != sign p) = edgeFunction x) :
    16 ≤ Fintype.card t.Pos := by
  rw [← t.sum_occurrences lab]
  apply sum_occurrences_ge16 _ restrict0
  · have h := t.occurrence_product_bound lab sign _ computes (by decide) family058
    simpa [Finset.prod_insert, mul_assoc] using h
  · have h := t.occurrence_product_bound lab sign _ computes (by decide) family016
    simpa [Finset.prod_insert, mul_assoc] using h
  · have h := t.occurrence_product_bound lab sign _ computes (by decide) family237
    simpa [Finset.prod_insert, mul_assoc] using h
  · have h := t.occurrence_product_bound lab sign _ computes (by decide) family04
    simpa [Finset.prod_insert] using h

/-- The corresponding lower bound counts binary gates, allowing unlimited
unary negations as well as free signs at the leaves. -/
theorem PetersenFormula2541_binaryGates
    (t : FormulaTree) (lab : t.Pos → Fin 9) (sign : t.Pos → Bool)
    (restrict0 : t.occurrences lab 0 ≤ 1)
    (computes : ∀ x, t.eval (fun p => x (lab p) != sign p) = edgeFunction x) :
    15 ≤ t.binaryGates := by
  have leaves := PetersenFormula2541 t lab sign restrict0 computes
  have bound := t.card_pos_le_binaryGates_add_one
  omega

end PEqualNP.Search
