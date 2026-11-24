import TourLayer

/-! Values on a Hamming ball determine every canonical ANF layer through its radius. -/

namespace BooleanTransfer.BallAgreement

open Finset MvPolynomial

variable {α : Type*}

/-- In characteristic two, the ANF coefficient at S is the subset zeta sum. -/
def coefficient (f : Finset α → ZMod 2) (S : Finset α) : ZMod 2 :=
  ∑ T ∈ S.powerset, f T

theorem coefficient_agree (f g : Finset α → ZMod 2) (d : ℕ)
    (ball : ∀ T, T.card ≤ d → f T = g T) (S : Finset α) (small : S.card ≤ d) :
    coefficient f S = coefficient g S := by
  apply sum_congr rfl
  intro T hT
  exact ball T ((card_le_card (mem_powerset.mp hT)).trans small)

/-- Equality of the coefficient prefix is equivalent to equality of values on the ball. -/
theorem coefficient_ball_iff (f g : Finset α → ZMod 2) (d : ℕ) :
    (∀ S, S.card ≤ d → coefficient f S = coefficient g S) ↔
      ∀ S, S.card ≤ d → f S = g S := by
  classical
  constructor
  · intro eqc S
    refine S.strongInductionOn ?_
    intro S ih small
    have self : S ∈ S.powerset := mem_powerset.mpr (Subset.rfl)
    have rest : ∑ T ∈ S.powerset.erase S, f T = ∑ T ∈ S.powerset.erase S, g T := by
      apply sum_congr rfl
      intro T hT
      obtain ⟨ne, sub⟩ := mem_erase.mp hT
      have inc := mem_powerset.mp sub
      exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨inc, ne⟩) ((card_le_card inc).trans small)
    have eq := eqc S small
    unfold coefficient at eq
    rw [← sum_erase_add _ f self, ← sum_erase_add _ g self, rest] at eq
    exact add_left_cancel eq
  · exact fun h S => coefficient_agree f g d h S

variable [Fintype α]

/-- The squarefree polynomial with the subset-inversion coefficients of f. -/
noncomputable def anf (f : Finset α → ZMod 2) : MvPolynomial α (ZMod 2) :=
  ∑ S : Finset α, C (coefficient f S) * ∏ i ∈ S, X i

/-- Equality on a ball gives formal polynomial equality of every layer in that ball. -/
theorem layers_agree (f g : Finset α → ZMod 2) (d : ℕ)
    (ball : ∀ T, T.card ≤ d → f T = g T) :
    ∀ j ≤ d, homogeneousComponent j (anf f) = homogeneousComponent j (anf g) := by
  classical
  intro j hj
  simp only [anf, map_sum]
  apply sum_congr rfl
  intro S _
  have mono : IsHomogeneous (∏ i ∈ S, (X i : MvPolynomial α (ZMod 2))) S.card := by
    simpa using IsHomogeneous.prod S (fun i => X (R := ZMod 2) i) (fun _ => 1)
      (fun i _ => isHomogeneous_X _ i)
  rw [homogeneousComponent_of_mem (mono.C_mul _), homogeneousComponent_of_mem (mono.C_mul _)]
  by_cases h : j = S.card
  · rw [coefficient_agree f g d ball S (h ▸ hj)]
  · simp [h]

open BooleanTransfer.TourLayer in
/-- A predicate correct on sparse directed graphs inherits the low layers of tour existence. -/
theorem tour_layers {m d : ℕ} (f : Finset (Arc m) → ZMod 2)
    (ball : ∀ E, E.card ≤ d → f E = if (tours E).Nonempty then 1 else 0) :
    ∀ j ≤ d, homogeneousComponent j (anf f) = homogeneousComponent j (decisionANF m) :=
  layers_agree f (fun E => if (tours E).Nonempty then 1 else 0) d ball

end BooleanTransfer.BallAgreement

#print axioms BooleanTransfer.BallAgreement.coefficient_agree
#print axioms BooleanTransfer.BallAgreement.layers_agree
#print axioms BooleanTransfer.BallAgreement.tour_layers
#print axioms BooleanTransfer.BallAgreement.coefficient_ball_iff
