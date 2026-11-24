import PartialLayer
import Mathlib.Data.Nat.Choose.Bounds

/-! Test monomials and counting for a fixed XOR of partial clipping operators.
The final cost counts evaluations of separately interpolated samples. -/

namespace BooleanTransfer.CoverCost

open Finset MvPolynomial BooleanTransfer.PartialLayer

variable {σ : Type*} [DecidableEq σ]

/-- The monomial on A with exponent two on D ∩ A and one on A ∖ D. -/
def testExponent (A D : Finset σ) : σ →₀ ℕ where
  support := A
  toFun i := if i ∈ A then if i ∈ D then 2 else 1 else 0
  mem_support_toFun i := by
    by_cases h : i ∈ A <;> by_cases k : i ∈ D <;> simp [h,k]

private theorem clip_test_iff (A D B : Finset σ) (sub : D ⊆ A) :
    clip (B : Set σ) (testExponent A D) = testExponent A ∅ ↔ D ⊆ B := by
  classical
  constructor
  · intro h i hi
    by_contra miss
    have eq := DFunLike.congr_fun h i
    simp [clip, testExponent, sub hi, hi, miss] at eq
  · intro h
    ext i
    by_cases ha : i ∈ A <;> by_cases hd : i ∈ D <;> by_cases hb : i ∈ B <;>
      simp_all [clip, testExponent]
    exact hb (h hd)

private theorem squarefree_degree (A : Finset σ) : (testExponent A ∅).degree = A.card := by
  rw [Finsupp.degree_apply]
  change (∑ i ∈ A, (testExponent A ∅) i) = A.card
  calc
    _ = ∑ _i ∈ A, 1 := Finset.sum_congr rfl fun i hi => by simp [testExponent, hi]
    _ = _ := by simp

/-- The squarefree coefficient detects exactly whether the sample contains D. -/
theorem coeff_sample (A D B : Finset σ) (sub : D ⊆ A) :
    coeff (testExponent A ∅) (reduceOn (B : Set σ) (monomial (testExponent A D) (1 : ZMod 2)))
      = if D ⊆ B then 1 else 0 := by
  classical
  have one : (1 : ZMod 2) ≠ 0 := by decide
  simp [reduceOn, support_monomial, coeff_monomial, one, clip_test_iff A D B sub]

/-- A correct degree-m layer on these individual tests forces a sample containing
every r-set. Samples are exactly those with nonzero coefficient in the XOR. -/
theorem covers_of_layer_tests [Fintype σ] (samples : Finset (Finset σ)) {m r : ℕ}
    (hr : r ≤ m) (hm : m ≤ Fintype.card σ)
    (tests : ∀ A D : Finset σ, A.card = m → D.card = r → D ⊆ A →
      homogeneousComponent m (∑ B ∈ samples,
        reduceOn (B : Set σ) (monomial (testExponent A D) (1 : ZMod 2))) =
      homogeneousComponent m (reduceOn Set.univ (monomial (testExponent A D) (1 : ZMod 2)))) :
    ∀ D : Finset σ, D.card = r → ∃ B ∈ samples, D ⊆ B := by
  classical
  intro D hd
  obtain ⟨A, sub, _, size⟩ := exists_subsuperset_card_eq (subset_univ D)
    (hd.trans_le hr) (by simpa using hm)
  have key := congrArg (coeff (testExponent A ∅)) (tests A D size hd sub)
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent, squarefree_degree, if_pos size] at key
  rw [coeff_sum, ← Finset.coe_univ, coeff_sample A D univ sub, if_pos (subset_univ D)] at key
  by_contra none
  push Not at none
  have zero : (∑ B ∈ samples, coeff (testExponent A ∅)
      (reduceOn (B : Set σ) (monomial (testExponent A D) (1 : ZMod 2)))) = 0 := by
    refine sum_eq_zero fun B hb => ?_
    rw [coeff_sample A D B sub, if_neg (none B hb)]
  have ne : (0 : ZMod 2) ≠ 1 := by decide
  exact ne (zero.symm.trans (by simpa only [if_pos size] using key))

/-- Counting covered r-sets gives both lower bounds. Overlap can only increase
the summed cardinalities. The last expression counts all sample assignments. -/
theorem cover_cost [Fintype σ] (samples : Finset (Finset σ)) (r : ℕ)
    (cover : ∀ D : Finset σ, D.card = r → ∃ B ∈ samples, D ⊆ B) :
    (Fintype.card σ).choose r ≤ ∑ B ∈ samples, B.card.choose r ∧
      (∑ B ∈ samples, B.card.choose r) ≤ ∑ B ∈ samples, 2 ^ B.card := by
  classical
  constructor
  · have sub : (univ : Finset σ).powersetCard r ⊆ samples.biUnion (powersetCard r) := by
      intro D hd
      have size := (mem_powersetCard.mp hd).2
      obtain ⟨B, hb, hD⟩ := cover D size
      exact mem_biUnion.mpr ⟨B, hb, mem_powersetCard.mpr ⟨hD, size⟩⟩
    simpa only [card_powersetCard, card_univ] using
      (card_le_card sub).trans card_biUnion_le
  · exact sum_le_sum fun B _ => Nat.choose_le_two_pow B.card r

end BooleanTransfer.CoverCost
