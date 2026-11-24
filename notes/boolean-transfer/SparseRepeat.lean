import TourLayer
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Truncated mixed clipping differences for one monomial and for formal degree layers. -/

namespace BooleanTransfer.SparseRepeat

open Finset MvPolynomial
open BooleanTransfer.PartialLayer

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- The only variables on which clipping changes a monomial. -/
def repeated (a : σ →₀ ℕ) : Finset σ := univ.filter (fun i => 1 < a i)

private noncomputable def excess (a : σ →₀ ℕ) (i : σ) : MvPolynomial σ R :=
  X i ^ (a i - 1)

/-- Once the squarefree monomial is factored out, clipping coordinate i
replaces its excess power by 1. Its difference contributes 1 minus that power. -/
noncomputable def differenceFactor (a : σ →₀ ℕ) (J : Finset σ) : MvPolynomial σ R :=
  (∏ i ∈ J, (1 - excess a i)) * ∏ i ∈ Jᶜ, excess a i

/-- The full squarefree monomial times all mixed differences up through order r. -/
noncomputable def truncatedTerm (a : σ →₀ ℕ) (c : R) (r : ℕ) : MvPolynomial σ R :=
  monomial (clip Set.univ a) c *
    ∑ J : Finset σ with J.card ≤ r, differenceFactor a J

private theorem factorZero {a : σ →₀ ℕ} {J : Finset σ} (h : ¬ J ⊆ repeated a) :
    differenceFactor (R := R) a J = 0 := by
  obtain ⟨i, hi, hn⟩ := Finset.not_subset.mp h
  have low : a i ≤ 1 := by simpa [repeated] using hn
  have van : (1 - excess a i : MvPolynomial σ R) = 0 := by
    simp [excess, Nat.sub_eq_zero_of_le low]
  rw [differenceFactor, Finset.prod_eq_zero hi van, zero_mul]

/-- A monomial with at most r repeated coordinates has no mixed correction
of order above r, so the truncated sum fully clips it. -/
theorem truncatedTerm_eq {a : σ →₀ ℕ} {r : ℕ} (h : (repeated a).card ≤ r) (c : R) :
    truncatedTerm a c r = monomial (clip Set.univ a) c := by
  classical
  have collapse : (∑ J : Finset σ with J.card ≤ r, differenceFactor (R := R) a J) =
      ∑ J : Finset σ, differenceFactor a J := by
    rw [sum_filter]
    refine sum_congr rfl fun J _ => ?_
    by_cases small : J.card ≤ r
    · simp [small]
    · have hz := factorZero (R := R) (a := a) (J := J)
          (fun hJ => small ((Finset.card_le_card hJ).trans h))
      simp [small, hz]
  rw [truncatedTerm, collapse]
  simp only [differenceFactor, ← Fintype.prod_add]
  simp

private theorem restore_excess (a : σ →₀ ℕ) (c : R) (T : Finset σ) :
    monomial (clip Set.univ a) c * (∏ i ∈ Tᶜ, excess a i) =
      monomial (clip (↑T : Set σ) a) c := by
  classical
  simp only [excess, prod_X_pow, monomial_mul, mul_one]
  apply congrArg (fun d : σ →₀ ℕ => monomial d c)
  ext i
  by_cases hi : i ∈ T
  · simp [clip, Finsupp.indicator, hi]
  · simp [clip, Finsupp.indicator, hi]
    omega

/-- The factorized correction is exactly the signed sum obtained by
distributing the product of (clip_i - identity) over the chosen coordinates. -/
theorem mixedDifference_eq (a : σ →₀ ℕ) (c : R) (J : Finset σ) :
    monomial (clip Set.univ a) c * differenceFactor a J =
      ∑ T ∈ J.powerset, (-1 : MvPolynomial σ R) ^ (J \ T).card *
        monomial (clip (↑T : Set σ) a) c := by
  classical
  rw [differenceFactor]
  simp_rw [sub_eq_add_neg, Finset.prod_add, Finset.prod_const_one, one_mul, Finset.prod_neg]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro T hT
  have sub : T ⊆ J := mem_powerset.mp hT
  have split : (J \ T) ∪ Jᶜ = Tᶜ := by
    ext i
    simp only [mem_union, mem_sdiff, mem_compl]
    constructor
    · rintro (⟨_, hn⟩ | hn)
      · exact hn
      · exact fun h => hn (sub h)
    · intro hn
      by_cases h : i ∈ J
      · exact Or.inl ⟨h, hn⟩
      · exact Or.inr h
  have dis : Disjoint (J \ T) Jᶜ := Finset.disjoint_left.mpr fun _ h hn =>
    (mem_compl.mp hn) (mem_sdiff.mp h).1
  rw [← restore_excess a c T, ← split, prod_union dis]
  ring

/-- Extend the truncated rule linearly to the finite formal expansion. -/
noncomputable def sparseReduction (r : ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ a ∈ p.support, truncatedTerm a (coeff a p) r

/-- This expression uses only ordinary partial clipping operations, with
the same subsets for every monomial of the input polynomial. -/
theorem sparseReduction_eq_signed (r : ℕ) (p : MvPolynomial σ R) :
    sparseReduction r p =
      ∑ J : Finset σ with J.card ≤ r, ∑ T ∈ J.powerset,
        (-1 : MvPolynomial σ R) ^ (J \ T).card * reduceOn (↑T : Set σ) p := by
  classical
  unfold sparseReduction truncatedTerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro J _
  simp_rw [mixedDifference_eq]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro T _
  rw [reduceOn, Finset.mul_sum]

omit [Fintype σ] [DecidableEq σ] in
private theorem clipped_degree (a : σ →₀ ℕ) :
    (clip Set.univ a).degree = a.support.card := by
  classical
  rw [Finsupp.degree_apply]
  calc
    _ = ∑ _i ∈ a.support, 1 := by
      apply sum_congr rfl
      intro i hi
      have h : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
      simp [clip, Nat.min_eq_right (Nat.one_le_iff_ne_zero.mpr h)]
    _ = _ := by simp

omit [Fintype σ] [DecidableEq σ] in
private theorem layer_monomial_mul_zero (a : σ →₀ ℕ) (c : R) {m : ℕ}
    (hm : m < a.degree) (q : MvPolynomial σ R) :
    homogeneousComponent m (monomial a c * q) = 0 := by
  induction q using MvPolynomial.induction_on' with
  | monomial b e =>
    rw [monomial_mul, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl)]
    apply if_neg
    rw [map_add]
    omega
  | add p q hp hq => simp [mul_add, map_add, hp, hq]

/-- Repeated coordinates may vary between monomials. Only monomials with
support at most m need the promise in order to recover the full degree-m layer. -/
theorem sparseReduction_layer (p : MvPolynomial σ R) (m r : ℕ)
    (hr : ∀ a ∈ p.support, a.support.card ≤ m → (repeated a).card ≤ r) :
    homogeneousComponent m (sparseReduction r p) =
      homogeneousComponent m (reduceOn Set.univ p) := by
  classical
  simp only [sparseReduction, reduceOn, map_sum]
  apply sum_congr rfl
  intro a ha
  by_cases hs : a.support.card ≤ m
  · rw [truncatedTerm_eq (hr a ha hs)]
  · have hi : m < (clip Set.univ a).degree := by
      rw [clipped_degree]
      omega
    rw [truncatedTerm, layer_monomial_mul_zero _ _ hi,
      homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), if_neg hi.ne]

open BooleanTransfer.TourLayer in
/-- Under the per-monomial bound, the formal m-layer of the signed sum of
ordinary partial clippings of a cube-correct tour decision polynomial is hc. -/
theorem tour_signed_layer {m r : ℕ} (p : MvPolynomial (Arc m) (ZMod 2))
    (hr : ∀ a ∈ p.support, a.support.card ≤ m → (repeated a).card ≤ r)
    (correct : ∀ E, eval (indicator (ZMod 2) E) p = if (tours E).Nonempty then 1 else 0) :
    homogeneousComponent m (∑ J : Finset (Arc m) with J.card ≤ r, ∑ T ∈ J.powerset,
        (-1 : MvPolynomial (Arc m) (ZMod 2)) ^ (J \ T).card * reduceOn (↑T : Set (Arc m)) p) =
      Statement.hc (ZMod 2) m := by
  classical
  rw [← sparseReduction_eq_signed r p, sparseReduction_layer p m r hr]
  exact partial_component_of_correct Set.univ p (by simp) correct

end BooleanTransfer.SparseRepeat

#print axioms BooleanTransfer.SparseRepeat.truncatedTerm_eq
#print axioms BooleanTransfer.SparseRepeat.sparseReduction_layer
#print axioms BooleanTransfer.SparseRepeat.tour_signed_layer
