import BooleanIdeal

/-! Clipping chosen positive exponents to one preserves monomial support.
For the homogeneous layer of degree m one need only clip repeated coordinates
of monomials with support at most m. -/

namespace BooleanTransfer.PartialLayer

open Finset MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Replace every positive exponent indexed by B with one. -/
noncomputable def clip (B : Set σ) (a : σ →₀ ℕ) : σ →₀ ℕ := by
  classical
  exact {
    support := a.support
    toFun := fun i => if i ∈ B then min (a i) 1 else a i
    mem_support_toFun := by
      intro i
      rw [Finsupp.mem_support_iff]
      split <;> omega }

/-- Partial multilinearization, by linear extension on the actual monomials. -/
noncomputable def reduceOn (B : Set σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ a ∈ p.support, monomial (clip B a) (coeff a p)

private theorem card_le_clip_degree (B : Set σ) (a : σ →₀ ℕ) :
    a.support.card ≤ (clip B a).degree := by
  classical
  calc
    a.support.card = ∑ _i ∈ (clip B a).support, 1 := by simp [clip]
    _ ≤ ∑ i ∈ (clip B a).support, (clip B a) i :=
      sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = _ := rfl

/-- The partial and full Boolean reductions have the same formal degree-m
component when every relevant repeated coordinate is included in B. -/
theorem homogeneous_reduceOn_eq (B : Set σ) (m : ℕ) (p : MvPolynomial σ R)
    (covers : ∀ a ∈ p.support, a.support.card ≤ m → ∀ i ∉ B, a i ≤ 1) :
    homogeneousComponent m (reduceOn B p) =
      homogeneousComponent m (reduceOn Set.univ p) := by
  classical
  simp only [reduceOn, map_sum]
  apply sum_congr rfl
  intro a ha
  by_cases h : a.support.card ≤ m
  · have eqClip : clip B a = clip Set.univ a := by
      ext i
      by_cases hi : i ∈ B
      · simp [clip, hi]
      · simp [clip, hi, Nat.min_eq_left (covers a ha h i hi)]
    rw [eqClip]
  · have hB : m < (clip B a).degree := lt_of_lt_of_le (Nat.lt_of_not_ge h) (card_le_clip_degree B a)
    have hU : m < (clip Set.univ a).degree :=
      lt_of_lt_of_le (Nat.lt_of_not_ge h) (card_le_clip_degree Set.univ a)
    simp only [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff a p) rfl),
      if_neg hB.ne, if_neg hU.ne]

/-- The full clipping map has individual degree at most one. -/
theorem degreeOf_reduceOn_univ (p : MvPolynomial σ R) (i : σ) :
    (reduceOn Set.univ p).degreeOf i ≤ 1 := by
  classical
  refine (degreeOf_sum_le i p.support _).trans (Finset.sup_le ?_)
  intro a ha
  rw [degreeOf_monomial_eq _ _ (MvPolynomial.mem_support_iff.mp ha)]
  simp [clip]

variable {K : Type*} [CommRing K]

/-- Any partial clipping preserves the value of each Boolean input. -/
theorem eval_reduceOn_cube (B : Set σ) (p : MvPolynomial σ K)
    (v : σ → K) (hv : IsCubePoint v) : eval v (reduceOn B p) = eval v p := by
  classical
  rw [reduceOn, map_sum, eval_eq v p]
  apply sum_congr rfl
  intro a _
  rw [eval_monomial]
  apply congrArg (coeff a p * ·)
  change (∏ i ∈ a.support, v i ^ (clip B a) i) = _
  apply prod_congr rfl
  intro i hi
  have ha : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hb : (clip B a) i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rcases hv i with he | he
  · simp [he, ha, hb]
  · simp [he]

/-- Full clipping is the unique multilinear representative modulo the Boolean ideal. -/
theorem canonical_iff_eq_reduceOn_univ [Finite σ] [IsDomain K] (p q : MvPolynomial σ K) :
    ((∀ i, q.degreeOf i ≤ 1) ∧ p - q ∈ booleanIdeal σ K) ↔ q = reduceOn Set.univ p := by
  constructor
  · rintro ⟨hml, hid⟩
    apply multilinear_ext hml (degreeOf_reduceOn_univ p)
    intro v hv
    rw [eval_reduceOn_cube _ _ _ hv]
    exact (eval_eq_of_sub_mem hv hid).symm
  · rintro rfl
    refine ⟨degreeOf_reduceOn_univ p, (mem_booleanIdeal_iff _).2 ?_⟩
    intro v hv
    simp [eval_reduceOn_cube _ _ _ hv]

end BooleanTransfer.PartialLayer

#print axioms BooleanTransfer.PartialLayer.homogeneous_reduceOn_eq
#print axioms BooleanTransfer.PartialLayer.canonical_iff_eq_reduceOn_univ
