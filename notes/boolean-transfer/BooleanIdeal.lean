import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring

/-! Boolean evaluation, the Boolean ideal, and two formal projections.
The singleton-block expression unfolds the same coefficient and monomial sums
as Paper.linearPart, while the degree cutoff uses Mathlib's homogeneousComponent.
-/

namespace BooleanTransfer

open MvPolynomial Finset

variable {R σ : Type*} [CommRing R]

def IsCubePoint (v : σ → R) : Prop := ∀ i, v i = 0 ∨ v i = 1

noncomputable def booleanIdeal (σ R : Type*) [CommRing R] : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ R)^2 - X i)

theorem booleanIdeal_le_ker {v : σ → R} (hv : IsCubePoint v) :
    booleanIdeal σ R ≤ RingHom.ker (eval v) := by
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  rcases hv i with hi | hi <;> simp [hi]

theorem eval_eq_of_sub_mem {v : σ → R} (hv : IsCubePoint v)
    {p q : MvPolynomial σ R} (h : p-q ∈ booleanIdeal σ R) : eval v p = eval v q := by
  have he := RingHom.mem_ker.mp (booleanIdeal_le_ker hv h)
  exact sub_eq_zero.mp (by simpa using he)

/-- For finitely many variables the Boolean ideal is the whole vanishing
ideal of the cube, by the grid form of the combinatorial Nullstellensatz. -/
theorem mem_booleanIdeal_iff [Finite σ] [IsDomain R] (p : MvPolynomial σ R) :
    p ∈ booleanIdeal σ R ↔ ∀ v, IsCubePoint v → eval v p = 0 := by
  classical
  constructor
  · intro h v hv
    exact RingHom.mem_ker.mp (booleanIdeal_le_ker hv h)
  · intro hp
    let S : σ → Finset R := fun _ => {0, 1}
    have gen (i : σ) :
        (∏ s ∈ S i, (X i - C s : MvPolynomial σ R)) = X i ^ 2 - X i := by
      simp [S, zero_ne_one, mul_sub, pow_two]
    obtain ⟨h, _, he⟩ := combinatorial_nullstellensatz_exists_linearCombination S
      (fun _ => ⟨0, by simp [S]⟩) p (by
        intro v hv
        apply hp v
        intro i
        simpa [S] using hv i)
    rw [he]
    simp_rw [gen]
    change _ ∈ Submodule.span (MvPolynomial σ R)
      (Set.range fun i : σ => (X i : MvPolynomial σ R)^2 - X i)
    rw [← Finsupp.range_linearCombination]
    exact ⟨h,rfl⟩

/-- In particular the only multilinear representative of the zero function is zero. -/
theorem multilinear_mem_booleanIdeal_eq_zero [Finite σ] [IsDomain R] (p : MvPolynomial σ R)
    (hp : p ∈ booleanIdeal σ R) (hml : ∀ i, p.degreeOf i ≤ 1) : p = 0 := by
  classical
  apply eq_zero_of_eval_zero_at_prod_finset p (fun _ => {0,1})
  · intro i
    simpa [zero_ne_one] using Nat.lt_succ_of_le (hml i)
  · intro v hv
    apply (mem_booleanIdeal_iff p).1 hp v
    intro i
    simpa using hv i

/-- Two multilinear polynomials agreeing everywhere on the cube are equal. -/
theorem multilinear_ext [Finite σ] [IsDomain R] {p q : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (heq : ∀ v, IsCubePoint v → eval v p = eval v q) : p = q := by
  apply sub_eq_zero.mp
  apply multilinear_mem_booleanIdeal_eq_zero
  · apply (mem_booleanIdeal_iff _).2
    intro v hv
    simp [heq v hv]
  · intro i
    exact le_trans (degreeOf_sub_le i p q) (max_le (hp i) (hq i))

/-- Every formal polynomial has a unique multilinear representative on the cube.
The construction in the proof processes the formal monomial expansion. -/
theorem existsUnique_multilinear [IsDomain R] [Finite σ] (p : MvPolynomial σ R) :
    ∃! q : MvPolynomial σ R, (∀ i, q.degreeOf i ≤ 1) ∧ p - q ∈ booleanIdeal σ R := by
  classical
  have existsRep (f : MvPolynomial σ R) :
      ∃ g : MvPolynomial σ R, (∀ i, g.degreeOf i ≤ 1) ∧
        ∀ v, IsCubePoint v → eval v f = eval v g := by
    induction f using MvPolynomial.induction_on' with
    | monomial m a =>
      refine ⟨C a * ∏ i ∈ m.support, X i, fun i => ?_, ?_⟩
      · refine le_trans (degreeOf_C_mul_le _ _ _) (le_trans (degreeOf_prod_le _ _ _) ?_)
        simp only [degreeOf_X]
        simp
        split <;> decide
      · intro v hv
        rw [eval_monomial, map_mul, eval_C, map_prod]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hm : m j ≠ 0 := Finsupp.mem_support_iff.mp hj
        rcases hv j with he | he <;> simp [he,hm]
    | add f g hf hg =>
      obtain ⟨f', df, ef⟩ := hf
      obtain ⟨g', dg, eg⟩ := hg
      exact ⟨f'+g', fun i => le_trans (degreeOf_add_le _ _ _) (max_le (df i) (dg i)),
        fun v hv => by simp [ef v hv, eg v hv]⟩
  obtain ⟨r, dr, er⟩ := existsRep p
  refine ⟨r, ⟨dr, (mem_booleanIdeal_iff _).2 fun v hv => by simp [er v hv]⟩, ?_⟩
  intro q hq
  exact multilinear_ext hq.1 dr fun v hv => (eval_eq_of_sub_mem hv hq.2).symm.trans (er v hv)

/-- The cutoff occurring before evaluation in Paper.lem_lowdeg at d=1. -/
theorem lowDegree_generator (i : σ) :
    (∑ j ∈ range (1+1), homogeneousComponent j ((X i : MvPolynomial σ R)^2 - X i))
      = -X i := by
  have h1 := isHomogeneous_X R i
  have h2 := isHomogeneous_X_pow (R := R) i 2
  simp [map_sub, homogeneousComponent_of_mem h1,
    homogeneousComponent_of_mem h2]

/-- The projected values already disagree on a Boolean input when its i-th
coordinate is one. Evaluation of the whole original generator is zero there. -/
theorem eval_lowDegree_generator (i : σ) (v : σ → R) (hi : v i = 1) :
    (∑ j ∈ range (1+1), eval v (homogeneousComponent j
      ((X i : MvPolynomial σ R)^2 - X i))) = -1 := by
  rw [← map_sum, lowDegree_generator]
  simp [hi]

/-- Paper.linearPart unfolded, including the exponent used by Nc.CaseI.cf. -/
noncomputable def blockLinearPart {k : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (p : MvPolynomial (Fin k × T) R) :=
  ∑ x : Fin k → T,
    C (p.coeff (∑ a : Fin k, Finsupp.single (a,x a) 1)) *
      ∏ a : Fin k, X (R := R) (a,x a)

noncomputable abbrev singletonLinearPart {k : ℕ} (p : MvPolynomial (Fin k × Unit) R) :=
  blockLinearPart p

/-- Exponent dilation is a cube-preserving substitution in every characteristic. -/
theorem eval_expand_cube (s : ℕ) (p : MvPolynomial σ R) {v : σ → R} (hv : IsCubePoint v) :
    eval v (expand (s+1) p) = eval v p := by
  rw [eval_expand]
  have eqv : v^(s+1) = v := by
    funext i
    rcases hv i with hi | hi <;> simp [Pi.pow_apply, hi]
  rw [eqv]

/-- A single simultaneous squaring of the inputs erases the full block-linear
part of *every* formal polynomial when there is a block. -/
theorem blockLinearPart_expand_two {k : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (i : Fin k) (p : MvPolynomial (Fin k × T) R) :
    blockLinearPart (expand 2 p) = 0 := by
  classical
  unfold blockLinearPart
  apply Finset.sum_eq_zero
  intro f _
  have h1 : (∑ a : Fin k, Finsupp.single (a,f a) (1 : ℕ)) (i,f i) = 1 := by
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Finsupp.single_eq_of_ne (fun e => hji (congrArg Prod.fst e).symm)
    · simp
  rw [coeff_expand_of_not_dvd p (show ¬2 ∣ _ from by rw [h1]; decide)]
  simp

/-- Dilation multiplies every surviving total monomial degree by the exponent. -/
theorem homogeneousComponent_expand_of_not_dvd (s j : ℕ) (h : ¬ s ∣ j)
    (p : MvPolynomial σ R) : homogeneousComponent j (expand s p) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [expand_monomial, homogeneousComponent_of_mem (isHomogeneous_monomial a rfl)]
    split
    · next e => exact (h ⟨m.degree, by simpa using e⟩).elim
    · rfl
  | add p q hp hq => simp [map_add, hp, hq]

/-- The exact low-degree sum stays at the constant term after dilation by d+1. -/
theorem lowDegree_expand (d : ℕ) (p : MvPolynomial σ R) :
    (∑ j ∈ range (d+1), homogeneousComponent j (expand (d+1) p)) = C (p.coeff 0) := by
  classical
  rw [Finset.sum_eq_single 0, homogeneousComponent_zero, coeff_expand_zero _ (Nat.succ_ne_zero d)]
  · intro j hj hne
    apply homogeneousComponent_expand_of_not_dvd
    intro h
    exact (Nat.not_le.mpr (Finset.mem_range.mp hj)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h)
  · simp

/-- The same two-polynomial obstruction works at an arbitrary positive cutoff,
including d=N in the actual low-degree application. -/
theorem cutoff_generator (d : ℕ) (hd : 0 < d) (i : σ) :
    (∑ j ∈ range (d+1), homogeneousComponent j ((X i : MvPolynomial σ R)^(d+1) - X i))
      = -X i := by
  rw [← expand_X (d+1) i]
  simp only [map_sub, Finset.sum_sub_distrib, lowDegree_expand]
  have h1 := isHomogeneous_X R i
  rw [Finset.sum_eq_single 1]
  · simp [homogeneousComponent_of_mem h1]
  · intro j _ hj
    simp [homogeneousComponent_of_mem h1, hj]
  · simp [Finset.mem_range, hd]

noncomputable def blockProduct (R : Type*) [CommRing R] (k : ℕ) : MvPolynomial (Fin k × Unit) R :=
  ∏ a : Fin k, X (a, ())

noncomputable def blockExample {k : ℕ} (R : Type*) [CommRing R] (i : Fin k) :=
  ((X (i,()) : MvPolynomial (Fin k × Unit) R)^2 - X (i,())) *
    ∏ a ∈ (univ.erase i), X (a,())

theorem blockExample_mem {k : ℕ} (i : Fin k) :
    blockExample R i ∈ booleanIdeal (Fin k × Unit) R := by
  apply Ideal.mul_mem_right
  exact Ideal.subset_span ⟨(i,()), rfl⟩

private theorem blockExample_eq {k : ℕ} (i : Fin k) :
    blockExample R i = (X (i,()) - 1) * blockProduct R k := by
  unfold blockExample blockProduct
  rw [← Finset.mul_prod_erase univ (fun a : Fin k => (X (a,()) : MvPolynomial _ R)) (mem_univ i)]
  ring

theorem singletonLinearPart_blockExample {k : ℕ} (i : Fin k) :
    singletonLinearPart (blockExample R i) = -blockProduct R k := by
  classical
  let d : (Fin k × Unit) →₀ ℕ := ∑ a : Fin k, Finsupp.single (a,()) 1
  have hprod : blockProduct R k = monomial d 1 := by
    dsimp only [blockProduct, d]
    rw [monomial_sum_one]
    rfl
  have hne : d + Finsupp.single (i,()) 1 ≠ d := by
    intro eq
    have h := DFunLike.congr_fun eq (i,())
    simp at h
  have hc : (blockExample R i).coeff d = -1 := by
    rw [blockExample_eq, sub_mul, one_mul, hprod, mul_comm (X (i,())),
      ← pow_one (X (i,()) : MvPolynomial (Fin k × Unit) R), ← monomial_add_single,
      coeff_sub, coeff_monomial, coeff_monomial]
    simp [hne]
  unfold singletonLinearPart blockLinearPart
  rw [Fintype.sum_unique]
  have hx : (default : Fin k → Unit) = fun _ => () := Subsingleton.elim _ _
  rw [hx]
  change C ((blockExample R i).coeff d) * blockProduct R k = _
  rw [hc]
  simp

theorem singletonLinearPart_blockExample_ne_zero [Nontrivial R] {k : ℕ} (i : Fin k) :
    singletonLinearPart (blockExample R i) ≠ 0 := by
  rw [singletonLinearPart_blockExample]
  intro h
  have he := congrArg (eval (fun _ : Fin k × Unit => (1:R))) h
  simp [blockProduct] at he

end BooleanTransfer
