import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring

/-! Signed Boolean coefficients under insertion of forced arc variables. -/

namespace BooleanTransfer.CoreCoefficient

open Finset

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The signed Boolean Möbius coefficient. Only values at subsets of the
specified finite support occur, so the ambient variable type may be infinite. -/
def signed (f : Finset ι → R) (S : Finset ι) : R :=
  ∑ U ∈ S.powerset, (-1 : R) ^ (S.card - U.card) * f U

private theorem insertDiff (f : Finset ι → R) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    signed f (insert a S) = signed (fun U => f (insert a U) - f U) S := by
  unfold signed
  rw [sum_powerset_insert ha, ← sum_add_distrib]
  apply sum_congr rfl
  intro U hu
  have sub := mem_powerset.mp hu
  have le := card_le_card sub
  have hn : a ∉ U := fun mem => ha (sub mem)
  rw [card_insert_of_notMem ha, card_insert_of_notMem hn, Nat.add_sub_add_right,
    show S.card + 1 - U.card = S.card - U.card + 1 by omega, pow_succ]
  ring

/-- A multilinear expansion with coefficient function c evaluates on the
Boolean assignment U as the sum of the coefficients of subsets of U. Signed
inversion recovers each individual coefficient over every commutative ring. -/
theorem inverse (c : Finset ι → R) (S : Finset ι) :
    signed (fun T => ∑ U ∈ T.powerset, c U) S = c S := by
  induction S using Finset.induction_on generalizing c with
  | empty => simp [signed]
  | @insert a S ha ih =>
    rw [insertDiff _ _ _ ha]
    refine Eq.trans ?_ (ih (fun U => c (insert a U)))
    apply sum_congr rfl
    intro U hu
    have hn : a ∉ U := fun mem => ha ((mem_powerset.mp hu) mem)
    dsimp only
    rw [sum_powerset_insert hn, add_sub_cancel_left]

/-- A polynomial in the squarefree basis on a finite edge set. -/
noncomputable def expansion (c : Finset ι → R) (E : Finset ι) : MvPolynomial ι R :=
  ∑ S ∈ E.powerset, MvPolynomial.C (c S) * ∏ i ∈ S, MvPolynomial.X i

/-- The exponent vector of the squarefree monomial indexed by S. -/
noncomputable def exponent (S : Finset ι) : ι →₀ ℕ := Finsupp.indicator S (fun _ _ => 1)

private theorem expInj : Function.Injective (exponent : Finset ι → (ι →₀ ℕ)) := by
  intro A B eq
  ext i
  have ev := DFunLike.congr_fun eq i
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [exponent, ha, hb] at ev ⊢

/-- The expansion coefficients are formal polynomial coefficients. -/
theorem formal (c : Finset ι → R) (E S : Finset ι) (h : S ⊆ E) :
    MvPolynomial.coeff (exponent S) (expansion c E) = c S := by
  simp only [expansion, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  have prodCoeff (T : Finset ι) : MvPolynomial.coeff (exponent S)
      (∏ i ∈ T, (MvPolynomial.X i : MvPolynomial ι R)) = if S = T then 1 else 0 := by
    calc
      _ = if exponent S = exponent T then (1 : R) else 0 := by
        have calcCoeff := MvPolynomial.coeff_prod_X_pow (R := R) (exponent S) (fun _ => 1) T
        by_cases same : exponent S = exponent T
        · have yes : exponent S = Finsupp.indicator T (fun _ _ => 1) := same
          simpa only [pow_one, if_pos yes, if_pos same] using calcCoeff
        · have no : exponent S ≠ Finsupp.indicator T (fun _ _ => 1) := same
          simpa only [pow_one, if_neg no, if_neg same] using calcCoeff
      _ = _ := by simp only [expInj.eq_iff]
  simp only [prodCoeff, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq, if_pos (mem_powerset.mpr h)]

private theorem cube (c : Finset ι → R) (E U : Finset ι) (h : U ⊆ E) :
    MvPolynomial.eval (fun i => if i ∈ U then (1 : R) else 0) (expansion c E) =
    ∑ S ∈ U.powerset, c S := by
  have filterEq : E.powerset.filter (· ⊆ U) = U.powerset := by
    ext S
    simp only [mem_filter, mem_powerset]
    exact ⟨And.right, fun hs => ⟨hs.trans h, hs⟩⟩
  unfold expansion
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X, prod_boole]
  rw [← filterEq, sum_filter]
  apply sum_congr rfl
  intro S _
  change c S * (if S ⊆ U then 1 else 0) = _
  split <;> simp

/-- Inversion extracts the actual squarefree expansion coefficient from its
Boolean evaluations, including in positive characteristic. -/
theorem extract (c : Finset ι → R) (E S : Finset ι) (h : S ⊆ E) :
    signed (fun U => MvPolynomial.eval (fun i => if i ∈ U then (1 : R) else 0)
      (expansion c E)) S = c S := by
  refine Eq.trans ?_ (inverse c S)
  apply sum_congr rfl
  intro U hu
  exact congrArg _ (cube c E U ((mem_powerset.mp hu).trans h))

private theorem sumSigned (f : Finset ι → R) (S : Finset ι) :
    ∑ U ∈ S.powerset, signed f U = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [signed]
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha, ih]
    have shift : ∑ U ∈ S.powerset, signed f (insert a U) =
        ∑ U ∈ S.powerset, signed (fun V => f (insert a V) - f V) U := by
      apply sum_congr rfl
      intro U hu
      exact insertDiff f U a (fun mem => ha ((mem_powerset.mp hu) mem))
    rw [shift, ih]
    abel

/-- The squarefree polynomial with the signed coefficients interpolates the
supplied truth table over any commutative ring. -/
theorem realizes (f : Finset ι → R) (E U : Finset ι) (h : U ⊆ E) :
    MvPolynomial.eval (fun i => if i ∈ U then (1 : R) else 0) (expansion (signed f) E) = f U :=
  (cube _ E U h).trans (sumSigned f U)

private theorem sumInterval {A : Type*} [AddCommMonoid A]
    (Y X : Finset ι) (h : Disjoint Y X) (term : Finset ι → A) :
    ∑ U ∈ (Y ∪ X).powerset.filter (Y ⊆ ·), term U = ∑ T ∈ X.powerset, term (Y ∪ T) := by
  symm
  apply sum_bij (fun T _ => Y ∪ T)
  · intro T ht
    exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset_union_right (mem_powerset.mp ht)),
      subset_union_left⟩
  · intro A ha B hb eq
    simpa only [union_sdiff_cancel_left (h.mono_right (mem_powerset.mp ha)),
      union_sdiff_cancel_left (h.mono_right (mem_powerset.mp hb))] using
      congrArg (· \ Y) eq
  · intro U hu
    obtain ⟨hu, hy⟩ := mem_filter.mp hu
    refine ⟨U \ Y, mem_powerset.mpr ?_, ?_⟩
    · intro a ha
      obtain ⟨ha, hn⟩ := mem_sdiff.mp ha
      exact (mem_union.mp ((mem_powerset.mp hu) ha)).resolve_left hn
    · exact sup_sdiff_cancel_right hy
  · intros; rfl

/-- When every forced variable must be present, its inclusion in the target
support preserves the signed coefficient of the remaining variables. The
factorization assumption is needed only on subsets of the target support. -/
theorem forced (f g : Finset ι → R) (Y X : Finset ι) (h : Disjoint Y X)
    (factor : ∀ U ⊆ Y ∪ X, f U = if Y ⊆ U then g (U \ Y) else 0) :
    signed f (Y ∪ X) = signed g X := by
  unfold signed
  calc
    _ = ∑ U ∈ (Y ∪ X).powerset.filter (Y ⊆ ·),
          (-1 : R) ^ ((Y ∪ X).card - U.card) * g (U \ Y) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro U hu
      rw [factor U (mem_powerset.mp hu)]
      split <;> simp
    _ = _ := by
      rw [sumInterval Y X h]
      apply sum_congr rfl
      intro T ht
      have dis := h.mono_right (mem_powerset.mp ht)
      rw [union_sdiff_cancel_left dis, card_union_of_disjoint h,
        card_union_of_disjoint dis, Nat.add_sub_add_left]

omit [DecidableEq ι] in
/-- A target support missing a mandatory variable has coefficient zero. -/
theorem missing (f : Finset ι → R) (Y S : Finset ι) (absent : ¬Y ⊆ S)
    (vanishes : ∀ U ⊆ S, ¬Y ⊆ U → f U = 0) : signed f S = 0 := by
  apply sum_eq_zero
  intro U hu
  have sub := mem_powerset.mp hu
  simp [vanishes U sub (fun inc => absent (inc.trans sub))]

/-- The entire canonical polynomial factors by the product of forced variables.
The disjointness hypothesis ensures that the resulting product is squarefree. -/
theorem stretch (f g : Finset ι → R) (Y X : Finset ι) (h : Disjoint Y X)
    (factor : ∀ U ⊆ Y ∪ X, f U = if Y ⊆ U then g (U \ Y) else 0) :
    expansion (signed f) (Y ∪ X) =
      (∏ i ∈ Y, MvPolynomial.X i) * expansion (signed g) X := by
  let term := fun U => MvPolynomial.C (signed f U) * ∏ i ∈ U, MvPolynomial.X i
  calc
    _ = ∑ U ∈ (Y ∪ X).powerset.filter (Y ⊆ ·), term U := by
      rw [sum_filter, expansion]
      apply sum_congr rfl
      intro U hu
      by_cases hy : Y ⊆ U
      · simp [hy, term]
      · have zero := missing f Y U hy (fun V hv hvy => by
          rw [factor V (hv.trans (mem_powerset.mp hu)), if_neg hvy])
        simp [hy, zero]
    _ = _ := by
      rw [sumInterval Y X h term, expansion, mul_sum]
      apply sum_congr rfl
      intro T ht
      have sub := mem_powerset.mp ht
      have dis := h.mono_right sub
      have eq := forced f g Y T dis (fun V hv => factor V (hv.trans (union_subset_union_right sub)))
      dsimp only [term]
      rw [eq, prod_union dis]
      ring

#print axioms inverse
#print axioms formal
#print axioms extract
#print axioms realizes
#print axioms forced
#print axioms missing
#print axioms stretch

end BooleanTransfer.CoreCoefficient
