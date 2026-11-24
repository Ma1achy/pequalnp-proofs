import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! The assertion that every hole is occupied is a product equation for each
hole. Lagrange interpolation expresses the linear discrepancy in the sum of
the labels as a linear combination of those product equations. This is an
identity of ordinary polynomials. Integer resolution acts on individual linear
heads and provides no rule for summing these product equations directly. -/

namespace PEqualNP.Search

open Finset Polynomial

/-- Evaluate the coefficient of degree `n-1` in the difference of the monic
node and label polynomials by interpolation at the pairwise distinct nodes. -/
theorem occupancy_sum_certificate {F : Type*} [Field F] {n : ℕ}
    (v y : Fin n → F) (distinct : Function.Injective v) :
    (∑ i, y i) - (∑ i, v i) =
      -∑ h, (∏ i, (v h - y i)) / ∏ k ∈ (univ.erase h), (v h - v k) := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    let s : Finset (Fin (n+1)) := univ
    have degree (w : Fin (n+1) → F) : (Lagrange.nodal s w).degree = ↑s.card :=
      Lagrange.degree_nodal
    have deglt : (Lagrange.nodal s v - Lagrange.nodal s y).degree < ↑s.card := by
      rw [← degree v]
      exact degree_sub_lt_left ((degree v).trans (degree y).symm) Lagrange.nodal_ne_zero
        (Lagrange.nodal_monic.trans Lagrange.nodal_monic.symm)
    have top (w : Fin (n+1) → F) :
        (Lagrange.nodal s w).coeff (s.card - 1) = -∑ i, w i := by
      have pos : 0 < (Lagrange.nodal s w).natDegree := by simp [s]
      simpa only [Lagrange.natDegree_nodal] using
        ((nextCoeff_of_natDegree_pos pos).symm.trans (prod_X_sub_C_nextCoeff w))
    have zero_at (h : Fin (n+1)) : (Lagrange.nodal s v).eval (v h) = 0 :=
      Lagrange.eval_nodal_at_node (by simp [s])
    have identity := Lagrange.coeff_eq_sum distinct.injOn deglt
    simp only [coeff_sub, top, eval_sub, zero_at,
      Lagrange.eval_nodal, zero_sub, neg_div, Finset.sum_neg_distrib] at identity
    simpa [s, sub_eq_add_neg, add_comm] using identity

/-- Every label assignment meeting the occupancy condition has the
same total as the distinct hole values. No separate injectivity hypothesis on
the labels is needed. -/
theorem occupancy_implies_sum {F : Type*} [Field F] {n : ℕ}
    (v y : Fin n → F) (distinct : Function.Injective v) (occupied : ∀ h, ∃ i, y i = v h) :
    (∑ i, y i) = ∑ i, v i := by
  classical
  have vanishes (h : Fin n) : (∏ i, (v h - y i)) = 0 := by
    obtain ⟨i, hi⟩ := occupied h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_eq_zero.mpr hi.symm)
  have cert := occupancy_sum_certificate v y distinct
  simpa [vanishes, sub_eq_zero] using cert

/-- A symbolic certificate over the rationals with one variable per row.
Each term contains precisely the factors expressing occupancy of one hole. -/
theorem occupancy_polynomial_certificate {n : ℕ} (v : Fin n → ℚ)
    (distinct : Function.Injective v) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) - MvPolynomial.C (∑ i, v i) =
      -∑ h, MvPolynomial.C ((∏ k ∈ (univ.erase h), (v h - v k))⁻¹) *
        ∏ i, (MvPolynomial.C (v h) - MvPolynomial.X i) := by
  apply MvPolynomial.funext
  intro y
  simpa [map_sub, map_sum, map_neg, map_mul, map_prod, div_eq_inv_mul] using
    occupancy_sum_certificate v y distinct

private theorem numbered_holes_injective (n : ℕ) :
    Function.Injective (fun h : Fin n => (h.val : ℚ)) := by
  intro a b same
  apply Fin.ext
  change (a.val : ℚ) = (b.val : ℚ) at same
  exact_mod_cast same

private theorem sum_fin_rat (n : ℕ) : (∑ i : Fin n, (i.val : ℚ)) = n*(n-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_succ]
    ring

/-- The occupancy certificate for the numbered holes. In the binary pigeonhole
application `n = 2^l` and the labels are the numeric values of the binary rows. -/
theorem numbered_occupancy_certificate {n : ℕ} (y : Fin n → ℚ) :
    (∑ i, y i) - (n:ℚ)*(n-1)/2 =
      -∑ h : Fin n, (∏ i, ((h.val:ℚ) - y i)) /
        ∏ k ∈ (univ.erase h), ((h.val:ℚ) - (k.val:ℚ)) := by
  simpa only [sum_fin_rat] using occupancy_sum_certificate
    (fun h : Fin n => (h.val:ℚ)) y (numbered_holes_injective n)

/-- Occupying every numbered hole forces its triangular total without assuming
that the labels are integers, distinct, or in the indicated range in advance. -/
theorem numbered_occupancy_implies_total {n : ℕ} (y : Fin n → ℚ)
    (occ : ∀ h : Fin n, ∃ i, y i = h.val) : (∑ i, y i) = (n:ℚ)*(n-1)/2 := by
  simpa only [sum_fin_rat] using occupancy_implies_sum
    (fun h : Fin n => (h.val:ℚ)) y (numbered_holes_injective n) occ

end PEqualNP.Search
