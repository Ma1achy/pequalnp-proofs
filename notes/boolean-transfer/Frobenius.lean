import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring

/-! Repeated squaring erases formal low-degree information in characteristic two,
while preserving Boolean-valued evaluations. -/

namespace BooleanTransfer.Frobenius

open MvPolynomial

private theorem add_two_pow {A : Type*} [CommRing A] (two : (2 : A) = 0)
    (a b : A) (j : ℕ) : (a+b)^(2^j) = a^(2^j) + b^(2^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.pow_succ, pow_mul, ih, add_sq, two, pow_mul, pow_mul]
    simp

private theorem poly_two {R V : Type*} [CommRing R] (two : (2 : R) = 0) :
    (2 : MvPolynomial V R) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (C (σ := V)) two

theorem erase_component {R V : Type*} [CommRing R] (two : (2 : R) = 0)
    (p : MvPolynomial V R) (j d : ℕ) (pos : 0 < d) (small : d < 2^j) :
    homogeneousComponent d (p^(2^j)) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_pow, homogeneousComponent_of_mem (isHomogeneous_monomial _ rfl), if_neg]
    rw [map_nsmul, nsmul_eq_mul]
    cases hm : m.degree with
    | zero => simp [Nat.ne_of_gt pos]
    | succ k =>
      have bound : 2^j ≤ 2^j * (k+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact Nat.ne_of_lt (lt_of_lt_of_le small bound)
  | add p q hp hq =>
    rw [add_two_pow (poly_two two) _ _ _, map_add, hp, hq, add_zero]

/-- Polynomial substitutions, including Boolean-preserving substitutions, commute
with squaring. All positive homogeneous components below the cutoff still vanish. -/
theorem erase_after_substitution {R S V W : Type*} [CommRing R] [CommRing S]
    (two : (2 : S) = 0) (φ : MvPolynomial V R →+* MvPolynomial W S)
    (p : MvPolynomial V R) (j d : ℕ) (pos : 0 < d) (small : d < 2^j) :
    homogeneousComponent d (φ (p^(2^j))) = 0 := by
  rw [map_pow]
  exact erase_component two (φ p) j d pos small

theorem same_bit {R V : Type*} [CommRing R] (p : MvPolynomial V R) (v : V → R)
    (bit : eval v p = 0 ∨ eval v p = 1) (j : ℕ) :
    eval v (p^(2^j)) = eval v p := by
  rw [map_pow]
  rcases bit with h | h <;> simp [h]

/-- A monomial with exponent one at any coordinate disappears after squaring.
This applies to each full singleton-in-each-block coefficient used by E.4. -/
theorem erase_squarefree_coeff {R V : Type*} [CommRing R] (two : (2 : R) = 0)
    (p : MvPolynomial V R) (d : V →₀ ℕ) (i : V) (one : d i = 1) :
    coeff d (p^2) = 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [monomial_pow, coeff_monomial, if_neg]
    intro h
    have hj := DFunLike.congr_fun h i
    simp [one, two_nsmul] at hj
    omega
  | add p q hp hq =>
    rw [add_sq, poly_two two, zero_mul, zero_mul, add_zero, coeff_add, hp, hq, add_zero]

end BooleanTransfer.Frobenius
