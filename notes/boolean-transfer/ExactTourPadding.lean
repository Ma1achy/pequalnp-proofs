import Paper.LowDeg

/-!
# Two homogeneous layers of exact-tour path padding

The outer variable counts all retained arcs. The inner variable counts visible
base arcs. A forced path contributes a power of the outer variable. Each
optional arc that must be absent in an exact tour contributes one minus that
variable. The coefficient identities use formal indeterminates over a ring.
-/

namespace BooleanTransfer.ExactTourPadding

open Polynomial

variable {R : Type} [CommRing R]

/-- Substitute the product of the two markers for the base degree marker,
then account for all mandatory and optional padding arcs. -/
noncomputable def padded (q : Polynomial R) (h k : ℕ) : Polynomial (Polynomial R) :=
  q.eval₂ (C.comp C) (C X * X) * X ^ h * (1 - X) ^ k

private theorem optionalTop (k : ℕ) :
    ((1 - X : Polynomial R) ^ k).coeff k = (-1 : R) ^ k := by
  have bound : (1 - X : Polynomial R).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_X_le)
  have hc := coeff_pow_of_natDegree_le (m := k) bound
  simpa [coeff_one] using hc

private theorem monoPadded (a : R) (i h k : ℕ) :
    padded (monomial i a) h k =
      C (monomial i a) * ((X ^ (i+h) * (1-X)^k : Polynomial R).map C) := by
  rw [padded, eval₂_monomial]
  simp only [RingHom.comp_apply, mul_pow, pow_add,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  ring

/-- Take the source layer of total degree `n+h+k`, then the target layer of
visible degree `n`. The latter returns the original degree-`n` coefficient,
with the sign of the top term in the absent-arc factors. -/
theorem twoLayer (q : Polynomial R) (n h k : ℕ) :
    ((padded q h k).coeff (n+h+k)).coeff n = (-1 : R)^k * q.coeff n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [padded, add_mul, mul_add] using congrArg₂ (· + ·) hp hq
  | monomial i a =>
    rw [monoPadded, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul, coeff_monomial]
    split_ifs with hi
    · subst i
      rw [show n+h+k = k+(n+h) by omega, coeff_X_pow_mul, optionalTop]
    · simp

/-- On a formal scaling line, the two extractions recover the indicated
homogeneous component of the multivariate base polynomial. -/
theorem homogeneousLayer {σ : Type} (q : MvPolynomial σ R) (u : σ → R) (n h k : ℕ) :
    ((padded (Nc.Acc.line u q) h k).coeff (n+h+k)).coeff n =
      (-1 : R)^k * MvPolynomial.eval u (MvPolynomial.homogeneousComponent n q) := by
  rw [twoLayer, Paper.line_coeff_eq]

private theorem mix (k : ℕ) :
    ∑ b ∈ Finset.range (k+1), C ((-1 : R)^b * k.choose b) * (1-X)^b =
      (X : Polynomial R)^k := by
  have binom := add_pow (-(1-X) : Polynomial R) 1 k
  rw [show -(1-X : Polynomial R)+1 = X by ring] at binom
  rw [binom]
  apply Finset.sum_congr rfl
  intro b _
  rw [show -(1-X : Polynomial R) = C (-1 : R) * (1-X) by simp]
  simp only [map_mul, map_pow, map_natCast, mul_pow, one_pow, mul_one]
  ring

/-- The same source layer, queried with b optional bits set to one for
b = 0,...,k, recovers the base layer by an integer linear combination. -/
theorem oracleSum (q : Polynomial R) (n h k : ℕ) :
    ∑ b ∈ Finset.range (k+1), ((-1 : R)^b * k.choose b) *
      (q * X^h * (1-X)^b).coeff (n+h+k) = q.coeff n := by
  have eq : ∑ b ∈ Finset.range (k+1),
      C ((-1 : R)^b * k.choose b) * (q * X^h * (1-X)^b) =
        q * X^(h+k) := by
    rw [pow_add, ← mul_assoc, ← mix (R := R) k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have comparison := congrArg (fun p : Polynomial R => p.coeff (n+h+k)) eq
  simp only [finsetSum_coeff, coeff_C_mul, Nat.add_assoc, coeff_mul_X_pow] at comparison
  simpa only [Nat.add_assoc] using comparison

end BooleanTransfer.ExactTourPadding

#print axioms BooleanTransfer.ExactTourPadding.twoLayer
#print axioms BooleanTransfer.ExactTourPadding.homogeneousLayer

#print axioms BooleanTransfer.ExactTourPadding.oracleSum
