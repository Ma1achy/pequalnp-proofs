import Paper.LowDeg

/-!
# Extracting a homogeneous layer through a signed cycle gadget

The two directed orientations of a bidirected cycle give monomials of the
same degree. Assigning their variables weights with respective products
`1` and `-1` turns their disjunction polynomial into a pure power of the
scaling variable. The coefficient shift holds over every commutative ring.
-/

namespace BooleanTransfer.LayerProjection

open MvPolynomial

variable {R σ : Type} [CommRing R]

/-- The polynomial representing the disjunction of two indicator variables. -/
def disjoin {A : Type*} [Ring A] (a b : A) : A := a + b - a * b

theorem gadget (k : ℕ) :
    disjoin ((Polynomial.X : Polynomial R) ^ k) (-Polynomial.X ^ k) =
      Polynomial.X ^ (2 * k) := by
  simp [disjoin, two_mul, pow_add]

/-- The padded coefficient of any polynomial on a scaling line. -/
theorem shift (q : Polynomial R) (k n : ℕ) :
    (q * disjoin (Polynomial.X ^ k) (-Polynomial.X ^ k)).coeff (n + 2 * k) =
      q.coeff n := by
  rw [gadget, Polynomial.coeff_mul_X_pow]

/-- The ray image of a squarefree product, including its scalar weight. -/
theorem arcProduct (u : σ → R) (s : Finset σ) :
    Nc.Acc.line u (∏ i ∈ s, X i) =
      Polynomial.C (∏ i ∈ s, u i) * Polynomial.X ^ s.card := by
  classical
  simp [Nc.Acc.line, Finset.prod_mul_distrib]

/-- Two equally long orientations with weight products of opposite sign give
an exact homogeneous layer shift for every base polynomial and every layer. -/
theorem layer (u : σ → R) (q : MvPolynomial σ R) (s t : Finset σ) (k n : ℕ)
    (hs : s.card = k) (ht : t.card = k)
    (hf : ∏ i ∈ s, u i = 1) (hr : ∏ i ∈ t, u i = -1) :
    eval u (homogeneousComponent (n + 2 * k)
      (q * disjoin (∏ i ∈ s, X i) (∏ i ∈ t, X i))) =
    eval u (homogeneousComponent n q) := by
  rw [← Paper.line_coeff_eq, ← Paper.line_coeff_eq]
  simp only [disjoin, map_mul, map_sub, map_add, arcProduct, hs, ht, hf, hr,
    map_one, map_neg, one_mul, neg_mul]
  exact shift (Nc.Acc.line u q) k n

private theorem mapComponent {A : Type} [CommRing A] (φ : R →+* A)
    (d : ℕ) (p : MvPolynomial σ R) :
    map φ (homogeneousComponent d p) = homogeneousComponent d (map φ p) := by
  ext a
  simp only [coeff_map, coeff_homogeneousComponent]
  split <;> simp

/-- Polynomial-valued substitutions give a formal equality in the output
polynomial ring. The coefficient ring may in particular be the integers or a field. -/
theorem symbolic {τ : Type} (u : σ → MvPolynomial τ R) (q : MvPolynomial σ R)
    (s t : Finset σ) (k n : ℕ) (hs : s.card = k) (ht : t.card = k)
    (hf : ∏ i ∈ s, u i = 1) (hr : ∏ i ∈ t, u i = -1) :
    eval₂ C u (homogeneousComponent (n + 2 * k)
      (q * disjoin (∏ i ∈ s, X i) (∏ i ∈ t, X i))) =
    eval₂ C u (homogeneousComponent n q) := by
  simp only [eval₂_eq_eval_map, mapComponent, disjoin, map_mul, map_add, map_sub,
    map_prod, map_X]
  exact layer u (map C q) s t k n hs ht hf hr

#print axioms gadget
#print axioms shift
#print axioms arcProduct
#print axioms layer
#print axioms symbolic

end BooleanTransfer.LayerProjection
