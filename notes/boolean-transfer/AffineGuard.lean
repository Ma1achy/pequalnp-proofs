import PromiseIdeal

/-! Affine Boolean guards and low-degree transport for arbitrary polynomial substitutions. -/
namespace BooleanTransfer.AffineGuard
open Finset MvPolynomial

variable {V W I R : Type*} [CommRing R]

/-- The ordinary ideal of polynomials all of whose monomials have degree at least k. -/
noncomputable def fromDegree (V R : Type*) [CommRing R] (k : ℕ) : Ideal (MvPolynomial V R) :=
  Ideal.span ((fun a => monomial a (1 : R)) '' {a : V →₀ ℕ | k ≤ a.degree})

private theorem membership (p : MvPolynomial V R) (k : ℕ) :
    p ∈ fromDegree V R k ↔ ∀ a, a.degree < k → coeff a p = 0 := by
  rw [fromDegree, mem_ideal_span_monomial_image]
  constructor
  · intro h a small
    by_contra nz
    obtain ⟨b,hb,sub⟩ := h a (mem_support_iff.mpr nz)
    exact (Nat.not_le_of_gt small) (hb.trans (Finsupp.degree_mono sub))
  · intro h a ha
    refine ⟨a,?_,le_rfl⟩
    change k ≤ a.degree
    by_contra! small
    exact (mem_support_iff.mp ha) (h a small)

private theorem relax {p : MvPolynomial V R} {a b : ℕ} (h : p ∈ fromDegree V R b) (ab : a ≤ b) :
    p ∈ fromDegree V R a :=
  (membership p a).mpr (fun i hi => (membership p b).mp h i (hi.trans_le ab))

theorem layers (p q : MvPolynomial V R) (d : ℕ) :
    p-q ∈ fromDegree V R (d+1) ↔
      ∀ k ≤ d, homogeneousComponent k p = homogeneousComponent k q := by
  rw [membership]
  constructor
  · intro h k hk
    ext a
    simp only [coeff_homogeneousComponent]
    split
    · rename_i same
      have eq := h a (by omega)
      simpa only [coeff_sub, sub_eq_zero] using eq
    · rfl
  · intro h a small
    have eq := congrArg (coeff a) (h a.degree (by omega))
    simpa only [coeff_homogeneousComponent, eq_self, ite_true, coeff_sub, sub_eq_zero] using eq

private theorem mulOrder {p q : MvPolynomial V R} {i j : ℕ}
    (hp : p ∈ fromDegree V R i) (hq : q ∈ fromDegree V R j) : p*q ∈ fromDegree V R (i+j) := by
  classical
  rw [membership]
  intro a small
  rw [coeff_mul]
  apply sum_eq_zero
  rintro ⟨u,v⟩ huv
  have e : u+v=a := mem_antidiagonal.mp huv
  have deg : u.degree+v.degree = a.degree := by rw [← e, map_add]
  by_cases hu : u.degree < i
  · rw [(membership p i).mp hp u hu, zero_mul]
  · rw [(membership q j).mp hq v (by omega), mul_zero]

private theorem prodOrder (S : Finset I) (p : I → MvPolynomial V R) (order : I → ℕ)
    (ok : ∀ i ∈ S, p i ∈ fromDegree V R (order i)) :
    (∏ i ∈ S, p i) ∈ fromDegree V R (∑ i ∈ S, order i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [prod_empty,sum_empty,membership]
    intro _ h; omega
  | @insert i S hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact mulOrder (ok i (mem_insert_self _ _)) (ih (fun j hj => ok j (mem_insert_of_mem hj)))

/-- A product has degree at least the number of its factors with zero constant term.
The factors may use overlapping variables and may have arbitrary higher-degree terms. -/
theorem countOrder (S : Finset I) (p : I → MvPolynomial V R) [DecidableEq R] :
    (∏ i ∈ S, p i) ∈ fromDegree V R (S.filter (fun i => constantCoeff (p i) = 0)).card := by
  let w (i : I) : ℕ := if constantCoeff (p i) = 0 then 1 else 0
  have ok (i : I) (_ : i ∈ S) : p i ∈ fromDegree V R (w i) := by
    rw [membership]
    intro a ha
    by_cases hi : constantCoeff (p i) = 0
    · have deg : a.degree = 0 := by simpa [w,hi] using ha
      have zero := (Finsupp.degree_eq_zero_iff a).mp deg
      simpa [zero, ← constantCoeff_eq] using hi
    · simp [w,hi] at ha
  have sumw : ∑ i ∈ S, w i = (S.filter (fun i => constantCoeff (p i) = 0)).card := by
    simp [w]
  rw [← sumw]
  exact prodOrder S p w ok

abbrev F (V : Type*) := MvPolynomial V (ZMod 2)

/-- Idempotence equations for any family of forms, including affine linear forms. -/
noncomputable def guardIdeal (A : Set (F V)) : Ideal (F V) :=
  Ideal.span ((fun g => g^2-g) '' A)

noncomputable def affine (b : ZMod 2) (S : Finset V) : F V := C b + ∑ i ∈ S, X i

/-- Arbitrary polynomial substitutions kill the guarded equations when every guarded
form has a scalar image in the two-element field. -/
theorem kill (φ : F V →+* F W) (A : Set (F V))
    (scalar : ∀ g ∈ A, ∃ c : ZMod 2, φ g = C c) : guardIdeal A ≤ RingHom.ker φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨c,eq⟩ := scalar g hg
  change φ (g^2-g) = 0
  have idem : ∀ z : ZMod 2, z^2=z := by decide
  rw [map_sub,map_pow,eq, ← map_pow, idem, sub_self]

/-- Scalar agreement modulo any target ideal suffices to transport all idempotence
equations into that ideal. Taking the high-degree ideal gives finite-order guard fixing. -/
theorem approximate (φ : F V →+* F W) (A : Set (F V)) (J : Ideal (F W))
    (scalar : ∀ g ∈ A, ∃ c : ZMod 2, φ g - C c ∈ J) : guardIdeal A ≤ J.comap φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨c,high⟩ := scalar g hg
  change φ (g^2-g) ∈ J
  have eq : (φ g + C c - 1) * (φ g - C c) = (φ g)^2 - φ g := by
    have bits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases bits c with rfl | rfl <;> simp <;> ring
  rw [map_sub, map_pow, ← eq]
  exact J.mul_mem_left _ high

open TourLayer CoreCoefficient PromiseIdeal

/-- Summing arbitrary polynomial images is sufficient to verify that a projected
affine guard is scalar; its individual input variables can remain nonconstant. -/
theorem affineScalar (f : V → F W) (b c : ZMod 2) (S : Finset V)
    (cancel : ∑ i ∈ S, f i = C c) : eval₂Hom C f (affine b S) = C (b+c) := by
  simp [affine,cancel]

private theorem largeProduct (d : ℕ) (S : Finset I) (f : I → F W)
    (certificate : (∃ e ∈ S, f e = 0) ∨ d < (S.filter (fun e => constantCoeff (f e) = 0)).card) :
    (∏ e ∈ S, f e) ∈ fromDegree W (ZMod 2) (d+1) := by
  rcases certificate with ⟨e,he,hz⟩ | high
  · rw [prod_eq_zero he hz]
    exact Ideal.zero_mem _
  · exact relax (countOrder S f) high

/-- Low layers of the projected tour sum are exactly those of the retained tours
when each discarded tour has a killed arc or more than d zero-constant factors. -/
theorem tourLayers {n : ℕ} (d : ℕ) (f : Arc n → F W) (keep : Finset (Equiv.Perm (Fin n)))
    (valid : ∀ s ∈ keep, s.IsCycleOn Set.univ)
    (discard : ∀ s : Equiv.Perm (Fin n), s.IsCycleOn Set.univ → s ∉ keep →
      (∃ e ∈ arcs s, f e = 0) ∨ d < ((arcs s).filter (fun e => constantCoeff (f e) = 0)).card) :
    ∀ i ≤ d, homogeneousComponent i (eval₂Hom C f (Statement.hc (ZMod 2) n)) =
      homogeneousComponent i (∑ s ∈ keep, ∏ e ∈ arcs s, f e) := by
  classical
  let allCycles := univ.filter (fun s : Equiv.Perm (Fin n) => s.IsCycleOn Set.univ)
  have sub : keep ⊆ allCycles := fun s hs => mem_filter.mpr ⟨mem_univ _, valid s hs⟩
  have row : eval₂Hom C f (Statement.hc (ZMod 2) n) = ∑ s ∈ allCycles, ∏ e ∈ arcs s, f e := by
    simp only [Statement.hc, map_sum, map_prod, eval₂Hom_X', allCycles, arcs, prod_map]
    rfl
  apply (layers _ _ d).mp
  rw [row, ← Finset.sum_sdiff_eq_sub sub]
  apply Ideal.sum_mem
  intro s hs
  obtain ⟨hc,hn⟩ := mem_sdiff.mp hs
  exact largeProduct d (arcs s) f (discard s (mem_filter.mp hc).2 hn)

/-- For every two-tour generator, one killed arc or more than d arcs with zero
constant term suffice to place its image strictly above degree d. -/
theorem pairOrder {n : ℕ} (d : ℕ) (f : Arc n → F W)
    (pairs : ∀ s t : Equiv.Perm (Fin n), s.IsCycleOn Set.univ → t.IsCycleOn Set.univ → s ≠ t →
      (∃ e ∈ arcs s ∪ arcs t, f e = 0) ∨
      d < ((arcs s ∪ arcs t).filter (fun e => constantCoeff (f e) = 0)).card) :
    errorIdeal n ≤ (fromDegree W (ZMod 2) (d+1)).comap (eval₂Hom C f) := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨_,⟨s,t,hs,ht,ne,rfl⟩,rfl⟩
  change eval₂Hom C f (monomial (exponent (arcs s ∪ arcs t)) 1) ∈ fromDegree W (ZMod 2) (d+1)
  have sq (S : Finset (Arc n)) : (∏ e ∈ S, (X e : F (Arc n))) = monomial (exponent S) 1 := by
    simpa [exponent] using (prod_X_pow (R := ZMod 2) (fun _ : Arc n => 1) S)
  rw [← sq, map_prod]
  simp only [eval₂Hom_X']
  exact largeProduct d _ f (pairs s t hs ht ne)

/-- Guards may agree with scalars just through the requested cutoff. -/
theorem extractApprox {n : ℕ} (d : ℕ) (φ : F (Arc n) →+* F W) (A : Set (F (Arc n)))
    (scalar : ∀ g ∈ A, ∃ c : ZMod 2, φ g - C c ∈ fromDegree W (ZMod 2) (d+1))
    (pairs : errorIdeal n ≤ (fromDegree W (ZMod 2) (d+1)).comap φ)
    (q : F W) (target : ∀ i ≤ d,
      homogeneousComponent i (φ (Statement.hc (ZMod 2) n)) = homogeneousComponent i q)
    (p : F (Arc n)) (correct : p-Statement.hc (ZMod 2) n ∈ guardIdeal A ⊔ errorIdeal n) :
    ∀ i ≤ d, homogeneousComponent i (φ p) = homogeneousComponent i q := by
  have le := sup_le (approximate φ A _ scalar) pairs
  have error : φ (p-Statement.hc (ZMod 2) n) ∈ fromDegree W (ZMod 2) (d+1) := le correct
  rw [map_sub] at error
  intro i hi
  exact ((layers _ _ d).mp error i hi).trans (target i hi)

/-- Transport simultaneous affine-guard and ordinary two-tour errors, requiring
only low-layer agreement of the projected source HC with the target polynomial. -/
theorem extract {n : ℕ} (d : ℕ) (φ : F (Arc n) →+* F W) (A : Set (F (Arc n)))
    (scalar : ∀ g ∈ A, ∃ c : ZMod 2, φ g = C c)
    (pairs : errorIdeal n ≤ (fromDegree W (ZMod 2) (d+1)).comap φ)
    (q : F W) (target : ∀ i ≤ d,
      homogeneousComponent i (φ (Statement.hc (ZMod 2) n)) = homogeneousComponent i q)
    (p : F (Arc n)) (correct : p-Statement.hc (ZMod 2) n ∈ guardIdeal A ⊔ errorIdeal n) :
    ∀ i ≤ d, homogeneousComponent i (φ p) = homogeneousComponent i q := by
  apply extractApprox d φ A _ pairs q target p correct
  intro g hg
  obtain ⟨c,eq⟩ := scalar g hg
  exact ⟨c, by rw [eq, sub_self]; exact Ideal.zero_mem _⟩

#print axioms layers
#print axioms countOrder
#print axioms kill
#print axioms approximate
#print axioms affineScalar
#print axioms tourLayers
#print axioms pairOrder
#print axioms extractApprox
#print axioms extract
end BooleanTransfer.AffineGuard
