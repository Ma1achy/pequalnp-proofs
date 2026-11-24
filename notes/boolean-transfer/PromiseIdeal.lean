import CoreCoefficient
import TourLayer
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! The error ideal of the zero-or-one Hamiltonian-cycle promise. -/
namespace BooleanTransfer.PromiseIdeal

open Finset MvPolynomial CoreCoefficient
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

private theorem squareIndex (a : ι →₀ ℕ) (h : ∀ i, a i ≤ 1) : exponent a.support = a := by
  ext i
  by_cases hi : i ∈ a.support
  · have nz := Finsupp.mem_support_iff.mp hi
    have hv : a i = 1 := by have := h i; omega
    simp [exponent, hi, hv]
  · simp [exponent, hi, Finsupp.notMem_support_iff.mp hi]

private theorem expansionML (c : Finset ι → R) (E : Finset ι) :
    expansion c E ∈ restrictDegree ι R 1 := by
  nontriviality R
  rw [mem_restrictDegree_iff_sup]
  intro i
  rw [← degreeOf_def]
  unfold expansion
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro S _
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le i _ _).trans
  simp only [degreeOf_X]
  rw [sum_ite_eq]
  split <;> decide

variable [Fintype ι]

private theorem asExpansion (p : MvPolynomial ι R) (ml : p ∈ restrictDegree ι R 1) :
    expansion (fun S => coeff (exponent S) p) univ = p := by
  ext a
  by_cases single : ∀ i, a i ≤ 1
  · have ix := squareIndex a single
    simpa only [ix] using
      formal (fun S => coeff (exponent S) p) univ a.support (subset_univ _)
  · have zero (q : MvPolynomial ι R) (bound : q ∈ restrictDegree ι R 1) : coeff a q = 0 := by
      apply notMem_support_iff.mp
      exact fun ha => single ((mem_restrictDegree _ _ _).mp bound a ha)
    rw [zero _ (expansionML _ _), zero _ ml]

private theorem recover (p : MvPolynomial ι R) (ml : p ∈ restrictDegree ι R 1) (S : Finset ι) :
    signed (fun T => eval (fun i => if i ∈ T then 1 else 0) p) S = coeff (exponent S) p := by
  simpa only [asExpansion p ml] using
    extract (fun T => coeff (exponent T) p) univ S (subset_univ _)

/-- On a downward-closed Boolean domain, agreement of multilinear polynomials
forces agreement of every formal coefficient whose support is in the domain. -/
theorem downward (D : Finset ι → Prop) (down : ∀ {S T}, S ⊆ T → D T → D S)
    (p q : MvPolynomial ι R) (hp : p ∈ restrictDegree ι R 1) (hq : q ∈ restrictDegree ι R 1)
    (same : ∀ S, D S → eval (fun i => if i ∈ S then 1 else 0) p =
      eval (fun i => if i ∈ S then 1 else 0) q)
    (a : ι →₀ ℕ) (ok : D a.support) : coeff a p = coeff a q := by
  by_cases single : ∀ i, a i ≤ 1
  · have ix := squareIndex a single
    rw [← ix, ← recover p hp, ← recover q hq]
    apply sum_congr rfl
    intro U hu
    exact congrArg _ (same U (down (mem_powerset.mp hu) ok))
  · have zero (f : MvPolynomial ι R) (ml : f ∈ restrictDegree ι R 1) : coeff a f = 0 :=
      notMem_support_iff.mp (fun ha => single ((mem_restrictDegree _ _ _).mp ml a ha))
    rw [zero p hp, zero q hq]

open TourLayer

private theorem tour_mem {n : ℕ} {E : Finset (Arc n)} {s : Equiv.Perm (Fin n)} :
    s ∈ tours E ↔ s.IsCycleOn Set.univ ∧ arcs s ⊆ E := by
  classical
  simp only [tours, mem_filter, mem_univ, true_and]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro edges ⟨i,j⟩ hj
    rw [← (mem_arcs s i j).mp hj]
    exact edges i
  · intro edges i
    exact edges (by simp)

private theorem square_le {n : ℕ} (S : Finset (Arc n)) (a : Arc n →₀ ℕ) :
    exponent S ≤ a ↔ S ⊆ a.support := by
  constructor
  · intro h i hi
    have hi' := h i
    rw [exponent, Finsupp.indicator_of_mem hi] at hi'
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h i
    by_cases hi : i ∈ S
    · rw [exponent, Finsupp.indicator_of_mem hi]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (h hi))
    · simp [exponent,hi]

/-- Squarefree monomials indexed by unions of two distinct spanning tours. -/
def generators (n : ℕ) : Set (Arc n →₀ ℕ) :=
  {a | ∃ s t : Equiv.Perm (Fin n), s.IsCycleOn Set.univ ∧ t.IsCycleOn Set.univ ∧
    s ≠ t ∧ a = exponent (arcs s ∪ arcs t)}

noncomputable def errorIdeal (n : ℕ) : Ideal (MvPolynomial (Arc n) (ZMod 2)) :=
  Ideal.span ((fun s => monomial s (1 : ZMod 2)) '' generators n)

/-- Ideal membership tests every monomial of the error, without a multilinearity assumption. -/
theorem membership {n : ℕ} (p : MvPolynomial (Arc n) (ZMod 2)) :
    p ∈ errorIdeal n ↔ ∀ a ∈ p.support, 1 < (tours a.support).card := by
  classical
  rw [errorIdeal, mem_ideal_span_monomial_image]
  apply forall₂_congr
  intro a _
  rw [one_lt_card]
  constructor
  · rintro ⟨_,⟨s,t,hs,ht,ne,rfl⟩,le⟩
    obtain ⟨hs',ht'⟩ := union_subset_iff.mp ((square_le _ _).mp le)
    exact ⟨s,tour_mem.mpr ⟨hs,hs'⟩,t,tour_mem.mpr ⟨ht,ht'⟩,ne⟩
  · rintro ⟨s,hs,t,ht,ne⟩
    obtain ⟨cs,es⟩ := tour_mem.mp hs
    obtain ⟨ct,et⟩ := tour_mem.mp ht
    exact ⟨_,⟨s,t,cs,ct,ne,rfl⟩,(square_le _ _).mpr (union_subset es et)⟩

private theorem uniqueDown {n : ℕ} {S T : Finset (Arc n)} (sub : S ⊆ T)
    (one : (tours T).card ≤ 1) : (tours S).card ≤ 1 := by
  apply (card_le_card ?_).trans one
  intro s hs
  obtain ⟨c,h⟩ := tour_mem.mp hs
  exact tour_mem.mpr ⟨c,h.trans sub⟩

private theorem hcML (n : ℕ) : Statement.hc (ZMod 2) n ∈ restrictDegree (Arc n) (ZMod 2) 1 := by
  rw [← decisionANF_component, mem_restrictDegree]
  intro a ha
  rw [support_homogeneousComponent] at ha
  exact (mem_restrictDegree _ _ _).mp (decisionANF_multilinear n) a (mem_filter.mp ha).1

private theorem hcPromise {n : ℕ} (S : Finset (Arc n)) (one : (tours S).card ≤ 1) :
    eval (indicator (ZMod 2) S) (Statement.hc (ZMod 2) n) = if (tours S).Nonempty then 1 else 0 := by
  classical
  rw [eval_hc_counts]
  by_cases some : (tours S).Nonempty
  · have pos := card_pos.mpr some
    have eq : (tours S).card = 1 := by omega
    simp [some,eq]
  · simp [Finset.not_nonempty_iff_eq_empty.mp some]

/-- A formally multilinear promise decider differs from the formal tour polynomial
by an element of the ideal generated by two-tour unions. -/
theorem error {n : ℕ} (p : MvPolynomial (Arc n) (ZMod 2)) (ml : p ∈ restrictDegree _ _ 1)
    (correct : ∀ S : Finset (Arc n), (tours S).card ≤ 1 →
      eval (indicator (ZMod 2) S) p = if (tours S).Nonempty then 1 else 0) :
    p - Statement.hc (ZMod 2) n ∈ errorIdeal n := by
  classical
  rw [membership]
  intro a ha
  by_contra! small
  apply (mem_support_iff.mp ha)
  rw [coeff_sub, sub_eq_zero]
  apply downward (fun S : Finset (Arc n) => (tours S).card ≤ 1) (fun sub => uniqueDown sub)
    p _ ml (hcML n) _ a small
  intro S one
  change eval (indicator _ S) _ = eval (indicator _ S) _
  rw [correct S one, hcPromise S one]

private theorem vanishes {n : ℕ} {S : Finset (Arc n)} (one : (tours S).card ≤ 1)
    {p : MvPolynomial (Arc n) (ZMod 2)} (member : p ∈ errorIdeal n) : eval (indicator _ S) p = 0 := by
  classical
  let ev := eval (indicator (ZMod 2) S)
  have le : errorIdeal n ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,⟨s,t,cs,ct,ne,rfl⟩,rfl⟩
    change eval (indicator _ S) (monomial (exponent (arcs s ∪ arcs t)) (1 : ZMod 2)) = 0
    have missing : ¬arcs s ∪ arcs t ⊆ S := by
      intro both
      obtain ⟨hs,ht⟩ := union_subset_iff.mp both
      exact ne (card_le_one_iff.mp one (tour_mem.mpr ⟨cs,hs⟩) (tour_mem.mpr ⟨ct,ht⟩))
    have prod (A : Finset (Arc n)) : ∏ x ∈ A, (X x : MvPolynomial (Arc n) (ZMod 2)) =
        monomial (exponent A) 1 := by
      simpa [exponent] using (prod_X_pow (R := ZMod 2) (fun _ : Arc n => 1) A)
    rw [← prod, map_prod]
    simp only [eval_X]
    change ∏ x ∈ arcs s ∪ arcs t, (if x ∈ S then (1 : ZMod 2) else 0) = 0
    rw [prod_boole]
    exact if_neg missing
  exact le member

/-- Exact characterization for formally multilinear polynomials. -/
theorem characterize {n : ℕ} (p : MvPolynomial (Arc n) (ZMod 2)) (ml : p ∈ restrictDegree _ _ 1) :
    (∀ S : Finset (Arc n), (tours S).card ≤ 1 →
        eval (indicator (ZMod 2) S) p = if (tours S).Nonempty then 1 else 0) ↔
      p - Statement.hc (ZMod 2) n ∈ errorIdeal n := by
  refine ⟨error p ml, ?_⟩
  intro member S one
  have zero := vanishes one member
  rw [map_sub, sub_eq_zero] at zero
  exact zero.trans (hcPromise S one)

private theorem large {n : ℕ} {S : Finset (Arc n)} (two : 1 < (tours S).card) : n < S.card := by
  by_contra! small
  obtain ⟨s,hs,t,ht,ne⟩ := one_lt_card.mp two
  have eq {s} (h : s ∈ tours S) : arcs s = S :=
    eq_of_subset_of_card_le (tour_mem.mp h).2 (by simpa using small)
  apply ne
  apply Equiv.ext
  intro i
  have hit : (i,s i) ∈ arcs t := by rw [eq ht, ← eq hs]; simp
  exact ((mem_arcs t i (s i)).mp hit).symm

private theorem cardDegree {n : ℕ} (a : Arc n →₀ ℕ) : a.support.card ≤ a.degree := by
  calc
    _ = ∑ _i ∈ a.support, 1 := by simp
    _ ≤ ∑ i ∈ a.support, a i := sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ = _ := rfl

/-- Every polynomial in the ordinary monomial ideal has zero components through degree n. -/
theorem low {n d : ℕ} (p : MvPolynomial (Arc n) (ZMod 2)) (mem : p ∈ errorIdeal n) (hd : d ≤ n) :
    homogeneousComponent d p = 0 := by
  ext a
  rw [coeff_homogeneousComponent, coeff_zero]
  split
  · rename_i ha
    by_contra nz
    have big := large ((membership p).mp mem a (mem_support_iff.mpr nz))
    have cap := cardDegree a
    omega
  · rfl

/-- Ordinary-ideal-equivalent formal representatives have exactly the upstream HC polynomial
as their degree-n component, even when the representative has repeated variables. -/
theorem layer {n : ℕ} (p : MvPolynomial (Arc n) (ZMod 2))
    (mem : p - Statement.hc (ZMod 2) n ∈ errorIdeal n) : homogeneousComponent n p = Statement.hc (ZMod 2) n := by
  have zero := low _ mem (d := n) le_rfl
  rw [map_sub, sub_eq_zero] at zero
  exact zero.trans (homogeneousComponent_eq_self (by
    rw [← decisionANF_component]
    exact homogeneousComponent_mem _ _))

#print axioms downward
#print axioms membership
#print axioms error
#print axioms characterize
#print axioms low
#print axioms layer

end BooleanTransfer.PromiseIdeal
