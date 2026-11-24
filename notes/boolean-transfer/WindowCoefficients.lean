import CoreCoefficient
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fin.Basic

/-! # Multilinear coefficients on a downward-closed promise

The residue lines in the example are the translates of `{0,1,3,9}` in
`Fin 13`. Forbidden triples contain only points, leaving line bits arbitrary.
The final result reconstructs the incidence decision using four fixed caps.
-/

namespace BooleanTransfer.WindowCoefficients

open Finset CoreCoefficient

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The Boolean values on a downward-closed family determine exactly the
signed coefficients indexed by that family, over every commutative ring. -/
theorem windowIff (W : Finset ι → Prop) (down : ∀ ⦃S T⦄, S ⊆ T → W T → W S)
    (f g : Finset ι → R) :
    (∀ S, W S → f S = g S) ↔ ∀ S, W S → signed f S = signed g S := by
  constructor
  · intro eq S hS
    apply sum_congr rfl
    intro T ht
    rw [eq T (down (mem_powerset.mp ht) hS)]
  · intro eq S hS
    have he : expansion (signed f) S = expansion (signed g) S := by
      apply sum_congr rfl
      intro T ht
      rw [eq T (down (mem_powerset.mp ht) hS)]
    rw [← realizes f S S (Subset.rfl), ← realizes g S S (Subset.rfl), he]

/-- A nonzero coefficient of the formal difference must contain a forbidden
support. Membership and line-variable information outside that support are free. -/
theorem forbiddenWitness (bad : Finset (Finset ι)) (f g : Finset ι → R)
    (eq : ∀ S, (∀ B ∈ bad, ¬ B ⊆ S) → f S = g S)
    (ambient S : Finset ι) (sub : S ⊆ ambient)
    (nz : MvPolynomial.coeff (exponent S)
      (expansion (signed f) ambient - expansion (signed g) ambient) ≠ 0) :
    ∃ B ∈ bad, B ⊆ S := by
  classical
  by_contra! clean
  have same := (windowIff (fun T => ∀ B ∈ bad, ¬ B ⊆ T)
    (by intro S T inc good B hB cmp; exact good B hB (cmp.trans inc)) f g).mp eq S clean
  exact nz (by rw [MvPolynomial.coeff_sub, formal _ _ _ sub, formal _ _ _ sub, same, sub_self])

private theorem supportOfExponent (S : Finset ι) : (exponent S).support = S := by
  ext i
  by_cases h : i ∈ S <;> simp [Finsupp.mem_support_iff, exponent, h]

/-- The support of a nonzero coefficient of either expansion is squarefree. -/
private theorem squarefreeWitness (c : Finset ι → R) (E : Finset ι) (d : ι →₀ ℕ)
    (nz : MvPolynomial.coeff d (expansion c E) ≠ 0) :
    ∃ S ⊆ E, d = exponent S := by
  classical
  by_contra! h
  apply nz
  simp only [expansion, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro T ht
  have coeff := MvPolynomial.coeff_prod_X_pow (R := R) d (fun _ => 1) T
  have ne : d ≠ Finsupp.indicator T (fun _ _ => 1) := h T (mem_powerset.mp ht)
  simpa only [pow_one, if_neg ne, mul_zero] using congrArg (c T * ·) coeff

/-- Point neighbours of the line indexed by w in the cyclic projective plane. -/
def linePoints (w : Fin 13) : Finset (Fin 13) := {w, w+1, w+3, w+9}

/-- The distinct forbidden point triples, with duplicates removed by union. -/
def triples : Finset (Finset (Fin 13)) := univ.biUnion (fun w => (linePoints w).powersetCard 3)

set_option maxRecDepth 10000 in
theorem tripleCount : triples.card = 52 := by decide +kernel

/-- Each labelled variable is a point or a line. Only the point inclusions
participate in the 52 forbidden triples. -/
theorem collinearWitness {L : Type*} [DecidableEq L]
    (f g : Finset (Fin 13 ⊕ L) → R)
    (eq : ∀ S, (∀ B ∈ triples, ¬ B.map Function.Embedding.inl ⊆ S) → f S = g S)
    (E S : Finset (Fin 13 ⊕ L)) (sub : S ⊆ E)
    (nz : MvPolynomial.coeff (exponent S)
      (expansion (signed f) E - expansion (signed g) E) ≠ 0) :
    ∃ B ∈ triples, B.map Function.Embedding.inl ⊆ S := by
  classical
  let bad : Finset (Finset (Fin 13 ⊕ L)) :=
    triples.image (fun B => B.map Function.Embedding.inl)
  obtain ⟨T, hT, ht⟩ := forbiddenWitness bad f g (fun V hV => eq V
    (fun B hB => hV _ (mem_image_of_mem _ hB))) E S sub nz
  rcases mem_image.mp hT with ⟨B, hB, rfl⟩
  exact ⟨B, hB, ht⟩

/-- This version accepts any formal monomial exponent, including arbitrary
line variables and potentially repeated coordinates in the proposed exponent. -/
theorem monomialContainsTriple {L : Type*} [DecidableEq L]
    (f g : Finset (Fin 13 ⊕ L) → R)
    (eq : ∀ S, (∀ B ∈ triples, ¬ B.map Function.Embedding.inl ⊆ S) → f S = g S)
    (E : Finset (Fin 13 ⊕ L)) (d : (Fin 13 ⊕ L) →₀ ℕ)
    (nz : MvPolynomial.coeff d
      (expansion (signed f) E - expansion (signed g) E) ≠ 0) :
    ∃ B ∈ triples, B.map Function.Embedding.inl ⊆ d.support := by
  have hit : ∃ S ⊆ E, d = exponent S := by
    by_cases hf : MvPolynomial.coeff d (expansion (signed f) E) = 0
    · apply squarefreeWitness (signed g) E d
      intro hg
      exact nz (by rw [MvPolynomial.coeff_sub, hf, hg, sub_self])
    · exact squarefreeWitness (signed f) E d hf
  obtain ⟨S, sub, rfl⟩ := hit
  rw [supportOfExponent]
  exact collinearWitness f g eq E S sub nz

/-- Absence of a forbidden triple is exactly the posted line-by-line promise. -/
theorem avoidsIff (P : Finset (Fin 13)) :
    (∀ B ∈ triples, ¬ B ⊆ P) ↔ ∀ w, (P ∩ linePoints w).card ≤ 2 := by
  constructor
  · intro clean w
    by_contra! large
    obtain ⟨B, sub, size⟩ := exists_subset_card_eq (show 3 ≤ (P ∩ linePoints w).card by omega)
    have triple : B ∈ triples := mem_biUnion.mpr
      ⟨w, mem_univ _, mem_powersetCard.mpr ⟨sub.trans inter_subset_right, size⟩⟩
    exact clean B triple (sub.trans inter_subset_left)
  · intro clean B hB sub
    obtain ⟨w, _, hB⟩ := mem_biUnion.mp hB
    obtain ⟨line, size⟩ := mem_powersetCard.mp hB
    have bound := (card_le_card (subset_inter sub line)).trans (clean w)
    omega

/-- Agreement on all inputs satisfying the posted promise forces every
nonzero discrepancy monomial to contain a collinear triple of point variables.
The selected lines are unrestricted. -/
theorem arcWindowDifference {L : Type*} [DecidableEq L]
    (f g : Finset (Fin 13 ⊕ L) → R) (agree : ∀ A,
      (∀ w, (A.toLeft ∩ linePoints w).card ≤ 2) → f A = g A)
    (E : Finset (Fin 13 ⊕ L)) (d : (Fin 13 ⊕ L) →₀ ℕ)
    (nz : MvPolynomial.coeff d
      (expansion (signed f) E - expansion (signed g) E) ≠ 0) :
    ∃ B ∈ triples, B ⊆ d.support.toLeft := by
  obtain ⟨B, hB, sub⟩ := monomialContainsTriple f g (fun A clean => agree A
    ((avoidsIff _).mp (fun B hB sub => clean B hB
      (map_inl_subset_iff_subset_toLeft.mpr sub)))) E d nz
  exact ⟨B, hB, map_inl_subset_iff_subset_toLeft.mp sub⟩

/-- Four specific point sets, each a translate of {0,1,2,6}. -/
def caps : Finset (Finset (Fin 13)) :=
  {{0,1,2,6}, {3,4,5,9}, {6,7,8,12}, {2,9,10,11}}

set_option maxRecDepth 10000 in
theorem capsSize : caps.card = 4 ∧ ∀ A ∈ caps, A.card = 4 := by decide +kernel

set_option maxRecDepth 10000 in
theorem capsCover : ∀ p : Fin 13, ∃ A ∈ caps, p ∈ A := by decide +kernel

set_option maxRecDepth 10000 in
theorem capsClean : ∀ A ∈ caps, ∀ w : Fin 13, (A ∩ linePoints w).card ≤ 2 := by decide +kernel

/-- Selecting a point incident to a selected line. -/
def hits (P L : Finset (Fin 13)) : Prop := ∃ p ∈ P, ∃ w ∈ L, p ∈ linePoints w

/-- Promised soundness, acceptance of each incident pair, and monotonicity
give the agreement hypothesis used by the four-restriction identity. -/
theorem promiseAgreement (accept : Finset (Fin 13) → Finset (Fin 13) → Prop)
    (mono : ∀ ⦃P Q L M⦄, P ⊆ Q → L ⊆ M → accept P L → accept Q M)
    (complete : ∀ p w, p ∈ linePoints w → accept {p} {w})
    (sound : ∀ P L, (∀ w, (P ∩ linePoints w).card ≤ 2) → accept P L → hits P L)
    (P L : Finset (Fin 13)) (clean : ∀ w, (P ∩ linePoints w).card ≤ 2) :
    accept P L ↔ hits P L := by
  refine ⟨sound P L clean, ?_⟩
  rintro ⟨p,hp,w,hw,edge⟩
  exact mono (singleton_subset_iff.mpr hp) (singleton_subset_iff.mpr hw) (complete p w edge)

/-- Four fixed calls to a promise-correct decision predicate reconstruct
incidence on every assignment; each call retains all selected lines. -/
theorem fourRestrictions (accept : Finset (Fin 13) → Finset (Fin 13) → Prop)
    (agree : ∀ P L, (∀ w, (P ∩ linePoints w).card ≤ 2) → (accept P L ↔ hits P L))
    (P L : Finset (Fin 13)) :
    (∃ A ∈ caps, accept (P ∩ A) L) ↔ hits P L := by
  have safe (A) (hA : A ∈ caps) (w) : ((P ∩ A) ∩ linePoints w).card ≤ 2 :=
    (card_le_card (inter_subset_inter_right inter_subset_right)).trans (capsClean A hA w)
  constructor
  · rintro ⟨A,hA,ok⟩
    obtain ⟨p,hp,w,hw,edge⟩ := (agree _ _ (safe A hA)).mp ok
    exact ⟨p,(mem_inter.mp hp).1,w,hw,edge⟩
  · rintro ⟨p,hp,w,hw,edge⟩
    obtain ⟨A,hA,hpA⟩ := capsCover p
    exact ⟨A,hA,(agree _ _ (safe A hA)).mpr ⟨p,mem_inter.mpr ⟨hp,hpA⟩,w,hw,edge⟩⟩

end BooleanTransfer.WindowCoefficients

#print axioms BooleanTransfer.WindowCoefficients.windowIff
#print axioms BooleanTransfer.WindowCoefficients.forbiddenWitness
#print axioms BooleanTransfer.WindowCoefficients.tripleCount
#print axioms BooleanTransfer.WindowCoefficients.collinearWitness
#print axioms BooleanTransfer.WindowCoefficients.fourRestrictions

#print axioms BooleanTransfer.WindowCoefficients.monomialContainsTriple

#print axioms BooleanTransfer.WindowCoefficients.arcWindowDifference
