import BallAgreement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-! Parity of a family of edge subsets preserved by a transitive prime-power group. -/

namespace BooleanTransfer.OrbitPadding

open MulAction Finset
open scoped Pointwise

variable {G E : Type*} [Group G] [Fintype E] [DecidableEq E] [MulAction G E]
variable [IsPretransitive G E]

/-- A subset of one orbit fixed by the entire group is empty or full. -/
theorem fixed_subset (s : Finset E) (fixed : ∀ g : G, g • s = s) :
    s = ∅ ∨ s = univ := by
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    rw [← fixed g]
    exact Finset.smul_mem_smul_finset hx

private def family (P : Finset E → Prop) (stable : ∀ (g : G) s, P s → P (g • s)) :
    SubMulAction G (Finset E) where
  carrier := P
  smul_mem' g := stable g _

private theorem fixed_family_cases (A : SubMulAction G (Finset E)) (t : fixedPoints G A) :
    t.val.val = ∅ ∨ t.val.val = univ := by
  apply fixed_subset (G := G)
  intro g
  exact congrArg (fun z : A => z.val) (t.property g)

/-- With neither endpoint accepted, the invariant family has cardinality divisible by p. -/
theorem interior_zero {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (P : Finset E → Prop)
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : ¬ P univ) :
    Nat.card {s // P s} ≡ 0 [MOD p] := by
  let A := family P stable
  let : IsEmpty (fixedPoints G A) := ⟨fun t => by
    have mem : P t.val.val := t.val.property
    rcases fixed_family_cases A t with e | u
    · exact he (e ▸ mem)
    · exact hu (u ▸ mem)⟩
  have h := hG.card_modEq_card_fixedPoints A
  rw [Nat.card_of_isEmpty (α := fixedPoints G A)] at h
  exact h

/-- In each strict intermediate cardinality, the population is zero modulo p. -/
theorem layer_zero {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (P : Finset E → Prop)
    (stable : ∀ (g : G) s, P s → P (g • s)) {d : ℕ} (hd : 0 < d) (hu : d < Fintype.card E) :
    Nat.card {s : Finset E // P s ∧ s.card = d} ≡ 0 [MOD p] := by
  apply interior_zero hG
  · intro g s h
    exact ⟨stable g s h.1, (Finset.card_smul_finset g s).trans h.2⟩
  · rintro ⟨_, h⟩
    simp only [card_empty] at h
    omega
  · rintro ⟨_, h⟩
    simp only [card_univ] at h
    omega

/-- If the complete edge set is accepted and the empty graph is rejected,
exactly one fixed point remains in the accepted family. -/
theorem family_one {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (P : Finset E → Prop)
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : P univ) :
    Nat.card {s // P s} ≡ 1 [MOD p] := by
  let A := family P stable
  let full : A := ⟨univ, hu⟩
  have fixed : full ∈ fixedPoints G A := fun g => Subtype.ext Finset.smul_finset_univ
  have one : Nat.card (fixedPoints G A) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨full, fixed⟩, fun t => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have mem : P t.val.val := t.val.property
    exact (fixed_family_cases A t).resolve_left (fun e => he (e ▸ mem))
  have h := hG.card_modEq_card_fixedPoints A
  rw [one] at h
  exact h

/-- Every cardinality-dependent weight over a ring of characteristic p cancels
away from the full set when the empty set is rejected and the full set accepted. -/
theorem weighted_by_card {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (R : Type*) [Ring R] [CharP R p] (P : Finset E → Prop) [DecidablePred P]
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : P univ) (w : ℕ → R) :
    (∑ s : Finset E, if P s then w s.card else 0) = w (Fintype.card E) := by
  classical
  let n := Fintype.card E
  let acc := univ.filter P
  have sizeBound (s : Finset E) (_ : s ∈ acc) : s.card ∈ range (n+1) :=
    mem_range.mpr (Nat.lt_succ_of_le s.card_le_univ)
  have full : acc.filter (fun s => s.card = n) = {univ} := by
    ext s
    simp only [acc, mem_filter, mem_univ, true_and, mem_singleton, n, card_eq_iff_eq_univ]
    refine ⟨And.right, ?_⟩
    rintro rfl
    exact ⟨hu, rfl⟩
  rw [← Finset.sum_filter]
  change ∑ s ∈ acc, w s.card = w n
  rw [← Finset.sum_fiberwise_of_maps_to' sizeBound w]
  rw [Finset.sum_eq_single n]
  · simp [full]
  · intro d _ hd
    have h := interior_zero hG (fun s => P s ∧ s.card = d)
      (fun g s hs => ⟨stable g s hs.1, (Finset.card_smul_finset g s).trans hs.2⟩)
      (fun hs => he hs.1) (fun hs => hd (hs.2.symm.trans card_univ))
    have hz : ((acc.filter (fun s => s.card = d)).card : R) = 0 := by
      apply (CharP.cast_eq_zero_iff R p _).mpr
      simpa [acc, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
        using Nat.modEq_zero_iff_dvd.mp h
    simp [nsmul_eq_mul, hz]
  · simp

/-- Diagonal of the Boolean point-indicator expansion as a literal univariate
polynomial identity in every ring of prime characteristic. -/
theorem diagonal_polynomial {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (R : Type*) [CommRing R] [CharP R p] (P : Finset E → Prop) [DecidablePred P]
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : P univ) :
    (∑ s : Finset E, if P s then (Polynomial.X : Polynomial R) ^ s.card *
      (1 - Polynomial.X) ^ (Fintype.card E - s.card) else 0) = Polynomial.X ^ Fintype.card E := by
  calc
    _ = (Polynomial.X : Polynomial R) ^ Fintype.card E *
        (1 - Polynomial.X) ^ (Fintype.card E - Fintype.card E) :=
      weighted_by_card hG (Polynomial R) P stable he hu
        (fun d => Polynomial.X ^ d * (1 - Polynomial.X) ^ (Fintype.card E - d))
    _ = _ := by rw [Nat.sub_self, pow_zero, mul_one]

/-- Boolean Möbius inversion at the full edge set, with the signs retained in
every prime characteristic. The empty-to-full change forces coefficient one. -/
theorem signed_top {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (P : Finset E → Prop) [DecidablePred P] (stable : ∀ (g : G) s, P s → P (g • s))
    (he : ¬ P ∅) (hu : P univ) :
    (∑ s : Finset E, if P s then (-1 : ZMod p) ^ (Fintype.card E - s.card) else 0) = 1 := by
  classical
  let pos (s : Finset E) := P s ∧ Even (Fintype.card E - s.card)
  let neg (s : Finset E) := P s ∧ ¬ Even (Fintype.card E - s.card)
  have pstable (g : G) (s : Finset E) (h : pos s) : pos (g • s) :=
    ⟨stable g s h.1, by simpa only [Finset.card_smul_finset] using h.2⟩
  have nstable (g : G) (s : Finset E) (h : neg s) : neg (g • s) :=
    ⟨stable g s h.1, by simpa only [Finset.card_smul_finset] using h.2⟩
  have hp := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (family_one hG pos pstable (fun h => he h.1) ⟨hu, by simp⟩)
  have hn := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (interior_zero hG neg nstable (fun h => he h.1) (fun h => h.2 (by simp)))
  have psum : (∑ s : Finset E, if pos s then (1 : ZMod p) else 0) = 1 := by
    rw [Finset.sum_boole pos]
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hp
  have nsum : (∑ s : Finset E, if neg s then (1 : ZMod p) else 0) = 0 := by
    rw [Finset.sum_boole neg]
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hn
  calc
    _ = ∑ s : Finset E, ((if pos s then (1 : ZMod p) else 0) -
                          (if neg s then (1 : ZMod p) else 0)) := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : P s <;> by_cases h' : Even (Fintype.card E - s.card) <;>
        simp [pos, neg, h, h', ← Nat.not_even_iff_odd]
    _ = 1 := by rw [Finset.sum_sub_distrib, psum, nsum, sub_zero]

/-- Base change to any ring of the same prime characteristic. -/
theorem signed_top_ring {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (R : Type*) [Ring R] [CharP R p] (P : Finset E → Prop) [DecidablePred P]
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : P univ) :
    (∑ s : Finset E, if P s then (-1 : R) ^ (Fintype.card E - s.card) else 0) = 1 := by
  let f : ZMod p →+* R := ZMod.castHom (dvd_refl p) R
  have h := congrArg f (signed_top hG P stable he hu)
  rw [map_sum, map_one] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : P s <;> simp [hs]

/-- The coefficient is taken with the companion's actual Boolean Möbius sum. -/
theorem top_coefficient (hG : IsPGroup 2 G) (P : Finset E → Prop) [DecidablePred P]
    (stable : ∀ (g : G) s, P s → P (g • s)) (he : ¬ P ∅) (hu : P univ) :
    BallAgreement.coefficient (fun s => if P s then 1 else 0) univ = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (family_one hG P stable he hu)
  simpa [BallAgreement.coefficient, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole] using h

end BooleanTransfer.OrbitPadding

#print axioms BooleanTransfer.OrbitPadding.fixed_subset
#print axioms BooleanTransfer.OrbitPadding.layer_zero
#print axioms BooleanTransfer.OrbitPadding.diagonal_polynomial
#print axioms BooleanTransfer.OrbitPadding.signed_top
#print axioms BooleanTransfer.OrbitPadding.signed_top_ring
#print axioms BooleanTransfer.OrbitPadding.top_coefficient
