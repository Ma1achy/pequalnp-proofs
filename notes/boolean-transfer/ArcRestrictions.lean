import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Ring.Basic

/-! Function-level normal forms for monotone incidence on a hereditary point-domain. -/

namespace ArcRestrictions

open Finset

variable {P L : Type*}

def incidence (adj : P → L → Prop) (A : Finset P) (B : Finset L) : Prop :=
  ∃ p ∈ A, ∃ l ∈ B, adj p l

/-- Pair completeness and soundness on the promise domain amount to a global
interval. No assumption on the shape of gates is made except semantic monotonicity. -/
theorem interval_iff (adj : P → L → Prop) (arc : Finset P → Prop)
    (C : Finset P → Finset L → Prop)
    (mono : ∀ {A A' B B'}, A ⊆ A' → B ⊆ B' → C A B → C A' B') :
    ((∀ p l, adj p l → C {p} {l}) ∧
      (∀ A B, arc A → C A B → incidence adj A B)) ↔
    ((∀ A B, incidence adj A B → C A B) ∧
      (∀ A B, C A B → incidence adj A B ∨ ¬ arc A)) := by
  constructor
  · rintro ⟨pairs, sound⟩
    refine ⟨?_, ?_⟩
    · rintro A B ⟨p, hp, l, hl, hpl⟩
      exact mono (singleton_subset_iff.mpr hp) (singleton_subset_iff.mpr hl) (pairs p l hpl)
    · intro A B h
      by_cases ha : arc A
      · exact Or.inl (sound A B ha h)
      · exact Or.inr ha
  · rintro ⟨lo, hi⟩
    refine ⟨?_, ?_⟩
    · intro p l hpl
      exact lo _ _ ⟨p, mem_singleton_self _, l, mem_singleton_self _, hpl⟩
    · intro A B ha h
      exact (hi A B h).resolve_right (fun no => no ha)

variable {V : Type*}

/-- Signed Boolean Möbius coefficients over an arbitrary commutative ring. -/
def mobius {R : Type*} [CommRing R] (f : Finset V → R) (S : Finset V) : R :=
  ∑ T ∈ S.powerset, (-1 : R) ^ (S.card - T.card) * f T

/-- A coefficient on an allowed support depends only on allowed cube values. -/
theorem mobius_agree {R : Type*} [CommRing R] (allowed : Finset V → Prop)
    (hereditary : ∀ {S T}, S ⊆ T → allowed T → allowed S)
    (f g : Finset V → R) (agree : ∀ S, allowed S → f S = g S) {S : Finset V}
    (hS : allowed S) : mobius f S = mobius g S := by
  apply sum_congr rfl
  intro T hT
  rw [agree T (hereditary (mem_powerset.mp hT) hS)]

/-- Covering all points by allowed sets recovers the full function by
evaluating the promised function on the restrictions separately. -/
theorem recover_of_cover [DecidableEq P] (adj : P → L → Prop) (C : Finset P → Finset L → Prop)
    (allowed : Finset P → Prop) (closed : ∀ {S T}, S ⊆ T → allowed T → allowed S)
    (agree : ∀ A B, allowed A → (C A B ↔ incidence adj A B))
    (parts : Finset (Finset P)) (covers : ∀ p : P, ∃ S ∈ parts, p ∈ S)
    (good : ∀ S ∈ parts, allowed S) (A : Finset P) (B : Finset L) :
    incidence adj A B ↔ ∃ S ∈ parts, C (A ∩ S) B := by
  constructor
  · rintro ⟨p, hp, l, hl, hpl⟩
    obtain ⟨S, hS, hs⟩ := covers p
    exact ⟨S, hS, (agree _ _ (closed inter_subset_right (good S hS))).mpr
      ⟨p, mem_inter.mpr ⟨hp, hs⟩, l, hl, hpl⟩⟩
  · rintro ⟨S, hS, hc⟩
    obtain ⟨p, hp, l, hl, hpl⟩ := (agree _ _ (closed inter_subset_right (good S hS))).mp hc
    exact ⟨p, (mem_inter.mp hp).1, l, hl, hpl⟩

end ArcRestrictions
