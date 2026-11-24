import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Finite

/-! Swapping the incoming targets of the roots joins two finite permutation cycles. -/

namespace BooleanTransfer.SplicePermutation

open Equiv Equiv.Perm

variable {α β : Type*}

/-- The two original permutations act on disjoint blocks. The final transposition
redirects each arc into either root to the other root. -/
def splice [DecidableEq α] [DecidableEq β] (a : α) (b : β)
    (σ : Perm α) (π : Perm β) : Perm (α ⊕ β) :=
  Equiv.swap (.inl a) (.inr b) * σ.sumCongr π

private theorem step_inl [DecidableEq α] [DecidableEq β] (a : α) (b : β)
    (σ : Perm α) (π : Perm β) (x : α) :
    splice a b σ π (.inl x) = if σ x = a then .inr b else .inl (σ x) := by
  simp [splice, Equiv.swap_apply_def]

private theorem step_inr [DecidableEq α] [DecidableEq β] (a : α) (b : β)
    (σ : Perm α) (π : Perm β) (y : β) :
    splice a b σ π (.inr y) = if π y = b then .inl a else .inr (π y) := by
  simp [splice, Equiv.swap_apply_def]

private theorem orbit_closed [Finite α] {f : Perm α} {P : α → Prop} {x y : α}
    (h : f.SameCycle x y) (hx : P x) (step : ∀ v, P v → P (f v)) : P y := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => simpa using hx
  | succ i ih => simpa [pow_succ'] using step _ ih

private theorem cycle_univ_iff_root (f : Perm α) (x : α) :
    f.IsCycleOn Set.univ ↔ ∀ y, f.SameCycle x y :=
  ⟨fun h y => h.2 (Set.mem_univ x) (Set.mem_univ y),
    fun h => ⟨f.bijective.bijOn_univ, fun u _ v _ => (h u).symm.trans (h v)⟩⟩

/-- On finite nonempty blocks, the spliced permutation is a single spanning
cycle exactly when both original permutations are spanning cycles. Singleton
blocks are allowed. -/
theorem isCycleOn_splice_iff [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (σ : Perm α) (π : Perm β) :
    (splice a b σ π).IsCycleOn Set.univ ↔
      σ.IsCycleOn Set.univ ∧ π.IsCycleOn Set.univ := by
  rw [cycle_univ_iff_root _ (.inl a), cycle_univ_iff_root σ a, cycle_univ_iff_root π b]
  constructor
  · intro h
    let P : (α ⊕ β) → Prop := Sum.elim (σ.SameCycle a) (π.SameCycle b)
    have step (v : α ⊕ β) (hv : P v) : P (splice a b σ π v) := by
      cases v with
      | inl x =>
        rw [step_inl]
        split
        · exact SameCycle.rfl
        · exact (show σ.SameCycle a x from hv).apply_right
      | inr y =>
        rw [step_inr]
        split
        · exact SameCycle.rfl
        · exact (show π.SameCycle b y from hv).apply_right
    have allVertices (v) : P v := orbit_closed (h v) (show P (.inl a) from SameCycle.rfl) step
    exact ⟨fun x => allVertices (.inl x), fun y => allVertices (.inr y)⟩
  · rintro ⟨left, right⟩
    let f := splice a b σ π
    have leftOrbit (x : α) : f.SameCycle (.inl a) (.inl x) := by
      refine orbit_closed (P := fun v => f.SameCycle (.inl a) (.inl v)) (left x) SameCycle.rfl ?_
      intro v hv
      by_cases h : σ v = a
      · simpa [h] using (SameCycle.rfl : f.SameCycle (.inl a) (.inl a))
      · have eq : f (.inl v) = .inl (σ v) := by simp [f, step_inl, h]
        exact eq ▸ hv.apply_right
    have bridge : f.SameCycle (.inl a) (.inr b) := by
      have eq : f (.inl (σ.symm a)) = .inr b := by simp [f, step_inl]
      exact eq ▸ (leftOrbit (σ.symm a)).apply_right
    intro v
    cases v with
    | inl x => exact leftOrbit x
    | inr y =>
      refine orbit_closed (P := fun v => f.SameCycle (.inl a) (.inr v)) (right y) bridge ?_
      intro v hv
      by_cases h : π v = b
      · simpa [h] using bridge
      · have eq : f (.inr v) = .inr (π v) := by simp [f, step_inr, h]
        exact eq ▸ hv.apply_right

/-- The disjoint union of the two arc relations before redirection. -/
def blockEdge (E : α → α → Prop) (F : β → β → Prop) :
    (α ⊕ β) → (α ⊕ β) → Prop
  | .inl x, .inl y => E x y
  | .inr x, .inr y => F x y
  | _, _ => False

/-- A candidate arc is present exactly when undoing the head swap gives an
arc in its original block. -/
def spliceEdge [DecidableEq α] [DecidableEq β] (a : α) (b : β)
    (E : α → α → Prop) (F : β → β → Prop) (u v : α ⊕ β) : Prop :=
  blockEdge E F u (Equiv.swap (.inl a) (.inr b) v)

private theorem supports_splice_iff [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (E : α → α → Prop) (F : β → β → Prop)
    (σ : Perm α) (π : Perm β) :
    (∀ x, spliceEdge a b E F x (splice a b σ π x)) ↔ (∀ x, E x (σ x)) ∧ (∀ y, F y (π y)) := by
  constructor
  · intro h
    exact ⟨fun x => by simpa [spliceEdge, splice, blockEdge] using h (.inl x),
      fun y => by simpa [spliceEdge, splice, blockEdge] using h (.inr y)⟩
  · rintro ⟨hl, hr⟩ (x | y)
    · simpa [spliceEdge, splice, blockEdge] using hl x
    · simpa [spliceEdge, splice, blockEdge] using hr y

/-- Every supported permutation on the spliced graph comes from a pair of
permutations of the original blocks. -/
theorem supported_is_splice [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (E : α → α → Prop) (F : β → β → Prop)
    (f : Perm (α ⊕ β)) (h : ∀ x, spliceEdge a b E F x (f x)) :
    ∃ σ π, splice a b σ π = f := by
  let τ : Perm (α ⊕ β) := Equiv.swap (.inl a) (.inr b)
  have preserves : Set.MapsTo (τ * f) (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨x, rfl⟩
    have hx : blockEdge E F (.inl x) ((τ * f) (.inl x)) := h (.inl x)
    cases hv : (τ * f) (.inl x) with
    | inl u => exact ⟨u, rfl⟩
    | inr v => rw [hv] at hx; exact False.elim hx
  obtain ⟨⟨σ, π⟩, eq⟩ := mem_sumCongrHom_range_of_perm_mapsTo_inl preserves
  change σ.sumCongr π = τ * f at eq
  refine ⟨σ, π, ?_⟩
  change τ * σ.sumCongr π = f
  rw [eq, ← mul_assoc]
  simp [τ]

/-- The predicate used to filter the upstream Hamiltonian-cycle polynomial,
together with the requirement that each chosen arc exists. -/
def HasSpanningCycle (E : α → α → Prop) : Prop :=
  ∃ σ : Perm α, σ.IsCycleOn Set.univ ∧ ∀ x, E x (σ x)

/-- Existence of a spanning permutation tour in the spliced graph factors
as the conjunction of the two original existence predicates. -/
theorem hasSpanningCycle_splice_iff [Finite α] [Finite β] [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (E : α → α → Prop) (F : β → β → Prop) :
    HasSpanningCycle (spliceEdge a b E F) ↔ HasSpanningCycle E ∧ HasSpanningCycle F := by
  constructor
  · rintro ⟨f, cycle, edges⟩
    obtain ⟨σ, π, rfl⟩ := supported_is_splice a b E F f edges
    obtain ⟨left, right⟩ := (isCycleOn_splice_iff ..).mp cycle
    obtain ⟨le, re⟩ := (supports_splice_iff ..).mp edges
    exact ⟨⟨σ, left, le⟩, ⟨π, right, re⟩⟩
  · rintro ⟨⟨σ, left, le⟩, ⟨π, right, re⟩⟩
    exact ⟨splice a b σ π, (isCycleOn_splice_iff ..).mpr ⟨left, right⟩,
      (supports_splice_iff ..).mpr ⟨le, re⟩⟩

end BooleanTransfer.SplicePermutation
