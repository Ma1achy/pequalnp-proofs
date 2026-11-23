import PEqualNP.Defs.SearchQSyn
import Mathlib.Data.ZMod.Basic

/-! Coefficientwise reduction from syntactic integer R(lin) to syntactic R(lin) over
a residue ring. For prime modulus the target is a finite field. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

abbrev ModEqn (p : ℕ) (V : Type) := (V → ZMod p) × ZMod p
abbrev ModLine (p : ℕ) (V : Type) := List (ModEqn p V)

/-- Map each coefficient and the right-hand side to its residue. -/
def reduceEquation (p : ℕ) {V : Type} (e : QEq V) : ModEqn p V :=
  (fun v => (e.1 v : ZMod p), (e.2 : ZMod p))

def reduceLine (p : ℕ) {V : Type} (L : QLine V) : ModLine p V :=
  L.map (reduceEquation p)

/-- A DAG derivation with the same six syntactic rules as the integer system.
The resolution multipliers now lie in the residue ring. -/
inductive IsModSynDerivation (p : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (Clause V)) : List (ModLine p V) → Prop
  | nil : IsModSynDerivation p F []
  | ax {ρ L} (C : Clause V) : IsModSynDerivation p F ρ → C ∈ F →
      (∀ e, e ∈ L ↔ ∃ t ∈ C, e = reduceEquation p (litQEq t)) →
      IsModSynDerivation p F (L :: ρ)
  | bool {ρ} (v : V) : IsModSynDerivation p F ρ →
      IsModSynDerivation p F (reduceLine p [litQEq (v, false), litQEq (v, true)] :: ρ)
  | res {ρ} {e f : ModEqn p V} {C D : ModLine p V} (α β : ZMod p) :
      IsModSynDerivation p F ρ → (e :: C) ∈ ρ → (f :: D) ∈ ρ →
      IsModSynDerivation p F (((α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)) :: ρ)
  | weaken {ρ C D} : IsModSynDerivation p F ρ → C ∈ ρ → (∀ e ∈ C, e ∈ D) →
      IsModSynDerivation p F (D :: ρ)
  | simp {ρ} {C : ModLine p V} : IsModSynDerivation p F ρ → C ∈ ρ →
      IsModSynDerivation p F (C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) :: ρ)

def IsModSynRefutation (p : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (Clause V)) (ρ : List (ModLine p V)) : Prop :=
  IsModSynDerivation p F ρ ∧ [] ∈ ρ

variable {V : Type}

/-- The modular image of a linear combination is the combination of the images. -/
private theorem reduce_combo (p : ℕ) (e f : QEq V) (α β : ℤ) :
    reduceEquation p (α • e.1 + β • f.1, α * e.2 + β * f.2) =
      ((α : ZMod p) • (reduceEquation p e).1 + (β : ZMod p) • (reduceEquation p f).1,
       (α : ZMod p) * (reduceEquation p e).2 + (β : ZMod p) * (reduceEquation p f).2) := by
  apply Prod.ext
  · funext v
    simp [reduceEquation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp [reduceEquation]

variable [Fintype V] [DecidableEq V]

private def ModSimulation (p : ℕ) (F : Set (Clause V)) (π : List (QLine V)) : Prop :=
  ∃ ρ, IsModSynDerivation p F ρ ∧ (∀ L ∈ π, reduceLine p L ∈ ρ) ∧ ρ.length ≤ 2 * π.length

private theorem extend_mod_sim {p : ℕ} {F : Set (Clause V)} {π : List (QLine V)}
    {L : QLine V} {ρ σ : List (ModLine p V)}
    (hold : ∀ K ∈ π, reduceLine p K ∈ ρ) (hlen : ρ.length ≤ 2 * π.length)
    (h : IsModSynDerivation p F (σ ++ ρ)) (hL : reduceLine p L ∈ σ)
    (hσ : σ.length ≤ 2) : ModSimulation p F (L :: π) := by
  refine ⟨σ ++ ρ, h, ?_, ?_⟩
  · intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact List.mem_append_left _ hL
    · exact List.mem_append_right _ (hold K hK)
  · simp only [List.length_append, List.length_cons]
    omega

/-- When the modulus does not divide any nonzero right-hand side on a zero-vector
equation, every integral derivation step can be projected in at most two steps. -/
private theorem mod_simulation_of_safe (p : ℕ) {F : Set (Clause V)} {π : List (QLine V)}
    (d : IsResLinQSynDerivation F π)
    (safe : ∀ L ∈ π, ∀ e ∈ L, e.1 = 0 → e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2) :
    ModSimulation p F π := by
  have tail_safe {K : QLine V} {τ : List (QLine V)}
      (h : ∀ L ∈ K :: τ, ∀ e ∈ L, e.1 = 0 → e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2) :
      ∀ L ∈ τ, ∀ e ∈ L, e.1 = 0 → e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2 :=
    fun L hL => h L (List.mem_cons_of_mem K hL)
  induction d with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @ax π L C _ hC hL ih =>
    obtain ⟨ρ, dρ, prev, len⟩ := ih (tail_safe safe)
    refine extend_mod_sim (σ := [reduceLine p L]) prev len (.ax C dρ hC ?_) List.mem_cons_self (by simp)
    intro e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      obtain ⟨t, ht, rfl⟩ := (hL _).mp hf
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact List.mem_map.mpr ⟨_, (hL _).mpr ⟨t, ht, rfl⟩, rfl⟩
  | bool v _ ih =>
    obtain ⟨ρ, dρ, prev, len⟩ := ih (tail_safe safe)
    exact extend_mod_sim (σ := [_]) prev len (.bool v dρ) List.mem_cons_self (by simp)
  | @res π e f C D α β _ hC hD ih =>
    obtain ⟨ρ, dρ, prev, len⟩ := ih (tail_safe safe)
    apply extend_mod_sim (σ := [_]) prev len _ List.mem_cons_self (by simp)
    simpa only [reduceLine, List.map_cons, List.map_append, reduce_combo, List.cons_append, List.nil_append] using
      IsModSynDerivation.res (α : ZMod p) (β : ZMod p) dρ (prev _ hC) (prev _ hD)
  | @weaken π C D _ hC hCD ih =>
    obtain ⟨ρ, dρ, prev, len⟩ := ih (tail_safe safe)
    refine extend_mod_sim (σ := [reduceLine p D]) prev len (.weaken dρ (prev _ hC) ?_) List.mem_cons_self (by simp)
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact List.mem_map.mpr ⟨_, hCD _ hf, rfl⟩
  | @simp π C _ hC ih =>
    obtain ⟨ρ, dρ, prev, len⟩ := ih (tail_safe safe)
    let K := (reduceLine p C).filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))
    let D := C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))
    have dk : IsModSynDerivation p _ (K :: ρ) := .simp dρ (prev C hC)
    refine extend_mod_sim (σ := [reduceLine p D, K]) prev len
      (.weaken dk List.mem_cons_self ?_) List.mem_cons_self (by simp)
    intro e he
    obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hmem
    apply List.mem_map.mpr
    refine ⟨f, List.mem_filter.mpr ⟨hf, ?_⟩, rfl⟩
    apply decide_eq_true
    rintro ⟨hz, hn⟩
    have hmod : (f.2 : ZMod p) ≠ 0 := by
      intro hzero
      exact safe C (List.mem_cons_of_mem _ hC) f hf hz hn
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
    apply (of_decide_eq_true hkeep)
    exact ⟨by ext v; simp [reduceEquation, hz], hmod⟩

/-- Project a DAG refutation to the syntactic modular system. Simplification can
erase extra equations after reduction; one syntactic weakening restores them. -/
theorem mod_refutation_of_safe (p : ℕ) {F : Set (Clause V)} {π : List (QLine V)}
    (hπ : IsResLinQSynRefutation F π)
    (safe : ∀ L ∈ π, ∀ e ∈ L, e.1 = 0 → e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2) :
    ∃ ρ, IsModSynRefutation p F ρ ∧ ρ.length ≤ 2 * π.length := by
  obtain ⟨ρ, d, prev, len⟩ := mod_simulation_of_safe p hπ.1 safe
  exact ⟨ρ, ⟨d, prev [] hπ.2⟩, len⟩

end PEqualNP.Search.Helpers
