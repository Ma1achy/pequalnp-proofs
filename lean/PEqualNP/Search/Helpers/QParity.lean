import PEqualNP.Defs.SearchQSyn
import PEqualNP.Defs.ProofComplexityLin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

/-! Reduction of the integer equations in an R(lin) line modulo two. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V]

/-- Reduce the coefficients and the right-hand side of an equation modulo two. -/
def qParity (e : QEq V) : LinEq V :=
  (Finset.univ.filter (fun v => e.1 v % 2 = 1), decide (e.2 % 2 = 1))

/-- A disjunction of integer equations reduced modulo two. -/
noncomputable def qLineParity (L : QLine V) : LinClause V := by
  classical
  exact L.toFinset.image qParity

@[simp] theorem qParity_lit [DecidableEq V] (l : V × Bool) :
    qParity (litQEq l) = ({l.1}, l.2) := by
  rcases l with ⟨v, b⟩
  apply Prod.ext
  · apply Finset.ext
    intro u
    change u ∈ Finset.univ.filter (fun w : V => (if w = v then (1 : ℤ) else 0) % 2 = 1) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases h : u = v <;> simp [h]
  · cases b <;> simp [qParity, litQEq]

/-- The reduced equation holds precisely when the integer sides agree modulo two. -/
theorem qParity_sat (a : V → Bool) (e : QEq V) :
    LinEqSat a (qParity e) ↔
      (∑ v, e.1 v * (if a v then 1 else 0)) ≡ e.2 [ZMOD 2] := by
  have h : (∑ v, e.1 v * (if a v then 1 else 0)) ≡
      (∑ v, if e.1 v % 2 = 1 ∧ a v = true then (1 : ℤ) else 0) [ZMOD 2] := by
    apply Int.ModEq.sum
    intro v _
    by_cases h : e.1 v % 2 = 1 <;> cases a v <;> simp [h, Int.ModEq]
    omega
  rw [Finset.sum_boole] at h
  unfold LinEqSat qParity
  simp only [Finset.filter_filter, Nat.odd_iff, decide_eq_true_eq]
  unfold Int.ModEq at *
  omega

/-- Satisfaction of the projected heads is preserved by an integer linear combination. -/
theorem qParity_combo (a : V → Bool) (e e' : QEq V) (α β : ℤ)
    (he : LinEqSat a (qParity e)) (he' : LinEqSat a (qParity e')) :
    LinEqSat a (qParity (α • e.1 + β • e'.1, α * e.2 + β * e'.2)) := by
  rw [qParity_sat] at *
  have h := he.mul_left α
  have h' := he'.mul_left β
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum] using h.add h'

/-- A false constant equation with odd right-hand side stays false after reduction. -/
theorem qParity_false (a : V → Bool) (e : QEq V) (hz : e.1 = 0) (ho : Odd e.2) :
    ¬ LinEqSat a (qParity e) := by
  rw [qParity_sat]
  obtain ⟨k, hk⟩ := ho
  simp [hz, Int.ModEq]
  omega

end PEqualNP.Search.Helpers
