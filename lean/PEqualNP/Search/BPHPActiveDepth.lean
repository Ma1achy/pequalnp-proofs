import PEqualNP.Search.QActiveEquations
import PEqualNP.Search.BPHPEquationDecisionDepth
import PEqualNP.Search.BPHPGrowingSupport

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- Only equations used in both roles require exact bounded-depth trees. Each
literal receives its canonical one-query code even if it also has other trees. -/
theorem active_depth_equation_simulation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (bounded : ∀ e, QProduced π e → QSelected π e → ∃ t : ParityTree V,
      t.depth ≤ k ∧ ∀ a, t.eval a = true ↔ QEq.Holds a e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let literal (e : QEq V) := ∃ t : V × Bool, e = litQEq t
  let small (e : QEq V) := ∃ t : ParityTree V, t.depth ≤ k ∧
    ∀ a, t.eval a = true ↔ QEq.Holds a e
  let easy (e : QEq V) := literal e ∨ small e
  let repr (e : QEq V) (h : easy e) := if hl : literal e then qCodeTree [] e
    else (show small e from h.resolve_left hl).choose
  have easyLit (t : V × Bool) : easy (litQEq t) := Or.inl ⟨t, rfl⟩
  apply active_code_equation_simulation k hk seed ref easy repr easyLit
  · intro t
    have hl : literal (litQEq t) := ⟨t, rfl⟩
    simpa only [repr, dite_eq_left hl, qCode] using qCode_lit [] t
  · intro e h a
    by_cases hl : literal e
    · simp only [repr, dite_eq_left hl]
      obtain ⟨t, rfl⟩ := hl
      exact qCodeTree_lit_eval [] t a
    · simpa only [repr, dite_eq_right hl] using (show small e from h.resolve_left hl).choose_spec.2 a
  · intro e h
    by_cases hl : literal e
    · simp only [repr, dite_eq_left hl]
      exact ⟨qCodeTree_leaves [] e hk (Nat.zero_le _),
        qCodeTree_cell_width [] e hk (Nat.zero_le _) true⟩
    · simp only [repr, dite_eq_right hl]
      let cert : small e := h.resolve_left hl
      have depth := cert.choose_spec.1
      exact ⟨cert.choose.leaves_le_pow_depth.trans (Nat.pow_le_pow_right (by decide) depth),
        fun B hm => (cert.choose.cell_card_le_depth true B hm).trans depth⟩
  · exact fun e hp hs => Or.inr (bounded e hp hs)

/-- At arbitrarily large dyadic bit widths, a polynomial-length integer
refutation must both produce and select an equation for which every exact
parity decision tree exceeds the stated growing depth. -/
theorem BPHPActiveDepth (p : Polynomial ℕ) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧ ∀ π : List (QLine (Fin (2 ^ (2 ^ t) + 1) × Fin (2 ^ t))),
      IsResLinQSynRefutation (BPHP (2 ^ (2 ^ t) + 1) (2 ^ t)) π →
      π.length ≤ p.eval (2 ^ (2 ^ t)) →
      ∃ e, QProduced π e ∧ QSelected π e ∧
        ∀ tree : ParityTree (Fin (2 ^ (2 ^ t) + 1) × Fin (2 ^ t)),
          (∀ a, tree.eval a = true ↔ QEq.Holds a e) → 2 ^ t / (2 * (t + 5)) < tree.depth := by
  classical
  obtain ⟨t, ht, hl, hk, hkl, hll, short⟩ := growing_simulation_barrier p N
  refine ⟨t, ht, fun π ref len => ?_⟩
  by_contra fail
  have bound (e) (hp : QProduced π e) (hs : QSelected π e) :
      ∃ tree : ParityTree (Fin (2 ^ (2 ^ t) + 1) × Fin (2 ^ t)),
        tree.depth ≤ 2 ^ t / (2 * (t + 5)) ∧ ∀ a, tree.eval a = true ↔ QEq.Holds a e := by
    by_contra none
    apply fail
    refine ⟨e, hp, hs, fun tree exactTree => ?_⟩
    exact lt_of_not_ge (fun low => none ⟨tree, low, exactTree⟩)
  obtain ⟨ρ, dρ, cost⟩ := active_depth_equation_simulation _ hk
    (collision_formula_nonempty _) ref bound
  have lb := bphp_linK_rate hl hk hkl hll dρ
  have ub : (ρ.length : ℝ) ≤ (equationStepCost (2 ^ t / (2 * (t + 5))) : ℝ) * π.length + 1 := by
    exact_mod_cast cost
  exact (lb.trans ub).not_gt (short π.length len)

/-- Transcript-based strategies also require more than the growing query budget
for some equation serving as both the result and a premise of resolution. -/
theorem bphp_active_adaptive_queries (p : Polynomial ℕ) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧ ∀ π : List (QLine (Fin (2 ^ (2 ^ t) + 1) × Fin (2 ^ t))),
      IsResLinQSynRefutation (BPHP (2 ^ (2 ^ t) + 1) (2 ^ t)) π →
      π.length ≤ p.eval (2 ^ (2 ^ t)) →
      ∃ e, QProduced π e ∧ QSelected π e ∧ ¬ AdaptiveEquation (2 ^ t / (2 * (t + 5))) e := by
  obtain ⟨t, ht, hard⟩ := BPHPActiveDepth p N
  refine ⟨t, ht, fun π ref len => ?_⟩
  obtain ⟨e, hp, hs, deep⟩ := hard π ref len
  refine ⟨e, hp, hs, ?_⟩
  rintro ⟨ask, out, computes⟩
  have depth := deep (adaptiveTree ask out _ []) (fun a => by simpa only [adaptiveTree_eval] using computes a)
  simpa using depth

end PEqualNP.Search
