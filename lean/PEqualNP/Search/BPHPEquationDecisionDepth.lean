import PEqualNP.Search.QEquationSimulation
import PEqualNP.Search.Helpers.AdaptiveQueryTree
import PEqualNP.Search.Helpers.BPHPLinKRate
import PEqualNP.Search.BPHPParityBarrier

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- A bounded number of parity queries computes the equation's truth on Boolean
assignments. The next query may depend on the whole transcript so far. -/
def AdaptiveEquation {V : Type} [Fintype V] (k : ℕ) (e : QEq V) : Prop :=
  ∃ (ask : List Bool → Finset V) (out : List Bool → Bool), ∀ a : V → Bool,
    out ((List.range k).foldl (fun h _ =>
      h ++ [decide (Odd (((ask h).filter (fun v => a v = true)).card))]) []) = true ↔ QEq.Holds a e

private theorem canonical_dead {V : Type} [Fintype V] [DecidableEq V] (e : QEq V)
    (z : e.1 = 0) (nz : e.2 ≠ 0) (a : V → Bool) : (qCodeTree [] e).eval a ≠ true := by
  intro h
  have hs : LinKLineSat a (qCode [] e) := (treeDNF_sat _ _).mpr h
  rw [qCode_dead [] e z nz] at hs
  simp [LinKLineSat] at hs

/-- A representation is needed only for equations actually used in the proof.
Literal and false-constant cases receive their canonical codes at every occurrence. -/
theorem equation_depth_simulation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (bounded : ∀ L ∈ π, ∀ e ∈ L, ∃ t : ParityTree V, t.depth ≤ k ∧
      ∀ a, t.eval a = true ↔ QEq.Holds a e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let canonical (e : QEq V) := (∃ l, e = litQEq l) ∨ (e.1 = 0 ∧ e.2 ≠ 0)
  let within (e : QEq V) (t : ParityTree V) := t.depth ≤ k ∧ ∀ a, t.eval a = true ↔ QEq.Holds a e
  let trees (e : QEq V) : ParityTree V :=
    if canonical e then qCodeTree [] e else
    if h : ∃ t, within e t then h.choose
    else .leaf false
  apply equation_tree_compilation k hk seed ref trees
  · intro t
    have h : canonical (litQEq t) := Or.inl ⟨t, rfl⟩
    simpa only [qCode, trees, ite_eq_left h] using qCode_lit [] t
  · intro e z nz a
    have h : canonical e := Or.inr ⟨z, nz⟩
    simpa only [trees, ite_eq_left h] using canonical_dead e z nz a
  · intro L hL e he
    by_cases can : canonical e
    · simp only [trees, ite_eq_left can]
      refine ⟨?_, qCodeTree_leaves [] e hk (Nat.zero_le _),
        qCodeTree_cell_width [] e hk (Nat.zero_le _) true⟩
      rcases can with ⟨l, rfl⟩ | ⟨z, nz⟩
      · exact qCodeTree_lit_eval [] l
      · intro a
        exact iff_of_false (canonical_dead e z nz a) (fun h => nz (by simpa [QEq.Holds, z] using h.symm))
    · have cert : ∃ t, within e t := bounded L hL e he
      simp only [trees, ite_eq_right can, dite_eq_left cert]
      have depth := cert.choose_spec.1
      exact ⟨cert.choose_spec.2, cert.choose.leaves_le_pow_depth.trans
        (Nat.pow_le_pow_right (by decide) depth),
        fun B hB => (cert.choose.cell_card_le_depth true B hB).trans depth⟩

/-- Unroll each transcript-based strategy into a bounded-depth parity tree. -/
theorem adaptive_equation_simulation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (bounded : ∀ L ∈ π, ∀ e ∈ L, AdaptiveEquation k e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  apply equation_depth_simulation k hk seed ref
  intro L hm e he
  obtain ⟨ask, out, cert⟩ := bounded L hm e he
  exact ⟨adaptiveTree ask out k [], by simp, fun a => by simpa only [adaptiveTree_eval] using cert a⟩

/-- The tree formulation allows different stopping depths on different paths. -/
theorem bphp_tree_equation_depth_lower_bound (k : ℕ) (hk : 1 ≤ k) (p : Polynomial ℕ) :
    ∃ l : ℕ, ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π →
      (∀ L ∈ π, ∀ e ∈ L, ∃ t : ParityTree (Fin (2 ^ l + 1) × Fin l),
        t.depth ≤ k ∧ ∀ a, t.eval a = true ↔ QEq.Holds a e) → p.eval (2 ^ l) < π.length := by
  obtain ⟨l, hard⟩ := bphp_polynomial_simulation_bound k hk (equationStepCost k) p
  refine ⟨l, fun π ref bounded => ?_⟩
  obtain ⟨ρ, hρ, size⟩ := equation_depth_simulation k hk (collision_formula_nonempty l) ref bounded
  exact hard hρ size

/-- For fixed adaptive equation depth, bit-pigeonhole refutations exceed any
polynomial in the number of holes on some instance. -/
theorem BPHPEquationDecisionDepth :
  ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ l : ℕ,
    ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ l + 1) × Fin l)),
      PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
      (∀ L ∈ π, ∀ e ∈ L, ∃ (ask : List Bool → Finset (Fin (2 ^ l + 1) × Fin l))
          (out : List Bool → Bool), ∀ a : (Fin (2 ^ l + 1) × Fin l) → Bool,
          out ((List.range k).foldl (fun h _ =>
            h ++ [decide (Odd (((ask h).filter (fun v => a v = true)).card))]) []) = true ↔
          PEqualNP.Search.QEq.Holds a e) → p.eval (2 ^ l) < π.length := by
  intro k hk p
  obtain ⟨l, hard⟩ := bphp_polynomial_simulation_bound k hk (equationStepCost k) p
  refine ⟨l, fun π ref bounded => ?_⟩
  obtain ⟨ρ, hρ, size⟩ := adaptive_equation_simulation k hk (collision_formula_nonempty l) ref bounded
  exact hard hρ size

end PEqualNP.Search
