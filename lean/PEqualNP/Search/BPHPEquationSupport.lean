import PEqualNP.Search.BPHPParityBarrier
import PEqualNP.Search.QEquationSimulation
import PEqualNP.Search.Helpers.BPHPLinKRate

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- A short proof contains one equation whose Boolean truth is undetermined
by every list of at most `k` parity queries, even if the list depends on the equation. -/
theorem bphp_equation_query_rate {l k : ℕ} (hl : 2 ≤ l) (hk : 1 ≤ k)
    (hkl : 64 * k ≤ 2 ^ l) (hll : 32 * l ≤ 2 ^ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (short : (equationStepCost k : ℝ) * π.length + 1 <
      Real.exp ((2 : ℝ)^l / (64 * (k : ℝ) * (32 * (l : ℝ))^k))) :
    ∃ L ∈ π, ∃ e ∈ L, ∀ Q : List (Finset (Fin (2 ^ l + 1) × Fin l)),
      Q.length ≤ k → ¬ Helpers.QDetermined Q e := by
  classical
  by_contra! queries
  obtain ⟨ρ, hρ, size⟩ :=
    parity_query_equation_simulation k hk (collision_formula_nonempty l) hπ queries
  have lb := Helpers.bphp_linK_rate hl hk hkl hll hρ
  have ub : (ρ.length : ℝ) ≤ (equationStepCost k : ℝ) * π.length + 1 := by exact_mod_cast size
  exact (lb.trans ub).not_gt short

/-- In a refutation below the finite-width parity lower bound, an individual
integer equation has more than `k` nonzero variable coefficients. -/
theorem bphp_equation_support_rate {l k : ℕ} (hl : 2 ≤ l) (hk : 1 ≤ k)
    (hkl : 64 * k ≤ 2 ^ l) (hll : 32 * l ≤ 2 ^ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (short : (equationStepCost k : ℝ) * π.length + 1 <
      Real.exp ((2 : ℝ)^l / (64 * (k : ℝ) * (32 * (l : ℝ))^k))) :
    ∃ L ∈ π, ∃ e ∈ L, k < (Finset.univ.filter (fun v => e.1 v ≠ 0)).card := by
  classical
  obtain ⟨L, hL, e, he, hard⟩ := bphp_equation_query_rate hl hk hkl hll hπ short
  refine ⟨L, hL, e, he, lt_of_not_ge (fun small => ?_)⟩
  exact hard (Helpers.supportQueries e) (by simpa only [Helpers.supportQueries_length] using small)
    (Helpers.supportQueries_determine e)

/-- Proofs using only equations determined by a fixed number of parity queries
exceed every polynomial in the number of holes on some bit-pigeonhole instance. -/
theorem bphp_parity_query_lower_bound (k : ℕ) (hk : 1 ≤ k) (p : Polynomial ℕ) :
    ∃ l : ℕ, ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π →
      (∀ L ∈ π, ∀ e ∈ L, ∃ Q : List (Finset (Fin (2 ^ l + 1) × Fin l)),
        Q.length ≤ k ∧ Helpers.QDetermined Q e) →
      p.eval (2 ^ l) < π.length := by
  obtain ⟨l, hard⟩ := Helpers.bphp_polynomial_simulation_bound k hk (equationStepCost k) p
  refine ⟨l, fun π ref queries => ?_⟩
  obtain ⟨ρ, hρ, size⟩ :=
    parity_query_equation_simulation k hk (collision_formula_nonempty l) ref queries
  exact hard hρ size

/-- For each fixed equation support bound, sparse syntactic refutations exceed
every polynomial in the number of holes on some bit-pigeonhole instance. -/
theorem BPHPEquationSupport :
    ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ l : ℕ,
      ∀ π : List (PEqualNP.Search.QLine (Fin (2 ^ l + 1) × Fin l)),
        PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
        (∀ L ∈ π, ∀ e ∈ L, (Finset.univ.filter (fun v => e.1 v ≠ 0)).card ≤ k) →
        p.eval (2 ^ l) < π.length := by
  intro k hk p
  obtain ⟨l, hard⟩ := bphp_parity_query_lower_bound k hk p
  refine ⟨l, fun π ref small => hard π ref fun L hL e he => ?_⟩
  exact ⟨Helpers.supportQueries e, by simpa only [Helpers.supportQueries_length] using small L hL e he,
    Helpers.supportQueries_determine e⟩

end PEqualNP.Search
