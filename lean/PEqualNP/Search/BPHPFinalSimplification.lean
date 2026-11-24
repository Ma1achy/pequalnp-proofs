import PEqualNP.Search.Helpers.QDeferSimp
import PEqualNP.Defs.ProofComplexityBit
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Intermediate removal of false constant equations can be deferred at polynomial cost.
The equivalence below has the quantifiers and size measure of L-alg-006. -/

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- A derivation of a disjunction of false constant equations becomes a refutation
by one final application of the simplification rule. -/
theorem refute_at_end {V : Type} [Fintype V] [DecidableEq V] {F : Set (ProofComplexity.Clause V)}
    {ρ : List (QLine V)} {G : QLine V} (hρ : NoSimpDerivation F ρ) (hG : G ∈ ρ)
    (bad : ∀ e ∈ G, e.1 = 0 ∧ e.2 ≠ 0) : IsResLinQSynRefutation F ([] :: ρ) := by
  have empty : G.filter (fun e => decide (¬ (e.1 = 0 ∧ e.2 ≠ 0))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [bad e he]
  exact ⟨empty ▸ hρ.toSyn.simp hG, List.mem_cons_self⟩

/-- A size-S syntactic refutation has a derivation of a false disjunction that
uses no simplification and costs at most 6S² before the last step. -/
theorem defer_simp_quadratic {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (ProofComplexity.Clause V)} {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) :
    ∃ ρ, NoSimpDerivation F ρ ∧ falseConstants π ∈ ρ ∧ resLinQSize ρ ≤ 6 * (resLinQSize π)^2 := by
  obtain ⟨ρ, h, hG, hlen, hmax⟩ := defer_simp_refutation hπ
  have len := hlen.trans (Nat.mul_le_mul_left 2 (qlength_le_size π))
  have wt := qWeight_falseConstants_le π
  have total := qSize_le_length_mul (ρ := ρ) (M := 3 * resLinQSize π) (fun L hL => by
    have := hmax L hL
    omega)
  refine ⟨ρ, h, hG, total.trans ?_⟩
  calc
    ρ.length * (3 * resLinQSize π) ≤ (2 * resLinQSize π) * (3 * resLinQSize π) :=
      Nat.mul_le_mul_right _ len
    _ = _ := by ring

/-- The unrestricted conjecture is equivalent to ruling out polynomial-size
simplification-free derivations of disjunctions of false constants. -/
theorem BPHPFinalSimplification :
    (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π → p.eval (2 ^ l) < resLinQSize π) ↔
    (∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ (ρ : List (QLine (Fin (2 ^ l + 1) × Fin l))), ∀ G ∈ ρ,
      NoSimpDerivation (BPHP (2 ^ l + 1) l) ρ →
      (∀ e ∈ G, e.1 = 0 ∧ e.2 ≠ 0) → p.eval (2 ^ l) < resLinQSize ρ) := by
  constructor
  · intro h p
    obtain ⟨l, hl⟩ := h (p+1)
    refine ⟨l, ?_⟩
    intro ρ G hm hd hb
    have ht := hl _ (refute_at_end hd hm hb)
    simp only [Polynomial.eval_add, Polynomial.eval_one, qSize_cons, qCost, qWeight_nil] at ht
    omega
  · intro h p
    obtain ⟨l, hl⟩ := h (6 * p ^ 2)
    refine ⟨l, ?_⟩
    intro π hπ
    obtain ⟨ρ, hd, hm, hb⟩ := defer_simp_quadratic hπ
    have ht := hl _ _ hm hd (fun e he => (mem_falseConstants.mp he).2)
    by_contra! short
    have le := Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left short 2)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat] at ht
    omega

end PEqualNP.Search
