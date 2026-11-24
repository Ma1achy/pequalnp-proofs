import PEqualNP.Search.Helpers.QBadPrimes
import PEqualNP.Search.Helpers.QModSimulation
import PEqualNP.Defs.ProofComplexityBit
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A sufficient finite-field lower bound for the full integer conjecture.
The characteristic may depend on the proof, with a polynomial bound in its bit size. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private theorem length_le_encoded_size {V : Type} [Fintype V] (π : List (QLine V)) :
    π.length ≤ resLinQSize π := by
  induction π with
  | nil => rfl
  | cons L π ih =>
    change π.length + 1 ≤ (1 + (L.map QEq.size).sum) + resLinQSize π
    omega

/-- A short unrestricted integer proof yields a short syntactic proof over one
of the explicitly bounded prime fields. -/
theorem small_prime_simulation {V : Type} [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) :
    ∃ p : ℕ, p.Prime ∧ p ≤ (4 * (resLinQSize π + 1)) ^ 2 ∧
      ∃ ρ, IsModSynRefutation p F ρ ∧ ρ.length ≤ 2 * π.length := by
  obtain ⟨p, hp, hb, hsafe⟩ := exists_small_rhs_safe_prime π
  exact ⟨p, hp, hb, mod_refutation_of_safe p hπ (fun L hl e he _ => hsafe L hl e he)⟩

/-- A uniform bounded-characteristic finite-field lower bound at each polynomial
budget suffices to prove the posted, unrestricted L-alg-006. -/
theorem BPHPModularReduction
    (hard : ∀ q : Polynomial ℕ, ∃ l : ℕ, ∀ p : ℕ, p.Prime →
      p ≤ (4 * (q.eval (2 ^ l) + 1)) ^ 2 →
      ∀ ρ, IsModSynRefutation p (BPHP (2 ^ l + 1) l) ρ →
        2 * q.eval (2 ^ l) < ρ.length) :
    ∀ q : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π → q.eval (2 ^ l) < resLinQSize π := by
  intro q
  obtain ⟨l, hl⟩ := hard q
  refine ⟨l, ?_⟩
  intro π hπ
  by_contra! hs
  obtain ⟨p, hp, hb, ρ, hρ, hlen⟩ := small_prime_simulation hπ
  have hchar : p ≤ (4 * (q.eval (2 ^ l) + 1)) ^ 2 := by
    exact hb.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 (Nat.succ_le_succ hs)) 2)
  have hlow := hl p hp hchar ρ hρ
  have hupper := (length_le_encoded_size π).trans hs
  omega

end PEqualNP.Search
