import PEqualNP.Search.BPHPBlockUpper
import PEqualNP.Search.Helpers.BlockParityRate
import PEqualNP.ProofComplexity.L036

/-! A single family of integer refutations beats every polynomial comparison
with parity refutations of the same formulas, measuring the integer proof in
encoded bits and the parity proof in number of lines. -/

namespace PEqualNP.Search

private theorem polynomial_le_exponent (p : Polynomial ℕ) {S E : ℕ}
    (bounded : S ≤ 2^E) (pos : 0 < E) :
    p.eval S ≤ 2^(((∑ i ∈ Finset.range (p.natDegree+1), p.coeff i)+p.natDegree)*E) := by
  let A := ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i
  have coef : A ≤ 2^(A*E) := (Nat.lt_two_pow_self (n := A)).le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ pos))
  calc
    _ ≤ A * (2^E)^p.natDegree := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left bounded i).trans
        (Nat.pow_le_pow_right Nat.one_le_two_pow (by simp at hi; omega))
    _ ≤ 2^(A*E) * (2^E)^p.natDegree := Nat.mul_le_mul_right _ coef
    _ = _ := by
      change _ = 2^((A+p.natDegree)*E)
      rw [← pow_mul, ← pow_add]
      congr 1
      ring

/-- The same chosen family of integer refutations witnesses the separation
simultaneously for all polynomials. The lower bound on the parity side applies
at every sufficiently large width and to every parity refutation. -/
theorem BPHPParitySeparation :
    ∃ π : (l : ℕ) → List (PEqualNP.Search.QLine (Fin (2^l+1) × Fin l)),
      (∀ l : ℕ, PEqualNP.Search.IsResLinQSynRefutation
        (PEqualNP.ProofComplexity.BPHP (2^l+1) l) (π l) ∧
        PEqualNP.Search.resLinQSize (π l) ≤ 2^(512*(l+2)*2^((l+1)/2))) ∧
      ∀ p : Polynomial ℕ, ∃ L : ℕ, ∀ l : ℕ, L ≤ l →
        ∀ ρ : List (PEqualNP.ProofComplexity.LinClause (Fin (2^l+1) × Fin l)),
          PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2^l+1) l) ρ →
          p.eval (PEqualNP.Search.resLinQSize (π l)) < ρ.length := by
  choose π hπ using BPHPBlockUpper
  refine ⟨π,hπ,?_⟩
  intro p
  let k := (∑ i ∈ Finset.range (p.natDegree+1), p.coeff i)+p.natDegree
  obtain ⟨L, rate⟩ := Helpers.block_parity_rate k
  refine ⟨max L 32,?_⟩
  intro l hl ρ ref
  have atL : L ≤ l := (le_max_left ..).trans hl
  have at32 : 32 ≤ l := (le_max_right ..).trans hl
  have upper := polynomial_le_exponent p (hπ l).2 (by positivity)
  have upperReal : ((p.eval (resLinQSize (π l)) : ℕ) : ℝ) ≤
      (2 : ℝ)^(k*(512*(l+2)*2^((l+1)/2))) := by exact_mod_cast upper
  have lower := PEqualNP.ProofComplexity.L036 l ρ at32 ref
  exact_mod_cast (upperReal.trans (rate l atL)).trans_lt lower

end PEqualNP.Search
