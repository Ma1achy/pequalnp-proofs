import PEqualNP.ProofComplexity.L061
import PEqualNP.Library.Machines.Run

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Finite-parameter form of the degree-to-size estimate for the binary
pigeonhole formula. The polynomial-calculus degree used here is `2^(l-2)`. -/
theorem bphp_linK_rate {l k : ℕ} (hl : 2 ≤ l) (hk : 1 ≤ k)
    (hkl : 64 * k ≤ 2 ^ l) (hll : 32 * l ≤ 2 ^ l)
    {ρ : List (PEqualNP.ProofComplexity.LinKLine (Fin (2 ^ l + 1) × Fin l))}
    (hρ : IsLinKRefutation k (BPHP (2 ^ l + 1) l) ρ) :
    Real.exp ((2 : ℝ)^l / (64 * (k : ℝ) * (32 * (l : ℝ))^k)) ≤ (ρ.length : ℝ) := by
  let D := 2 ^ (l-2)
  have hd : 4 * D = 2 ^ l := by
    have he : l - 2 + 2 = l := by omega
    calc
      4 * 2 ^ (l - 2) = 2 ^ (l - 2 + 2) := by rw [pow_add]; ring
      _ = 2 ^ l := congrArg (2 ^ ·) he
  have hnr : ¬ PCRefutable (cnfSystem (BPHP (2^l+1) l)) D :=
    LinKBit.bphp_not_refutable _ l D hl (by omega)
  have hr := LinKWire.general LinKSim.simulation_refutation _ _ ρ k (2*l) D
    LinKBit.bphp_width hk (by omega) (by omega) hnr hρ
  simp only [Fintype.card_prod, Fintype.card_fin] at hr
  push_cast at hr
  have hd' : 4 * (D : ℝ) = (2 : ℝ)^l := by exact_mod_cast hd
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl' : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hn : (1 : ℝ) ≤ (2 : ℝ)^l := one_le_pow₀ (by norm_num)
  have h1 : (D : ℝ) / (16 * k) = (2 : ℝ)^l / (64 * k) := by
    rw [← hd']; ring
  have h2 : 1 / (32 * (l : ℝ)) ≤ D / (4 * (((2 : ℝ)^l + 1) * l)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hl'.le]
  refine (Real.exp_le_exp.mpr ?_).trans hr
  rw [h1]
  calc
    (2 : ℝ)^l / (64 * k * (32 * (l : ℝ))^k) =
        2^l / (64 * k) * (1 / (32 * (l : ℝ)))^k := by rw [one_div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 k) (by positivity)

/-- Any linear-cost simulation into bounded-width parity resolution transfers
the superpolynomial lower bound to the source size, measured in holes. -/
theorem bphp_polynomial_simulation_bound (k : ℕ) (hk : 1 ≤ k) (C : ℕ)
    (p : Polynomial ℕ) : ∃ l : ℕ, ∀ {s : ℕ} {ρ : List (LinKLine (Fin (2 ^ l + 1) × Fin l))},
      IsLinKRefutation k (BPHP (2 ^ l + 1) l) ρ →
      ρ.length ≤ C * s + 1 → p.eval (2 ^ l) < s := by
  let q := Polynomial.C C * p.comp (Polynomial.X + 1) + 1
  obtain ⟨l, hard⟩ := L061 k hk q
  refine ⟨l, fun {s} {ρ} hρ size => ?_⟩
  have lb := hard ρ hρ
  simp [q, Polynomial.eval_comp] at lb
  have hcard : 2 ^ l ≤ (2 ^ l + 1) * l + 1 := by
    cases l with
    | zero => decide
    | succ m => rw [Nat.mul_succ]; omega
  by_contra! small
  have h := Nat.mul_le_mul_left C (small.trans (PEqualNP.Library.Machines.eval_mono p hcard))
  omega

end PEqualNP.Search.Helpers
