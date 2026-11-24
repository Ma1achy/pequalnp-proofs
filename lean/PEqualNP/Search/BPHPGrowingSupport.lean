import PEqualNP.Search.BPHPEquationSupport
import PEqualNP.ProofComplexity.Helpers.ExpBeatsPoly
import PEqualNP.Library.Helpers.OutputLength

/-! A growing support bound. At dyadic bit width l = 2^t, integer equations on
at most floor(l/(2(t+5))) variables cannot give polynomial-length bit-PHP proofs. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- For l=2^t=4m, the parity lower-bound exponent is at least 2^m over the
whole parameter range 64k ≤ 2^m and (t+5)k ≤ 2m. -/
theorem dyadic_linK_exponent {t l k m : ℕ} (hl : l = 2 ^ t) (hm : l = 4 * m)
    (hk : 0 < k) (h64 : 64 * k ≤ 2 ^ m) (hlog : (t + 5) * k ≤ 2 * m) :
    (2 : ℝ)^m ≤ 2^l / (64 * (k : ℝ) * (32 * (l : ℝ))^k) := by
  have h32 : 32 * l = 2 ^ (t + 5) := by rw [hl, pow_add]; ring
  have hb : (32 * l) ^ k ≤ 2 ^ (2 * m) := by
    rw [h32, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hlog
  have hnat : 2 ^ m * (64 * k * (32 * l)^k) ≤ 2 ^ l := by
    calc
      _ ≤ 2 ^ m * (2 ^ m * 2 ^ (2*m)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h64 hb)
      _ = 2^l := by rw [← pow_add, ← pow_add, hm]; congr 1; omega
  have hlpos : 0 < l := hl ▸ Nat.two_pow_pos t
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast hnat

private theorem step_cost_le_quadratic {l k : ℕ} (hk : k ≤ l) :
    equationStepCost k ≤ 8 * (2 ^ l)^2 := by
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hk
  have hsucc : k + 1 ≤ 2 ^ l := Nat.lt_of_le_of_lt hk Nat.lt_two_pow_self
  have hm : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  calc
    _ ≤ (8 * 2 ^ l) * 2 ^ l := Nat.mul_le_mul (by omega) hpow
    _ = _ := by ring

private theorem denominator_fits {u : ℕ} (h : 6 ≤ u) : 2 * (u + 7) ≤ 4 * 2 ^ u := by
  have ht : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
  omega

private theorem nat_budget_below_exp {s j m : ℕ} (hs : s ≤ 2 ^ j) (hj : j < 2 ^ m) :
    (s : ℝ) < Real.exp ((2 : ℝ) ^ m) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (2 : ℝ) ^ j := by exact_mod_cast hs
    _ ≤ (Real.exp 1) ^ j := pow_le_pow_left₀ (by norm_num) h2 _
    _ = Real.exp (j : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    _ < _ := Real.exp_lt_exp.mpr (by exact_mod_cast hj)

set_option maxHeartbeats 600000 in
/-- For an arbitrarily large dyadic bit width, even a line-by-line simulation
at the growing width k=floor(l/(2(t+5))) stays below the parity lower bound
when the original proof length is at most the prescribed polynomial in holes. -/
theorem growing_simulation_barrier (p : Polynomial ℕ) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧
      let l := 2 ^ t
      let k := l / (2 * (t + 5))
      2 ≤ l ∧ 1 ≤ k ∧ 64 * k ≤ 2 ^ l ∧ 32 * l ≤ 2 ^ l ∧
        ∀ s : ℕ, s ≤ p.eval (2 ^ l) →
          (equationStepCost k : ℝ) * s + 1 <
            Real.exp ((2 : ℝ)^l / (64 * (k : ℝ) * (32 * (l : ℝ))^k)) := by
  let q : Polynomial ℕ := 8 * Polynomial.X^2 * p + 1
  obtain ⟨a, d, hp⟩ := PEqualNP.Library.Helpers.poly_le_monomial q
  let u := N + a + 4*d + 16
  let t := u + 2
  let m := 2 ^ u
  let l := 2 ^ t
  let k := l / (2 * (t + 5))
  have hu : 16 ≤ u := by dsimp [u]; omega
  have hm : l = 4*m := by simp [l, t, m, pow_add, mul_comm]
  have hmp : u < m := Nat.lt_two_pow_self
  have hm16 : 16 ≤ m := by omega
  have hfour := PEqualNP.ProofComplexity.Helpers.pow_four_le_two_pow m hm16
  have big : 256 * m ≤ 2 ^ m := by
    apply le_trans _ hfour
    have h' : 16*m ≤ m*m := Nat.mul_le_mul_right m hm16
    have h'' : 16*(m*m) ≤ (m*m)*m := Nat.mul_le_mul_right (m*m) hm16 |>.trans_eq (by ring)
    have h''' : m*m*m ≤ m^4 := by
      calc m*m*m ≤ (m*m*m)*m := Nat.le_mul_of_pos_right _ (by omega)
           _ = m^4 := by ring
    nlinarith
  have fit : 2 * (t+5) ≤ l := by
    rw [hm]; exact denominator_fits (u := u) (by omega)
  have hk : 1 ≤ k := (Nat.le_div_iff_mul_le (by dsimp [t]; omega)).mpr (by simpa using fit)
  have hkl : k ≤ l := Nat.div_le_self _ _
  have hk64 : 64*k ≤ 2^m := by omega
  have kh : k*(2*(t+5)) ≤ l := Nat.div_mul_le_self _ _
  have hklog : (t+5)*k ≤ 2*m := by nlinarith only [kh, hm]
  have hml : 2^m ≤ 2^l := Nat.pow_le_pow_right (by decide) (by omega)
  have ha : a + l*d < 2^m := by
    have hmd : a + 4*d < m := by dsimp [u] at hmp; omega
    have h1 : (a + 4*d)*m < m*m := Nat.mul_lt_mul_of_pos_right hmd (by omega)
    have ha' : a ≤ a*m := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : m*m ≤ m^4 := by
      calc m*m = m^2 := by ring
           _ ≤ m^4 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith only [hm, ha', h1, h2, hfour]
  have hq : q.eval (2^l) ≤ 2 ^ (a + l*d) := by
    calc
      _ ≤ a * (2^l)^d := hp _ Nat.one_le_two_pow
      _ ≤ 2 ^ a * (2 ^ l)^d := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = _ := by rw [← pow_mul, ← pow_add]
  have exp_target : ((q.eval (2^l) : ℕ) : ℝ) < Real.exp ((2 : ℝ)^m) :=
    nat_budget_below_exp hq ha
  refine ⟨t, by dsimp [t, u]; omega, ?_⟩
  change 2 ≤ l ∧ 1 ≤ k ∧ 64*k ≤ 2^l ∧ 32*l ≤ 2^l ∧ _
  refine ⟨by omega, hk, by omega, by omega, ?_⟩
  intro s short
  have sim : equationStepCost k * s + 1 ≤ q.eval (2^l) := by
    simpa [q] using Nat.add_le_add_right (Nat.mul_le_mul (step_cost_le_quadratic hkl) short) 1
  calc
    _ ≤ ((q.eval (2^l) : ℕ) : ℝ) := by exact_mod_cast sim
    _ < _ := exp_target
    _ ≤ _ := Real.exp_le_exp.mpr (dyadic_linK_exponent (t := t) rfl hm hk hk64 hklog)

/-- Every polynomial-length proof at some arbitrarily large dyadic width uses
an equation with more than floor(l/(2(t+5))) nonzero variable coefficients. -/
theorem BPHPGrowingSupport (p : Polynomial ℕ) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧ ∀ π : List (QLine (Fin (2 ^ (2 ^ t) + 1) × Fin (2 ^ t))),
      IsResLinQSynRefutation (BPHP (2 ^ (2 ^ t) + 1) (2 ^ t)) π →
      π.length ≤ p.eval (2 ^ (2 ^ t)) →
      ∃ L ∈ π, ∃ e ∈ L, 2 ^ t / (2 * (t + 5)) <
        (Finset.univ.filter (fun v => e.1 v ≠ 0)).card := by
  obtain ⟨t, hN, hl, hk, hkl, hll, short⟩ := growing_simulation_barrier p N
  refine ⟨t, hN, fun π hπ hs => ?_⟩
  exact bphp_equation_support_rate hl hk hkl hll hπ (short π.length hs)

end PEqualNP.Search
