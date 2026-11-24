import PEqualNP.Search.Helpers.QParity

/-!
# Removing the common binary factor of an integer equation

The order is the first k for which the coefficients and the right-hand side
are not all divisible by 2^(k+1). The zero equation is assigned order zero.
Dividing by 2^k gives an equation with an odd entry whenever the input is
nonzero. In particular every false constant remains false after projection.
-/

namespace PEqualNP.Search.Helpers

variable {V : Type}

private def commonPow (e : QEq V) (k : ℕ) : Prop :=
  (∀ v, (2 : ℤ)^k ∣ e.1 v) ∧ (2 : ℤ)^k ∣ e.2

private theorem some_power_fails (e : QEq V) (he : e ≠ 0) : ∃ k, ¬ commonPow e (k+1) := by
  classical
  have fails (z : ℤ) (hz : z ≠ 0) : ¬ (2 : ℤ)^(z.natAbs+1) ∣ z := by
    intro h
    have hh := Int.natAbs_le_of_dvd_ne_zero h hz
    rw [Int.natAbs_pow] at hh
    change 2 ^ (z.natAbs + 1) ≤ z.natAbs at hh
    exact (Nat.not_lt_of_ge hh) (lt_trans (Nat.lt_succ_self _) (Nat.lt_two_pow_self))
  by_cases h : e.2 = 0
  · have ex : ∃ v, e.1 v ≠ 0 := by
      by_contra! all
      exact he (Prod.ext (funext all) h)
    obtain ⟨v, hv⟩ := ex
    exact ⟨_, fun hc => fails _ hv (hc.1 v)⟩
  · exact ⟨_, fun hc => fails _ h hc.2⟩

/-- Largest common power-of-two exponent of all entries, with zero assigned order zero. -/
noncomputable def qOrder (e : QEq V) : ℕ := by
  classical
  exact if h : e = 0 then 0 else Nat.find (some_power_fails e h)

private theorem qOrder_bounds {e : QEq V} (he : e ≠ 0) :
    commonPow e (qOrder e) ∧ ¬ commonPow e (qOrder e + 1) := by
  classical
  simp only [qOrder, dite_eq_right he]
  let h := some_power_fails e he
  have hf := Nat.find_spec h
  refine ⟨?_, hf⟩
  by_cases hz : Nat.find h = 0
  · change commonPow e (Nat.find h)
    rw [hz]
    simp [commonPow]
  · have before := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find h)] using before

private theorem qOrder_dvd (e : QEq V) : commonPow e (qOrder e) := by
  by_cases h : e = 0
  · subst e
    simp [commonPow, qOrder]
  · exact (qOrder_bounds h).1

/-- Divide each coefficient and the right-hand side by the largest common binary factor. -/
noncomputable def qPrimitive (e : QEq V) : QEq V :=
  (fun v => e.1 v / (2 : ℤ)^qOrder e, e.2 / (2 : ℤ)^qOrder e)

theorem qPrimitive_coeff (e : QEq V) (v : V) :
    e.1 v = (2 : ℤ)^qOrder e * (qPrimitive e).1 v :=
  (Int.mul_ediv_cancel' ((qOrder_dvd e).1 v)).symm

theorem qPrimitive_rhs (e : QEq V) : e.2 = (2 : ℤ)^qOrder e * (qPrimitive e).2 :=
  (Int.mul_ediv_cancel' (qOrder_dvd e).2).symm

@[simp] theorem qOrder_zero : qOrder (0 : QEq V) = 0 := by classical simp [qOrder]

@[simp] theorem qPrimitive_zero : qPrimitive (0 : QEq V) = 0 := by
  apply Prod.ext
  · funext v
    simp [qPrimitive]
  · simp [qPrimitive]

/-- A nonzero primitive equation has an odd coefficient or an odd right-hand side. -/
theorem qPrimitive_odd {e : QEq V} (he : e ≠ 0) :
    (∃ v, Odd ((qPrimitive e).1 v)) ∨ Odd ((qPrimitive e).2) := by
  by_contra! hn
  have next (z y : ℤ) (hy : z = (2 : ℤ)^qOrder e * y) (hi : Even y) :
      (2 : ℤ)^(qOrder e + 1) ∣ z := by
    obtain ⟨s, hs⟩ := hi.two_dvd
    exact ⟨s, by rw [hy, hs, pow_succ, mul_assoc]⟩
  exact (qOrder_bounds he).2 ⟨fun v => next _ _ (qPrimitive_coeff e v) (hn.1 v),
    next _ _ (qPrimitive_rhs e) hn.2⟩

@[simp] theorem qPrimitive_lit [DecidableEq V] (s : V × Bool) :
    qPrimitive (litQEq s) = litQEq s := by
  have h : qOrder (litQEq s) = 0 := by
    have hdiv := (qOrder_dvd (litQEq s)).1 s.1
    rw [show (litQEq s).1 s.1 = 1 by simp [litQEq]] at hdiv
    by_contra hne
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hk, pow_succ] at hdiv
    have ht : (2 : ℤ) ∣ 1 := dvd_trans (dvd_mul_left _ _) hdiv
    norm_num at ht
  simp [qPrimitive, h]

theorem qParity_primitive_false [Fintype V] (a : V → Bool) (e : QEq V) (hz : e.1 = 0)
    (hn : e.2 ≠ 0) : ¬ PEqualNP.ProofComplexity.LinEqSat a (qParity (qPrimitive e)) := by
  have hpc : (qPrimitive e).1 = 0 := by funext v; simp [qPrimitive, hz]
  apply qParity_false a (qPrimitive e) hpc
  obtain hs | hs := qPrimitive_odd (show e ≠ 0 from fun h => hn (congrArg Prod.snd h))
  · obtain ⟨v, h⟩ := hs
    simp [hpc] at h
  · exact hs

end PEqualNP.Search.Helpers
