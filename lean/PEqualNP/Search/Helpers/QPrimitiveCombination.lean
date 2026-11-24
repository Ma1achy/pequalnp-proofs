import PEqualNP.Search.Helpers.QPrimitive
import PEqualNP.Search.Helpers.QRow

/-! A resolution step can lose a Boolean assignment after primitive parity projection
only when its two heads have the same nontrivial parity equation. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

private theorem equal_parities {V : Type} [Fintype V] (e f : QEq V)
    (h : ∀ t, qCoord e t % 2 = qCoord f t % 2) : qParity e = qParity f := by
  apply Prod.ext
  · ext v
    simp [qParity, show e.1 v % 2 = f.1 v % 2 from h (some v)]
  · simp [qParity, show e.2 % 2 = f.2 % 2 from h none]

private theorem nonempty_of_odd_entry {V : Type} [Fintype V] (e : QEq V) (a : V → Bool)
    (holds : LinEqSat a (qParity e)) (odd : ∃ t, qCoord e t % 2 = 1) :
    (qParity e).1.Nonempty := by
  obtain ⟨_ | v, h⟩ := odd
  · have hb : (qParity e).2 = true := by simpa [qParity, qCoord] using h
    by_contra! hempty
    simp [LinEqSat, hempty, hb] at holds
  · exact ⟨v, by simpa [qParity, qCoord] using h⟩

private theorem scaled_obstruction {V : Type} [Fintype V] (E F G : QEq V) (a : V → Bool)
    (he : LinEqSat a (qParity E)) (hf : LinEqSat a (qParity F))
    (hg : ¬ LinEqSat a (qParity G)) (k : ℕ) (A B : ℤ)
    (hA : A ≠ 0 → ∃ t, qCoord E t % 2 = 1)
    (hB : B ≠ 0 → ∃ t, qCoord F t % 2 = 1)
    (h : ∀ t, A * qCoord E t + B * qCoord F t = 2 ^ k * qCoord G t) :
    qParity E = qParity F ∧ (qParity E).1.Nonempty := by
  induction k generalizing A B with
  | zero =>
    have eq : (A • E.1 + B • F.1, A * E.2 + B * F.2) = G := by
      apply Prod.ext
      · funext v
        simpa [qCoord, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h (some v)
      · simpa [qCoord] using h none
    apply False.elim
    exact hg (eq ▸ qParity_combo a E F A B he hf)
  | succ k ih =>
    have reduced (t) :
        ((A % 2) * (qCoord E t % 2) + (B % 2) * (qCoord F t % 2)) % 2 = 0 := by
      have ht := congrArg (fun x : ℤ => x % 2) (h t)
      change (A * qCoord E t + B * qCoord F t) % 2 = (2 ^ (k + 1) * qCoord G t) % 2 at ht
      rw [pow_succ', mul_assoc, Int.mul_emod, Int.emod_self] at ht
      simp only [Int.zero_mul, Int.zero_emod] at ht
      rwa [Int.add_emod, Int.mul_emod A, Int.mul_emod B, ← Int.add_emod] at ht
    by_cases hA0 : A % 2 = 0 <;> by_cases hB0 : B % 2 = 0
    · apply ih (A / 2) (B / 2) (fun hn => hA (by omega)) (fun hn => hB (by omega))
      intro t
      have hA' : A = 2 * (A / 2) := by omega
      have hB' : B = 2 * (B / 2) := by omega
      have ht := h t
      rw [hA', hB', pow_succ'] at ht
      linarith
    · obtain ⟨t, ht⟩ := hB (by omega)
      have := reduced t
      rw [hA0, show B % 2 = 1 by omega, ht] at this
      norm_num at this
    · obtain ⟨t, ht⟩ := hA (by omega)
      have := reduced t
      rw [hB0, show A % 2 = 1 by omega, ht] at this
      norm_num at this
    · refine ⟨equal_parities E F (fun t => ?_), nonempty_of_odd_entry E a he (hA (by omega))⟩
      have ht := reduced t
      simp only [show A % 2 = 1 by omega, show B % 2 = 1 by omega, one_mul] at ht
      omega

private theorem entry_decomposition {V : Type} (e : QEq V) (t : Option V) :
    qCoord e t = (2 : ℤ) ^ qOrder e * qCoord (qPrimitive e) t := by
  cases t with
  | none => exact qPrimitive_rhs e
  | some v => exact qPrimitive_coeff e v

/-- If both primitive heads hold modulo two and the primitive resolvent head fails
at the same Boolean point, the input heads have identical augmented parity
vectors, with at least one nonzero variable coefficient modulo two. -/
theorem primitive_combo_obstruction {V : Type} [Fintype V] (a : V → Bool)
    (e f : QEq V) (α β : ℤ)
    (he : LinEqSat a (qParity (qPrimitive e))) (hf : LinEqSat a (qParity (qPrimitive f)))
    (hg : ¬ LinEqSat a (qParity (qPrimitive (α • e.1 + β • f.1, α * e.2 + β * f.2)))) :
    qParity (qPrimitive e) = qParity (qPrimitive f) ∧ (qParity (qPrimitive e)).1.Nonempty := by
  classical
  let g : QEq V := (α • e.1 + β • f.1, α * e.2 + β * f.2)
  let coeff (z : ℤ) (x : QEq V) := if x = 0 then 0 else z * 2 ^ qOrder x
  have nonzero (z : ℤ) (x : QEq V) (hc : coeff z x ≠ 0) :
      ∃ t, qCoord (qPrimitive x) t % 2 = 1 := by
    have hx : x ≠ 0 := fun h => hc (by simp [coeff, h])
    rcases qPrimitive_odd hx with ⟨v, hv⟩ | hr
    · exact ⟨some v, Int.odd_iff.mp hv⟩
    · exact ⟨none, Int.odd_iff.mp hr⟩
  have restore (z : ℤ) (x : QEq V) (t : Option V) :
      coeff z x * qCoord (qPrimitive x) t = z * qCoord x t := by
    by_cases hx : x = 0
    · subst x
      cases t <;> simp [qCoord, coeff]
    · rw [show coeff z x = z * 2 ^ qOrder x by simp [coeff, hx], mul_assoc,
        ← entry_decomposition x t]
  apply scaled_obstruction _ _ (qPrimitive g) a he hf hg (qOrder g)
    (coeff α e) (coeff β f) (nonzero _ _) (nonzero _ _)
  intro t
  rw [restore, restore, ← entry_decomposition]
  cases t <;> simp [qCoord, g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end PEqualNP.Search.Helpers
