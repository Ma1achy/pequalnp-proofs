import PEqualNP.Search.Helpers.QPrimitive
import PEqualNP.Search.Helpers.QRow

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type}

private theorem coord_factor (e : QEq V) (i : Option V) :
    qCoord e i = (2 : ℤ) ^ qOrder e * qCoord (qPrimitive e) i := by
  cases i with
  | none => exact qPrimitive_rhs e
  | some v => exact qPrimitive_coeff e v

/-- Removing the common dyadic factors does not change which augmented minors vanish. -/
theorem qMinor_zero_iff_primitive (e f : QEq V) (i j : Option V) :
    qCoord e i * qCoord f j = qCoord e j * qCoord f i ↔
    qCoord (qPrimitive e) i * qCoord (qPrimitive f) j =
      qCoord (qPrimitive e) j * qCoord (qPrimitive f) i := by
  rw [coord_factor e i, coord_factor e j, coord_factor f i, coord_factor f j]
  rw [mul_mul_mul_comm, mul_mul_mul_comm ((2 : ℤ) ^ qOrder e) (qCoord (qPrimitive e) j)]
  exact mul_right_inj' (by positivity)

private theorem odd_coord {e : QEq V} (h : e ≠ 0) : ∃ i, Odd (qCoord (qPrimitive e) i) := by
  rcases qPrimitive_odd h with ⟨v, hv⟩ | hv
  · exact ⟨some v, hv⟩
  · exact ⟨none, hv⟩

private theorem parity_of_vanishing_minors {ι : Type} (x y : ι → ℤ)
    (hx : ∃ i, Odd (x i)) (hy : ∃ j, Odd (y j))
    (h : ∀ i j, x i * y j = x j * y i) (k : ι) : x k % 2 = y k % 2 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hprod := Int.odd_mul.mpr ⟨hi, hj⟩
  rw [h i j] at hprod
  have hyi := (Int.odd_mul.mp hprod).2
  have hiff := congrArg Odd (h i k)
  simp only [Int.odd_mul, hi, hyi, true_and, and_true] at hiff
  by_cases hodd : Odd (x k)
  · exact (Int.odd_iff.mp hodd).trans (Int.odd_iff.mp (hiff ▸ hodd)).symm
  · exact (Int.not_odd_iff.mp hodd).trans (Int.not_odd_iff.mp (hiff ▸ hodd)).symm

variable [Fintype V]

/-- Two nonzero rationally dependent augmented rows give the same parity
equation once each row's common power of two is removed. -/
theorem qParity_primitive_eq_of_vanishing_minors (e f : QEq V) (he : e ≠ 0) (hf : f ≠ 0)
    (h : ∀ i j, qCoord e i * qCoord f j = qCoord e j * qCoord f i) :
    qParity (qPrimitive e) = qParity (qPrimitive f) := by
  have eq := parity_of_vanishing_minors _ _ (odd_coord he) (odd_coord hf)
    (fun i j => (qMinor_zero_iff_primitive e f i j).mp (h i j))
  apply Prod.ext
  · apply Finset.ext
    intro v
    simpa [qParity, qCoord] using congrArg (fun z => z = (1 : ℤ)) (eq (some v)) |>.to_iff
  · exact congrArg (fun z : ℤ => decide (z = 1)) (eq none)

/-- Failure of the primitive projection on a resolution implies that the two
parent equations have a nonzero integer minor, allowing the RHS as one column. -/
theorem exists_minor_of_primitive_failure (a : V → Bool) (e f : QEq V) (α β : ℤ)
    (he : LinEqSat a (qParity (qPrimitive e))) (hf : LinEqSat a (qParity (qPrimitive f)))
    (hg : ¬ LinEqSat a (qParity (qPrimitive (α • e.1 + β • f.1, α * e.2 + β * f.2)))) :
    ∃ i j, qCoord e i * qCoord f j ≠ qCoord e j * qCoord f i := by
  classical
  by_contra! h
  let g : QEq V := (α • e.1 + β • f.1, α * e.2 + β * f.2)
  have hn : g ≠ 0 := by
    intro hz
    apply hg
    change LinEqSat a (qParity (qPrimitive g))
    rw [hz, qPrimitive_zero, qParity_sat]
    simp [Int.ModEq]
  have hc (i : Option V) : qCoord g i = α * qCoord e i + β * qCoord f i := by
    cases i <;> rfl
  apply hg
  change LinEqSat a (qParity (qPrimitive g))
  by_cases hx : e ≠ 0
  · rw [← qParity_primitive_eq_of_vanishing_minors e g hx hn]
    · exact he
    · intro i j
      rw [hc i, hc j]
      linear_combination β * h i j
  · have he0 : e = 0 := not_ne_iff.mp hx
    have hf0 : f ≠ 0 := by
      intro hz
      apply hn
      simp [g, he0, hz]
    rw [← qParity_primitive_eq_of_vanishing_minors f g hf0 hn]
    · exact hf
    · intro i j
      rw [hc i, hc j]
      linear_combination -α * h i j

end PEqualNP.Search.Helpers
