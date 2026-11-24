import PEqualNP.Search.Helpers.BinaryRowEquation
import PEqualNP.Search.Helpers.QSynRename
import Mathlib.Data.Fin.Embedding

/-! Subtracting two singleton balance equations with different omitted rows gives
equality of the two binary labels in a single integer resolution step. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- The sum of the binary row labels equals `b`. -/
def binaryTotal {m l : ℕ} (b : ℤ) : QEq (Fin m × Fin l) :=
  (fun v => 2 ^ v.2.val, b)

/-- The sum of the binary labels of all rows except `i` equals `b`. -/
def binaryTotalExcept {m l : ℕ} (i : Fin (m+1)) (b : ℤ) : QEq (Fin (m+1) × Fin l) :=
  (fun v => if v.1 = i then 0 else 2 ^ v.2.val, b)

/-- Renaming the full balance equation along the injection that skips row `i`
sets just that row's coefficients to zero. -/
theorem qRenameEq_binaryTotal {m l : ℕ} (i : Fin (m+1)) (b : ℤ) :
    qRenameEq (rowEmbedding i.succAboveEmb l) (binaryTotal b) = binaryTotalExcept i b := by
  apply Prod.ext
  · funext v
    rcases v with ⟨r,k⟩
    by_cases same : r = i
    · subst r
      have outside : (i,k) ∉ Set.range (rowEmbedding i.succAboveEmb l) := by
        rintro ⟨⟨s,t⟩, h⟩
        exact i.succAbove_ne s (congrArg Prod.fst h)
      rw [qRenameEq_off _ _ outside]
      simp [binaryTotalExcept]
    · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq same
      change (qRenameEq (rowEmbedding i.succAboveEmb l) (binaryTotal b)).1
        (rowEmbedding i.succAboveEmb l (s,k)) = _
      rw [qRenameEq_at]
      simp [binaryTotal,binaryTotalExcept,i.succAbove_ne]
  · rfl

/-- One syntactic resolution cancels all the shared rows and the common right-hand side. -/
theorem binaryTotalExcept_cut {m l : ℕ} {F : Set (Clause (Fin (m+1) × Fin l))}
    {ρ : List (QLine (Fin (m+1) × Fin l))} (i j : Fin (m+1)) (b : ℤ)
    (d : IsResLinQSynDerivation F ρ) (hi : [binaryTotalExcept i b] ∈ ρ)
    (hj : [binaryTotalExcept j b] ∈ ρ) :
    IsResLinQSynDerivation F ([binaryRowEq i j] :: ρ) := by
  have eqn : ((-1:ℤ) • (binaryTotalExcept (l:=l) i b).1 +
      (1:ℤ) • (binaryTotalExcept (l:=l) j b).1,
      (-1:ℤ) * b + 1*b) = binaryRowEq i j := by
    apply Prod.ext
    · funext v
      by_cases hi : v.1 = i <;> by_cases hj : v.1 = j <;>
        simp [binaryTotalExcept,binaryRowEq,binaryRowCoeff,hi,hj] <;> split_ifs <;> simp
    · simp [binaryRowEq]
  have step := d.res (-1) 1 hi hj
  change IsResLinQSynDerivation F ([_] :: ρ) at step
  rwa [← eqn]

/-- A coarse bound on the encoded size of the single added equality line. -/
theorem binaryRowEq_singleton_size {m l : ℕ} (i j : Fin m) :
    resLinQSize [[binaryRowEq (l := l) i j]] ≤ 2 + m*l * 2^l := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m × Fin l))) fun v _ =>
    (show ((binaryRowEq i j).1 v).natAbs.size ≤ ((binaryRowEq i j).1 v).natAbs from
      Nat.size_le.mpr Nat.lt_two_pow_self).trans (binaryRowEq_abs_bound i j v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul] at h
  simpa [resLinQSize, QEq.size, binaryRowEq, ← Nat.add_assoc] using
    (Nat.add_le_add_left h 2)

end PEqualNP.Search.Helpers
