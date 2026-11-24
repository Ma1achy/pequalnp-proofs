import PEqualNP.Defs.SearchQ
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

/-- The integer coefficients that read one pigeon row as a binary number. -/
def binaryRowCoeff {m l : ℕ} (i : Fin m) (v : Fin m × Fin l) : ℤ :=
  if v.1 = i then 2 ^ v.2.val else 0

/-- The singleton equation equating the binary labels of two pigeons. -/
def binaryRowEq {m l : ℕ} (i j : Fin m) : QEq (Fin m × Fin l) :=
  (binaryRowCoeff i - binaryRowCoeff j, 0)

private def rowNumber {l : ℕ} (f : Fin l → Bool) : ℕ :=
  ∑ b : Fin l, if f b then 2 ^ b.val else 0

private theorem rowNumber_injective {l : ℕ} : Function.Injective (rowNumber (l := l)) := by
  classical
  let bits (f : Fin l → Bool) := (Finset.univ.filter (fun b => f b = true)).image Fin.val
  have repr (f : Fin l → Bool) : (∑ b ∈ bits f, 2 ^ b) = rowNumber f := by
    rw [Finset.sum_image (fun u _ v _ h => Fin.ext h)]
    simp [rowNumber, Finset.sum_filter]
  intro f g same
  have seteq : bits f = bits g := Finset.geomSum_injective (n := 2) (by decide)
    ((repr f).trans (same.trans (repr g).symm))
  funext b
  have mem (x : Fin l → Bool) : b.val ∈ bits x ↔ x b = true := by
    simp [bits, Fin.val_inj]
  have h : f b = true ↔ g b = true := by rw [← mem, ← mem, seteq]
  cases h₁ : f b <;> cases h₂ : g b <;> simp_all

private theorem sum_binaryRowCoeff {m l : ℕ} (a : Fin m × Fin l → Bool) (i : Fin m) :
    (∑ v, binaryRowCoeff i v * (if a v then 1 else 0)) =
      (rowNumber (fun b => a (i,b)) : ℤ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold rowNumber
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single i]
  · cases h : a (i,b) <;> simp [binaryRowCoeff, h]
  · intro z _ hzi
    simp [binaryRowCoeff, hzi]
  · simp

theorem binaryRowEq_holds {m l : ℕ} (a : Fin m × Fin l → Bool) (i j : Fin m) :
    QEq.Holds a (binaryRowEq i j) ↔ ∀ b, a (i,b) = a (j,b) := by
  unfold QEq.Holds binaryRowEq
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_binaryRowCoeff, sub_eq_zero,
    Int.natCast_inj]
  exact ⟨fun h b => congrFun (rowNumber_injective h) b,
    fun h => congrArg rowNumber (funext h)⟩

theorem binaryRowEq_off {m l : ℕ} (i j : Fin m) (v : Fin m × Fin l)
    (hi : v.1 ≠ i) (hj : v.1 ≠ j) : (binaryRowEq i j).1 v = 0 := by
  simp [binaryRowEq, binaryRowCoeff, hi, hj]

theorem binaryRowEq_abs_bound {m l : ℕ} (i j : Fin m) (v : Fin m × Fin l) :
    ((binaryRowEq i j).1 v).natAbs ≤ 2 ^ l := by
  have h : 2 ^ v.2.val ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) v.2.isLt.le
  change ((if v.1 = i then (2 : ℤ)^v.2.val else 0) -
    (if v.1 = j then (2 : ℤ)^v.2.val else 0)).natAbs ≤ 2^l
  split_ifs <;> simp_all only [sub_self, sub_zero, zero_sub, Int.natAbs_neg, Int.natAbs_pow,
    Int.natAbs_zero, Nat.zero_le, show (2 : ℤ).natAbs = 2 from rfl]

end PEqualNP.Search.Helpers
