import PEqualNP.Defs.SearchQ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Search.Helpers

open PEqualNP.Search

variable {V : Type}

private theorem primeFactors_card_le_bits (n : ℕ) : n.primeFactors.card ≤ n.size := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h := Finset.pow_card_le_prod n.primeFactors id 2
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact (Nat.lt_size.mpr (h.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (Nat.prod_primeFactors_dvd n)))).le

private def linePrimes (L : QLine V) : Finset ℕ :=
  (L.map (fun e => e.2.natAbs.primeFactors)).foldr (· ∪ ·) ∅

/-- Primes dividing any nonzero right-hand side, including the constants
potentially removed by syntactic simplification. -/
def rhsBadPrimes (π : List (QLine V)) : Finset ℕ :=
  (π.map linePrimes).foldr (· ∪ ·) ∅

theorem mem_rhsBadPrimes {π : List (QLine V)} {p : ℕ} :
    p ∈ rhsBadPrimes π ↔ p.Prime ∧ ∃ L ∈ π, ∃ e ∈ L, e.2 ≠ 0 ∧ (p : ℤ) ∣ e.2 := by
  have line (L : QLine V) :
      p ∈ linePrimes L ↔ p.Prime ∧ ∃ e ∈ L, e.2 ≠ 0 ∧ (p : ℤ) ∣ e.2 := by
    induction L with
    | nil => simp [linePrimes]
    | cons e L ih =>
      change p ∈ e.2.natAbs.primeFactors ∪ linePrimes L ↔ _
      simp only [Finset.mem_union, Nat.mem_primeFactors, ih, List.mem_cons, Int.natCast_dvd,
        Int.natAbs_ne_zero]
      grind
  induction π with
  | nil => simp [rhsBadPrimes]
  | cons L π ih =>
    change p ∈ linePrimes L ∪ rhsBadPrimes π ↔ _
    simp only [Finset.mem_union, line, ih, List.mem_cons]
    grind

/-- The complete set of exceptional primes costs at most the proof's encoded size. -/
theorem rhsBadPrimes_card_le_size [Fintype V] (π : List (QLine V)) :
    (rhsBadPrimes π).card ≤ resLinQSize π := by
  have line (L : QLine V) : (linePrimes L).card ≤ (L.map QEq.size).sum := by
    induction L with
    | nil => simp [linePrimes]
    | cons e L ih =>
      change (e.2.natAbs.primeFactors ∪ linePrimes L).card ≤ e.size + (L.map QEq.size).sum
      have he : e.2.natAbs.primeFactors.card ≤ e.size := by
        unfold QEq.size
        exact (primeFactors_card_le_bits _).trans (Nat.le_add_left _ _)
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add he ih)
  induction π with
  | nil => simp [rhsBadPrimes, resLinQSize]
  | cons L π ih =>
    change (linePrimes L ∪ rhsBadPrimes π).card ≤ (1 + (L.map QEq.size).sum) + resLinQSize π
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ((line L).trans (Nat.le_add_left _ _)) ih)

/-- From any larger pool of primes, select a modulus preserving every nonzero
right-hand side in the proof. -/
theorem exists_rhs_safe_prime [Fintype V] (π : List (QLine V)) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hsize : resLinQSize π < P.card) :
    ∃ p ∈ P, p.Prime ∧ ∀ L ∈ π, ∀ e ∈ L, e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2 := by
  obtain ⟨p, hp, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card
    ((rhsBadPrimes_card_le_size π).trans_lt hsize)
  exact ⟨p, hp, hP p hp, fun L hL e he hn hd =>
    hgood (mem_rhsBadPrimes.mpr ⟨hP p hp, L, hL, e, he, hn, hd⟩)⟩

/-- A quadratic bound on the range needed to find at least `m` primes. -/
private theorem enough_primes (m : ℕ) (hm : 0 < m) :
    m ≤ ((4 * m) ^ 2).primesLE.card := by
  rw [Nat.primesLE_card_eq_primeCounting]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : 4 ≤ (4 * m) ^ 2 := by nlinarith
  have hlogpos : 0 < Real.log (((4 * m) ^ 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < (4 * m) ^ 2 by omega))
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  have hbase : Real.log (4 * (m : ℝ)) ≤ 4 * m :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hbound : (m : ℝ) ≤ (((4 * m) ^ 2 : ℕ) : ℝ) * Real.log 2 /
      Real.log (((4 * m) ^ 2 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hlogpos).mpr
    push_cast
    rw [Real.log_pow]
    calc
      _ ≤ (m : ℝ) * (2 * (4 * m)) := by norm_num; gcongr
      _ = (4 * (m : ℝ)) ^ 2 * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (sq_nonneg _)
  exact_mod_cast hbound.trans (Chebyshev.pi_ge_of_four_le hn)

/-- A modulus of size quadratic in the proof size suffices to preserve every
nonzero right-hand side. -/
theorem exists_small_rhs_safe_prime [Fintype V] (π : List (QLine V)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ (4 * (resLinQSize π + 1)) ^ 2 ∧
      ∀ L ∈ π, ∀ e ∈ L, e.2 ≠ 0 → ¬ (p : ℤ) ∣ e.2 := by
  let N := (4 * (resLinQSize π + 1)) ^ 2
  obtain ⟨p, hp, hprime, hsafe⟩ := exists_rhs_safe_prime π N.primesLE
    (fun _ h => (Nat.mem_primesLE.mp h).2) (enough_primes _ (Nat.zero_lt_succ _))
  exact ⟨p, hprime, (Nat.mem_primesLE.mp hp).1, hsafe⟩

end PEqualNP.Search.Helpers
