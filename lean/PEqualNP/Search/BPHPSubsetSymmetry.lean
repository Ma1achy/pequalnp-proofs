import PEqualNP.Search.Helpers.BPHPSubsetState
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace PEqualNP.Search

private theorem symmetry_count (l : ℕ) (hl : 5 ≤ l) : 2^l * l.factorial ≤ 2^(2^(l-1)) := by
  induction l, hl using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have spare : k+1 ≤ 2^(k-1) := by
      have h := Nat.lt_two_pow_self (n := k-2)
      have heq : 2^(k-1) = 2^(k-2)*2 := by
        rw [← pow_succ]; congr 1; omega
      omega
    have mult : 2*(k+1) ≤ 2^(2^(k-1)) := calc
      2*(k+1) ≤ 2 * 2^k := Nat.mul_le_mul_left _ Nat.lt_two_pow_self
      _ = 2^(k+1) := by rw [pow_succ, mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) spare
    have two : 2^(k-1) + 2^(k-1) = 2^k := by
      rw [← two_mul, mul_comm, ← pow_succ]; congr 1; omega
    calc
      2^(k+1) * (k+1).factorial = (2*(k+1)) * (2^k * k.factorial) := by
        rw [pow_succ,Nat.factorial_succ]; ring
      _ ≤ 2^(2^(k-1)) * 2^(2^(k-1)) := Nat.mul_le_mul mult ih
      _ = 2^(2^((k+1)-1)) := by rw [← pow_add,two]; simp

/-- Coordinate permutations and simultaneous bit flips cannot compress the
family of all subsets of holes to a polynomial-size list of representatives. -/
theorem BPHPSubsetSymmetry :
  ∀ (l : ℕ) (reps : List (Finset (Fin l → Bool))),
  (∀ S : Finset (Fin l → Bool), ∃ R ∈ reps, ∃ (σ : Equiv.Perm (Fin l)) (mask : Fin l → Bool),
    S = R.image (fun x j => Bool.xor (x (σ j)) (mask j))) →
  let n := 2 ^ l
  2 ^ n ≤ (n * l.factorial) * reps.length ∧
    (5 ≤ l → 2 ^ (n / 2) ≤ reps.length) := by
  intro l reps cover n
  let render : Fin reps.length × (Equiv.Perm (Fin l) × (Fin l → Bool)) → Finset (Fin l → Bool) :=
    fun (i,σ,mask) => (reps.get i).image (fun x j => Bool.xor (x (σ j)) (mask j))
  have allSets : Function.Surjective render := by
    intro S
    obtain ⟨R,hR,σ,mask,eq⟩ := cover S
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hR
    refine ⟨(i,σ,mask), ?_⟩
    change (reps.get i).image _ = S
    rw [hi]
    exact eq.symm
  have count := Fintype.card_le_of_surjective render allSets
  have bound : 2^n ≤ (n*l.factorial)*reps.length := by
    simpa [n,Fintype.card_prod,Fintype.card_perm,Fintype.card_fun,Nat.mul_left_comm,
      Nat.mul_comm,Nat.mul_assoc] using count
  refine ⟨bound, ?_⟩
  intro hl
  have hhalf : n / 2 = 2^(l-1) := by
    have hn : n = 2^(l-1)*2 := by
      change 2^l = _
      rw [← pow_succ]; congr 1; omega
    rw [hn]; simp
  have twice : 2^(n/2) * 2^(n/2) = 2^n := by
    rw [← pow_add,hhalf,← two_mul,mul_comm,← pow_succ]
    congr 2; omega
  have small : n*l.factorial ≤ 2^(n/2) := by simpa only [hhalf] using symmetry_count l hl
  have both : 2^(n/2) * 2^(n/2) ≤ 2^(n/2) * reps.length := by
    rw [twice]
    exact bound.trans (Nat.mul_le_mul_right _ small)
  exact Nat.le_of_mul_le_mul_left both (Nat.two_pow_pos _)

/-- A constant assignment tests membership in the excluded hole set. -/
theorem subsetState_constant {l : ℕ} (H : Finset (Fin l → Bool)) (h : Fin l → Bool) :
    QLine.Holds (fun v => h v.2) (subsetState H) ↔ h ∉ H := by
  constructor
  · rintro ⟨e, hm, sat⟩
    obtain ⟨i, g, _, outside, rfl⟩ := (mem_subsetState H e).mp hm
    have eqn : h = g := funext ((Helpers.rowPatternEq_holds _ i g).mp sat)
    exact eqn ▸ outside
  · intro outside
    let i : Fin (2^l+1) := ⟨0, Nat.zero_lt_succ _⟩
    refine ⟨Helpers.rowPatternEq i h, (mem_subsetState _ _).mpr ⟨i,h,Nat.zero_le _,outside,rfl⟩, ?_⟩
    exact (Helpers.rowPatternEq_holds _ i h).mpr (fun _ => rfl)

/-- Semantic equivalence of two dynamic-programming lines forces their
indexing sets to coincide. Constant-row assignments suffice to distinguish them. -/
theorem subsetState_eq_of_equivalent {l : ℕ} {H K : Finset (Fin l → Bool)}
    (equiv : ∀ a, QLine.Holds a (subsetState H) ↔ QLine.Holds a (subsetState K)) : H = K := by
  ext h
  have test := equiv (fun v => h v.2)
  simpa only [subsetState_constant, not_iff_not] using test

/-- The orbit bound applies when a state is represented by any semantically
equivalent state obtained from a listed representative's indexing set. -/
theorem subsetState_symmetry_bound (l : ℕ) (reps : List (Finset (Fin l → Bool)))
    (cover : ∀ H : Finset (Fin l → Bool), ∃ R ∈ reps, ∃ (σ : Equiv.Perm (Fin l)) (mask : Fin l → Bool),
      ∀ a, QLine.Holds a (subsetState H) ↔
        QLine.Holds a (subsetState (R.image (fun x j => Bool.xor (x (σ j)) (mask j))))) :
    let n := 2 ^ l
    2 ^ n ≤ (n * l.factorial) * reps.length ∧ (5 ≤ l → 2 ^ (n / 2) ≤ reps.length) := by
  apply BPHPSubsetSymmetry l reps
  intro H
  obtain ⟨R,hr,σ,mask,equiv⟩ := cover H
  exact ⟨R,hr,σ,mask,subsetState_eq_of_equivalent equiv⟩

end PEqualNP.Search
