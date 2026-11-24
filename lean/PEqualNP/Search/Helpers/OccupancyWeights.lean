import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

private theorem left_product (a : ℕ) :
    (∏ k ∈ Finset.range a, ((a : ℚ) - k)) = a.factorial := by
  have cast : (∏ k ∈ Finset.range a, ((a : ℚ) - k)) = ∏ k ∈ Finset.range a, ((a-k : ℕ) : ℚ) := by
    apply Finset.prod_congr rfl
    intro k hk
    exact (Nat.cast_sub (Finset.mem_range.mp hk).le).symm
  rw [cast, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

private theorem shifted_product (a d : ℕ) :
    (∏ k ∈ Finset.range d, ((a : ℚ) - (a+1+k : ℕ))) = (-1:ℚ)^d * d.factorial := by
  have val (k : ℕ) : ((a:ℚ) - (a+1+k : ℕ)) = (-1:ℚ) * ((k+1 : ℕ) : ℚ) := by push_cast; ring
  simp_rw [val]
  rw [Finset.prod_mul_distrib, ←Nat.cast_prod]
  simp

/-- Factorial scaling of the Lagrange weight at an integer node. -/
theorem occupancyWeight_scaled {n : ℕ} (h : Fin (n+1)) :
    (n.factorial : ℚ) / (∏ k ∈ (Finset.univ.erase h), ((h.val : ℚ) - (k.val : ℚ))) =
      (-1 : ℚ)^(n-h.val) * (n.choose h.val : ℚ) := by
  let a := h.val
  have ha : a ≤ n := Nat.le_of_lt_succ h.isLt
  let f (k : ℕ) : ℚ := if k=a then 1 else (a:ℚ)-k
  have den : (∏ k ∈ (Finset.univ.erase h), ((h.val : ℚ) - (k.val : ℚ))) =
      (a.factorial:ℚ) * ((-1:ℚ)^(n-a) * (n-a).factorial) := by
    calc
      _ = ∏ k ∈ Finset.univ.erase h, f k.val := by
        apply Finset.prod_congr rfl
        intro k hk
        have ne : k.val ≠ a := fun eq => Finset.ne_of_mem_erase hk (Fin.ext eq)
        simp [f,ne,a]
      _ = ∏ k : Fin (n+1), f k.val := by
        simpa [f,a] using Finset.prod_erase_mul Finset.univ (fun k : Fin (n+1) => f k.val) (Finset.mem_univ h)
      _ = ∏ k ∈ Finset.range (a+1+(n-a)), f k := by
        rw [Finset.prod_fin_eq_prod_range]
        rw [show a+1+(n-a) = n+1 by omega]
        exact Finset.prod_congr rfl fun k hk => dite_eq_left (Finset.mem_range.mp hk)
      _ = _ := by
        rw [Finset.prod_range_add,Finset.prod_range_succ]
        have small : (∏ k ∈ Finset.range a, f k) = (a.factorial:ℚ) := by
          rw [← left_product a]
          exact Finset.prod_congr rfl fun k hk => ite_eq_right (Finset.mem_range.mp hk).ne
        rw [small,show f a = 1 by simp [f],mul_one]
        congr 1
        calc
          _ = ∏ k ∈ Finset.range (n-a), ((a:ℚ)-(a+1+k : ℕ)) :=
            Finset.prod_congr rfl fun k _ => ite_eq_right (by omega : a+1+k ≠ a)
          _ = _ := shifted_product a (n-a)
  rw [den]
  have choose : (n.choose a : ℚ) * (a.factorial:ℚ) * ((n-a).factorial:ℚ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  have nz : (a.factorial:ℚ) * ((-1:ℚ)^(n-a) * (n-a).factorial) ≠ 0 := by positivity
  apply (div_eq_iff nz).mpr
  have sign : ((-1:ℚ)^(n-a)) * ((-1:ℚ)^(n-a)) = 1 := by rw [←mul_pow]; norm_num
  change (n.factorial:ℚ) = (-1:ℚ)^(n-a) * (n.choose a:ℚ) * _
  rw [←choose]
  linear_combination -((n.choose a : ℚ) * a.factorial * (n-a).factorial) * sign

end PEqualNP.Search.Helpers
