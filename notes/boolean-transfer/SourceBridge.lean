import BooleanIdeal
import Paper.Flat
import Nc.Acc.Prog

/-! Counterexamples stated against the pinned project's own block projection and word code. -/

namespace BooleanTransfer.SourceBridge

open MvPolynomial

/-- Paper.linearPart uses exactly the coefficient and product in the companion definition. -/
theorem paper_linearPart_eq {R T : Type} [CommRing R] [Fintype T] [DecidableEq T]
    {k : ℕ} (p : MvPolynomial (Fin k × T) R) :
    Paper.linearPart p = blockLinearPart p := rfl

theorem paper_linearPart_blockExample (R : Type) [CommRing R] {k : ℕ} (i : Fin k) :
    Paper.linearPart (blockExample R i) = -blockProduct R k := by
  exact singletonLinearPart_blockExample i

theorem paper_linearPart_expand_two {R T : Type} [CommRing R] [Fintype T] [DecidableEq T]
    {k : ℕ} (i : Fin k) (p : MvPolynomial (Fin k × T) R) :
    Paper.linearPart (expand 2 p) = 0 :=
  blockLinearPart_expand_two i p

/-- The low-degree sum in Paper.lem_lowdeg at its actual valid nil-tree code
(with N=2). The original generator evaluates to zero while the cutoff gives -1. -/
theorem lowDegree_nil_code (R : Type) [CommRing R] (d : ℕ) (hd : 0 < d) :
    let v := NS1.codeB R 2 (NS1.tbits NS1.Tree.nil)
    let x : MvPolynomial (Fin 2 × Option Bool) R := X (0,some false)
    NS1.Tree.nil.size < 2 ∧ eval v (x^(d+1)-x) = 0 ∧
      (∑ j ∈ Finset.range (d+1), eval v (homogeneousComponent j (x^(d+1)-x))) = -1 := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · simp [NS1.codeB, NS1.tbits]
  · rw [← map_sum, cutoff_generator d hd]
    simp [NS1.codeB, NS1.tbits]

/-- Interleave all input dilations of each gate. Binary-power input dilation by
2^t has a straight-line circuit with at most (t+1)s gates in every characteristic. -/
theorem computes_expand_pow_two {R V : Type*} [CommSemiring R] {p : MvPolynomial V R} {s : ℕ}
    (hp : Nc.Computes p s) (t : ℕ) : Nc.Computes (expand (2^t) p) (s*(t+1)) := by
  obtain ⟨l,hl,out,ho,eqo⟩ := hp
  let L (k : ℕ) := expand (2^(k%(t+1))) (l (k/(t+1)))
  have val (i j : ℕ) (hj : j<t+1) : L (i*(t+1)+j) = expand (2^j) (l i) := by
    have quot : (i*(t+1)+j)/(t+1)=i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hj, Nat.zero_add]
    simp [L, Nat.mod_eq_of_lt hj, quot]
  have prior {i j a : ℕ} (h : i<j) : i*(t+1)+a < j*(t+1)+a :=
    Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos t)) a
  have bound {i : ℕ} (hi : i<s) {j : ℕ} (hj : j<t+1) : i*(t+1)+j < s*(t+1) := by
    calc
      i*(t+1)+j < i*(t+1)+(t+1) := Nat.add_lt_add_left hj _
      _ = (i+1)*(t+1) := (Nat.succ_mul ..).symm
      _ ≤ s*(t+1) := Nat.mul_le_mul_right _ hi
  refine ⟨L, ?_, out*(t+1)+t, bound ho (Nat.lt_succ_self _), by rw [val _ _ (Nat.lt_succ_self _),eqo]⟩
  intro k hk
  let i := k/(t+1)
  let j := k%(t+1)
  have hj : j<t+1 := Nat.mod_lt _ (Nat.succ_pos t)
  have e : i*(t+1)+j=k := by simpa [i,j,Nat.mul_comm] using Nat.div_add_mod k (t+1)
  have hi : i<s := (Nat.div_lt_iff_lt_mul (Nat.succ_pos t)).mpr hk
  rw [←e]
  rcases hl i hi with ⟨v,h⟩ | ⟨a,h⟩ | ⟨u,hu,v,hv,h⟩ | ⟨u,hu,v,hv,h⟩
  · cases jj : j with
    | zero =>
      exact Or.inl ⟨v,by rw [val _ _ (by omega),h,expand_X]; simp⟩
    | succ z =>
      exact Or.inr (Or.inr (Or.inr ⟨i*(t+1)+z, by omega, i*(t+1)+z, by omega, by
        rw [val _ _ (by omega),val _ _ (by omega),h,expand_X,expand_X,Nat.pow_succ,pow_mul,pow_two]⟩))
  · exact Or.inr (Or.inl ⟨a, by rw [val _ _ hj,h,expand_C]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨u*(t+1)+j,prior hu,v*(t+1)+j,prior hv,by
      rw [val _ _ hj,val _ _ hj,val _ _ hj,h,map_add]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨u*(t+1)+j,prior hu,v*(t+1)+j,prior hv,by
      rw [val _ _ hj,val _ _ hj,val _ _ hj,h,map_mul]⟩))
/-- Input squaring needs at most twice the number of original instructions. -/
theorem computes_expand_two {R V : Type*} [CommSemiring R] {p : MvPolynomial V R} {s : ℕ}
    (hp : Nc.Computes p s) : Nc.Computes (expand 2 p) (2*s) := by
  simpa [Nat.mul_comm] using computes_expand_pow_two hp 1

/-- A small representative can have both formal interfaces erased at once in
every characteristic. The construction preserves the Boolean function. -/
theorem exists_small_erased {R T : Type} [CommRing R] [Fintype T] [DecidableEq T]
    {k s : ℕ} (i : Fin k) {p : MvPolynomial (Fin k × T) R} (hp : Nc.Computes p s)
    (t d : ℕ) (hd : d < 2^(t+1)) :
    ∃ q : MvPolynomial (Fin k × T) R, Nc.Computes q (s*(t+2)) ∧
      (∀ v, IsCubePoint v → eval v q = eval v p) ∧ Paper.linearPart q = 0 ∧
      (∑ j ∈ Finset.range (d+1), homogeneousComponent j q) = C (p.coeff 0) := by
  let e := 2^(t+1)
  have he : 0 < e := Nat.pow_pos (by decide)
  refine ⟨expand e p, computes_expand_pow_two hp (t+1), ?_, ?_, ?_⟩
  · intro v hv
    have heq : e-1+1=e := by omega
    simpa only [heq] using eval_expand_cube (e-1) p hv
  · dsimp only [e]
    rw [Nat.pow_succ', expand_mul]
    exact paper_linearPart_expand_two i _
  · rw [Finset.sum_eq_single 0, homogeneousComponent_zero, coeff_expand_zero _ (Nat.ne_of_gt he)]
    · intro j hj hn
      apply homogeneousComponent_expand_of_not_dvd
      intro h
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
      have hj' := Finset.mem_range.mp hj
      change d < e at hd
      omega
    · simp

end BooleanTransfer.SourceBridge
