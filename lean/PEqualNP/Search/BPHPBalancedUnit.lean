import PEqualNP.Search.BPHPBalancedPair
import PEqualNP.Search.BPHPPairRefutation
import PEqualNP.Search.Helpers.QUnscaleBitEquality

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

private theorem qBitDiff_holds {V : Type} [Fintype V] [DecidableEq V]
    (a : V → Bool) (x y : V) : QEq.Holds a (qBitDiff x y 0) ↔ a x = a y := by
  unfold QEq.Holds qBitDiff litQEq
  simp only [Pi.sub_apply, Int.sub_mul, Finset.sum_sub_distrib, ite_mul, Int.one_mul,
    Int.zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases a x <;> cases a y <;> decide

/-- Any singleton with a nonzero coefficient derived on the balanced instance
gives an unbalanced refutation. The bound depends on binary encoding cost and
is uniform over all choices and sizes of the integer coefficients. -/
theorem bphp_refutation_of_balanced_unit {l : ℕ} {π : List (QLine (Fin (2^l) × Fin l))}
    {e : QEq (Fin (2^l) × Fin l)} (d : IsResLinQSynDerivation (BPHP (2^l) l) π)
    (unit : [e] ∈ π) (coeff : e.1 ≠ 0) :
    ∃ ρ, IsResLinQSynRefutation (BPHP (2^l+1) l) ρ ∧
      resLinQSize ρ ≤ 42*(2^l)^2*resLinQSize π + 1200*(2^l+1)^5 := by
  let n := 2^l
  let S := resLinQSize π
  have hn : 0 < n := Nat.two_pow_pos _
  let i : Fin (n+1) := ⟨0,by omega⟩
  let j : Fin (n+1) := ⟨1,by omega⟩
  have ne : i ≠ j := by simp [i,j]
  obtain ⟨c,hc,csize,scaled⟩ := bphp_scaled_pair_from_unit d unit coeff
  apply (bphp_refute_from_local_units i j ne (42*S+1102) ?_).imp
  · intro ρ h
    refine ⟨h.1,h.2.trans ?_⟩
    have power : 2^(2*l) = n^2 := by rw [Nat.mul_comm 2 l, pow_mul]
    have hl : l ≤ n := Nat.le_of_lt Nat.lt_two_pow_self
    rw [power]
    change n^2*(42*S+1102+(8*l+3)*(10+(n+1)*l+10*l)+10*(8*l+1)) ≤ 42*n^2*S + 1200*(n+1)^5
    calc
      _ ≤ n^2*(42*S+1102+(8*n+3)*(10+(n+1)*n+10*n)+10*(8*n+1)) := by gcongr
      _ ≤ _ := by ring_nf; omega
  · intro a h
    obtain ⟨k,diff⟩ := h
    obtain ⟨τ,dτ,member,price⟩ := scaled i j k ne
    let x := (i,k)
    let y := (j,k)
    have xy : x ≠ y := fun eq => ne (congrArg Prod.fst eq)
    obtain ⟨σ,dσ,hit,cost⟩ := qUnscaleBitEquality x y xy c hc τ dτ
      (fun K hK => (Set.mem_singleton_iff.mp hK) ▸ member)
    refine ⟨qBitDiff x y 0, σ ++ τ, dσ,List.mem_append_left _ hit,?_,?_,rfl,?_,
      fun eq => diff ((qBitDiff_holds a x y).mp eq)⟩
    · have add : resLinQSize (σ ++ τ) = resLinQSize σ + resLinQSize τ := by
        simp only [resLinQSize, List.map_append, List.sum_append]
        rfl
      dsimp [S]
      omega
    · intro v
      simp only [qBitDiff,litQEq,Pi.sub_apply]
      split_ifs <;> decide
    · intro v hvi hvj
      have vx : v ≠ x := fun h => hvi (congrArg Prod.fst h)
      have vy : v ≠ y := fun h => hvj (congrArg Prod.fst h)
      simp [qBitDiff,litQEq,vx,vy]

/-- A polynomial bound on the first nontrivial singleton at every positive
width disproves the posted lower bound, even if the singleton is chosen freely
at each width. -/
theorem polynomial_refutations_of_balanced_units (p : Polynomial ℕ)
    (units : ∀ l : ℕ, 0 < l → ∃ (π : List (QLine (Fin (2^l) × Fin l))) (e : QEq _),
      IsResLinQSynDerivation (BPHP (2^l) l) π ∧ [e] ∈ π ∧ e.1 ≠ 0 ∧ resLinQSize π ≤ p.eval (2^l)) :
    ∃ q : Polynomial ℕ, ∀ l : ℕ, ∃ ρ, IsResLinQSynRefutation (BPHP (2^l+1) l) ρ ∧
      resLinQSize ρ ≤ q.eval (2^l) := by
  refine ⟨42*Polynomial.X^2*p + 1200*(Polynomial.X+1)^5,?_⟩
  intro l
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat]
  cases l with
  | zero =>
    have input : (∅ : ProofComplexity.Clause (Fin (2^0+1) × Fin 0)) ∈ BPHP (2^0+1) 0 :=
      ⟨0,1,fun _ => false,by decide,by simp⟩
    exact ⟨[[]],⟨IsResLinQSynDerivation.ax ∅ .nil input (by simp),List.mem_cons_self⟩,by
      simp [resLinQSize]⟩
  | succ l =>
    obtain ⟨π,e,d,hm,nonzero,price⟩ := units (l+1) (Nat.succ_pos _)
    obtain ⟨ρ,ref,cost⟩ := bphp_refutation_of_balanced_unit d hm nonzero
    exact ⟨ρ,ref,cost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ price) _)⟩

end PEqualNP.Search
