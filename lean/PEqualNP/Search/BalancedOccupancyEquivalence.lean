import PEqualNP.Search.BPHPBalancedOccupancy
import PEqualNP.Search.BPHPRefuteFromOccupancy
import PEqualNP.Search.BPHPAffineHull
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private theorem zero_hole_occupied (l : ℕ) (a : Fin (2^l) × Fin l → Bool)
    (sat : Satisfies a (BPHP (2^l) l)) : QLine.Holds a (zeroOccupancyLine (2^l) l) := by
  let row (i : Fin (2^l)) (b : Fin l) := a (i,b)
  have bij : Function.Bijective row := Fintype.bijective_iff_injective_and_card row |>.mpr
    ⟨(bphp_sat_iff_rows_injective a).mp sat,by simp⟩
  obtain ⟨i,h⟩ := bij.surjective (fun _ => false)
  refine ⟨(binaryRowCoeff i,0),mem_zeroOccupancyLine i,Finset.sum_eq_zero ?_⟩
  rintro ⟨j,b⟩ _
  by_cases he : j=i
  · subst j
    have bit : a (i,b) = false := congrFun h b
    simp [binaryRowCoeff,bit]
  · simp [binaryRowCoeff,he]

private theorem zero_ref : IsResLinQSynRefutation (BPHP (2^0+1) 0) [[]] := by
  have axiomMem : (∅ : ProofComplexity.Clause (Fin (2^0+1) × Fin 0)) ∈ BPHP (2^0+1) 0 :=
    ⟨0,1,fun _ => false,by decide,by simp⟩
  exact ⟨.ax ∅ .nil axiomMem (by simp),List.mem_cons_self⟩

/-- L-alg-006 is equivalent to the superpolynomial cost of proving that a fixed
hole is occupied with equally many pigeons and holes. -/
theorem BalancedOccupancyEquivalence :
  let G := fun (l : ℕ) =>
    List.ofFn (fun i : Fin (2^l) => ((fun v : Fin (2^l) × Fin l =>
      if v.1 = i then (2 : ℤ)^v.2.val else 0), (0 : ℤ)))
  (∀ l a, PEqualNP.ProofComplexity.Satisfies a (PEqualNP.ProofComplexity.BPHP (2^l) l) →
    PEqualNP.Search.QLine.Holds a (G l)) ∧
  ((∀ p : Polynomial ℕ, ∃ l : ℕ, ∀ π : List (PEqualNP.Search.QLine (Fin (2^l+1) × Fin l)),
    PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2^l+1) l) π →
      p.eval (2^l) < PEqualNP.Search.resLinQSize π) ↔
   (∀ p : Polynomial ℕ, ∃ l : ℕ, 0 < l ∧ ∀ ρ : List (PEqualNP.Search.QLine (Fin (2^l) × Fin l)),
    PEqualNP.Search.IsResLinQSynDerivation (PEqualNP.ProofComplexity.BPHP (2^l) l) ρ →
      G l ∈ ρ → p.eval (2^l) < PEqualNP.Search.resLinQSize ρ)) := by
  dsimp only
  refine ⟨zero_hole_occupied,?_⟩
  constructor
  · intro hard p
    obtain ⟨l,lower⟩ := hard (4000*(Polynomial.X+1)^7*(p+1)+1)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one] at lower
    have hl : 0 < l := by
      by_contra! hz
      obtain rfl : l=0 := by omega
      have bound := lower _ zero_ref
      change _ < 1 at bound
      omega
    refine ⟨l,hl,?_⟩
    intro ρ d mem
    obtain ⟨π,ref,cost⟩ := bphp_refute_from_occupancy d mem
    have h := lower _ ref
    by_contra! small
    have small' := Nat.mul_le_mul_left (4000*(2^l+1)^7) (Nat.add_le_add_right small 1)
    omega
  · intro hard p
    obtain ⟨l,hl,lower⟩ := hard ((1000*(Polynomial.X+1)^4+2*p)*p)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one] at lower
    refine ⟨l,?_⟩
    intro π ref
    obtain ⟨ρ,d,mem,cost⟩ := BPHPBalancedOccupancy hl ref
    have h := lower _ d mem
    by_contra! small
    exact (not_lt_of_ge (cost.trans (Nat.mul_le_mul (Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 small) _) small))) h

end PEqualNP.Search
