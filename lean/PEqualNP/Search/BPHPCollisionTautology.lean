import PEqualNP.Search.BPHPCollisionGuard
import PEqualNP.Search.Helpers.QPaddedDeduction
import PEqualNP.Search.BPHPRowEquality
import PEqualNP.Search.Helpers.BPHPEssential

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

private theorem qsyn_mono {V : Type} [Fintype V] [DecidableEq V]
    {F G : Set (PEqualNP.ProofComplexity.Clause V)} (sub : F ⊆ G) {π : List (QLine V)}
    (d : IsResLinQSynDerivation F π) : IsResLinQSynDerivation G π := by
  induction d with
  | nil => exact .nil
  | ax C _ h rep ih => exact .ax C ih (sub h) rep
  | bool v _ ih => exact .bool v ih
  | res α β _ h₁ h₂ ih => exact .res α β ih h₁ h₂
  | weaken _ h sub' ih => exact .weaken ih h sub'
  | simp _ h ih => exact .simp ih h

/-- A derivation of the disjunction of all pigeon collisions from Boolean
axioms alone becomes a bit-pigeonhole refutation at additive polynomial cost. -/
theorem bphp_collision_tautology_to_refutation {l : ℕ}
    {ρ : List (QLine (Fin (2^l+1) × Fin l))} (d : IsResLinQSynDerivation ∅ ρ)
    (h : collisionLine (2^l+1) l ∈ ρ) :
    ∃ π, IsResLinQSynRefutation (BPHP (2^l+1) l) π ∧
      resLinQSize π ≤ resLinQSize ρ + 500*(2^l+1)^10 := by
  let n := 2^l
  have hl : l ≤ n := Nat.lt_two_pow_self.le
  obtain ⟨σ,ref,cost⟩ := bphp_collisionLine_elimination (collisionLine (n+1) l)
    (fun _ he => mem_collisionLine.mp he) (qsyn_mono (Set.empty_subset _) d) h
  refine ⟨σ ++ ρ,ref,?_⟩
  have c := (rowEqualityContextCost_le l (qWeight (collisionLine (n+1) l))).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (collisionLine_weight (n+1) l)) _)
  have c' := cost.trans (Nat.mul_le_mul (collisionLine_length (n+1) l) c)
  have bound : resLinQSize σ ≤ 500*(n+1)^10 := by
    refine c'.trans ?_
    change (n+1)^2 * (400*(n+1)^6 + 21*(n+1)^3 * ((n+1)^2 * (1+(n+1)*l*(l+1)))) ≤ _
    calc
      _ ≤ (n+1)^2 * (400*(n+1)^6 + 21*(n+1)^3 * ((n+1)^2 * (1+(n+1)*n*(n+1)))) := by gcongr
      _ ≤ _ := by ring_nf; omega
  have size : resLinQSize (σ ++ ρ) = resLinQSize σ + resLinQSize ρ := by
    simp only [resLinQSize,List.map_append,List.sum_append]
    rfl
  rw [size,Nat.add_comm]
  exact Nat.add_le_add_left bound _

/-- From any integer refutation of bit pigeonhole, derive the disjunction of all
collisions using only Boolean axioms. The encoded cost is linear in the input
proof size and polynomial in the number of holes. -/
theorem bphp_refutation_to_collision_tautology {l : ℕ} (hl : 0 < l)
    {π : List (QLine (Fin (2^l+1) × Fin l))}
    (ref : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    ∃ ρ, IsResLinQSynDerivation ∅ ρ ∧ collisionLine (2^l+1) l ∈ ρ ∧
      resLinQSize ρ ≤ 1000*(2^l+1)^5 * resLinQSize π := by
  let n := 2^l
  have hl' : l ≤ n := Nat.lt_two_pow_self.le
  obtain ⟨ρ, d, h, cost⟩ := qPaddedDeductionCanonical
    (collisionLine (n+1) l) (collisionGuardCost (n+1) l) ref
    (fun _ hC => bphp_collision_guard hl hC)
  refine ⟨ρ, d, h, cost.trans ?_⟩
  have per : 2 + (collisionGuardCost (n+1) l + 3*qWeight (collisionLine (n+1) l)) ≤
      1000*(n+1)^5 := by
    obtain w := collisionLine_weight (n+1) l
    unfold collisionGuardCost
    change 2 + ((8*l+4)*(10 + (n+1)*l*n + 2*l*n + 8*l) +
      (1 + 8*l + (n+1)^2*(1+(n+1)*l*(l+1))) + 3*qWeight (collisionLine (n+1) l)) ≤ _
    calc
      _ ≤ 2 + ((8*n+4)*(10 + (n+1)*n*n + 2*n*n + 8*n) +
          (1 + 8*n + (n+1)^2*(1+(n+1)*n*(n+1))) +
          3*((n+1)^2*(1+(n+1)*n*(n+1)))) := by
            have : qWeight (collisionLine (n+1) l) ≤ (n+1)^2*(1+(n+1)*n*(n+1)) := w.trans (by gcongr)
            gcongr
      _ ≤ _ := by ring_nf; omega
  calc
    _ ≤ (2 + (collisionGuardCost (n+1) l + 3*qWeight (collisionLine (n+1) l))) * resLinQSize π := by
      rw [Nat.add_mul (2 : ℕ)]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (qlength_le_size π)) _
    _ ≤ _ := Nat.mul_le_mul_right _ per

/-- The reduction also costs polynomially in the number of encoded bits of the
source proof alone. Every refutation includes all collision clauses. -/
theorem bphp_collision_tautology_cubic {l : ℕ} (hl : 0 < l)
    {π : List (QLine (Fin (2^l+1) × Fin l))}
    (ref : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    ∃ ρ, IsResLinQSynDerivation ∅ ρ ∧ collisionLine (2^l+1) l ∈ ρ ∧
      resLinQSize ρ ≤ 64000*(resLinQSize π)^3 := by
  obtain ⟨ρ, d, h, cost⟩ := bphp_refutation_to_collision_tautology hl ref
  refine ⟨ρ,d,h,cost.trans ?_⟩
  let n := 2^l
  let S := resLinQSize π
  have hn : 0 < n := Nat.two_pow_pos l
  have pair : (n+1).choose 2 * 2 = (n+1)*n := by
    simpa using Nat.choose_succ_right_eq (n+1) 1
  have cubic : n^3 ≤ S := by
    calc
      n^3 = n*(n*n) := by ring
      _ ≤ (n+1)*(n*n) := Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = 2*((n+1).choose 2 * n) := by rw [← Nat.mul_assoc, ← pair]; ring
      _ ≤ (2*l+1)*((n+1).choose 2 * n) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ S := bphp_syn_size_lower_bound hl ref
  have powBound : (n+1)^5 ≤ (2*n)^6 :=
    (Nat.pow_le_pow_left (by omega : n+1 ≤ 2*n) 5).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  calc
    _ ≤ 1000*(2*n)^6*S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ powBound)
    _ = 64000*(n^3*n^3)*S := by ring
    _ ≤ 64000*(S*S)*S := by gcongr
    _ = _ := by ring

end PEqualNP.Search
