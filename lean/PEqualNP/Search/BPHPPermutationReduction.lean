import PEqualNP.Search.Helpers.BinaryBalanceCut
import PEqualNP.Search.BPHPRowEquality
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A short syntactic derivation of the total sum of a permutation would give
a short integer refutation of binary pigeonhole. The source instance has
equally many pigeons and holes. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private theorem append_traces {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (ProofComplexity.Clause V)} {π τ : List (QLine V)}
    (d : IsResLinQSynDerivation F π) (base : IsResLinQSynDerivation F τ) :
    IsResLinQSynDerivation F (π ++ τ) := by
  induction d with
  | nil => exact base
  | ax C _ hc rep ih => exact ih.ax C hc rep
  | bool v _ ih => exact ih.bool v
  | res α β _ hC hD ih => exact ih.res α β (List.mem_append_left _ hC) (List.mem_append_left _ hD)
  | weaken _ hC sub ih => exact ih.weaken (List.mem_append_left _ hC) sub
  | simp _ hC ih => exact ih.simp (List.mem_append_left _ hC)

private theorem size_append {V : Type} [Fintype V] (π τ : List (QLine V)) :
    resLinQSize (π ++ τ) = resLinQSize π + resLinQSize τ := by simp [resLinQSize]

/-- Omit one row at a time from two copies of the same derivation. Their sum
equations differ by a single binary row equality. Eliminating this equality
costs polynomially many encoded bits in the number of holes. -/
theorem BPHPPermutationReduction (l : ℕ) (b : ℤ)
    {π : List (QLine (Fin (2^l) × Fin l))}
    (d : IsResLinQSynDerivation (BPHP (2^l) l) π)
    (total : [binaryTotal b] ∈ π) :
    ∃ ρ, IsResLinQSynRefutation (BPHP (2^l + 1) l) ρ ∧
      resLinQSize ρ ≤ 2 * resLinQSize π + 403 * (2^l + 1)^6 := by
  let n := 2^l
  have positive : 0 < n := Nat.two_pow_pos l
  let i : Fin (n+1) := ⟨0, by omega⟩
  let j : Fin (n+1) := ⟨1, by omega⟩
  have ne : i ≠ j := by simp [i, j]
  let copy (u : Fin (n+1)) := qRenameProof (rowEmbedding u.succAboveEmb l) π
  have valid (u : Fin (n+1)) : IsResLinQSynDerivation (BPHP (n+1) l) (copy u) :=
    bphp_rename_derivation u.succAboveEmb d
  have subtotal (u : Fin (n+1)) : [binaryTotalExcept u b] ∈ copy u := by
    have h := qRenameProof_mem (rowEmbedding u.succAboveEmb l) total
    simpa only [List.map_cons, List.map_nil, qRenameEq_binaryTotal] using h
  let τ := copy i ++ copy j
  have single : IsResLinQSynDerivation (BPHP (n+1) l) ([binaryRowEq i j] :: τ) :=
    binaryTotalExcept_cut i j b (append_traces (valid i) (valid j))
      (List.mem_append_left _ (subtotal i)) (List.mem_append_right _ (subtotal j))
  obtain ⟨σ, done, empty, cost⟩ := bphp_rowEquality_cut (l := l) i j ne _ single
    (fun K hm => (Set.mem_singleton_iff.mp hm) ▸ List.mem_cons_self)
  refine ⟨_, ⟨done, List.mem_append_left _ empty⟩, ?_⟩
  have costσ := cost.trans (rowEqualityCutCost_le l)
  have costτ : resLinQSize τ = 2 * resLinQSize π := by simp [τ, copy, size_append, two_mul]
  have row := binaryRowEq_singleton_size (l := l) i j
  have hl : l ≤ n := Nat.le_of_lt Nat.lt_two_pow_self
  have extra : 2 + (n+1)*l*n ≤ 3*(n+1)^6 := by
    calc
      _ ≤ 2 + (n+1)*n*n := by gcongr
      _ ≤ _ := by ring_nf; omega
  change resLinQSize (σ ++ ([[binaryRowEq i j]] ++ τ)) ≤ _
  rw [size_append, size_append, costτ]
  change resLinQSize σ ≤ 400 * (n+1)^6 at costσ
  change resLinQSize [[binaryRowEq i j]] ≤ 2 + (n+1)*l*n at row
  change _ ≤ 2 * resLinQSize π + 403*(n+1)^6
  omega

/-- A polynomial-size proof of the balanced sum for every width would provide
a polynomial-size refutation family, negating the exact L-alg-006 statement. -/
theorem polynomial_refutations_of_permutation_totals
    (p : Polynomial ℕ)
    (balanced : ∀ l : ℕ, ∃ (b : ℤ) (π : List (QLine (Fin (2^l) × Fin l))),
      IsResLinQSynDerivation (BPHP (2^l) l) π ∧ [binaryTotal b] ∈ π ∧ resLinQSize π ≤ p.eval (2^l)) :
    ∃ q : Polynomial ℕ, ∀ l : ℕ, ∃ ρ, IsResLinQSynRefutation (BPHP (2^l+1) l) ρ ∧
      resLinQSize ρ ≤ q.eval (2^l) := by
  refine ⟨2*p + 403*(Polynomial.X+1)^6, ?_⟩
  intro l
  obtain ⟨b, π, d, hm, small⟩ := balanced l
  obtain ⟨ρ, ref, sz⟩ := BPHPPermutationReduction l b d hm
  refine ⟨ρ, ref, sz.trans ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  omega

end PEqualNP.Search
