import PEqualNP.Search.Helpers.ParityTree
import PEqualNP.Search.Helpers.ParitySeparation
import Mathlib.Data.Nat.Choose.Central

/-!
# Parity decision trees for a single integer equation

For a fixed assignment x in a constant-weight accepting leaf, the bits on
the true positions of x identify every other member: if y and z agree there,
the affine combination x XOR y XOR z still has all of x's true bits. It has
the same weight and must equal x. Thus a weight-k leaf has at most 2^k points.
-/

namespace PEqualNP.Search.Helpers.ParityMiddleSlice

open PEqualNP.ProofComplexity

private def ones {n : ℕ} (a : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i = true)

/-- A single integer equation expressing Hamming weight k. -/
def weightEquation (n k : ℕ) : QLine (Fin n) := [(fun _ => 1, (k : ℤ))]

private theorem holds_weight {n k : ℕ} (a : Fin n → Bool) :
    QLine.Holds a (weightEquation n k) ↔ (ones a).card = k := by
  simp [weightEquation, QLine.Holds, QEq.Holds, ones]

private noncomputable def cell {n : ℕ} (C : LinClause (Fin n)) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun a => ¬ LinClauseSat a C)

private theorem mem_cell {n : ℕ} {C : LinClause (Fin n)} {a : Fin n → Bool} :
    a ∈ cell C ↔ ¬ LinClauseSat a C := by classical simp [cell]

private theorem cell_bound {n k : ℕ} (C : LinClause (Fin n))
    (h : ∀ a ∈ cell C, (ones a).card = k) : (cell C).card ≤ 2 ^ k := by
  classical
  by_cases hn : (cell C).Nonempty
  · obtain ⟨x, hx⟩ := hn
    let key (a : Fin n → Bool) (i : ↥(ones x)) := a i
    have inj : Set.InjOn key (cell C : Set (Fin n → Bool)) := by
      intro y hy z hz eqkey
      let u := fun i => (x i ^^ y i) ^^ z i
      have hu : u ∈ cell C := mem_cell.mpr
        (ParitySeparation.falsifying_affine C x y z (mem_cell.mp hx) (mem_cell.mp hy) (mem_cell.mp hz))
      have inc : ones x ⊆ ones u := by
        intro i hi
        have same := congrFun eqkey ⟨i, hi⟩
        change y i = z i at same
        have xi := (Finset.mem_filter.mp hi).2
        simp [ones, u, same, xi]
      have ee := Finset.eq_of_subset_of_card_le inc ((h u hu).trans (h x hx).symm).le
      funext i
      have bit : x i = true ↔ u i = true := by
        simpa [ones] using (show i ∈ ones x ↔ i ∈ ones u by rw [ee])
      dsimp [u] at bit
      cases h1 : x i <;> cases h2 : y i <;> cases h3 : z i <;> simp_all
    have count := Finset.card_le_card_of_injOn (t := Finset.univ) key
      (fun _ _ => Finset.mem_univ _) inj
    simpa [h x hx] using count
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

theorem card_weight_slice (n k : ℕ) :
    (Finset.univ.filter (fun a : Fin n → Bool =>
      (Finset.univ.filter (fun i => a i = true)).card = k)).card = n.choose k := by
  classical
  let support (a : Fin n → Bool) := Finset.univ.filter (fun i => a i = true)
  calc
    _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
      apply Finset.card_bij (fun a _ => support a)
      · intro a ha
        exact Finset.mem_powersetCard_univ.mpr (Finset.mem_filter.mp ha).2
      · intro a _ b _ hab
        funext i
        have h : a i = true ↔ b i = true := by
          simpa [support] using (show i ∈ support a ↔ i ∈ support b from hab ▸ Iff.rfl)
        simpa using h
      · intro s hs
        let a (i : Fin n) := decide (i ∈ s)
        have ha : support a = s := by ext i; simp [support, a]
        refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ha⟩
        exact (congrArg Finset.card ha).trans (Finset.mem_powersetCard_univ.mp hs)
    _ = n.choose k := by simp [Finset.card_powersetCard]

/-- Every parity tree computing the weight-k equation needs enough leaves to
cover the binomial slice by sets of size at most 2^k. -/
theorem tree_weight_bound (n k : ℕ) (t : ParityTree (Fin n))
    (h : ∀ a, t.eval a = true ↔ QLine.Holds a (weightEquation n k)) :
    n.choose k ≤ t.leaves * 2 ^ k := by
  classical
  let slice := Finset.univ.filter (fun a : Fin n → Bool => (ones a).card = k)
  let accept := t.cells.toFinset.filter (fun p => p.1 = true)
  have cov : slice ⊆ accept.biUnion (fun p => cell p.2) := by
    intro a ha
    have atTrue := (h a).mpr ((holds_weight a).mpr (Finset.mem_filter.mp ha).2)
    obtain ⟨C, hc, hf⟩ := t.exists_mem_cells a
    rw [atTrue] at hc
    exact Finset.mem_biUnion.mpr ⟨(true, C),
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, rfl⟩, mem_cell.mpr hf⟩
  have budget : ∀ p ∈ accept, (cell p.2).card ≤ 2 ^ k := by
    intro p hp
    obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hp
    apply cell_bound
    intro a ha
    have he := t.eval_of_mem_cells a (List.mem_toFinset.mp hm) (mem_cell.mp ha)
    exact (holds_weight a).mp ((h a).mp (he.trans hb))
  have ha : accept.card ≤ t.leaves := by
    exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans_eq t.length_cells)
  calc n.choose k = slice.card := (card_weight_slice n k).symm
    _ ≤ (accept.biUnion (fun p => cell p.2)).card := Finset.card_le_card cov
    _ ≤ accept.card * 2 ^ k := Finset.card_biUnion_le_card_mul _ _ _ budget
    _ ≤ t.leaves * 2 ^ k := Nat.mul_le_mul_right _ ha

/-- Exponential lower bound for testing one equation on 2k bits. -/
theorem middle_slice_exponential (k : ℕ) (hk : 4 ≤ k) (t : ParityTree (Fin (2 * k)))
    (h : ∀ a, t.eval a = true ↔ QLine.Holds a (weightEquation (2 * k) k)) :
    2 ^ k < k * t.leaves := by
  have hc := (Nat.four_pow_lt_mul_centralBinom k hk).trans_le
    (Nat.mul_le_mul_left k (tree_weight_bound (2 * k) k t h))
  have h4 : 4 ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [h4, ← Nat.mul_assoc] at hc
  exact Nat.lt_of_mul_lt_mul_right hc

end PEqualNP.Search.Helpers.ParityMiddleSlice
