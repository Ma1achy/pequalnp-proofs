import PEqualNP.Search.Helpers.ParityTree

/-! A parity query may depend on the history of previous answers. Each query
adds one level to the tree and at most one equation to a leaf's blocking clause. -/
namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type}

/-- Unroll an adaptive strategy for the next `k` queries, starting with history `h`. -/
def adaptiveTree (ask : List Bool → Finset V) (out : List Bool → Bool) :
    ℕ → List Bool → ParityTree V
  | 0, h => .leaf (out h)
  | k + 1, h => .node (ask h) (adaptiveTree ask out k (h ++ [false]))
      (adaptiveTree ask out k (h ++ [true]))

theorem adaptiveTree_eval (ask : List Bool → Finset V) (out : List Bool → Bool)
    (k : ℕ) (h : List Bool) (a : V → Bool) :
    (adaptiveTree ask out k h).eval a =
      out ((List.range k).foldl (fun state _ =>
        state ++ [decide (Odd (((ask state).filter (fun v => a v = true)).card))]) h) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    by_cases odd : Odd ((ask h).filter (fun v => a v = true)).card <;>
      simp [adaptiveTree, ParityTree.eval, odd, ih]

theorem adaptiveTree_leaves (ask : List Bool → Finset V) (out : List Bool → Bool)
    (k : ℕ) (h : List Bool) : (adaptiveTree ask out k h).leaves = 2 ^ k := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih => simp [adaptiveTree, ParityTree.leaves, ih, pow_succ, Nat.mul_two]

namespace ParityTree

/-- Maximum number of queries along a root-to-leaf path. -/
def depth : ParityTree V → ℕ
  | .leaf _ => 0
  | .node _ lo hi => max lo.depth hi.depth + 1

theorem leaves_le_pow_depth (t : ParityTree V) : t.leaves ≤ 2 ^ t.depth := by
  induction t with
  | leaf _ => simp [leaves, depth]
  | node f lo hi hlo hhi =>
    have low := hlo.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left lo.depth hi.depth))
    have high := hhi.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right lo.depth hi.depth))
    simpa [leaves, depth, pow_succ, Nat.mul_two] using Nat.add_le_add low high

variable [DecidableEq V]

private theorem cellAt_card_le (t : ParityTree V) (G : LinClause V) {b : Bool}
    {B : LinClause V} (hb : (b, B) ∈ t.cellsAt G) : B.card ≤ t.depth + G.card := by
  induction t generalizing G with
  | leaf label =>
    simp only [cellsAt, List.mem_singleton, Prod.mk.injEq] at hb
    simp [hb.2, depth]
  | node f lo hi hlo hhi =>
    simp only [cellsAt, List.mem_append] at hb
    simp only [depth]
    rcases hb with hb | hb
    · have bound := hlo _ hb
      have := Finset.card_insert_le (f, true) G
      omega
    · have bound := hhi _ hb
      have := Finset.card_insert_le (f, false) G
      omega

theorem cell_card_le_depth (t : ParityTree V) (b : Bool) (B : LinClause V)
    (hc : (b, B) ∈ t.cells) : B.card ≤ t.depth := by
  simpa using cellAt_card_le t ∅ hc

end ParityTree

@[simp] theorem adaptiveTree_depth (ask : List Bool → Finset V) (out : List Bool → Bool)
    (k : ℕ) (h : List Bool) : (adaptiveTree ask out k h).depth = k := by
  induction k generalizing h <;> simp [adaptiveTree, ParityTree.depth, *]

variable [DecidableEq V]

theorem adaptiveTree_cell_width (ask : List Bool → Finset V) (out : List Bool → Bool)
    (k : ℕ) (h : List Bool) {b : Bool} {B : LinClause V}
    (hb : (b, B) ∈ (adaptiveTree ask out k h).cells) : B.card ≤ k := by
  simpa using (adaptiveTree ask out k h).cell_card_le_depth b B hb

end PEqualNP.Search.Helpers
