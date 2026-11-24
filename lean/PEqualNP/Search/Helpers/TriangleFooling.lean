import PEqualNP.Defs.SearchCP
import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

/-- Two points in a triangle have at least one of their two crossings in the triangle. -/
private theorem triangle_contains_crossing {V : Type} {side : V → Bool}
    {T : Set (V → Bool)} (tri : IsTri side T) {x y : V → Bool} (hx : x ∈ T) (hy : y ∈ T) :
    mix side x y ∈ T ∨ mix side y x ∈ T := by
  obtain ⟨a, b, left, right, mem⟩ := tri
  rcases le_total (a x) (a y) with h | h
  · left
    apply (mem _).2
    rw [left, right]
    exact lt_of_le_of_lt h ((mem y).1 hy)
  · right
    apply (mem _).2
    rw [left, right]
    exact lt_of_le_of_lt h ((mem x).1 hx)

/-- If every crossing of distinct indexed points leaves `S`, each triangle contained in `S`
can cover at most one index. -/
theorem triangle_fooling_bound {V I : Type} [Fintype I] (side : V → Bool)
    (S : Set (V → Bool)) (points : I → V → Bool) (diagonal : ∀ i, points i ∈ S)
    (cross : ∀ i j, i ≠ j → mix side (points i) (points j) ∉ S)
    (cover : Finset (Set (V → Bool))) (tri : ∀ T ∈ cover, IsTri side T)
    (safe : ∀ T ∈ cover, T ⊆ S) (covers : ∀ x ∈ S, ∃ T ∈ cover, x ∈ T) :
    Fintype.card I ≤ cover.card := by
  classical
  have exists_triangle (i : I) : ∃ T : ↥cover, points i ∈ T.val := by
    obtain ⟨T, hT, hi⟩ := covers _ (diagonal i)
    exact ⟨⟨T, hT⟩, hi⟩
  choose triangle contains using exists_triangle
  have injective : Function.Injective triangle := by
    intro i j same
    by_contra distinct
    have hj : points j ∈ (triangle i).val := same ▸ contains j
    rcases triangle_contains_crossing (tri _ (triangle i).property) (contains i) hj with h | h
    · exact cross i j distinct (safe _ (triangle i).property h)
    · exact cross j i (Ne.symm distinct) (safe _ (triangle i).property h)
  simpa using Fintype.card_le_of_injective triangle injective

end PEqualNP.Search.Helpers
