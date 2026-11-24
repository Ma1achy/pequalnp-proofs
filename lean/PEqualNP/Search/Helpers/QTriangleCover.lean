import PEqualNP.Search.Helpers.TriangleFooling
import PEqualNP.Search.Helpers.QPaddingCost

/-! A linear-size integer line whose falsifying assignments require exponentially
many triangles under a fixed variable split. Each equation states that both
players chose the same member of a pair. -/

namespace PEqualNP.Search.Helpers

abbrev ChoiceBit (k : ℕ) := (Fin k × Bool) × Bool

/-- The last coordinate identifies the player who owns the variable. -/
def choiceSide {k : ℕ} (v : ChoiceBit k) : Bool := v.2

def choiceEquation {k : ℕ} (u : Fin k × Bool) : QEq (ChoiceBit k) :=
  (fun v => (if v = (u,true) then 1 else 0) + (if v = (u,false) then 1 else 0), 2)

noncomputable def intersectLine (k : ℕ) : QLine (ChoiceBit k) :=
  (Finset.univ : Finset (Fin k × Bool)).toList.map choiceEquation

private theorem choiceEquation_iff {k : ℕ} (a : ChoiceBit k → Bool) (u : Fin k × Bool) :
    QEq.Holds a (choiceEquation u) ↔ a (u,true) = true ∧ a (u,false) = true := by
  unfold QEq.Holds choiceEquation
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases a (u,true) <;> cases a (u,false) <;> decide

private theorem intersectLine_iff {k : ℕ} (a : ChoiceBit k → Bool) :
    QLine.Holds a (intersectLine k) ↔ ∃ u, a (u,true) = true ∧ a (u,false) = true := by
  constructor
  · rintro ⟨e,he,h⟩
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp he
    exact ⟨u,(choiceEquation_iff a u).mp h⟩
  · rintro ⟨u,h⟩
    exact ⟨_, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
      (choiceEquation_iff a u).mpr h⟩

private theorem choiceEquation_size {k : ℕ} (u : Fin k × Bool) : (choiceEquation u).size = 5 := by
  have size (v : ChoiceBit k) : ((choiceEquation u).1 v).natAbs.size =
      (if v = (u,true) then 1 else 0) + (if v = (u,false) then 1 else 0) := by
    rcases v with ⟨x,b⟩
    cases b <;> by_cases same : x = u <;> simp [choiceEquation,same]
  unfold QEq.size
  simp only [size, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change 1 + (1 + 1) + Nat.size 2 = 5
  decide

theorem intersectLine_cost (k : ℕ) : qCost (intersectLine k) = 10*k + 1 := by
  simp [qCost, qWeight, intersectLine, Function.comp_def, choiceEquation_size, Nat.mul_comm]
  omega

private def diagonalChoice {k : ℕ} (w : Fin k → Bool) (v : ChoiceBit k) : Bool :=
  if v.2 then decide (v.1.2 = w v.1.1) else decide (v.1.2 ≠ w v.1.1)

/-- Any exact cover of the falsifying assignments of the 2k equations by
triangles has at least 2^k members, although the line has encoded cost 10k+1. -/
theorem intersectLine_triangle_lower (k : ℕ) (cover : Finset (Set (ChoiceBit k → Bool)))
    (tri : ∀ T ∈ cover, IsTri choiceSide T)
    (safe : ∀ T ∈ cover, ∀ a ∈ T, ¬ QLine.Holds a (intersectLine k))
    (covers : ∀ a, ¬ QLine.Holds a (intersectLine k) → ∃ T ∈ cover, a ∈ T) :
    2^k ≤ cover.card := by
  let S : Set (ChoiceBit k → Bool) := {a | ¬ QLine.Holds a (intersectLine k)}
  have diagonal (w : Fin k → Bool) : diagonalChoice w ∈ S := by
    intro h
    obtain ⟨u,yes,no⟩ := (intersectLine_iff _).mp h
    simp [diagonalChoice] at yes no
    exact no yes
  have cross (u w : Fin k → Bool) (ne : u ≠ w) : mix choiceSide (diagonalChoice u) (diagonalChoice w) ∉ S := by
    intro h
    apply h
    apply (intersectLine_iff _).mpr
    obtain ⟨i,hi⟩ : ∃ i, u i ≠ w i := Function.ne_iff.mp ne
    exact ⟨(i,u i), by simp [mix,choiceSide,diagonalChoice,hi]⟩
  simpa using triangle_fooling_bound choiceSide S diagonalChoice diagonal cross cover tri safe covers

end PEqualNP.Search.Helpers
