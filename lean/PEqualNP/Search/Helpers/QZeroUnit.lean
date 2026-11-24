import PEqualNP.Search.Helpers.QBuildAtPoint
import PEqualNP.Search.Helpers.QCoordinateCases

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

@[simp] theorem qZero_size : (0 : QEq V).size = 1 := by simp [QEq.size]

/-- A single available variable suffices to derive the universally true equation,
including when the input clause set is empty. -/
theorem qZeroUnit (v : V) : QCanAdd F ∅ [0] 380 := by
  have h := qCoordinateCases (F := F) (Γ := ∅) [v] (by simp) [0] 130
  have g : qWeight ([0] : QLine V) = 1 := by simp [qWeight]
  apply (by simpa only [List.length_cons,List.length_nil,g] using h)
  intro a ρ d _
  let L := [litQEq (v,a v)]
  have len : qWeight L ≤ 4 := by simpa [L,qWeight] using qLit_size_le v (a v)
  obtain ⟨σ,dσ,mem,cost⟩ := qBuildAtPoint (F := F) [v] (fun _ => !(a v)) L 0 (0 : QEq V)
    (by simp) (by simp) (by simp) (by simp [QEq.Holds])
    (by intro u hu; obtain rfl := List.mem_singleton.mp hu; simp [L]) d
  let T : QLine V := [litQEq (v,a v),0]
  have add : IsResLinQSynDerivation F (T::(σ++ρ)) := .weaken dσ (List.mem_append_left _ mem)
    (by intro x; simp [T,L,or_comm])
  refine ⟨T::σ,add,List.mem_cons_self,?_⟩
  have cap : qCost T ≤ 6 := by
    simpa [T,qCost,qWeight] using (show 1+((litQEq (v,a v)).size+1) ≤ 6 by have := qLit_size_le v (a v); omega)
  change qCost T + resLinQSize σ ≤ 130
  simp at cost
  omega

end PEqualNP.Search.Helpers
