import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Search

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Appending one binary AND or OR makes the combination of two chosen wires
the output. Either index may read the default value, as in the circuit model. -/
theorem HeawoodFinalGate (n : ℕ) (d : Circuit) (hd : Monotone2 d)
    (op : GateOp) (hop : op = .and ∨ op = .or) (a b : ℕ) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ d.size + 1 ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        op.eval [(d.wires (List.ofFn x)).getD a false, (d.wires (List.ofFn x)).getD b false] := by
  let g : Gate := ⟨op, [a,b]⟩
  let C : Circuit := ⟨d.gates ++ [g], n+d.gates.length⟩
  refine ⟨C, ?_, by simp [C, Circuit.size], ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with old | last
    · exact hd f old
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨hop, Nat.le_refl 2⟩
  · intro x
    let w := d.wires (List.ofFn x)
    have len : w.length = n+d.gates.length := by
      simp [w, LowMergeProof.wires_length]
    change ((d.gates ++ [g]).foldl LowMergeProof.step (List.ofFn x)).getD (n+d.gates.length) false = _
    rw [List.foldl_append]
    change (w ++ [op.eval [w.getD a false, w.getD b false]]).getD (n+d.gates.length) false = _
    rw [←len, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl

end PEqualNP.Search
