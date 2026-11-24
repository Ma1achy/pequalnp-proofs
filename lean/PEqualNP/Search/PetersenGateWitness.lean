import PEqualNP.Defs.MetaComplexityMinimal

/-! Explicit circuits for the nine-input graph edge function appearing in
L-meta-2150 and L-meta-2152. Wire 9 realizes the prescribed first function.
Its value is unneeded by the five-star factorization. -/

namespace PEqualNP.Search.PetersenGateWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The twelve products in the order given by the desk statements. -/
def edgeFunction (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

/-- Factor the edge disjunction into stars with centers 0, 1, 3, 7, and 8. -/
def orSecond : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [10, 5]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [15, 8]⟩, ⟨.and, [3, 16]⟩,
    ⟨.or, [2, 5]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [6, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [22, 17]⟩,
    ⟨.or, [23, 19]⟩, ⟨.or, [24, 21]⟩], 25⟩

/-- Compute edge 01 at the second gate, then join it to the remaining five stars. -/
def andSecond : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [15, 8]⟩, ⟨.and, [3, 16]⟩,
    ⟨.or, [2, 5]⟩, ⟨.and, [7, 18]⟩, ⟨.or, [6, 5]⟩,
    ⟨.and, [8, 20]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [22, 14]⟩,
    ⟨.or, [23, 17]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [25, 21]⟩], 26⟩

/-- Each gate reads only original inputs and earlier gates; each output is present. -/
theorem validWireIndices :
    (orSecond.gates.zipIdx.all (fun (g, k) => g.inputs.all (fun w => decide (w < 9 + k)))) ∧
    orSecond.output < 9 + orSecond.size ∧
    (andSecond.gates.zipIdx.all (fun (g, k) => g.inputs.all (fun w => decide (w < 9 + k)))) ∧
    andSecond.output < 9 + andSecond.size := by decide

theorem orSecond_correct :
    orSecond.size = 17 ∧ FanInTwo orSecond ∧
    (∀ x : Fin 9 → Bool, (orSecond.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧
    Option.map Gate.op orSecond.gates[1]? = some GateOp.or ∧
    circuitFun 9 orSecond = edgeFunction := by
  have equations (x : Fin 9 → Bool) :
      (orSecond.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) ∧
      circuitFun 9 orSecond x = edgeFunction x := by
    change (orSecond.wires [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8]).getD 9 false = (x 0 || x 4) ∧
      orSecond.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] = edgeFunction x
    simp [orSecond, Circuit.eval, Circuit.wires, GateOp.eval, edgeFunction, List.getD,
      Bool.and_or_distrib_left]
    simp only [Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  refine ⟨rfl, ?_, fun x => (equations x).1, rfl, funext (fun x => (equations x).2)⟩
  intro g hg
  simp only [orSecond, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl), by decide⟩

theorem andSecond_correct :
    andSecond.size = 18 ∧ FanInTwo andSecond ∧
    (∀ x : Fin 9 → Bool, (andSecond.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧
    Option.map Gate.op andSecond.gates[1]? = some GateOp.and ∧
    circuitFun 9 andSecond = edgeFunction := by
  have equations (x : Fin 9 → Bool) :
      (andSecond.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) ∧
      circuitFun 9 andSecond x = edgeFunction x := by
    change (andSecond.wires [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8]).getD 9 false = (x 0 || x 4) ∧
      andSecond.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] = edgeFunction x
    simp [andSecond, Circuit.eval, Circuit.wires, GateOp.eval, edgeFunction, List.getD,
      Bool.and_or_distrib_left]
    simp only [Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  refine ⟨rfl, ?_, fun x => (equations x).1, rfl, funext (fun x => (equations x).2)⟩
  intro g hg
  simp only [andSecond, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl), by decide⟩

end PEqualNP.Search.PetersenGateWitness
