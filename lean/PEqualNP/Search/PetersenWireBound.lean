import PEqualNP.MetaComplexity.Helpers.Columns
import PEqualNP.Search.PetersenGateWitness

/-! Finite wire-index ranges for the nine-input circuit search.
At gate j, index n+j denotes false because only n+j wires exist at that point.
The final output has its own false index n+size. -/

namespace PEqualNP.Search.PetersenWireBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

private def capGates (n : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => clampGate n g :: capGates (n+1) gs

/-- Keep every opcode and argument position. Replace all unavailable operands
at a gate by the single first unavailable index at that gate. -/
def normalize (n : ℕ) (C : Circuit) : Circuit :=
  ⟨capGates n C.gates, min C.output (n+C.size)⟩

/-- Each gate and output may still refer to one unavailable (false) wire. -/
def Bounded (n : ℕ) (C : Circuit) : Prop :=
  C.output ≤ n+C.size ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i ≤ n+j

private theorem cap_length (n : ℕ) (gs : List Gate) : (capGates n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [capGates,ih]

@[simp] theorem normalize_size (n : ℕ) (C : Circuit) : (normalize n C).size = C.size :=
  cap_length n C.gates

private theorem cap_at (n : ℕ) (gs : List Gate) (j : ℕ) :
    (capGates n gs)[j]? = gs[j]?.map (clampGate (n+j)) := by
  induction gs generalizing n j with
  | nil => simp [capGates]
  | cons g gs ih =>
    cases j with
    | zero => simp [capGates]
    | succ j => simpa [capGates,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (n+1) j

@[simp] theorem normalize_op (n : ℕ) (C : Circuit) (j : ℕ) :
    (normalize n C).gates[j]?.map Gate.op = C.gates[j]?.map Gate.op := by
  change ((capGates n C.gates)[j]?).map _ = _
  rw [cap_at]
  cases C.gates[j]? <;> rfl

theorem normalize_bounded (n : ℕ) (C : Circuit) : Bounded n (normalize n C) := by
  refine ⟨by rw [normalize_size]; exact Nat.min_le_right _ _, ?_⟩
  intro j g hg
  change (capGates n C.gates)[j]? = some g at hg
  rw [cap_at] at hg
  obtain ⟨g₀,_,rfl⟩ := Option.map_eq_some_iff.mp hg
  intro i hi
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

theorem normalize_fanInTwo (n : ℕ) {C : Circuit} (h : FanInTwo C) : FanInTwo (normalize n C) := by
  intro g hg
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
  change (capGates n C.gates)[i]? = some g at hi
  rw [cap_at] at hi
  obtain ⟨g₀,hg₀,rfl⟩ := Option.map_eq_some_iff.mp hi
  have orig := h g₀ (List.mem_of_getElem? hg₀)
  exact ⟨orig.1, by simpa [clampGate] using orig.2⟩

private theorem cap_wires (gs : List Gate) (w : List Bool) :
    wiresFrom (capGates w.length gs) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let vals := g.inputs.map (fun i => w.getD i false)
    let next := w ++ [g.op.eval vals]
    have same : (clampGate w.length g).inputs.map (fun i => w.getD i false) = vals := by
      simp only [clampGate,List.map_map,vals]
      exact List.map_congr_left (fun i _ => getD_min le_rfl i)
    change wiresFrom (capGates (w.length+1) gs) (w ++ [g.op.eval _]) = wiresFrom gs next
    rw [same]
    simpa [next] using ih next

theorem normalize_wires (n : ℕ) (C : Circuit) (x : List Bool) (h : x.length = n) :
    (normalize n C).wires x = C.wires x := h ▸ cap_wires C.gates x

theorem normalize_eval (n : ℕ) (C : Circuit) (x : List Bool) (h : x.length = n) :
    (normalize n C).eval x = C.eval x := by
  unfold Circuit.eval
  rw [normalize_wires n C x h]
  apply getD_min
  change (wiresFrom C.gates x).length ≤ n + C.size
  rw [length_wiresFrom,h]; rfl

/-- The bounded finite search has precisely the same counterexamples as each
held statement. Instantiate second with AND for L-meta-2150, OR for L-meta-2152. -/
theorem bounded_witness_iff (second : GateOp) (s : ℕ) :
    let witness := fun C : Circuit => FanInTwo C ∧ C.size ≤ s ∧
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧
      circuitFun 9 C = PetersenGateWitness.edgeFunction ∧ C.gates[1]?.map Gate.op = some second
    (∃ C, witness C) ↔ ∃ C, Bounded 9 C ∧ witness C := by
  intro witness
  constructor
  · rintro ⟨C,basis,sz,first,result,op⟩
    refine ⟨normalize 9 C, normalize_bounded 9 C, normalize_fanInTwo 9 basis,
      by simpa using sz, ?_, ?_, by simpa using op⟩
    · intro x
      rw [normalize_wires 9 C _ (by simp)]
      exact first x
    · calc circuitFun 9 (normalize 9 C) = circuitFun 9 C :=
             funext (fun x => normalize_eval 9 C _ (by simp))
           _ = _ := result
  · rintro ⟨C,_,h⟩
    exact ⟨C,h⟩

/-- The negation posted in each held job is equivalent to a bounded
15-gate witness, including witnesses with unavailable input or output wires. -/
theorem desk_counterexample_iff (second : GateOp) :
    (¬ ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
      circuitFun 9 C = PetersenGateWitness.edgeFunction →
      C.gates[1]?.map Gate.op = some second → 16 ≤ C.size) ↔
    ∃ C : Circuit, Bounded 9 C ∧ FanInTwo C ∧ C.size ≤ 15 ∧
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧
      circuitFun 9 C = PetersenGateWitness.edgeFunction ∧ C.gates[1]?.map Gate.op = some second := by
  have bounded := bounded_witness_iff second 15
  dsimp only at bounded
  rw [← bounded]
  constructor
  · intro counter
    by_contra none
    apply counter
    intro C basis first target op
    by_contra! sz
    exact none ⟨C,basis,by omega,first,target,op⟩
  · rintro ⟨C,basis,sz,first,target,op⟩ allCircuits
    have := allCircuits C basis first target op
    omega

end PEqualNP.Search.PetersenWireBound
