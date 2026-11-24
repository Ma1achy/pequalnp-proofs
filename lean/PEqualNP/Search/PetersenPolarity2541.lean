import PEqualNP.Search.PetersenSingleRead2541
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-! Transfer a signed-input circuit in L-meta-2541 to the unsigned problem
when every use of input zero is a NOT, a unary AND/OR, or an AND/OR with both
operands zero. A NOT ignores operands after its first. -/

namespace PEqualNP.Search.PetersenPolarity2541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.LowMergeProof
open PEqualNP.Search.PetersenSingleRead2541 (signed)
open PEqualNP.Search.PetersenGateWitness (edgeFunction)

/-- Every syntactic occurrence of zero is in a NOT or an identity on bit zero. -/
def SimpleReads (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .not ∨
    ((g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0] ∨ g.inputs = [0,0]))

private def atZero (op : GateOp) (tail : List ℕ) : Gate :=
  match op with
  | .not => ⟨.and,[0]⟩
  | .and | .or => ⟨.not,[0]⟩
  | _ => ⟨op,0::tail⟩

private def changeGate (g : Gate) : Gate :=
  match g.inputs with
  | 0::tail => atZero g.op tail
  | _ => g

/-- Keep the gate order and output index, changing the polarity at readers of bit zero. -/
def changeCircuit (C : Circuit) : Circuit := ⟨C.gates.map changeGate,C.output⟩

theorem change_size (C : Circuit) : (changeCircuit C).size = C.size := by
  simp [Circuit.size,changeCircuit]

private theorem reads_change (g : Gate) :
    (changeGate g).inputs.contains 0 = g.inputs.contains 0 := by
  rcases g with ⟨op, _ | ⟨_ | i,is⟩⟩
  all_goals cases op <;> rfl

theorem change_read_count (C : Circuit) :
    ((changeCircuit C).gates.filter (fun g => g.inputs.contains 0)).length =
      (C.gates.filter (fun g => g.inputs.contains 0)).length := by
  change ((C.gates.map changeGate).filter _).length = _
  rw [List.filter_map]
  simp only [List.length_map,Function.comp_def,reads_change]

theorem change_fanin {C : Circuit} (fan : FanInTwo C) : FanInTwo (changeCircuit C) := by
  intro h mem
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp mem
  have old := fan g hg
  rcases g with ⟨op,_ | ⟨_ | i,is⟩⟩
  all_goals first | exact old | cases op <;> (first | exact old | simp [changeGate,atZero])

private theorem change_gate_value (g : Gate)
    (allowed : 0 ∈ g.inputs → g.op = .not ∨
      ((g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0] ∨ g.inputs = [0,0])))
    (v : Bool) (tail : List Bool) :
    (changeGate g).op.eval ((changeGate g).inputs.map fun i => (v::tail).getD i false) =
      g.op.eval (g.inputs.map fun i => ((!v)::tail).getD i false) := by
  by_cases mem : 0 ∈ g.inputs
  · rcases allowed mem with hn | ⟨hop,hins⟩
    · rcases g with ⟨op, _ | ⟨_ | i,is⟩⟩ <;> change op = .not at hn <;> subst op
      all_goals simp [changeGate,atZero,GateOp.eval]
    · rcases g with ⟨op,ins⟩
      change op = .and ∨ op = .or at hop
      change ins = [0] ∨ ins = [0,0] at hins
      rcases hop with rfl | rfl <;> rcases hins with rfl | rfl
      all_goals simp [changeGate,atZero,GateOp.eval]
  · have old : changeGate g = g := by
      rcases g with ⟨op, _ | ⟨_ | i,is⟩⟩
      all_goals first | rfl | exact (mem List.mem_cons_self).elim
    rw [old]
    apply congrArg _
    apply List.map_congr_left
    rintro (_ | i) hi
    · exact (mem hi).elim
    · rfl

/-- Both evaluations have identical tails, even at intermediate gates and
when a gate reads an unavailable wire. -/
private theorem fold_change (gs : List Gate)
    (allowed : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .not ∨
      ((g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0] ∨ g.inputs = [0,0])))
    (v : Bool) (tail : List Bool) :
    ∃ t, (gs.map changeGate).foldl step (v::tail) = v::t ∧
      gs.foldl step ((!v)::tail) = (!v)::t := by
  induction gs generalizing tail with
  | nil => exact ⟨tail,rfl,rfl⟩
  | cons g gs ih =>
    have equal := change_gate_value g (allowed g List.mem_cons_self) v tail
    let bit := g.op.eval (g.inputs.map fun i => ((!v)::tail).getD i false)
    obtain ⟨t,ht,hb⟩ := ih (fun g hg => allowed g (List.mem_cons_of_mem _ hg)) (tail ++ [bit])
    refine ⟨t,?_,hb⟩
    change (gs.map changeGate).foldl step
      (v::(tail ++ [(changeGate g).op.eval ((changeGate g).inputs.map fun i => (v::tail).getD i false)])) = _
    rw [equal]
    exact ht

/-- All wire indices except zero agree with the original circuit on the
flipped input. The graph function and the bound on the circuit size are
unneeded for this transport. -/
theorem change_wire (C : Circuit) (allowed : SimpleReads C) (a : Fin 9 → Bool) (q : ℕ)
    (ne : q ≠ 0) : ((changeCircuit C).wires (List.ofFn a)).getD q false =
      (C.wires (List.ofFn (signed true a))).getD q false := by
  obtain ⟨t,ha,hb⟩ := fold_change C.gates allowed (a 0) (List.ofFn (fun j : Fin 8 => a j.succ))
  have sa : List.ofFn (signed true a) = (!a 0) :: List.ofFn (fun j : Fin 8 => a j.succ) := by
    rw [List.ofFn_succ]
    simp [signed]
  rw [sa,show List.ofFn a = _ from List.ofFn_succ,wires_eq,wires_eq]
  change ((C.gates.map changeGate).foldl step _).getD q false = _
  rw [ha,hb]
  cases q with
  | zero => contradiction
  | succ q => rfl

/-- The unsigned bound excludes the flipped sign whenever input zero has
only the permitted types of readers. The assumed unsigned bound may itself
be restricted to circuits with at most one syntactic reader. -/
theorem flipped_rejection_of_unsigned
    (unsigned : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      ∃ a : Fin 9 → Bool, circuitFun 9 D a ≠ edgeFunction a)
    (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14)
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (allowed : SimpleReads C) :
    ∃ a : Fin 9 → Bool, circuitFun 9 C (signed true a) ≠ edgeFunction a := by
  by_cases output : C.output = 0
  · let a : Fin 9 → Bool := fun _ => false
    refine ⟨a,?_⟩
    change (C.wires (List.ofFn (signed true a))).getD C.output false ≠ _
    rw [output,wires_input _ _ _ (by simp)]
    decide
  · obtain ⟨a,ha⟩ := unsigned (changeCircuit C) (change_fanin fan)
      ((change_size C).trans_le size) ((change_read_count C).trans_le single)
    refine ⟨a,?_⟩
    change (C.wires (List.ofFn (signed true a))).getD C.output false ≠ _
    rw [←change_wire C allowed a _ output]
    exact ha

/-- Use the unsigned premise with the explicit polarity parameter of L-meta-2848. -/
theorem flipped_rejection_of_2848
    (unsigned : ∀ (D : Circuit) (b : Bool), FanInTwo D → D.size ≤ 14 →
      (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 → b = false →
      ∃ a : Fin 9 → Bool, circuitFun 9 D (signed b a) ≠ edgeFunction a)
    (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14)
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (allowed : SimpleReads C) :
    ∃ a : Fin 9 → Bool, circuitFun 9 C (signed true a) ≠ edgeFunction a := by
  apply flipped_rejection_of_unsigned _ C fan size single allowed
  intro D hf hs hr
  obtain ⟨a,ha⟩ := unsigned D false hf hs hr rfl
  have e : signed false a = a := by
    funext i
    by_cases hi : i = 0 <;> simp [signed,hi]
  rw [e] at ha
  exact ⟨a,ha⟩

/-- When all syntactic readers are NOT, even a later ignored occurrence of
zero causes no obstruction to the transformation. -/
theorem simpleReads_of_not (C : Circuit)
    (notReaders : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .not) : SimpleReads C :=
  fun g hg hz => Or.inl (notReaders g hg hz)

end PEqualNP.Search.PetersenPolarity2541
