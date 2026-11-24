import PEqualNP.Search.PetersenGateWitness
import PEqualNP.Outside.L_meta_1483

/-! A necessary condition for a circuit in L-meta-2541, for either sign of input zero.
A binary reader must pass changes of input zero on every pivotal assignment. Its
other operand therefore has a prescribed value on this family of 32 assignments. -/

namespace PEqualNP.Search.PetersenSingleRead2541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1483
open PEqualNP.Search.PetersenGateWitness (edgeFunction)

/-- Fix the eight other raw inputs and set input zero to `v`. -/
def row (z : Fin 8 → Bool) (v : Bool) : Fin 9 → Bool := Fin.cases v z

def signed (b : Bool) (a : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i = 0 then b != a 0 else a i

def Pivotal (z : Fin 8 → Bool) : Prop :=
  edgeFunction (row z false) = false ∧ edgeFunction (row z true) = true

private theorem signed_row (b : Bool) (z : Fin 8 → Bool) (v : Bool) :
    signed b (row z v) = row z (b != v) := by
  funext i
  refine Fin.cases (by simp [signed,row]) (fun j => ?_) i
  simp [signed,row]

/-- An assignment is pivotal exactly when the remaining induced graph has no
active edge and at least one neighbor of zero, namely 1, 4 or 5, is active. -/
theorem pivotal_iff (z : Fin 8 → Bool) : Pivotal z ↔
    edgeFunction (row z false) = false ∧ (z 0 || z 3 || z 4) = true := by
  have eval (d : Bool) : edgeFunction (row z d) =
      (d && z 0 || z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && d ||
       d && z 4 || z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 4 && z 6 ||
       z 5 && z 7 || z 7 && z 4) := rfl
  simp only [Pivotal,eval]
  generalize z 0 = a
  generalize z 1 = b
  generalize z 2 = c
  generalize z 3 = d
  generalize z 4 = e
  generalize z 5 = f
  generalize z 6 = g
  generalize z 7 = h
  revert a b c d e f g h
  decide

private theorem unique_pos {α : Type} (f : α → Bool) (xs : List α)
    (bound : (xs.filter f).length ≤ 1) {p r : ℕ} {g k : α}
    (hp : xs[p]? = some g) (hr : xs[r]? = some k) (fg : f g = true) (fk : f k = true) :
    p = r := by
  induction xs generalizing p r with
  | nil => simp at hp
  | cons i is ih =>
    by_cases fi : f i = true
    · have empty : is.filter f = [] := by
        simp [fi] at bound
        simpa using bound
      have head {j : ℕ} {a : α} (hj : (i::is)[j]? = some a) (ha : f a = true) : j = 0 := by
        cases j with
        | zero => rfl
        | succ j =>
          have m : a ∈ is := List.mem_of_getElem? (by simpa using hj : is[j]? = some a)
          have mem := List.mem_filter.mpr ⟨m,ha⟩
          rw [empty] at mem
          contradiction
      exact (head hp fg).trans (head hr fk).symm
    · cases p <;> cases r <;> simp_all
      exact ih hp hr

private theorem same_reader {C : Circuit}
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    {p : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (mem : 0 ∈ g.inputs)
    {j : ℕ} (hj : LNext 9 C 0 j) : j = 9+p := by
  obtain ⟨⟨_,r,k,hk,rfl,hm⟩,_⟩ := hj
  have eq := unique_pos (fun (g : Gate) => g.inputs.contains 0) C.gates single hk hg
    (by simpa using hm) (by simpa using mem)
  rw [eq]

private theorem output_not_zero {C : Circuit} {b : Bool}
    (correct : ∀ a, circuitFun 9 C (signed b a) = edgeFunction a) : C.output ≠ 0 := by
  intro ho
  let a : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
  let z : Fin 9 → Bool := fun _ => false
  have eq : val C (signed b a) C.output = val C (signed b z) C.output := by
    rw [ho,show (0:ℕ) = (0 : Fin 9).val from rfl,val_input,val_input]
    simp [signed,a,z]
  change circuitFun 9 C (signed b a) = circuitFun 9 C (signed b z) at eq
  rw [correct,correct] at eq
  exact (by decide : edgeFunction a ≠ edgeFunction z) eq

/-- A change in the output caused by bit zero traverses the one permitted reader.
Every earlier operand other than zero itself is insensitive to this change. -/
private theorem unique_reader_separates {C : Circuit} {p : ℕ} {g : Gate}
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (hg : C.gates[p]? = some g) (mem : 0 ∈ g.inputs) (out : C.output ≠ 0)
    (a b : Fin 9 → Bool) (agree : ∀ i : Fin 9, i ≠ 0 → a i = b i)
    (diff : val C a C.output ≠ val C b C.output) :
    val C a (9+p) ≠ val C b (9+p) ∧
    ∀ t ∈ g.inputs, t ≠ 0 → operand C a (9+p) t = operand C b (9+p) t := by
  obtain ⟨i,hi,path⟩ := difference C a b C.output .refl diff
  have eq : i = 0 := by by_contra h; exact hi (agree i h)
  subst i
  rcases path.cases_head with h | ⟨j,step,tail⟩
  · exact (out h.symm).elim
  have hj := same_reader single hg mem step.2
  subst j
  refine ⟨trace_start tail diff,?_⟩
  intro t hm ne
  by_cases earlier : t < 9+p
  · simp only [operand,earlier,↓reduceIte]
    by_contra d
    have live := live_before (show Next 9 C t (9+p) from ⟨earlier,p,g,hg,rfl,hm⟩) step.2.2
    obtain ⟨i,hi,ti⟩ := difference C a b t live d
    have eq : i = 0 := by by_contra h; exact hi (agree i h)
    subst i
    rcases ti.cases_head with h | ⟨j,st,tj⟩
    · exact ne h.symm
    · have ej := same_reader single hg mem st.2
      have hle := trace_le tj
      omega
  · simp [operand,earlier]

/-- A unique AND reader must see true on its other operand at every pivotal
assignment. A unique OR reader must see false. This holds for either input
polarity and for either setting of the signed bit itself. -/
theorem partner_on_pivotal (C : Circuit) (b neutral : Bool)
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (correct : ∀ a, circuitFun 9 C (signed b a) = edgeFunction a)
    {p : ℕ} {g : Gate} {t : ℕ} (hg : C.gates[p]? = some g) (ne : t ≠ 0)
    (ins : g.inputs = [0,t] ∨ g.inputs = [t,0])
    (op : g.op = if neutral then GateOp.and else GateOp.or)
    (z : Fin 8 → Bool) (piv : Pivotal z) (v : Bool) :
    operand C (row z v) (9+p) t = neutral := by
  have m0 : 0 ∈ g.inputs := by rcases ins with h | h <;> simp [h]
  have mt : t ∈ g.inputs := by rcases ins with h | h <;> simp [h]
  have diff : val C (row z false) C.output ≠ val C (row z true) C.output := by
    have a := correct (row z false)
    have c := correct (row z true)
    rw [signed_row,piv.1] at a
    rw [signed_row,piv.2] at c
    change circuitFun 9 C (row z false) ≠ circuitFun 9 C (row z true)
    cases b <;> simp_all
  have agrees (i : Fin 9) (hi : i ≠ 0) : row z false i = row z true i := by
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    rfl
  obtain ⟨changed,stable⟩ := unique_reader_separates single hg m0 (output_not_zero correct)
    (row z false) (row z true) agrees diff
  have same := stable t mt ne
  have bit (d : Bool) : operand C (row z d) (9+p) 0 = d := by
    rw [operand,ite_eq_left (by omega),show (0:ℕ) = (0:Fin 9).val from rfl,val_input]
    rfl
  rw [val_gate C _ hg,val_gate C _ hg] at changed
  cases neutral <;> rcases ins with inp | inp <;>
    simp [op,inp,GateOp.eval,bit,←same] at changed <;>
    cases v <;> simpa [←same] using changed


def bits (mask : ℕ) (i : Fin 8) := mask.testBit i.val

/-- The 32 pivotal assignments, encoded least significant bit first, starting
with graph vertex 1. -/
def pivotalMasks : List ℕ :=
  [1,5,8,9,10,16,17,18,20,21,24,25,26,40,42,48,50,52,56,58,
   65,69,72,73,104,129,136,137,138,193,200,201]

theorem exact_pivotal_masks : (List.range 256).filter (fun m =>
    !(edgeFunction (row (bits m) false)) && edgeFunction (row (bits m) true)) = pivotalMasks := by
  decide

def remainingEdge (i j : Fin 8) : Bool :=
  edgeFunction (row (fun k => decide (k = i ∨ k = j)) false)

/-- All four settings of a nonedge pair occur on pivotal assignments. For an
edge pair the settings 00, 01 and 10 occur. -/
theorem pivotal_pair_projection (i j : Fin 8) (ne : i ≠ j) (a b : Bool)
    (ok : a = false ∨ b = false ∨ remainingEdge i j = false) :
    ∃ z : Fin 8 → Bool, Pivotal z ∧ z i = a ∧ z j = b := by
  have cert : ∀ i j : Fin 8, i ≠ j → ∀ a b : Bool,
      a = false ∨ b = false ∨ remainingEdge i j = false →
      pivotalMasks.any (fun m => (bits m i == a) && (bits m j == b)) = true := by decide
  obtain ⟨m,hm,ok⟩ := List.any_eq_true.1 (cert i j ne a b ok)
  have hp := (List.mem_filter.1 (exact_pivotal_masks ▸ hm)).2
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  exact ⟨bits m,hp,by simpa using (Bool.and_eq_true_iff.mp ok).1,
    by simpa using (Bool.and_eq_true_iff.mp ok).2⟩

/-- A partner that depends on only two raw variables is constant, or the
variables form one of the nine remaining edges and the only exceptional
truth-table entry is 11. In the latter case the partner is the edge product
for an OR reader and its negation for an AND reader. -/
theorem classify_two_input_partner (i j : Fin 8) (ne : i ≠ j) (neutral : Bool)
    (h : Bool → Bool → Bool)
    (forced : ∀ z : Fin 8 → Bool, Pivotal z → h (z i) (z j) = neutral) :
    (∀ a b, h a b = neutral) ∨ (remainingEdge i j = true ∧
      ∀ a b : Bool, h a b = if a && b then !neutral else neutral) := by
  have H (a b : Bool) (ok : a = false ∨ b = false ∨ remainingEdge i j = false) :
      h a b = neutral := by
    obtain ⟨z,piv,ha,hb⟩ := pivotal_pair_projection i j ne a b ok
    simpa [ha,hb] using forced z piv
  by_cases last : h true true = neutral
  · left
    intro a b
    cases a <;> cases b <;> first | exact last | exact H _ _ (by simp)
  · right
    have edge : remainingEdge i j = true := by
      cases e : remainingEdge i j
      · exact (last (H true true (Or.inr (Or.inr e)))).elim
      · rfl
    refine ⟨edge,?_⟩
    intro a b
    cases a <;> cases b
    all_goals first | exact H _ _ (by simp) | simpa using Bool.eq_not.mpr last

/-- The two-input classification applied directly to a proposed unique reader
of the circuit. The two indices refer to vertices 1 through 8. -/
theorem partner_dichotomy (C : Circuit) (b neutral : Bool)
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (correct : ∀ a, circuitFun 9 C (signed b a) = edgeFunction a)
    {p : ℕ} {g : Gate} {t : ℕ} (hg : C.gates[p]? = some g) (ne : t ≠ 0)
    (ins : g.inputs = [0,t] ∨ g.inputs = [t,0])
    (op : g.op = if neutral then GateOp.and else GateOp.or)
    (i j : Fin 8) (ij : i ≠ j) (h : Bool → Bool → Bool)
    (depends : ∀ z : Fin 8 → Bool, operand C (row z false) (9+p) t = h (z i) (z j)) :
    (∀ a b, h a b = neutral) ∨ (remainingEdge i j = true ∧
      ∀ a b : Bool, h a b = if a && b then !neutral else neutral) := by
  apply classify_two_input_partner i j ij neutral h
  intro z piv
  rw [←depends]
  exact partner_on_pivotal C b neutral single correct hg ne ins op z piv false

/-- No other raw input can be the partner of the unique binary reader. -/
theorem partner_index_ge_nine (C : Circuit) (b neutral : Bool)
    (single : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (correct : ∀ a, circuitFun 9 C (signed b a) = edgeFunction a)
    {p : ℕ} {g : Gate} {t : ℕ} (hg : C.gates[p]? = some g) (ne : t ≠ 0)
    (ins : g.inputs = [0,t] ∨ g.inputs = [t,0])
    (op : g.op = if neutral then GateOp.and else GateOp.or) : 9 ≤ t := by
  by_contra! lt
  let i : Fin 8 := ⟨t-1,by omega⟩
  obtain ⟨j,hj⟩ := exists_ne i
  obtain ⟨z,piv,hi,_⟩ := pivotal_pair_projection i j (Ne.symm hj) (!neutral) false (Or.inr (Or.inl rfl))
  have h := partner_on_pivotal C b neutral single correct hg ne ins op z piv false
  have et : t = i.succ.val := by dsimp [i]; omega
  rw [operand,ite_eq_left (by omega),et,val_input] at h
  change z i = neutral at h
  rw [hi] at h
  cases neutral <;> contradiction

end PEqualNP.Search.PetersenSingleRead2541
