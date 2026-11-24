import Mathlib
import PEqualNP.Defs

namespace RawPartner
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def polarity (b : Bool) (x : Fin 9 → Bool) (j : Fin 9) := if j = 0 then b != x 0 else x j

def probe (j k : Fin 9) (v z : Bool) (i : Fin 9) :=
  if i = 0 then z else if i = j then v else decide (i = k)

set_option maxRecDepth 10000 in
theorem separates : ∀ (j : Fin 9), j ≠ 0 → ∀ (v : Bool), ∃ k : Fin 9,
    edge (probe j k v false) = false ∧ edge (probe j k v true) = true := by decide +kernel

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step {j : ℕ} (control : Bool) (g : Gate) (w w' : List Bool)
    (same : ∀ i, i ≠ 0 → w.getD i false = w'.getD i false)
    (fixed : w.getD j false = control) (j0 : j ≠ 0)
    (reader : 0 ∈ g.inputs → g.op = (if control then GateOp.or else GateOp.and) ∧ j ∈ g.inputs) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  by_cases r : 0 ∈ g.inputs
  · obtain ⟨op,mem⟩ := reader r
    have fixed' := (same j j0).symm.trans fixed
    have l : control ∈ g.inputs.map (fun i => w.getD i false) := fixed ▸ List.mem_map_of_mem mem
    have l' : control ∈ g.inputs.map (fun i => w'.getD i false) := fixed' ▸ List.mem_map_of_mem mem
    cases control with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at op
      rw [op]
      exact (List.all_eq_false.mpr ⟨false,l,by decide⟩).trans
        (List.all_eq_false.mpr ⟨false,l',by decide⟩).symm
    | true =>
      simp only [ite_true] at op
      rw [op]
      exact (List.any_eq_true.mpr ⟨true,l,rfl⟩).trans
        (List.any_eq_true.mpr ⟨true,l',rfl⟩).symm
  · congr 1
    exact List.map_congr_left (fun i hi => same i (fun e => r (e ▸ hi)))

theorem after (gs : List Gate) {j : ℕ} (j0 : j ≠ 0) (control : Bool)
    (readers : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = (if control then GateOp.or else GateOp.and) ∧ j ∈ g.inputs)
    (w w' : List Bool) (len : w.length = w'.length) (hj : j < w.length)
    (fixed : w.getD j false = control)
    (same : ∀ i, i ≠ 0 → w.getD i false = w'.getD i false) :
    ∀ i, i ≠ 0 → (gs.foldl appendGate w).getD i false = (gs.foldl appendGate w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact same
  | cons g gs ih =>
    have val := step control g w w' same fixed j0 (readers g (by simp))
    let a := g.op.eval (g.inputs.map fun i => w.getD i false)
    change ∀ i, i ≠ 0 → (gs.foldl appendGate (w ++ [a])).getD i false =
        (gs.foldl appendGate (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])).getD i false
    rw [← val]
    apply ih (fun h hh => readers h (by simp [hh])) _ _ (by simp [len]) (by simp; omega)
        ((List.getD_append _ _ _ _ hj).trans fixed)
    intro i hi
    by_cases h : i < w.length
    · have h' : i < w'.length := len ▸ h
      simpa only [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h'] using same i hi
    · have h' : w'.length ≤ i := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h',len]

theorem initialWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl appendGate (appendGate w g)).getD i false = _
    rw [ih _ (by simp [appendGate];omega)]
    exact List.getD_append _ _ _ _ hi

theorem getFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i,h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem impossible (C : Circuit) (b control : Bool) (j : Fin 9) (j0 : j ≠ 0)
    (readers : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = (if control then GateOp.or else GateOp.and) ∧ j.val ∈ g.inputs) :
    ∃ x, circuitFun 9 C (polarity b x) ≠ edge x := by
  by_contra! agrees
  by_cases out : C.output = 0
  · have raw (x : Fin 9 → Bool) : (b != x 0) = edge x := by
      have h := agrees x
      change (C.gates.foldl appendGate (List.ofFn (polarity b x))).getD C.output false = _ at h
      rw [out, initialWire C.gates _ 0 (by simp)] at h
      simpa [List.getD_eq_getElem?_getD,polarity] using h
    have empty := raw (fun _ => false)
    have pair := raw (fun i => decide (i = 1 ∨ i = 2))
    have hp : edge (fun i : Fin 9 => decide (i = 1 ∨ i = 2)) = true := by decide
    have he : edge (fun _ : Fin 9 => false) = false := rfl
    rw [hp] at pair
    rw [he] at empty
    cases b with
    | false => exact Bool.false_ne_true pair
    | true => exact Bool.false_ne_true empty.symm
  · obtain ⟨k,lo,hi⟩ := separates j j0 control
    let x := probe j k control false
    let y := probe j k control true
    have h := after C.gates (j:=j.val) (by simpa using j0) control readers
      (List.ofFn (polarity b x)) (List.ofFn (polarity b y)) (by simp) (by simp)
      (by rw [getFn _ _ j.isLt]; simp [polarity,x,probe,j0]) (by
        intro i hi
        by_cases h : i < 9
        · have nz : (⟨i,h⟩ : Fin 9) ≠ 0 := fun eq => hi (congrArg Fin.val eq)
          rw [getFn _ _ h, getFn _ _ h]; simp [polarity,x,y,probe,nz]
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte]) C.output out
    change circuitFun 9 C (polarity b x) = circuitFun 9 C (polarity b y) at h
    rw [agrees,agrees] at h
    exact Bool.false_ne_true (lo.symm.trans (h.trans hi))
end RawPartner

namespace RawPartner
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def repairNot (g : Gate) : Gate :=
  if 0 ∈ g.inputs ∧ g.inputs.head? = some 0 then ⟨GateOp.and, [0]⟩ else g

def NotOnly (g : Gate) : Prop := 0 ∈ g.inputs → g.op = GateOp.not

theorem repairedValue (g : Gate) (hg : NotOnly g) (w w' : List Bool)
    (other : ∀ i, i ≠ 0 → w.getD i false = w'.getD i false)
    (opp : w.getD 0 false = !(w'.getD 0 false)) :
    (repairNot g).op.eval ((repairNot g).inputs.map fun i => w.getD i false) =
    g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  by_cases has : 0 ∈ g.inputs
  · have op := hg has
    cases h : g.inputs with
    | nil => simp [h] at has
    | cons i tail =>
      by_cases zero : i = 0
      · subst i; simpa [repairNot,h,op,GateOp.eval] using opp
      · simpa [repairNot,h,op,GateOp.eval,zero] using other i zero
  · have eq : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => other i (fun e => has (e ▸ hi)))
    simpa [repairNot,has] using congrArg g.op.eval eq 

theorem repairedFold (gs : List Gate) (hg : ∀ g ∈ gs, NotOnly g)
    (w w' : List Bool) (len : w.length = w'.length) (pos : 0 < w.length)
    (opp : w.getD 0 false = !(w'.getD 0 false))
    (same : ∀ i, i ≠ 0 → w.getD i false = w'.getD i false) :
    ∀ i, i ≠ 0 → ((gs.map repairNot).foldl appendGate w).getD i false =
      (gs.foldl appendGate w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact same
  | cons g gs ih =>
    have val := repairedValue g (hg g (by simp)) w w' same opp
    let a := g.op.eval (g.inputs.map fun i => w'.getD i false)
    simp only [List.map_cons,List.foldl_cons,appendGate]
    rw [val]
    apply ih (fun g h => hg g (by simp [h])) (w ++ [a]) (w' ++ [a]) (by simp [len]) (by simp)
    · have pos' : 0 < w'.length := len ▸ pos
      rw [List.getD_append _ _ _ _ pos, List.getD_append _ _ _ _ pos']
      exact opp
    · intro i hn
      by_cases h : i < w.length
      · have h' : i < w'.length := len ▸ h
        rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h']
        exact same i hn
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]

theorem notOnlyTransfers (C : Circuit) (fan : FanInTwo C) (hs : C.size ≤ 14)
    (readers : ∀ g ∈ C.gates, NotOnly g)
    (agree : ∀ x, circuitFun 9 C (polarity true x) = edge x) : HasCircuitSize 9 edge 14 := by
  have out : C.output ≠ 0 := by
    intro e
    have h := agree (fun _ => false)
    change (C.gates.foldl appendGate (List.ofFn (polarity true (fun _ => false)))).getD C.output false = false at h
    rw [e,initialWire _ _ _ (by simp)] at h
    exact Bool.false_ne_true h.symm
  let D : Circuit := ⟨C.gates.map repairNot,C.output⟩
  refine ⟨D,?_,by simpa [D,Circuit.size] using hs,?_⟩
  · intro g mem
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp mem
    unfold repairNot
    split
    · simp
    · exact fan g hg
  · intro x
    rw [← agree x]
    apply repairedFold C.gates readers _ _ (by simp) (by simp) _ _ C.output out
    · rw [getFn _ _ (by decide),getFn _ _ (by decide)]
      simp [polarity]
    · intro i hi
      by_cases h : i < 9
      · rw [getFn _ _ h,getFn _ _ h]
        have ne : (⟨i,h⟩ : Fin 9) ≠ 0 := fun e => hi (congrArg Fin.val e)
        simp [polarity,ne]
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,↓reduceDIte]

end RawPartner
