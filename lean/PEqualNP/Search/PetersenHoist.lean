import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Search.PetersenHoist

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def val (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) := w ++ [val w g]

def replace (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def bump (i : Nat) := if i < 9 then i else i + 1

def move (p i : Nat) := if i < p then bump i else if i = p then 9 else i

def hoist (pre : List Gate) (g : Gate) (post : List Gate) (o : Nat) : Circuit :=
  ⟨g :: (pre.map (replace bump) ++ post.map (replace (move (9+pre.length)))), move (9+pre.length) o⟩

theorem good_gate (f : Nat → Nat) (g : Gate)
    (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (replace f g).op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ (replace f g).inputs.length ≤ 2 := by
  simpa [replace] using h

theorem legal_hoist {pre post : List Gate} {g : Gate} {o : Nat} (h : FanInTwo ⟨pre ++ g :: post, o⟩) :
    FanInTwo (hoist pre g post o) := by
  intro q hq
  change q ∈ g :: _ ++ _ at hq
  rcases List.mem_cons.mp hq with e | hm
  · subst q
    exact h _ (by simp)
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
      exact good_gate _ _ (h _ (by simp [hp]))
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
      exact good_gate _ _ (h _ (by simp [hp]))

theorem size_hoist (pre post : List Gate) (g : Gate) (o : Nat) :
    (hoist pre g post o).size = (⟨pre ++ g :: post,o⟩ : Circuit).size := by
  simp [hoist,Circuit.size, Nat.add_assoc]

theorem val_replace {w v : List Bool} {f : Nat → Nat} (h : ∀ i, v.getD (f i) false = w.getD i false)
    (g : Gate) : val v (replace f g) = val w g := by
  simp only [val, replace, List.map_map, Function.comp_def, h]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,step]; omega

theorem keeps (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step]; omega),step,List.getD_append _ _ _ _ hi]

theorem raw_val (pre : List Gate) (g : Gate) (h : ∀ i ∈ g.inputs, i < 9)
    (w : List Bool) (len : w.length = 9) : val (pre.foldl step w) g = val w g := by
  unfold val
  apply congrArg g.op.eval
  exact List.map_congr_left fun i hi => keeps pre w (len ▸ h i hi)

theorem bump_input (w : List Bool) (hw : w.length = 9) (a : Bool) (i : Nat) :
    (w ++ [a]).getD (bump i) false = w.getD i false := by
  by_cases hi : i < 9
  · simp only [bump,hi,ite_true]
    exact List.getD_append _ _ _ _ (by omega)
  · simp only [bump,hi,ite_false]
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

theorem bump_run (gs : List Gate) {w v : List Bool} (hw : 9 ≤ w.length)
    (hv : v.length = w.length+1) (h : ∀ i, v.getD (bump i) false = w.getD i false) :
    ∀ i, ((gs.map (replace bump)).foldl step v).getD (bump i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (by simp [step]; omega) (by simp [step,hv])
    intro i
    change (v ++ [_]).getD _ _ = (w ++ [_]).getD _ _
    rw [val_replace h]
    by_cases hi : i < w.length
    · have hb : bump i < v.length := by unfold bump; split <;> omega
      rw [List.getD_append _ _ _ _ hb,List.getD_append _ _ _ _ hi,h]
    · have hb : bump i = i+1 := by simp [bump,show ¬ i < 9 by omega]
      rw [hb,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega

theorem move_run (gs : List Gate) (p : Nat) {w v : List Bool} (hp : p < w.length) (hp9 : 9 ≤ p)
    (hv : v.length = w.length) (h : ∀ i, v.getD (move p i) false = w.getD i false) :
    ∀ i, ((gs.map (replace (move p))).foldl step v).getD (move p i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (by simp [step]; omega) (by simp [step,hv])
    intro i
    change (v ++ [_]).getD _ _ = (w ++ [_]).getD _ _
    rw [val_replace h]
    by_cases hi : i < w.length
    · have hb : move p i < v.length := by unfold move bump; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ hb,List.getD_append _ _ _ _ hi,h]
    · have hb : move p i = i := by simp [move,show ¬ i<p by omega,show i≠p by omega]
      rw [hb,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hv]

theorem eval_hoist (pre post : List Gate) (g : Gate) (o : Nat)
    (raw : ∀ i ∈ g.inputs, i < 9) (x : List Bool) (hx : x.length = 9) :
    (hoist pre g post o).eval x = (⟨pre ++ g :: post,o⟩ : Circuit).eval x := by
  let w := pre.foldl step x
  let v := (pre.map (replace bump)).foldl step (step x g)
  let p := 9+pre.length
  have pw : w.length = p := by simp [w,p,run_length,hx]
  have pv : v.length = p+1 := by simp [v,p,run_length,step,hx]; omega
  have v9 : v.getD 9 false = val w g := by
    rw [raw_val pre g raw x hx]
    change ((pre.map _).foldl step (step x g)).getD 9 false = _
    rw [keeps _ _ (by simp [step,hx])]
    simp [step,hx]
  have pair : ∀ i, v.getD (move p i) false = (step w g).getD i false := by
    intro i
    by_cases hi : i < p
    · rw [move,ite_eq_left hi,step,List.getD_append _ _ _ _ (by omega : i < w.length)]
      exact bump_run pre (by omega : 9 ≤ x.length) (by simp) (bump_input x hx _) i
    by_cases he : i = p
    · subst i
      simpa [move,step,List.getD_append_right _ _ _ _ (by omega : w.length ≤ p),pw] using v9
    · rw [move,ite_eq_right hi,ite_eq_right he,List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by simp [step,pw]; omega)]
  change (((pre.map (replace bump)) ++ (post.map (replace (move p)))).foldl step
    (step x g)).getD (move p o) false = ((pre ++ g::post).foldl step x).getD o false
  rw [List.foldl_append,List.foldl_append,List.foldl_cons]
  exact move_run post p (by simp [step,pw]) (by simp [p]) (by simp [step,pw,pv]) pair o

theorem first_value (g : Gate) (tail : List Gate) (out : Nat) (x : List Bool)
    (hx : x.length = 9) : (Circuit.wires ⟨g::tail,out⟩ x).getD 9 false = val x g := by
  change (tail.foldl step (step x g)).getD 9 false = _
  rw [keeps _ _ (by simp [step,hx])]
  simp [step,hx]

def inp (π : Fin 9 → Fin 9) (i : Nat) : Nat :=
  if hi : i < 9 then (π ⟨i,hi⟩).val else i

def permC (π : Fin 9 → Fin 9) (C : Circuit) : Circuit :=
  ⟨C.gates.map (replace (inp π)), inp π C.output⟩

theorem legal_perm (π : Fin 9 → Fin 9) {C : Circuit} (h : FanInTwo C) : FanInTwo (permC π C) := by
  intro g hg
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
  exact good_gate _ _ (h _ hp)

theorem input_perm (π : Fin 9 → Fin 9) (x : Fin 9 → Bool) (i : Nat) :
    (List.ofFn x).getD (inp π i) false = (List.ofFn (x ∘ π)).getD i false := by
  by_cases hi : i < 9
  · simp only [inp,hi,dite_true,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
      Fin.is_lt,Option.getD_some,Function.comp_def]
  · rw [inp,dif_neg hi,List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

theorem perm_run (gs : List Gate) (π : Fin 9 → Fin 9) {w v : List Bool} (hw : 9 ≤ w.length)
    (hv : v.length = w.length) (h : ∀ i, v.getD (inp π i) false = w.getD i false) :
    ∀ i, ((gs.map (replace (inp π))).foldl step v).getD (inp π i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (by simp [step]; omega) (by simp [step,hv])
    intro i
    change (v ++ [_]).getD _ _ = (w ++ [_]).getD _ _
    rw [val_replace h]
    by_cases hi : i < w.length
    · have hb : inp π i < v.length := by unfold inp; split <;> first | omega | exact lt_of_lt_of_le (Fin.is_lt _) (by omega)
      rw [List.getD_append _ _ _ _ hb,List.getD_append _ _ _ _ hi,h]
    · have hb : inp π i = i := dif_neg (by omega)
      rw [hb,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hv]

theorem eval_perm (π : Fin 9 → Fin 9) (C : Circuit) (x : Fin 9 → Bool) :
    circuitFun 9 (permC π C) x = circuitFun 9 C (x ∘ π) :=
  perm_run C.gates π (by simp) (by simp) (input_perm π x) C.output

end PEqualNP.Search.PetersenHoist
