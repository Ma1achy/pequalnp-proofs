import PEqualNP.Search.PetersenSingleRead2541
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-! A signed Petersen circuit with fourteen gates gives an AND-inverter graph
with at most thirteen binary AND gates. The compiler preserves sharing and
uses free inversions on both operands and on the output. -/

namespace PEqualNP.Search.PetersenAIG2541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Search.PetersenGateWitness (edgeFunction)
open PEqualNP.Search.PetersenSingleRead2541 (signed row)

abbrev Signal (n : ℕ) := (Fin n → Bool) → Bool

/-- Constants, raw inputs, earlier ANDs, and their complements have no extra cost. -/
inductive Available {n : ℕ} (gates : List (Signal n)) : Signal n → Prop where
  | const (b : Bool) : Available gates (fun _ => b)
  | input (i : Fin n) : Available gates (fun x => x i)
  | gate {f : Signal n} (h : f ∈ gates) : Available gates f
  | inv {f : Signal n} (h : Available gates f) : Available gates (fun x => !f x)

/-- Store a straight-line list of binary AND signals in reverse chronological order. -/
inductive Built {n : ℕ} : List (Signal n) → Prop where
  | nil : Built []
  | and {gates : List (Signal n)} {a b : Signal n} (prior : Built gates)
      (ha : Available gates a) (hb : Available gates b) :
      Built ((fun x => a x && b x) :: gates)

def HasAIG (n k : ℕ) (f : Signal n) : Prop :=
  ∃ gates : List (Signal n), Built gates ∧ gates.length ≤ k ∧ Available gates f

theorem Available.weaken {n : ℕ} {gates : List (Signal n)} {f : Signal n}
    (h : Available gates f) (w : Signal n) : Available (w :: gates) f := by
  induction h with
  | const => exact .const _
  | input => exact .input _
  | gate h => exact .gate (List.mem_cons_of_mem _ h)
  | inv _ ih => exact .inv ih

/-- Only a binary AND or OR costs an AIG gate. -/
def binaryCost (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | .and, [_,_] | .or, [_,_] => 1
  | _, _ => 0

private def evalGate {n : ℕ} (w : List (Signal n)) (g : Gate) : Signal n :=
  fun x => g.op.eval (g.inputs.map fun i => (w.getD i (fun _ => false)) x)

private def appendGate {n : ℕ} (w : List (Signal n)) (g : Gate) : List (Signal n) :=
  w ++ [evalGate w g]

private def Extension {n : ℕ} (gates : List (Signal n)) (f : Signal n) (cost : ℕ) : Prop :=
  ∃ D, Built D ∧ D.length ≤ gates.length + cost ∧
    (∀ s, Available gates s → Available D s) ∧ Available D f

private theorem free {n : ℕ} {gates : List (Signal n)} (hg : Built gates) {f : Signal n}
    (h : Available gates f) : Extension gates f 0 :=
  ⟨gates,hg,le_rfl,fun _ hs => hs,h⟩

private theorem meet {n : ℕ} {gates : List (Signal n)} (hg : Built gates) {a b : Signal n}
    (ha : Available gates a) (hb : Available gates b) :
    Extension gates (fun x => a x && b x) 1 :=
  ⟨_,.and hg ha hb,le_rfl,fun _ hs => hs.weaken _,.gate List.mem_cons_self⟩

private theorem join {n : ℕ} {gates : List (Signal n)} (hg : Built gates) {a b : Signal n}
    (ha : Available gates a) (hb : Available gates b) :
    Extension gates (fun x => a x || b x) 1 := by
  let f : Signal n := fun x => (!a x) && (!b x)
  refine ⟨f::gates,.and hg (.inv ha) (.inv hb),le_rfl,fun _ hs => hs.weaken f,?_⟩
  have eq : (fun x => a x || b x) = (fun x => !f x) := by funext x; simp [f]
  rw [eq]
  exact .inv (.gate List.mem_cons_self)

private theorem gate_extension {n : ℕ} {gates w : List (Signal n)} (hg : Built gates)
    (hw : ∀ s ∈ w, Available gates s) (g : Gate)
    (op : g.op = .and ∨ g.op = .or ∨ g.op = .not) (len : g.inputs.length ≤ 2) :
    Extension gates (evalGate w g) (binaryCost g) := by
  have avail (i : ℕ) : Available gates (w.getD i (fun _ => false)) := by
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact .const false
  rcases g with ⟨op',ls⟩
  change op' = .and ∨ op' = .or ∨ op' = .not at op
  change ls.length ≤ 2 at len
  rcases ls with _ | ⟨i, _ | ⟨j, _ | ⟨k,ks⟩⟩⟩
  · rcases op with rfl | rfl | rfl
    all_goals first | exact free hg (.const true) | exact free hg (.const false)
  · rcases op with rfl | rfl | rfl
    · convert free hg (avail i) using 1
      funext x
      simp [evalGate,GateOp.eval]
      rfl
    · convert free hg (avail i) using 1
      funext x
      simp [evalGate,GateOp.eval]
      rfl
    · exact free hg (.inv (avail i))
  · rcases op with rfl | rfl | rfl
    · convert meet hg (avail i) (avail j) using 1
      funext x
      simp [evalGate,GateOp.eval]
      rfl
    · convert join hg (avail i) (avail j) using 1
      funext x
      simp [evalGate,GateOp.eval]
      rfl
    · exact free hg (.inv (avail i))
  · simp at len

private theorem compile_seq {n : ℕ} (gs : List Gate)
    (fan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w D : List (Signal n)) (built : Built D) (avail : ∀ s ∈ w, Available D s) :
    ∃ D', Built D' ∧ D'.length ≤ D.length + (gs.map binaryCost).sum ∧
      ∀ s ∈ gs.foldl appendGate w, Available D' s := by
  induction gs generalizing w D with
  | nil => exact ⟨D,built,le_rfl,avail⟩
  | cons g gs ih =>
    obtain ⟨op,len⟩ := fan g List.mem_cons_self
    obtain ⟨D₁,b₁,l₁,keep,new⟩ := gate_extension built avail g op len
    have wa : ∀ s ∈ appendGate w g, Available D₁ s := by
      intro s hs
      rcases List.mem_append.1 hs with old | add
      · exact keep s (avail s old)
      · simpa using (List.mem_singleton.1 add ▸ new : Available D₁ s)
    obtain ⟨D₂,b₂,l₂,h₂⟩ := ih (fun h hh => fan h (List.mem_cons_of_mem _ hh))
      (appendGate w g) D₁ b₁ wa
    refine ⟨D₂,b₂,?_,h₂⟩
    simp only [List.map_cons,List.sum_cons]
    omega

private theorem eval_fold {n : ℕ} (gs : List Gate) (w : List (Signal n)) (x : Fin n → Bool) :
    (gs.foldl appendGate w).map (fun s => s x) =
      gs.foldl PEqualNP.MetaComplexity.LowMergeProof.step (w.map fun s => s x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    apply congrArg (fun t => gs.foldl PEqualNP.MetaComplexity.LowMergeProof.step t)
    simp only [appendGate,List.map_append,List.map_cons,List.map_nil,
      PEqualNP.MetaComplexity.LowMergeProof.step,evalGate,List.append_cancel_left_eq,
      List.cons.injEq,and_true]
    apply congrArg _
    apply List.map_congr_left
    intro i _
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa)]
      simp
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

/-- Compile any input preprocessing by available literals (or constants) and
any fan-in-two AND/OR/NOT circuit, counting only its binary AND/OR gates. -/
theorem compile_circuit {n m : ℕ} (C : Circuit) (fan : FanInTwo C) (inputs : Fin m → Signal n)
    (hlits : ∀ i, Available [] (inputs i)) :
    HasAIG n (C.gates.map binaryCost).sum (fun x => circuitFun m C (fun i => inputs i x)) := by
  let w := List.ofFn inputs
  obtain ⟨D,bd,size,hw⟩ := compile_seq C.gates (fun g hm => fan g hm) w [] .nil
    (by intro s hs; obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hs; exact hlits i)
  let done := C.gates.foldl appendGate w
  have out : Available D (done.getD C.output (fun _ => false)) := by
    by_cases h : C.output < done.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact .const false
  refine ⟨D,bd,by simpa using size,?_⟩
  convert out using 1
  funext x
  have eq := eval_fold C.gates w x
  have ix := congrArg (fun L : List Bool => L.getD C.output false) eq
  have e : (w.map fun s => s x) = List.ofFn (fun i => inputs i x) := by simp [w,List.map_ofFn,Function.comp_def]
  rw [e] at ix
  change _ = (C.wires _).getD C.output false at ix
  change (C.wires (List.ofFn (fun i => inputs i x))).getD C.output false = (done.getD C.output _) x
  rw [←ix]
  change (done.map _).getD C.output _ = _
  by_cases h : C.output < done.length
  · rw [List.getD_eq_getElem _ _ (by simpa),List.getD_eq_getElem _ _ h]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),List.getD_eq_default _ _ (by omega)]

private theorem cost_le_one (g : Gate) : binaryCost g ≤ 1 := by
  rcases g with ⟨op, _ | ⟨i, _ | ⟨j, _ | ⟨k,ls⟩⟩⟩⟩
  all_goals cases op <;> first | exact Nat.le_refl _ | exact Nat.zero_le _

private theorem sum_le_length (gs : List Gate) : (gs.map binaryCost).sum ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have := cost_le_one g
    omega

private theorem strict_of_not (gs : List Gate) (someNot : ∃ g ∈ gs, g.op = .not) :
    (gs.map binaryCost).sum < gs.length := by
  induction gs with
  | nil => simp at someNot
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    obtain ⟨h,hm,op⟩ := someNot
    rcases List.mem_cons.1 hm with rfl | hm
    · have zero : binaryCost h = 0 := by simp [binaryCost,op]
      have := sum_le_length gs
      omega
    · have := ih ⟨h,hm,op⟩
      have := cost_le_one g
      omega

/-- With vertex 1 on, switching the physical raw bit zero from false to true
turns the signed target from true to false. Any AND/OR/NOT circuit realizing
this therefore uses a NOT. -/
theorem signed_needs_not (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ a, circuitFun 9 C (signed true a) = edgeFunction a) :
    ∃ g ∈ C.gates, g.op = .not := by
  by_contra! none
  have mono : Monotone2 C := by
    intro g hm
    obtain ⟨op,len⟩ := fan g hm
    refine ⟨?_,len⟩
    rcases op with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (none g hm h).elim
  let a : Fin 9 → Bool := fun i => decide (i = 1)
  let b : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
  have order : ∀ i, signed true b i = true → signed true a i = true := by decide
  have high : PEqualNP.Outside.L_meta_1483.val C (signed true b) C.output = true := by
    change circuitFun 9 C _ = _
    rw [correct]
    decide
  have low : PEqualNP.Outside.L_meta_1483.val C (signed true a) C.output = false := by
    change circuitFun 9 C _ = _
    rw [correct]
    decide
  have yes := PEqualNP.Outside.L_meta_1483.acts_mono mono order C.output high
  rw [low] at yes
  contradiction

/-- A refutation of 13-AND feasibility rejects all 14-gate circuits for the
flipped sign, including circuits with multiple readers of zero. -/
theorem flipped_rejection_of_no_aig13 (no : ¬HasAIG 9 13 edgeFunction)
    (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14) :
    ∃ a : Fin 9 → Bool, circuitFun 9 C (signed true a) ≠ edgeFunction a := by
  by_contra! correct
  have nt := signed_needs_not C fan correct
  have cost := strict_of_not C.gates nt
  change C.gates.length ≤ 14 at size
  let input (i : Fin 9) : Signal 9 := fun a => signed true a i
  have av (i : Fin 9) : Available [] (input i) := by
    by_cases hi : i = 0
    · subst i
      simpa [input,signed] using (Available.inv (Available.input (gates := []) (0 : Fin 9)))
    · simpa [input,signed,hi] using (Available.input (gates := []) i)
  obtain ⟨D,ok,le,avout⟩ := compile_circuit C fan input av
  apply no
  refine ⟨D,ok,by omega,?_⟩
  have eq : (fun x => circuitFun 9 C (fun i => input i x)) = edgeFunction := funext correct
  rwa [eq] at avout

end PEqualNP.Search.PetersenAIG2541
