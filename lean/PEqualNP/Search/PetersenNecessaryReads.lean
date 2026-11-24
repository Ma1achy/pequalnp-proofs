import PEqualNP.Search.PetersenGateWitness
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-! For every pair of distinct graph inputs, fixing either input to either
Boolean value leaves the edge function sensitive to the other. This forces
any circuit whose first wire computes AND or OR on the pair to read both
raw inputs again. -/

namespace PEqualNP.Search.PetersenGateWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof

private theorem append_agree {a b : List Bool} {i : ℕ} (len : a.length = b.length)
    (agree : a.getD i false = b.getD i false) (v : Bool) :
    (a ++ [v]).getD i false = (b ++ [v]).getD i false := by
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (len ▸ hi), agree]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]

/-- Future gates cannot recover the only differing wire if none of them reads it. -/
private theorem fold_agree {r : ℕ} (gs : List Gate)
    (noRead : ∀ g ∈ gs, r ∉ g.inputs) (a b : List Bool) (len : a.length = b.length)
    (agree : ∀ i ≠ r, a.getD i false = b.getD i false) :
    ∀ j ≠ r, (gs.foldl step a).getD j false = (gs.foldl step b).getD j false := by
  induction gs generalizing a b with
  | nil => exact agree
  | cons g gs ih =>
    have mapEq : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact agree i (fun eq => noRead g List.mem_cons_self (eq ▸ hi))
    apply ih (fun g hg => noRead g (List.mem_cons_of_mem _ hg))
    · simp [step,len]
    · intro i hi
      simp only [step, mapEq]
      exact append_agree len (agree i hi) _

private theorem output_ge_nine (C : Circuit) (computed : circuitFun 9 C = edgeFunction) :
    9 ≤ C.output := by
  by_contra! h
  let q : Fin 9 := ⟨C.output,h⟩
  let a : Fin 9 → Bool := fun k => decide (k = q)
  have zero : ∀ q : Fin 9, edgeFunction (fun k => decide (k = q)) = false := by decide
  have ev := congrFun computed a
  change (C.wires (List.ofFn a)).getD C.output false = edgeFunction a at ev
  rw [wires_input _ _ _ (by simpa using h), zero q] at ev
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at ev
  simp only [h, ↓reduceDIte, Option.getD_some, a, q, decide_true, Bool.true_eq_false] at ev

private theorem masked_read (C : Circuit) (r : Fin 9) (out : 9 ≤ C.output)
    (a b : Fin 9 → Bool) (agree : ∀ j, j ≠ r → a j = b j)
    (masked : (C.wires (List.ofFn a)).getD 9 false = (C.wires (List.ofFn b)).getD 9 false)
    (diff : circuitFun 9 C a ≠ circuitFun 9 C b) :
    ∃ g ∈ C.gates.tail, r.val ∈ g.inputs := by
  by_contra! unread
  have start (i : ℕ) (hi : i ≠ r.val) :
      (List.ofFn a).getD i false = (List.ofFn b).getD i false := by
    by_cases h : i < 9
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn]
      simpa only [h, ↓reduceDIte, Option.getD_some] using
        agree (⟨i,h⟩ : Fin 9) (fun eq => hi (congrArg Fin.val eq))
    · rw [List.getD_eq_default, List.getD_eq_default] <;> simpa using Nat.le_of_not_gt h
  apply diff
  change (C.wires (List.ofFn a)).getD C.output false = _
  rcases C with ⟨gs, o⟩
  have out' : 9 ≤ o := out
  have ne : o ≠ r.val := by have := r.isLt; omega
  cases gs with
  | nil => exact start o ne
  | cons g gs =>
    let val (x : Fin 9 → Bool) := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
    have val_at (x : Fin 9 → Bool) :
        ((⟨g :: gs,o⟩ : Circuit).wires (List.ofFn x)).getD 9 false = val x := by
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _
      rw [fold_getD_lt _ _ _ (by simp [step])]
      simp [step, val]
    rw [val_at, val_at] at masked
    change (gs.foldl step (step (List.ofFn a) g)).getD o false =
      (gs.foldl step (step (List.ofFn b) g)).getD o false
    apply fold_agree gs unread _ _ (by simp [step]) _ o ne
    intro i hi
    change (List.ofFn a ++ [val a]).getD i false = (List.ofFn b ++ [val b]).getD i false
    rw [masked]
    exact append_agree (by simp) (start i hi) _

/-- The edge function changes when only `u` varies, while `v` is fixed. -/
def SensitiveWithFixedInput (u v : Fin 9) (fixed : Bool) : Prop :=
  ∃ a b : Fin 9 → Bool, a v = fixed ∧ b v = fixed ∧
    (∀ j, j ≠ u → a j = b j) ∧ edgeFunction a ≠ edgeFunction b

private def maskInput (u v w : Fin 9) (fixed value : Bool) : Fin 9 → Bool :=
  fun i => if i = u then value else if i = v then fixed else decide (i = w)

/-- A third index can activate a neighbor when the two selected indices
alone cannot distinguish the two values of `u`. -/
theorem sensitiveWithFixedInput (u v : Fin 9) (hne : u ≠ v) (fixed : Bool) :
    SensitiveWithFixedInput u v fixed := by
  have certificate : ∀ u v : Fin 9, u ≠ v → ∀ f : Bool, ∃ w : Fin 9,
      edgeFunction (maskInput u v w f false) ≠ edgeFunction (maskInput u v w f true) := by
    decide
  obtain ⟨w, hw⟩ := certificate u v hne fixed
  exact ⟨maskInput u v w fixed false, maskInput u v w fixed true,
    by simp [maskInput, Ne.symm hne], by simp [maskInput, Ne.symm hne],
    fun j hj => by simp [maskInput, hj], hw⟩

/-- If fixing `v` masks the first wire, the circuit must reread `u` after it. -/
theorem rereadOfMask (C : Circuit) (u v : Fin 9) (hne : u ≠ v) (fixed : Bool)
    (absorbs : ∀ x : Fin 9 → Bool, x v = fixed →
      (C.wires (List.ofFn x)).getD 9 false = fixed)
    (computed : circuitFun 9 C = edgeFunction) :
    ∃ g ∈ C.gates.tail, u.val ∈ g.inputs := by
  obtain ⟨a, b, ha, hb, agree, diff⟩ := sensitiveWithFixedInput u v hne fixed
  apply masked_read C u (output_ge_nine C computed) a b agree
  · rw [absorbs a ha, absorbs b hb]
  · rwa [computed]

/-- Every circuit whose first wire computes OR or AND on two distinct inputs
must read both raw inputs again. The two subsequent reads may share a gate. -/
theorem PetersenNecessaryReadsOfPair (C : Circuit) (u v : Fin 9) (hne : u ≠ v)
    (first : (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u || x v)) ∨
             (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u && x v)))
    (computed : circuitFun 9 C = edgeFunction) :
    (∃ g ∈ C.gates.tail, u.val ∈ g.inputs) ∧ (∃ g ∈ C.gates.tail, v.val ∈ g.inputs) := by
  rcases first with h | h
  · exact ⟨rereadOfMask C u v hne true (fun x hfix => by rw [h x]; simp [hfix]) computed,
      rereadOfMask C v u (Ne.symm hne) true (fun x hfix => by rw [h x]; simp [hfix]) computed⟩
  · exact ⟨rereadOfMask C u v hne false (fun x hfix => by rw [h x]; simp [hfix]) computed,
      rereadOfMask C v u (Ne.symm hne) false (fun x hfix => by rw [h x]; simp [hfix]) computed⟩

/-- When the first wire is a unary function of `v` (in particular, NOT),
every other raw input must be read after it. -/
theorem PetersenNecessaryReadsOfUnary (C : Circuit) (v : Fin 9) (op : Bool → Bool)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = op (x v))
    (computed : circuitFun 9 C = edgeFunction) :
    ∀ u : Fin 9, u ≠ v → ∃ g ∈ C.gates.tail, u.val ∈ g.inputs := by
  intro u hne
  obtain ⟨a, b, ha, hb, agree, diff⟩ := sensitiveWithFixedInput u v hne false
  apply masked_read C u (output_ge_nine C computed) a b agree
  · rw [first, first, ha, hb]
  · rwa [computed]

/-- The prescribed first wire `x₀ ∨ x₄` forces a later read of each endpoint. -/
theorem PetersenNecessaryReads (C : Circuit)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4))
    (computed : circuitFun 9 C = edgeFunction) :
    (∃ g ∈ C.gates.tail, 0 ∈ g.inputs) ∧ (∃ g ∈ C.gates.tail, 4 ∈ g.inputs) :=
  PetersenNecessaryReadsOfPair C 0 4 (by decide) (Or.inl first) computed

end PEqualNP.Search.PetersenGateWitness
