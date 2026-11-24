import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2541.Unary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def value (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun v g => v ++ [value v g]) w
def quiet (gs : List Gate) := ∀ g ∈ gs, 0 ∉ g.inputs
def skip (k i : ℕ) := if i < k then i else if i = k then 0 else i-1
def rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => change (run gs (w ++ [_])).length = _; rw [ih]; simp; omega

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run,List.foldl_append]

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem tail_agrees (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool) (hq : quiet gs)
    (hbefore : ∀ i < w.length, i ≠ 0 → f i < v.length)
    (hfuture : ∀ i, w.length ≤ i → f i = v.length + (i-w.length))
    (hval : ∀ i, i ≠ 0 → w.getD i false = v.getD (f i) false) :
    ∀ i, i ≠ 0 → (run gs w).getD i false = (run (gs.map (rename f)) v).getD (f i) false := by
  induction gs generalizing w v with
  | nil => exact hval
  | cons g gs ih =>
    have qg := hq g List.mem_cons_self
    have he : value w g = value v (rename f g) := by
      unfold value rename
      rw [List.map_map]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact hval i (fun e => qg (e ▸ hi))
    change ∀ i, i≠0 → (run gs (w++[value w g])).getD i false =
      (run (gs.map (rename f)) (v++[value v (rename f g)])).getD (f i) false
    apply ih _ _ (fun a ha => hq a (List.mem_cons_of_mem _ ha))
    · simp only [List.length_append,List.length_singleton]
      intro i hi hn
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h|rfl
      · exact Nat.lt_succ_of_lt (hbefore i h hn)
      · simp [hfuture _ le_rfl]
    · simp only [List.length_append,List.length_singleton]
      intro i hi
      rw [hfuture i (by omega)]
      omega
    · intro i hn
      by_cases h : i < w.length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (hbefore i h hn)]
        exact hval i hn
      · rcases eq_or_lt_of_le (Nat.le_of_not_gt h) with rfl | hi
        · rw [hfuture _ le_rfl]
          simpa using he
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by
            simp only [List.length_append,List.length_singleton]; rw [hfuture _ (by omega)]; omega)]

theorem pre_agrees (pre : List Gate) (w v : List Bool) (hq : quiet pre)
    (hlen : w.length = v.length)
    (hval : ∀ i, i≠0 → w.getD i false = v.getD i false) :
    ∀ i, i≠0 → (run pre w).getD i false = (run pre v).getD i false := by
  have hid (g : Gate) : rename id g = g := by cases g; simp [rename]
  have hm : rename id = id := funext hid
  simpa [hm] using tail_agrees id pre w v hq
    (fun i hi _ => by simpa [← hlen] using hi)
    (fun i hi => by simp only [id_eq,← hlen]; omega) hval

def erased (n : ℕ) (pre post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ post.map (rename (skip (n + pre.length))), skip (n + pre.length) o⟩

theorem erased_eval (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ) (hn : 0 < n)
    (ho : o ≠ 0) (hpre : quiet pre) (hpost : quiet post) (w v : List Bool)
    (hw : w.length = n) (hv : v.length = n) (hval : ∀ i, i≠0 → w.getD i false = v.getD i false)
    (hg : value (run pre w) g = v.getD 0 false) :
    (⟨pre ++ g::post,o⟩ : Circuit).eval w = (erased n pre post o).eval v := by
  let a := run pre w
  let b := run pre v
  let k := n + pre.length
  have ha : a.length=k := by simp [a,k,run_len,hw]
  have hb : b.length=k := by simp [b,k,run_len,hv]
  have hab := pre_agrees pre w v hpre (hw.trans hv.symm) hval
  have hg0 : value a g = b.getD 0 false := hg.trans ((run_keep pre v 0 (by omega)).symm)
  change (run (pre ++ g::post) w).getD o false = (run (pre ++ post.map (rename (skip k))) v).getD (skip k o) false
  rw [run_append,run_append]
  change (run post (a++[value a g])).getD o false = (run (post.map (rename (skip k))) b).getD (skip k o) false
  apply tail_agrees _ _ _ _ hpost _ _ _ _ ho
  · simp only [List.length_append,List.length_singleton,ha,hb]
    intro i hi _
    unfold skip
    split_ifs <;> dsimp [k] at * <;> omega
  · simp only [List.length_append,List.length_singleton,ha,hb]
    intro i hi
    simp only [skip,ite_eq_right (by omega : ¬ i < k),ite_eq_right (by omega : i ≠ k)]; omega
  · intro i hn0
    by_cases hi : i < k
    · rw [List.getD_append _ _ _ _ (by omega)]
      simpa [skip,hi] using hab i hn0
    · rcases eq_or_lt_of_le (Nat.le_of_not_gt hi) with rfl|hlt
      · simpa [skip,←ha] using hg0
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by
            simp only [skip,ite_eq_right (by omega : ¬ i<k),ite_eq_right (by omega : i≠k)]; omega)]

theorem erased_fan (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hfan : FanInTwo ⟨pre ++ g::post,o⟩) : FanInTwo (erased n pre post o) := by
  intro t ht
  change t ∈ pre ++ post.map _ at ht
  rcases List.mem_append.mp ht with h | h
  · exact hfan _ (List.mem_append_left _ h)
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have h := hfan a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    exact ⟨h.1,by simpa [rename] using h.2⟩

theorem erased_size (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ) :
    (erased n pre post o).size + 1 = (⟨pre++g::post,o⟩ : Circuit).size := by
  simp [erased,Circuit.size]; omega

def Literal (g : Gate) (p : Bool) : Prop :=
  (p = false ∧ (g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0] ∨ g.inputs = [0,0])) ∨
  (p = true ∧ g.op = .not ∧ ∃ l, g.inputs = 0::l)

theorem literal_value (g : Gate) (p : Bool) (h : Literal g p) (w : List Bool) :
    value w g = (p != w.getD 0 false) := by
  change g.op.eval (g.inputs.map _) = _
  rcases h with ⟨rfl,hop,hin⟩|⟨rfl,hop,l,hin⟩
  · rcases hop with hop|hop <;> rcases hin with hin|hin <;> cases hw : w[0]?.getD false <;>
      simp [hop,hin,GateOp.eval,List.getD_eq_getElem?_getD,hw]
  · cases hw : w[0]?.getD false <;> simp [hop,hin,GateOp.eval,List.getD_eq_getElem?_getD,hw]

theorem literal_mem (g : Gate) (p : Bool) (h : Literal g p) : 0 ∈ g.inputs := by
  rcases h with ⟨_,_,hin|hin⟩|⟨_,_,l,hin⟩ <;> simp [hin]

def readers (gs : List Gate) := (gs.filter fun g => g.inputs.contains 0).length

theorem quiet_iff (gs : List Gate) : quiet gs ↔ readers gs = 0 := by
  unfold quiet readers
  rw [List.length_eq_zero_iff,List.filter_eq_nil_iff]
  simp only [List.contains_iff_mem]

theorem unique_quiet {pre post : List Gate} {g : Gate} (hg : 0 ∈ g.inputs)
    (h : readers (pre ++ g::post) ≤ 1) : quiet pre ∧ quiet post := by
  have hread : g.inputs.contains 0 = true := List.contains_iff_mem.mpr hg
  unfold readers at h
  simp only [List.filter_append,List.filter_cons,hread,ite_true,List.length_append,List.length_cons] at h
  rw [quiet_iff,quiet_iff]
  unfold readers
  constructor <;> omega

def twist (b : Bool) (x : Fin 9 → Bool) := fun i : Fin 9 => if i = 0 then b != x 0 else x i

theorem twist_out {i : ℕ} (hi : i ≠ 0) (b t : Bool) (x : Fin 9 → Bool) :
    (List.ofFn (twist b x)).getD i false = (List.ofFn (twist t x)).getD i false := by
  by_cases hb : i < 9
  · have h : (⟨i,hb⟩ : Fin 9) ≠ 0 := by intro e; exact hi (congrArg Fin.val e)
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD]
    simp only [List.getElem?_ofFn,hb,Option.getD_some,dite_eq_left]
    simp [twist,h]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem twist_zero (b : Bool) (x : Fin 9 → Bool) :
    (List.ofFn (twist b x)).getD 0 false = (b != x 0) := by simp [twist,List.getD_eq_getElem?_getD]

theorem reachable_absorb (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hmem : 0 ∈ g.inputs) (hg : ∀ x : Fin 9 → Bool,
      value (run pre (List.ofFn (twist b x))) g = (p != (b != x 0))) (ho : o ≠ 0) (hr : readers (pre++g::post) ≤ 1) :
    ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
      circuitFun 9 (erased 9 pre post o) (twist (p != b) x) := by
  intro x
  obtain ⟨hp,hs⟩ := unique_quiet hmem hr
  apply erased_eval 9 pre post g o (by decide) ho hp hs _ _ (by simp) (by simp) (fun i hn => twist_out hn _ _ _)
  rw [hg x,twist_zero]
  cases p <;> cases b <;> cases x 0 <;> decide

theorem semantic_absorb (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hmem : 0 ∈ g.inputs) (hg : ∀ w : List Bool, w.length = 9 + pre.length →
      value w g = (p != w.getD 0 false)) (ho : o ≠ 0) (hr : readers (pre++g::post) ≤ 1) :
    ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
      circuitFun 9 (erased 9 pre post o) (twist (p != b) x) := by
  apply reachable_absorb _ _ _ _ _ _ hmem _ ho hr
  intro x
  rw [hg _ (by simp [run_len]),run_keep _ _ _ (by simp),twist_zero]

theorem literal_absorb (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hg : Literal g p) (ho : o ≠ 0) (hr : readers (pre++g::post) ≤ 1) :
    ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
      circuitFun 9 (erased 9 pre post o) (twist (p != b) x) :=
  semantic_absorb _ _ _ _ _ _ (literal_mem _ _ hg) (fun w _ => literal_value _ _ hg w) ho hr

theorem dangling_or_value (g : Gate) (j : ℕ) (w : List Bool) (hj : w.length ≤ j)
    (hop : g.op = .or) (hin : g.inputs = [0,j] ∨ g.inputs = [j,0]) :
    value w g = w.getD 0 false := by
  have hz := List.getD_eq_default w false hj
  rcases hin with hin|hin <;> change _ = _ <;>
    simp only [value,hop,hin,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,hz]
    <;> cases w.getD 0 false <;> decide

theorem dangling_or_reduction (pre post : List Gate) (g : Gate) (o j : ℕ) (b : Bool)
    (hj : 9 + pre.length ≤ j) (hop : g.op = .or)
    (hin : g.inputs = [0,j] ∨ g.inputs = [j,0]) (ho : o ≠ 0)
    (hf : FanInTwo ⟨pre++g::post,o⟩) (hs : (⟨pre++g::post,o⟩ : Circuit).size ≤ 14)
    (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
      ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) = circuitFun 9 D (twist b x) := by
  have hm : 0 ∈ g.inputs := by rcases hin with hin|hin <;> simp [hin]
  have he := semantic_absorb pre post g o b false hm (fun w hw => by
    rw [dangling_or_value _ _ _ (hw ▸ hj) hop hin]; simp) ho hr
  have hlen := erased_size 9 pre post g o
  exact ⟨_,erased_fan 9 pre post g o hf,by omega,by simpa using he⟩

theorem literal_reduction (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hg : Literal g p) (ho : o ≠ 0)
    (hf : FanInTwo ⟨pre++g::post,o⟩) (hs : (⟨pre++g::post,o⟩ : Circuit).size ≤ 14)
    (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
      ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) = circuitFun 9 D (twist (p != b) x) := by
  have hlen := erased_size 9 pre post g o
  exact ⟨_,erased_fan 9 pre post g o hf,by omega,literal_absorb pre post g o b p hg ho hr⟩



def flipped (p : Bool) : Gate := ⟨if p then .or else .not, [0]⟩

theorem flipped_literal (p : Bool) : Literal (flipped p) (!p) := by
  cases p <;> simp [Literal,flipped]

theorem flipped_readers (pre post : List Gate) (g : Gate) (p : Bool) (hg : 0 ∈ g.inputs) :
    readers (pre ++ flipped p :: post) = readers (pre ++ g :: post) := by
  have h := List.contains_iff_mem.mpr hg
  have h' : (flipped p).inputs.contains 0 = true := rfl
  simp only [readers,List.filter_append,List.filter_cons,h,h',ite_true,List.length_append,List.length_cons]

theorem flipped_fan (pre post : List Gate) (g : Gate) (o : ℕ) (p : Bool)
    (hf : FanInTwo ⟨pre ++ g :: post,o⟩) : FanInTwo ⟨pre ++ flipped p :: post,o⟩ := by
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact hf _ (List.mem_append_left _ h)
  rcases List.mem_cons.mp h with rfl | h
  · cases p <;> simp [flipped]
  · exact hf _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))

theorem reachable_twist_swap (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hmem : 0 ∈ g.inputs) (hg : ∀ x : Fin 9 → Bool,
      value (run pre (List.ofFn (twist b x))) g = (p != (b != x 0))) (ho : o ≠ 0) (hf : FanInTwo ⟨pre++g::post,o⟩)
    (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
        circuitFun 9 D (twist (!b) x) := by
  have hr' : readers (pre ++ flipped p :: post) ≤ 1 := by rwa [flipped_readers _ _ _ _ hmem]
  refine ⟨⟨pre ++ flipped p :: post,o⟩,flipped_fan _ _ _ _ _ hf,by simp [Circuit.size],hr',?_⟩
  intro x
  rw [reachable_absorb _ _ _ _ _ _ hmem hg ho hr, literal_absorb _ _ _ _ _ _ (flipped_literal p) ho hr']
  have e : ((!p) != (!b)) = (p != b) := by cases p <;> cases b <;> decide
  rw [e]

theorem semantic_twist_swap (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hmem : 0 ∈ g.inputs) (hg : ∀ w : List Bool, w.length = 9 + pre.length →
      value w g = (p != w.getD 0 false)) (ho : o ≠ 0) (hf : FanInTwo ⟨pre++g::post,o⟩)
    (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
        circuitFun 9 D (twist (!b) x) := by
  apply reachable_twist_swap pre post g o b p hmem _ ho hf hr
  intro x
  rw [hg _ (by simp [run_len]),run_keep _ _ _ (by simp),twist_zero]

theorem neutral_operand_value (g : Gate) (j : ℕ) (w : List Bool)
    (hin : g.inputs = [0,j] ∨ g.inputs = [j,0])
    (hs : (g.op = .and ∧ w.getD j false = true) ∨ (g.op = .or ∧ w.getD j false = false)) :
    value w g = w.getD 0 false := by
  rcases hs with ⟨h,hv⟩ | ⟨h,hv⟩ <;> rcases hin with hin | hin <;>
    simp only [value,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
      List.any_cons,List.any_nil,id_eq,hv] <;> cases w.getD 0 false <;> decide

theorem neutral_operand_twist_swap (pre post : List Gate) (g : Gate) (o j : ℕ) (b : Bool)
    (hin : g.inputs = [0,j] ∨ g.inputs = [j,0])
    (hs : (g.op = .and ∧ ∀ x, (run pre (List.ofFn (twist b x))).getD j false = true) ∨
          (g.op = .or ∧ ∀ x, (run pre (List.ofFn (twist b x))).getD j false = false))
    (ho : o ≠ 0) (hf : FanInTwo ⟨pre++g::post,o⟩) (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
        circuitFun 9 D (twist (!b) x) := by
  have hm : 0 ∈ g.inputs := by rcases hin with hin|hin <;> simp [hin]
  apply reachable_twist_swap _ _ _ _ _ false hm _ ho hf hr
  intro x
  have neutral : (g.op = .and ∧ (run pre (List.ofFn (twist b x))).getD j false = true) ∨
      (g.op = .or ∧ (run pre (List.ofFn (twist b x))).getD j false = false) :=
    hs.imp (fun h => ⟨h.1,h.2 x⟩) (fun h => ⟨h.1,h.2 x⟩)
  rw [neutral_operand_value _ _ _ hin neutral,run_keep _ _ _ (by simp),twist_zero]
  simp

theorem literal_twist_swap (pre post : List Gate) (g : Gate) (o : ℕ) (b p : Bool)
    (hg : Literal g p) (ho : o ≠ 0) (hf : FanInTwo ⟨pre++g::post,o⟩)
    (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
        circuitFun 9 D (twist (!b) x) :=
  semantic_twist_swap _ _ _ _ _ _ (literal_mem _ _ hg) (fun w _ => literal_value _ _ hg w) ho hf hr

theorem dangling_or_twist_swap (pre post : List Gate) (g : Gate) (o j : ℕ) (b : Bool)
    (hj : 9 + pre.length ≤ j) (hop : g.op = .or)
    (hin : g.inputs = [0,j] ∨ g.inputs = [j,0]) (ho : o ≠ 0)
    (hf : FanInTwo ⟨pre++g::post,o⟩) (hr : readers (pre++g::post) ≤ 1) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist b x) =
        circuitFun 9 D (twist (!b) x) := by
  have hm : 0 ∈ g.inputs := by rcases hin with hin|hin <;> simp [hin]
  apply semantic_twist_swap _ _ _ _ _ false hm _ ho hf hr
  intro w hw
  rw [dangling_or_value _ _ _ (hw ▸ hj) hop hin]
  simp

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

theorem projection_gap (gs : List Gate) (b : Bool) :
    ∃ x, circuitFun 9 ⟨gs,0⟩ (twist b x) ≠ target x := by
  let x : Fin 9 → Bool := fun i => if i = 0 then b else decide (i = 1 ∨ i = 2)
  refine ⟨x,?_⟩
  change (run gs (List.ofFn (twist b x))).getD 0 false ≠ target x
  rw [run_keep _ _ _ (by simp),twist_zero]
  cases b <;> decide

theorem signed_binary_reader (pre post : List Gate) (g : Gate) (o : ℕ)
    (hOrd : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → readers D.gates ≤ 1 →
      ¬ (∀ x, circuitFun 9 D (twist false x) = target x))
    (hMatch : ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist true x) = target x)
    (hf : FanInTwo ⟨pre++g::post,o⟩) (hs : (⟨pre++g::post,o⟩ : Circuit).size ≤ 14)
    (hr : readers (pre++g::post) ≤ 1) (hm : 0 ∈ g.inputs) (ho : o ≠ 0)
    (hhead : g.op = .not → g.inputs.headD 0 = 0) :
    ∃ j : ℕ, j ≠ 0 ∧ (g.op = .and ∨ g.op = .or) ∧
      (g.inputs = [0,j] ∨ g.inputs = [j,0]) ∧ (g.op = .or → j < 9 + pre.length) := by
  have noswap : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size = (⟨pre++g::post,o⟩ : Circuit).size ∧
      readers D.gates ≤ 1 ∧ ∀ x, circuitFun 9 ⟨pre++g::post,o⟩ (twist true x) =
        circuitFun 9 D (twist (!true) x) := by
    rintro ⟨D,hF,hS,hR,hE⟩
    exact hOrd D hF (hS ▸ hs) hR (fun x => (hE x).symm.trans (hMatch x))
  have nlit (p : Bool) : ¬ Literal g p := fun h =>
    noswap (literal_twist_swap pre post g o true p h ho hf hr)
  have ng : g.op ≠ .not := by
    intro en
    have hd := hhead en
    cases el : g.inputs with
    | nil => simp [el] at hm
    | cons i l =>
      have hi : i = 0 := by simpa [el] using hd
      exact nlit true (Or.inr ⟨rfl,en,l,hi ▸ el⟩)
  obtain ⟨ops,len⟩ := hf g (List.mem_append_right _ (List.mem_cons_self : g ∈ g :: post))
  have hbin : g.op = .and ∨ g.op = .or := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    tauto
  have h1 : g.inputs ≠ [0] := fun el => nlit false (Or.inl ⟨rfl,hbin,Or.inl el⟩)
  have h2 : g.inputs ≠ [0,0] := fun el => nlit false (Or.inl ⟨rfl,hbin,Or.inr el⟩)
  suffices pair : ∃ j : ℕ, j ≠ 0 ∧ (g.inputs = [0,j] ∨ g.inputs = [j,0]) by
    obtain ⟨j,hj,hin⟩ := pair
    refine ⟨j,hj,hbin,hin,?_⟩
    intro hop
    by_contra! he
    exact noswap (dangling_or_twist_swap pre post g o j true he hop hin ho hf hr)
  cases el : g.inputs with
  | nil => simp [el] at hm
  | cons i l =>
    cases l with
    | nil =>
      have hi : i = 0 := by simpa [el,eq_comm] using hm
      exact (h1 (hi ▸ el)).elim
    | cons j l =>
      cases l with
      | cons k ks => simp [el] at len
      | nil =>
        have hij : i=0 ∨ j=0 := by simpa [el,eq_comm] using hm
        rcases hij with rfl | rfl
        · exact ⟨j,fun ej => h2 (ej ▸ el),Or.inl rfl⟩
        · exact ⟨i,fun ei => h2 (ei ▸ el),Or.inr rfl⟩

end PEqualNP.Outside.L_meta_2541.Unary

namespace PEqualNP.Outside.L_meta_2541.Polarity

open PEqualNP.CircuitLowerBounds

def target (x : Fin 9 → Bool) : Bool := (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))

def set0 (b : Bool) (x : Fin 9 → Bool) (i : Fin 9) := if i = 0 then b else x i

def Pivot (x : Fin 9 → Bool) : Prop := target (set0 false x) ≠ target (set0 true x)
instance (x : Fin 9 → Bool) : Decidable (Pivot x) := inferInstanceAs (Decidable (_ ≠ _))

def edge (i j : Fin 8) : Bool := target (fun k => decide (k = i.succ ∨ k = j.succ))

def representative (i j : Fin 8) (a b : Bool) : Fin 9 → Bool :=
  let words : List ℕ := [16, 0, 0, 2, 16, 20, 2, 0, 16, 40, 2, 10, 32, 16, 2, 18, 16, 32, 2, 34, 16, 80, 2, 0, 16, 144, 2, 130, 16, 272, 2, 258, 16, 2, 20, 0, 2, 0, 0, 20, 2, 10, 20, 0, 2, 16, 36, 20, 2, 32, 20, 36, 2, 80, 20, 84, 2, 130, 20, 0, 2, 258, 20, 276, 16, 2, 40, 10, 2, 20, 10, 0, 2, 0, 0, 10, 2, 16, 10, 0, 2, 32, 10, 40, 2, 80, 10, 104, 2, 130, 10, 138, 2, 258, 10, 0, 32, 2, 16, 18, 2, 36, 16, 20, 2, 10, 16, 0, 2, 0, 0, 16, 2, 32, 16, 48, 2, 96, 16, 80, 2, 130, 16, 144, 2, 258, 16, 272, 16, 2, 32, 34, 2, 20, 32, 36, 2, 10, 32, 40, 2, 16, 32, 48, 2, 0, 0, 32, 2, 80, 32, 96, 2, 130, 32, 0, 2, 258, 32, 0, 16, 2, 80, 0, 2, 20, 80, 84, 2, 10, 80, 104, 2, 16, 96, 80, 2, 32, 80, 96, 2, 0, 0, 80, 2, 130, 80, 208, 2, 258, 80, 0, 16, 2, 144, 130, 2, 20, 130, 0, 2, 10, 130, 138, 2, 16, 130, 144, 2, 32, 130, 0, 2, 80, 130, 208, 2, 0, 0, 130, 2, 258, 130, 386, 16, 2, 272, 258, 2, 20, 258, 276, 2, 10, 258, 0, 2, 16, 258, 272, 2, 32, 258, 0, 2, 80, 258, 0, 2, 130, 258, 386, 2, 0, 0, 258]
  let word := words.getD (4*(8*i.val+j.val)+2*a.toNat+b.toNat) 0
  fun k => word.testBit k.val

theorem projections : ∀ (i j : Fin 8) (a b : Bool), (i = j → a = b) →
    (i ≠ j → edge i j = true → a = true → b = false) →
    Pivot (representative i j a b) ∧ representative i j a b i.succ = a ∧
      representative i j a b j.succ = b := by decide +kernel

theorem projection (i : Fin 8) (a : Bool) : ∃ z, Pivot z ∧ z i.succ = a := by
  obtain ⟨hz,ha,_⟩ := projections i i a a (by simp) (by simp)
  exact ⟨_,hz,ha⟩

def Matches (C : Circuit) (flip : Bool) :=
  ∀ x : Fin 9 → Bool, C.eval (List.ofFn (set0 (flip != x 0) x)) = target x

def runGate (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
def push (w : List Bool) (g : Gate) : List Bool := w ++ [runGate g w]
def Avoids (gs : List Gate) := ∀ g ∈ gs, 0 ∉ g.inputs
def Agree (w v : List Bool) := w.length = v.length ∧ ∀ i : ℕ, i ≠ 0 → w.getD i false = v.getD i false

theorem add_agree {w v : List Bool} (h : Agree w v) {a b : Bool} (e : a=b) :
    Agree (w++[a]) (v++[b]) := by
  subst b
  have hl := h.1
  refine ⟨by simp [h.1],?_⟩
  intro i hi
  by_cases hn : i < w.length
  · rw [List.getD_append _ _ _ _ hn,List.getD_append _ _ _ _ (by omega : i<v.length)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
        List.getD_append_right _ _ _ _ (by omega : v.length ≤ i),h.1]

theorem fold_agree {gs : List Gate} {w v : List Bool} (hn : Avoids gs) (h : Agree w v) :
    Agree (gs.foldl push w) (gs.foldl push v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun q hq => hn q (by simp [hq]))
    apply add_agree h
    apply congrArg g.op.eval
    exact List.map_congr_left (fun i hi => h.2 i (fun e => hn g (by simp) (e ▸ hi)))

theorem preserved {w : List Bool} (i : ℕ) (hi : i < w.length) (gs : List Gate) :
    (gs.foldl push w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (by simp [push]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem input_agree (a b : Bool) (z : Fin 9 → Bool) :
    Agree (List.ofFn (set0 a z)) (List.ofFn (set0 b z)) := by
  refine ⟨by simp,?_⟩
  intro j hn
  by_cases hj : j < 9
  · have hne : (⟨j,hj⟩ : Fin 9) ≠ 0 := fun e => hn (congrArg Fin.val e)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn, hj, dite_true, Option.getD_some,
      set0, hne, ite_false]
  · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hj),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hj)]

theorem output_ne {C : Circuit} {flip : Bool} (hm : Matches C flip) : C.output ≠ 0 := by
  intro hz
  have hx (z : Fin 9 → Bool) : (flip != z 0) = target z := by
    have h := hm z
    change (C.gates.foldl push _).getD C.output false = _ at h
    rw [hz,preserved 0 (by simp)] at h
    simpa [set0] using h
  have h0 := hx (fun _ => false)
  have h1 := hx (fun i => decide (i=1 ∨ i=2))
  cases flip <;> simp [target] at h0 h1

theorem overwritten (a : Bool) (z : Fin 9 → Bool) (flip : Bool) :
    set0 (flip != (set0 a z 0)) (set0 a z) = set0 (flip != a) z := by
  funext i
  by_cases h : i=0 <;> simp [set0,h]

theorem must_switch {pre post : List Gate} {g : Gate} {o : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hm : Matches ⟨pre++g::post,o⟩ flip)
    {z : Fin 9 → Bool} (hs : Pivot z) :
    runGate g (pre.foldl push (List.ofFn (set0 (flip != false) z))) ≠
    runGate g (pre.foldl push (List.ofFn (set0 (flip != true) z))) := by
  intro h
  have ho : o ≠ 0 := output_ne hm
  have h1 := hm (set0 false z)
  have h2 := hm (set0 true z)
  rw [overwritten] at h1 h2
  change ((pre++g::post).foldl push _).getD o false = _ at h1 h2
  rw [List.foldl_append,List.foldl_cons] at h1 h2
  apply hs
  rw [← h1,← h2]
  exact (fold_agree hpost (add_agree (fold_agree hpre (input_agree _ _ _)) h)).2 _ ho

def side (pre : List Gate) (j : ℕ) (z : Fin 9 → Bool) :=
  (pre.foldl push (List.ofFn (set0 false z))).getD j false

theorem side_read {pre : List Gate} (hn : Avoids pre) {j : ℕ} (hj : j≠0)
    (z : Fin 9 → Bool) (a : Bool) :
    (pre.foldl push (List.ofFn (set0 a z))).getD j false = side pre j z :=
  (fold_agree hn (input_agree _ _ z)).2 j hj

theorem and_block {g : Gate} {w : List Bool} {j : ℕ} (hop : g.op = .and)
    (hj : j∈g.inputs) (hz : w.getD j false=false) : runGate g w = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [runGate,hop,GateOp.eval,List.all_eq_true] at h
  have hh := h _ (List.mem_map_of_mem hj)
  change w.getD j false = true at hh
  rw [hz] at hh
  contradiction

theorem or_block {g : Gate} {w : List Bool} {j : ℕ} (hop : g.op = .or)
    (hj : j∈g.inputs) (hz : w.getD j false=true) : runGate g w = true := by
  simp only [runGate,hop,GateOp.eval,List.any_eq_true]
  exact ⟨w.getD j false,List.mem_map_of_mem hj,hz⟩

theorem neutral_on_pivot {pre post : List Gate} {g : Gate} {o j : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hm : Matches ⟨pre++g::post,o⟩ flip)
    (hj : j∈g.inputs) (hpos : j≠0) {z : Fin 9 → Bool} (hs : Pivot z) :
    (g.op = .and → side pre j z = true) ∧ (g.op = .or → side pre j z = false) := by
  have hdiff := must_switch hpre hpost hm hs
  have ha := side_read hpre hpos z (flip != false)
  have hb := side_read hpre hpos z (flip != true)
  constructor
  · intro hop
    cases hv : side pre j z with
    | false => exact (hdiff ((and_block hop hj (ha.trans hv)).trans (and_block hop hj (hb.trans hv)).symm)).elim
    | true => rfl
  · intro hop
    cases hv : side pre j z with
    | false => rfl
    | true => exact (hdiff ((or_block hop hj (ha.trans hv)).trans (or_block hop hj (hb.trans hv)).symm)).elim

theorem two_coordinate_constraint {pre post : List Gate} {g : Gate} {o j : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hm : Matches ⟨pre++g::post,o⟩ flip)
    (hj : j∈g.inputs) (hpos : j≠0) (i k : Fin 8) (f : Bool → Bool → Bool)
    (hmodel : ∀ z, side pre j z = f (z i.succ) (z k.succ))
    (a b : Bool) (heq : i = k → a=b) (hedge : i ≠ k → edge i k = true → a = true → b = false) :
    (g.op = .and → f a b = true) ∧ (g.op = .or → f a b = false) := by
  obtain ⟨hp,ha,hb⟩ := projections i k a b heq hedge
  have h := neutral_on_pivot hpre hpost hm hj hpos hp
  rwa [hmodel,ha,hb] at h

theorem primary_not_operand {pre post : List Gate} {g : Gate} {o : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hm : Matches ⟨pre++g::post,o⟩ flip)
    (hop : g.op = .and ∨ g.op = .or) (i : Fin 8) : i.succ.val ∉ g.inputs := by
  intro h
  have side_eq (z : Fin 9 → Bool) : side pre i.succ.val z = z i.succ := by
    rw [side,preserved _ (by simpa only [List.length_ofFn] using i.succ.isLt)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn, i.succ.isLt, dite_true, Option.getD_some, Fin.eta, set0, Fin.succ_ne_zero, ite_false]
  rcases hop with ha|ho
  · obtain ⟨z,hp,hz⟩ := projection i false
    have hi := (neutral_on_pivot hpre hpost hm h (by simp) hp).1 ha
    rw [side_eq z,hz] at hi
    contradiction
  · obtain ⟨z,hp,hz⟩ := projection i true
    have hi := (neutral_on_pivot hpre hpost hm h (by simp) hp).2 ho
    rw [side_eq z,hz] at hi
    contradiction

theorem has_reader {C : Circuit} {flip : Bool} (hm : Matches C flip) : ∃ g ∈ C.gates, 0 ∈ g.inputs := by
  by_contra! hnone
  obtain ⟨z,hp,_⟩ := projection 0 false
  have h0 := hm (set0 false z)
  have h1 := hm (set0 true z)
  rw [overwritten] at h0 h1
  apply hp
  rw [←h0,←h1]
  exact (fold_agree hnone (input_agree _ _ _)).2 _ (output_ne hm)

theorem unique_split {C : Circuit} {flip : Bool} (hm : Matches C flip)
    (hcount : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1) :
    ∃ pre g post, C.gates = pre++g::post ∧ 0 ∈ g.inputs ∧ Avoids pre ∧ Avoids post := by
  obtain ⟨g,hg,hz⟩ := has_reader hm
  obtain ⟨pre,post,hs⟩ := List.append_of_mem hg
  have hhas : g.inputs.contains 0 = true := List.contains_iff_mem.mpr hz
  rw [hs,List.filter_append,List.filter_cons_of_pos (p := fun k : Gate => k.inputs.contains 0) hhas,List.length_append,List.length_cons] at hcount
  have none {s : List Gate} (hh : (s.filter (fun k => k.inputs.contains 0)).length=0) : Avoids s := by
    have hv := List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp hh)
    intro k hk h
    exact hv k hk (List.contains_iff_mem.mpr h)
  exact ⟨pre,g,post,hs,hz,none (by omega),none (by omega)⟩

inductive Flat where
  | const (b : Bool)
  | lit (neg : Bool) (i : Fin 8)
  | both (i j : Fin 8)
  | either (i j : Fin 8)

def Flat.eval (t : Flat) (z : Fin 9 → Bool) : Bool :=
  match t with
  | .const b => b
  | .lit b i => b != z i.succ
  | .both i j => z i.succ && z j.succ
  | .either i j => z i.succ || z j.succ

theorem flat_constraint {pre post : List Gate} {g : Gate} {o j : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hm : Matches ⟨pre++g::post,o⟩ flip)
    (hj : j∈g.inputs) (hpos : j≠0) (s : Flat) (hmodel : ∀ z, side pre j z=s.eval z) :
    (g.op=.and → ∀ z, side pre j z=true) ∧
    (g.op=.or → (∀ z, side pre j z=false) ∨
       ∃ i k : Fin 8, i≠k ∧ edge i k=true ∧ ∀ z, side pre j z=(z i.succ && z k.succ)) := by
  have force {z} (hz : Pivot z) := neutral_on_pivot hpre hpost hm hj hpos hz
  constructor
  · intro hop z
    cases s with
    | const b =>
      obtain ⟨w,hw,_⟩ := projection 0 false
      exact (hmodel z).trans ((hmodel w).symm.trans ((force hw).1 hop))
    | lit b i =>
      obtain ⟨w,hw,hv⟩ := projection i b
      have hf := (force hw).1 hop
      rw [hmodel] at hf
      simp [Flat.eval,hv] at hf
    | both i k =>
      obtain ⟨hp,hi,hk⟩ := projections i k false false (by simp) (by simp)
      have hf := (force hp).1 hop
      rw [hmodel] at hf
      simp [Flat.eval,hi,hk] at hf
    | either i k =>
      obtain ⟨hp,hi,hk⟩ := projections i k false false (by simp) (by simp)
      have hf := (force hp).1 hop
      rw [hmodel] at hf
      simp [Flat.eval,hi,hk] at hf
  · intro hop
    cases s with
    | const b =>
      left; intro z
      obtain ⟨w,hw,_⟩ := projection 0 false
      exact (hmodel z).trans ((hmodel w).symm.trans ((force hw).2 hop))
    | lit b i =>
      obtain ⟨w,hw,hv⟩ := projection i (!b)
      have hf := (force hw).2 hop
      rw [hmodel] at hf
      cases b <;> simp [Flat.eval,hv] at hf
    | either i k =>
      obtain ⟨w,hw,hv⟩ := projection i true
      have hf := (force hw).2 hop
      rw [hmodel] at hf
      simp [Flat.eval,hv] at hf
    | both i k =>
      by_cases e : i=k
      · subst k
        obtain ⟨w,hw,hv⟩ := projection i true
        have hf := (force hw).2 hop
        rw [hmodel] at hf
        simp [Flat.eval,hv] at hf
      · cases hEdge : edge i k with
        | false =>
          obtain ⟨hp,hi,hk⟩ := projections i k true true (by simp) (by simp [hEdge])
          have hf := (force hp).2 hop
          rw [hmodel] at hf
          simp [Flat.eval,hi,hk] at hf
        | true => exact Or.inr ⟨i,k,e,hEdge,hmodel⟩


def primary (j : ℕ) : Option (Fin 8) :=
  if h : 0 < j ∧ j < 9 then some ⟨j-1, by omega⟩ else none

def atom (r : Option (Fin 8)) (z : Fin 9 → Bool) :=
  match r with
  | none => false
  | some i => z i.succ

theorem primary_read (j : ℕ) (z : Fin 9 → Bool) :
    (List.ofFn (set0 false z)).getD j false = atom (primary j) z := by
  by_cases hz : j = 0
  · subst j
    simp [primary, atom, set0]
  · by_cases hj : j < 9
    · have hp : 0 < j ∧ j < 9 := ⟨by omega,hj⟩
      have he : (⟨j,hj⟩ : Fin 9) ≠ 0 := fun e => hz (congrArg Fin.val e)
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hj,dite_true,
        Option.getD_some,set0,he,ite_false,primary,hp,atom]
      congr 1
      apply Fin.ext
      change j=j-1+1
      omega
    · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hj)]
      simp [primary,hj,atom]

def singleShape (neg : Bool) : Option (Fin 8) → Flat
  | none => .const neg
  | some i => .lit neg i

def andShape : Option (Fin 8) → Option (Fin 8) → Flat
  | some i, some j => .both i j
  | _,_ => .const false

def orShape : Option (Fin 8) → Option (Fin 8) → Flat
  | some i, some j => .either i j
  | some i, none | none, some i => .lit false i
  | none, none => .const false

theorem first_shape (g : Gate)
    (op : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2) :
    ∃ s : Flat, ∀ z, runGate g (List.ofFn (set0 false z)) = s.eval z := by
  cases hin : g.inputs with
  | nil =>
    rcases op with h|h|h
    · exact ⟨.const true,fun z => by simp [runGate,h,hin,GateOp.eval,Flat.eval]⟩
    · exact ⟨.const false,fun z => by simp [runGate,h,hin,GateOp.eval,Flat.eval]⟩
    · exact ⟨.const true,fun z => by simp [runGate,h,hin,GateOp.eval,Flat.eval]⟩
  | cons a l =>
    cases hl : l with
    | nil =>
      rw [hl] at hin
      rcases op with h|h|h
      · refine ⟨singleShape false (primary a),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,primary_read]
        cases e : primary a <;> simp [Flat.eval,atom,singleShape]
      · refine ⟨singleShape false (primary a),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,primary_read]
        cases e : primary a <;> simp [Flat.eval,atom,singleShape]
      · refine ⟨singleShape true (primary a),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,primary_read]
        cases e : primary a <;> simp [Flat.eval,atom,singleShape]
    | cons b r =>
      have hr : r=[] := by simpa [hin,hl] using hlen
      rw [hl,hr] at hin
      rcases op with h|h|h
      · refine ⟨andShape (primary a) (primary b),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,primary_read]
        cases e : primary a <;> cases f : primary b <;> simp [Flat.eval,atom,andShape]
      · refine ⟨orShape (primary a) (primary b),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,primary_read]
        cases e : primary a <;> cases f : primary b <;> simp [Flat.eval,atom,orShape]
      · refine ⟨singleShape true (primary a),?_⟩
        intro z
        simp only [runGate,h,hin,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,primary_read]
        cases e : primary a <;> simp [Flat.eval,atom,singleShape]

theorem early_shape {pre post : List Gate} {g : Gate} {o : ℕ}
    (hlen : pre.length ≤ 1) (hf : PEqualNP.MetaComplexity.FanInTwo ⟨pre++g::post,o⟩) (j : ℕ) :
    ∃ s : Flat, ∀ z, side pre j z = s.eval z := by
  have raw : ∃ s : Flat, ∀ z, (List.ofFn (set0 false z)).getD j false = s.eval z := by
    refine ⟨singleShape false (primary j),?_⟩
    intro z
    rw [primary_read]
    cases h : primary j <;> simp [atom,singleShape,Flat.eval]
  cases pre with
  | nil => exact raw
  | cons k t =>
    have ht : t=[] := by simpa using hlen
    subst t
    by_cases hj : j < 9
    · obtain ⟨s,hs⟩ := raw
      exact ⟨s,fun z => (preserved _ (by simpa only [List.length_ofFn] using hj) [k]).trans (hs z)⟩
    · by_cases he : j=9
      · subst j
        obtain ⟨hops,hkl⟩ := hf k (by simp)
        obtain ⟨s,hs⟩ := first_shape k hops hkl
        refine ⟨s,?_⟩
        intro z
        change (_ ++ [_]).getD 9 false = _
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simpa using hs z
      · refine ⟨.const false,?_⟩
        intro z
        apply List.getD_eq_default
        change (_ ++ [_]).length ≤ j
        simp
        omega

theorem first_wire_shape {pre post : List Gate} {g : Gate} {o : ℕ}
    (hpos : 0 < pre.length) (hf : PEqualNP.MetaComplexity.FanInTwo ⟨pre++g::post,o⟩) :
    ∃ s : Flat, ∀ z, side pre 9 z = s.eval z := by
  cases pre with
  | nil => simp at hpos
  | cons k t =>
    obtain ⟨hops,hkl⟩ := hf k (by simp)
    obtain ⟨s,hs⟩ := first_shape k hops hkl
    refine ⟨s,?_⟩
    intro z
    rw [side,List.foldl_cons,preserved _ (by simp [push])]
    unfold push
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simpa using hs z

end PEqualNP.Outside.L_meta_2541.Polarity

namespace PEqualNP.Outside.L_meta_2541.Polarity
open PEqualNP.CircuitLowerBounds

theorem not_tail_never_matches {pre post : List Gate} {g : Gate} {o j : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hop : g.op = .not)
    (hj : j≠0) (hin : ∃ l, g.inputs = j::l) : ¬ Matches ⟨pre++g::post,o⟩ flip := by
  intro hm
  obtain ⟨l,hl⟩ := hin
  obtain ⟨z,hp,_⟩ := projection 0 false
  apply must_switch hpre hpost hm hp
  have e := (fold_agree hpre (input_agree (flip != false) (flip != true) z)).2 _ hj
  simpa only [runGate,hop,hl,List.map_cons,GateOp.eval,List.headD_cons] using congrArg Bool.not e

theorem push_len (gs : List Gate) (w : List Bool) : (gs.foldl push w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp [push]; omega

theorem dangling_and_never_matches {pre post : List Gate} {g : Gate} {o j : ℕ} {flip : Bool}
    (hpre : Avoids pre) (hpost : Avoids post) (hop : g.op = .and)
    (hj : 9 + pre.length ≤ j) (hin : j∈g.inputs) : ¬ Matches ⟨pre++g::post,o⟩ flip := by
  intro hm
  obtain ⟨z,hp,_⟩ := projection 0 false
  have ht := (neutral_on_pivot hpre hpost hm hin (by omega) hp).1 hop
  have hf : side pre j z = false := by
    apply List.getD_eq_default
    simpa only [push_len,List.length_ofFn] using hj
  rw [hf] at ht
  contradiction

end PEqualNP.Outside.L_meta_2541.Polarity

namespace PEqualNP.Outside.L_meta_2541.Polarity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- An exact input-0 reader classification, conditional on the unsigned lower bound.
The prefix output at wire `j` is independent of the original raw coordinate 0. -/
theorem signed_reader
    (ordinary : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → Unary.readers D.gates ≤ 1 →
      ¬ Matches D false)
    {C : Circuit} (hf : FanInTwo C) (hs : C.size ≤ 14) (hc : Unary.readers C.gates ≤ 1)
    (hm : Matches C true) :
    ∃ pre g post j, C.gates = pre ++ g :: post ∧ Avoids pre ∧ Avoids post ∧
      (g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0,j] ∨ g.inputs = [j,0]) ∧
      9 ≤ j ∧ j < 9 + pre.length ∧
      (∃ z, side pre j z = false) ∧ (∃ z, side pre j z = true) ∧
      (∀ z, Pivot z → (g.op = .and → side pre j z = true) ∧
        (g.op = .or → side pre j z = false)) ∧
      (j = 9 → g.op = .or ∧ ∃ i k : Fin 8, i ≠ k ∧ edge i k = true ∧
          ∀ z, side pre j z = (z i.succ && z k.succ)) := by
  obtain ⟨pre,g,post,he,hz,hp,hq⟩ := unique_split hm hc
  cases C with
  | mk gs o =>
    change gs = _ at he
    subst gs
    have ho : o ≠ 0 := output_ne hm
    have hhead (hop : g.op=.not) : g.inputs.headD 0 = 0 := by
      cases e : g.inputs with
      | nil => rfl
      | cons a t =>
        simp only [List.headD_cons]
        by_contra hne
        exact not_tail_never_matches hp hq hop hne ⟨t,e⟩ hm
    obtain ⟨j,hj,hbin,hin,hvb⟩ :=
      Unary.signed_binary_reader pre post g o ordinary hm hf hs hc hz ho hhead
    have hjm : j ∈ g.inputs := by rcases hin with h|h <;> simp [h]
    have hlb : 9 ≤ j := by
      by_contra! hl
      let i : Fin 8 := ⟨j-1,by omega⟩
      have hi : i.succ.val = j := by change j-1+1=j; omega
      exact primary_not_operand hp hq hm hbin i (hi ▸ hjm)
    have hub : j < 9 + pre.length := by
      rcases hbin with ha|hr
      · by_contra! hge
        exact dangling_and_never_matches hp hq ha hge hjm hm
      · exact hvb hr
    have piv {z} (h : Pivot z) := neutral_on_pivot hp hq hm hjm hj h
    have constBad : ¬ ((g.op = .and ∧ ∀ z, side pre j z = true) ∨
        (g.op = .or ∧ ∀ z, side pre j z = false)) := by
      intro h
      have si (z) : (Unary.run pre (List.ofFn (Unary.twist true z))).getD j false = side pre j z :=
        side_read hp hj z (true != z 0)
      obtain ⟨D,hD,hDs,hDr,hEq⟩ := Unary.neutral_operand_twist_swap pre post g o j true hin
        (h.imp (fun a => ⟨a.1,fun z => (si z).trans (a.2 z)⟩)
          (fun a => ⟨a.1,fun z => (si z).trans (a.2 z)⟩)) ho hf hc
      exact ordinary D hD (hDs ▸ hs) hDr (fun z => (hEq z).symm.trans (hm z))
    obtain ⟨w,hw,_⟩ := projection 0 false
    have varies : (∃ z, side pre j z = false) ∧ (∃ z, side pre j z = true) := by
      rcases hbin with ha|hr
      · refine ⟨?_,w,(piv hw).1 ha⟩
        by_contra! h
        exact constBad (Or.inl ⟨ha,fun z => by cases e : side pre j z <;> simp_all⟩)
      · refine ⟨⟨w,(piv hw).2 hr⟩,?_⟩
        by_contra! h
        exact constBad (Or.inr ⟨hr,fun z => by cases e : side pre j z <;> simp_all⟩)
    refine ⟨pre,g,post,j,rfl,hp,hq,hbin,hin,hlb,hub,varies.1,varies.2,
      fun _ h => piv h,?_⟩
    rintro rfl
    obtain ⟨s,hsf⟩ := first_wire_shape (by omega) hf
    have hcst := flat_constraint hp hq hm hjm hj s hsf
    have hr : g.op=.or := hbin.resolve_left (fun ha => constBad (Or.inl ⟨ha,hcst.1 ha⟩))
    exact ⟨hr,(hcst.2 hr).resolve_left (fun he => constBad (Or.inr ⟨hr,he⟩))⟩

end PEqualNP.Outside.L_meta_2541.Polarity

/-- Public interface expressed entirely in the project definitions, taking the exact unsigned child as premise. -/
theorem PEqualNP.Outside.SignedReader : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.false → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →
let T := fun x : Fin 9 → Bool => (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
let set0 := fun (b : Bool) (x : Fin 9 → Bool) (i : Fin 9) => if i = 0 then b else x i
let S := fun (pre : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ) (z : Fin 9 → Bool) =>
  PEqualNP.CircuitLowerBounds.Circuit.eval ⟨pre,j⟩ (List.ofFn (set0 false z))
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
  (C.gates.filter (fun k => k.inputs.contains 0)).length ≤ 1 →
  (∀ x, PEqualNP.MetaComplexity.circuitFun 9 C (set0 (true != x 0) x) = T x) →
  ∃ (pre : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (post : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ),
    C.gates = pre ++ g :: post ∧ (∀ k ∈ pre, 0 ∉ k.inputs) ∧ (∀ k ∈ post, 0 ∉ k.inputs) ∧
    (g.op = .and ∨ g.op = .or) ∧ (g.inputs = [0,j] ∨ g.inputs = [j,0]) ∧
    9 ≤ j ∧ j < 9 + pre.length ∧
    (∃ z, S pre j z = false) ∧ (∃ z, S pre j z = true) ∧
    (∀ z, T (set0 false z) ≠ T (set0 true z) →
      (g.op = .and → S pre j z = true) ∧ (g.op = .or → S pre j z = false)) ∧
    (j = 9 → g.op = .or ∧ ∃ i k : Fin 8, i ≠ k ∧
       T (fun l => decide (l = i.succ ∨ l = k.succ)) = true ∧
       ∀ z, S pre j z = (z i.succ && z k.succ)) := by
  intro hu
  dsimp only
  intro C hf hs hr h
  apply PEqualNP.Outside.L_meta_2541.Polarity.signed_reader _ hf hs hr h
  intro D hf hs hr h
  obtain ⟨x,hx⟩ := hu D false hf hs hr rfl
  exact hx (h x)
