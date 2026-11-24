import Mathlib
import PEqualNP.Defs

-- The circuit is represented by the truth words available after each gate.
-- Restricting input rows can make a gate constant or identify it with an
-- earlier wire. Each cut below records pairs on which the original output
-- differs, so the restriction lemmas certify the number of gates saved.
-- A split checks every possible next gate on the current words.

namespace PEqualNP.Outside.L_meta_1543.Cert

abbrev Wire (X : Type) := X → Bool

inductive Step {X : Type} (S : Set (Wire X)) : Wire X → Prop where
  | conj {a b : Wire X} (ha : a ∈ S) (hb : b ∈ S) : Step S (fun x => a x && b x)
  | disj {a b : Wire X} (ha : a ∈ S) (hb : b ∈ S) : Step S (fun x => a x || b x)
  | neg {a : Wire X} (ha : a ∈ S) : Step S (fun x => !(a x))

inductive Build {X : Type} : Set (Wire X) → Nat → Wire X → Prop where
  | here {S : Set (Wire X)} {f : Wire X} (h : f ∈ S) : Build S 0 f
  | next {S : Set (Wire X)} {n : Nat} {g f : Wire X} (h : Step S g)
      (tail : Build (insert g S) n f) : Build S (n+1) f

end PEqualNP.Outside.L_meta_1543.Cert
namespace PEqualNP.Outside.L_meta_1543.Cert
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fetch {X : Type} (v : X → List Bool) (i : Nat) : Wire X := fun x => (v x).getD i false
def gateVal {X : Type} (v : X → List Bool) (g : Gate) : Wire X :=
  fun x => g.op.eval (g.inputs.map fun i => (v x).getD i false)

end PEqualNP.Outside.L_meta_1543.Cert
namespace PEqualNP.Outside.L_meta_1543.Cert
open PEqualNP.CircuitLowerBounds

theorem gateStep {X : Type} {S : Set (Wire X)} (v : X → List Bool) (g : Gate)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (bounded : g.inputs.length ≤ 2) (hh : ∀ i, fetch v i ∈ S)
    (ft : (fun _ : X => false) ∈ S) (tt : (fun _ : X => true) ∈ S) :
    Step S (gateVal v g) := by
  rcases g with ⟨o, inputs⟩
  change o = .and ∨ o = .or ∨ o = .not at op
  change inputs.length ≤ 2 at bounded
  unfold gateVal
  cases inputs with
  | nil =>
    rcases op with rfl | rfl | rfl
    · simpa [GateOp.eval] using Step.neg ft
    · simpa [GateOp.eval] using Step.neg tt
    · simpa [GateOp.eval] using Step.neg ft
  | cons i rest =>
    cases rest with
    | nil =>
      rcases op with rfl | rfl | rfl
      · simpa [GateOp.eval, fetch] using Step.conj (hh i) tt
      · simpa [GateOp.eval, fetch] using Step.disj (hh i) ft
      · simpa [GateOp.eval, fetch] using Step.neg (hh i)
    | cons j tail =>
      cases tail with
      | nil =>
        rcases op with rfl | rfl | rfl
        · simpa [GateOp.eval, fetch] using Step.conj (hh i) (hh j)
        · simpa [GateOp.eval, fetch] using Step.disj (hh i) (hh j)
        · simpa [GateOp.eval, fetch] using Step.neg (hh i)
      | cons k ks => simp at bounded

end PEqualNP.Outside.L_meta_1543.Cert
namespace PEqualNP.Outside.L_meta_1543.Cert
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireAppend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_wire_append {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

def Inputs (n : Nat) : Set (Wire (Fin n → Bool)) :=
  {w : Wire (Fin n → Bool) | w = (fun _ => false) ∨ w = (fun _ => true) ∨ ∃ i : Fin n, w = (fun x => x i)}

theorem availableInputs (n i : Nat) : fetch (fun x : Fin n → Bool => List.ofFn x) i ∈ Inputs n := by
  unfold Inputs
  simp only [Set.mem_setOf_eq]
  by_cases h : i < n
  · right; right
    exact ⟨⟨i,h⟩,by funext x; simp [fetch,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]⟩
  · left
    funext x
    simp [fetch,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]

theorem foldBuild {X : Type}
    (make : ∀ {S : Set (Wire X)} (v : X → List Bool) (g : Gate),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      (∀ i, fetch v i ∈ S) → (fun _ : X => false) ∈ S → (fun _ : X => true) ∈ S → Step S (gateVal v g))
    (gs : List Gate) (o : Nat) (S : Set (Wire X)) (v : X → List Bool) (L : Nat)
    (lengths : ∀ x, (v x).length = L) (available : ∀ i, fetch v i ∈ S)
    (hf : (fun _ : X => false) ∈ S) (ht : (fun _ : X => true) ∈ S)
    (allowed : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Build S gs.length (fetch (fun x => gs.foldl wireAppend (v x)) o) := by
  induction gs generalizing S v L with
  | nil => exact Build.here (available o)
  | cons g gs ih =>
    obtain ⟨op,sz⟩ := allowed g (by simp)
    have step := make v g op sz available hf ht
    let w : X → List Bool := fun x => wireAppend (v x) g
    have lengthw (x : X) : (w x).length = L+1 := by simp [w,wireAppend,lengths]
    have next (i : Nat) : fetch w i ∈ insert (gateVal v g) S := by
      by_cases prev : i < L
      · have eq : fetch w i = fetch v i := by
          funext x
          simp only [fetch,w,wireAppend,getD_wire_append,lengths,ite_eq_left prev]
        exact Set.mem_insert_of_mem _ (eq ▸ available i)
      by_cases last : i = L
      · have eq : fetch w i = gateVal v g := by
          funext x
          simp only [fetch,w,wireAppend,getD_wire_append,lengths,ite_eq_right prev,ite_eq_left last,gateVal]
        exact Set.mem_insert_iff.mpr (Or.inl eq)
      · have eq : fetch w i = (fun _ => false) := by
          funext x
          simp only [fetch,w,wireAppend,getD_wire_append,lengths,ite_eq_right prev,ite_eq_right last]
        exact Set.mem_insert_of_mem _ (eq ▸ hf)
    exact Build.next step (ih _ w (L+1) lengthw next (Set.mem_insert_of_mem _ hf)
      (Set.mem_insert_of_mem _ ht) (fun g' h => allowed g' (List.mem_cons_of_mem _ h)))

end PEqualNP.Outside.L_meta_1543.Cert
namespace PEqualNP.Outside.L_meta_1543.Cert
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem buildOfHasCircuitSize {n s : Nat} {f : (Fin n → Bool) → Bool} (H : HasCircuitSize n f s) :
    ∃ k ≤ s, Build {w : Wire (Fin n → Bool) | w = (fun _ => false) ∨ w = (fun _ => true) ∨
        ∃ i : Fin n, w = (fun x => x i)} k f := by
  obtain ⟨C,allowed,size,correct⟩ := H
  refine ⟨C.gates.length,size,?_⟩
  have h : Build (Inputs n) C.gates.length (fun x => C.eval (List.ofFn x)) :=
    foldBuild (fun v g => gateStep v g) C.gates C.output (Inputs n) (fun x => List.ofFn x) n
      (fun x => by simp) (availableInputs n) (Or.inl rfl) (Or.inr (Or.inl rfl)) allowed
  exact (funext correct) ▸ h

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

theorem pullStep {X Y : Type} {S : Set (Wire X)} {T : Set (Wire Y)}
    {g : Wire X} (step : Step S g) (r : Y → X)
    (inc : ∀ w ∈ S, w ∘ r ∈ T) : Step T (g ∘ r) := by
  cases step with
  | conj ha hb => exact Step.conj (inc _ ha) (inc _ hb)
  | disj ha hb => exact Step.disj (inc _ ha) (inc _ hb)
  | neg ha => exact Step.neg (inc _ ha)

theorem pullBuild {X Y : Type} {S : Set (Wire X)} {T : Set (Wire Y)}
    {f : Wire X} {n : Nat} (prog : Build S n f) (r : Y → X)
    (inc : ∀ w ∈ S, w ∘ r ∈ T) : Build T n (f ∘ r) := by
  induction prog generalizing T with
  | here h => exact Build.here (inc _ h)
  | @next S n g f step tail ih =>
    apply Build.next (pullStep step r inc)
    apply ih
    intro w hw
    rcases Set.mem_insert_iff.mp hw with h|h
    · subst w
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (inc _ h)

theorem pullBuild_unpaid {X Y : Type} {S : Set (Wire X)} {T : Set (Wire Y)}
    {f : Wire X} {n : Nat} (prog : Build S n f) (r : Y → X)
    (inc : ∀ w ∈ S, w ∘ r ∈ T) : ∃ k ≤ n, Build T k (f ∘ r) :=
  ⟨n, Nat.le_refl _, pullBuild prog r inc⟩

theorem foldVaryingStep {X Y : Type} {S : Set (Wire X)} {T : Set (Wire Y)}
    {g : Wire X} (step : Step S g) (r : Y → X) (a b : X)
    (inc : ∀ w ∈ S, w ∘ r ∈ T) (constants : ∀ c : Bool, (fun _ : Y => c) ∈ T)
    (pinned : ∀ w ∈ S, w a ≠ w b → ∃ c : Bool, w ∘ r = fun _ => c) :
    g ∘ r ∈ T ∨ g a = g b := by
  cases step with
  | @conj u v hu hv =>
    by_cases du : u a = u b
    · by_cases dv : v a = v b
      · exact Or.inr (by simp [du,dv])
      · obtain ⟨c,hc⟩ := pinned v hv dv
        left
        change (fun y => u (r y) && (v ∘ r) y) ∈ T
        rw [hc]
        cases c <;> simp <;> first | exact inc u hu | exact constants _
    · obtain ⟨c,hc⟩ := pinned u hu du
      left
      change (fun y => (u ∘ r) y && v (r y)) ∈ T
      rw [hc]
      cases c <;> simp <;> first | exact inc v hv | exact constants _
  | @disj u v hu hv =>
    by_cases du : u a = u b
    · by_cases dv : v a = v b
      · exact Or.inr (by simp [du,dv])
      · obtain ⟨c,hc⟩ := pinned v hv dv
        left
        change (fun y => u (r y) || (v ∘ r) y) ∈ T
        rw [hc]
        cases c <;> simp <;> first | exact inc u hu | exact constants _
    · obtain ⟨c,hc⟩ := pinned u hu du
      left
      change (fun y => (u ∘ r) y || v (r y)) ∈ T
      rw [hc]
      cases c <;> simp <;> first | exact inc v hv | exact constants _
  | @neg u hu =>
    by_cases du : u a = u b
    · exact Or.inr (by simp [du])
    · obtain ⟨c,hc⟩ := pinned u hu du
      left
      change (fun y => !((u ∘ r) y)) ∈ T
      rw [hc]
      exact constants _

theorem pullBuild_paid {X Y : Type} {S : Set (Wire X)} {T : Set (Wire Y)}
    {f : Wire X} {n : Nat} (prog : Build S n f) (r : Y → X) (a b : X)
    (dist : f a ≠ f b) (nonconstant : ∃ y z, f (r y) ≠ f (r z))
    (inc : ∀ w ∈ S, w ∘ r ∈ T) (constants : ∀ c : Bool, (fun _ : Y => c) ∈ T)
    (pinned : ∀ w ∈ S, w a ≠ w b → ∃ c : Bool, w ∘ r = fun _ => c) :
    ∃ k < n, Build T k (f ∘ r) := by
  induction prog generalizing T with
  | here hf =>
    obtain ⟨c,hc⟩ := pinned _ hf dist
    obtain ⟨y,z,h⟩ := nonconstant
    exact False.elim (h ((congrFun hc y).trans (congrFun hc z).symm))
  | @next S n g f step tail ih =>
    rcases foldVaryingStep step r a b inc constants pinned with folded|same
    · refine ⟨n, Nat.lt_succ_self _, pullBuild tail r ?_⟩
      intro w hw
      rcases Set.mem_insert_iff.mp hw with h|h
      · subst w; exact folded
      · exact inc _ h
    · let T' := insert (g ∘ r) T
      have inc' : ∀ w ∈ insert g S, w ∘ r ∈ T' := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with h|h
        · subst w; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (inc _ h)
      have pinned' : ∀ w ∈ insert g S, w a ≠ w b → ∃ c : Bool, w ∘ r = fun _ => c := by
        intro w hw d
        rcases Set.mem_insert_iff.mp hw with h|h
        · subst w; exact False.elim (d same)
        · exact pinned w h d
      obtain ⟨k,hk,out⟩ := ih dist nonconstant inc' (fun c => Set.mem_insert_of_mem _ (constants c)) pinned'
      exact ⟨k+1, Nat.succ_lt_succ hk, Build.next (pullStep step r inc) out⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

abbrev ChangesOn {X ι : Type} (a b : ι → X) (w : Wire X) (i : ι) : Prop :=
  w (a i) ≠ w (b i)

abbrev ChangesOnce {X ι : Type} (a b : ι → X) (I : Finset ι) (w : Wire X) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ChangesOn a b w i → ChangesOn a b w j → i = j

abbrev PinnedOn {X Y : Type} (r : Y → X) (w : Wire X) : Prop :=
  ∃ c : Bool, w ∘ r = fun _ => c

theorem binaryStepRep {X : Type} {S : Set (Wire X)} {g : Wire X}
    (step : Step S g) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ op : Bool → Bool → Bool, g = fun x => op (u x) (v x) := by
  cases step with
  | conj hu hv => exact ⟨_,hu,_,hv,Bool.and,rfl⟩
  | disj hu hv => exact ⟨_,hu,_,hv,Bool.or,rfl⟩
  | neg hu => exact ⟨_,hu,_,hu,(fun a _ => !a),rfl⟩

theorem binaryAfterErase {X Y ι : Type} [DecidableEq ι]
    {S : Set (Wire X)} (a b : ι → X) (r : Y → X) (I : Finset ι)
    (one : ∀ w ∈ S, ChangesOnce a b I w)
    (pin : ∀ w ∈ S, ∀ i ∈ I, ChangesOn a b w i → PinnedOn r w)
    (u v : Wire X) (hu : u ∈ S) (hv : v ∈ S) (op : Bool → Bool → Bool)
    (i : ι) (hi : i ∈ I) (du : ChangesOn a b u i) :
    let g : Wire X := fun x => op (u x) (v x)
    ChangesOnce a b (I.erase i) g ∧
      ∀ j ∈ I.erase i, ChangesOn a b g j → PinnedOn r g := by
  dsimp only
  have stay (j) (hj : j ∈ I.erase i) : u (a j) = u (b j) := by
    by_contra h
    exact (Finset.mem_erase.mp hj).1 ((one u hu i hi j
      (Finset.mem_of_mem_erase hj) du h).symm)
  have inV (j) (hj : j ∈ I.erase i)
      (d : ChangesOn a b (fun x => op (u x) (v x)) j) : ChangesOn a b v j := by
    intro eq
    exact d (congrArg₂ op (stay j hj) eq)
  constructor
  · intro j hj k hk dj dk
    exact one v hv j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk)
      (inV j hj dj) (inV k hk dk)
  · intro j hj dj
    obtain ⟨c,hc⟩ := pin u hu i hi du
    obtain ⟨d,hd⟩ := pin v hv j (Finset.mem_of_mem_erase hj) (inV j hj dj)
    refine ⟨op c d, ?_⟩
    funext y
    exact congrArg₂ op (congrFun hc y) (congrFun hd y)

theorem stepAfterErase {X Y ι : Type} [DecidableEq ι]
    {S : Set (Wire X)} {g : Wire X} (step : Step S g)
    (a b : ι → X) (r : Y → X) (I : Finset ι)
    (one : ∀ w ∈ S, ChangesOnce a b I w)
    (pin : ∀ w ∈ S, ∀ i ∈ I, ChangesOn a b w i → PinnedOn r w)
    (i : ι) (hi : i ∈ I) (dg : ChangesOn a b g i) :
    ChangesOnce a b (I.erase i) g ∧
      ∀ j ∈ I.erase i, ChangesOn a b g j → PinnedOn r g := by
  obtain ⟨u,hu,v,hv,op,rfl⟩ := binaryStepRep step
  by_cases du : ChangesOn a b u i
  · exact binaryAfterErase a b r I one pin u v hu hv op i hi du
  · have same : u (a i) = u (b i) := Classical.not_not.mp du
    have dv : ChangesOn a b v i := fun h => dg (congrArg₂ op same h)
    exact binaryAfterErase a b r I one pin v u hv hu (fun s t => op t s) i hi dv

theorem pullBuild_multi {X Y ι : Type} [DecidableEq ι]
    {S : Set (Wire X)} {T : Set (Wire Y)} {n : Nat} {f : Wire X}
    (prog : Build S n f) (r : Y → X) (a b : ι → X) (I : Finset ι)
    (dist : ∀ i ∈ I, ChangesOn a b f i) (nonconstant : ∃ y z, f (r y) ≠ f (r z))
    (inc : ∀ w ∈ S, w ∘ r ∈ T) (constants : ∀ c : Bool, (fun _ : Y => c) ∈ T)
    (one : ∀ w ∈ S, ChangesOnce a b I w)
    (pin : ∀ w ∈ S, ∀ i ∈ I, ChangesOn a b w i → PinnedOn r w) :
    ∃ k, k + I.card ≤ n ∧ Build T k (f ∘ r) := by
  classical
  induction prog generalizing I T with
  | @here S f hf =>
    by_cases emp : I = ∅
    · subst I
      exact ⟨0,by simp,Build.here (inc _ hf)⟩
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr emp
      obtain ⟨c,hc⟩ := pin f hf i hi (dist i hi)
      obtain ⟨y,z,d⟩ := nonconstant
      exact False.elim (d ((congrFun hc y).trans (congrFun hc z).symm))
  | @next S n g f step tail ih =>
    by_cases hit : ∃ i ∈ I, ChangesOn a b g i
    · obtain ⟨i,hi,dg⟩ := hit
      have fold : g ∘ r ∈ T :=
        (foldVaryingStep step r (a i) (b i) inc constants (fun w hw => pin w hw i hi)).resolve_right dg
      obtain ⟨oneG,pinG⟩ := stepAfterErase step a b r I one pin i hi dg
      have inc' : ∀ w ∈ insert g S, w ∘ r ∈ T := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · exact fold
        · exact inc _ h
      have one' : ∀ w ∈ insert g S, ChangesOnce a b (I.erase i) w := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · exact oneG
        · intro j hj k hk
          exact one w h j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk)
      have pin' : ∀ w ∈ insert g S, ∀ j ∈ I.erase i, ChangesOn a b w j → PinnedOn r w := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · exact pinG
        · intro j hj
          exact pin w h j (Finset.mem_of_mem_erase hj)
      obtain ⟨k,hk,ct⟩ := ih (I.erase i) (fun j hj => dist j (Finset.mem_of_mem_erase hj))
        nonconstant inc' constants one' pin'
      have card := Finset.card_erase_add_one hi
      exact ⟨k,by omega,ct⟩
    · let T' := insert (g ∘ r) T
      have inc' : ∀ w ∈ insert g S, w ∘ r ∈ T' := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (inc _ h)
      have one' : ∀ w ∈ insert g S, ChangesOnce a b I w := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · intro i hi j hj di
          exact False.elim (hit ⟨i,hi,di⟩)
        · exact one w h
      have pin' : ∀ w ∈ insert g S, ∀ j ∈ I, ChangesOn a b w j → PinnedOn r w := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|h
        · intro j hj dj
          exact False.elim (hit ⟨j,hj,dj⟩)
        · exact pin w h
      obtain ⟨k,hk,ct⟩ := ih I dist nonconstant inc'
        (fun c => Set.mem_insert_of_mem _ (constants c)) one' pin'
      exact ⟨k+1,by omega, Build.next (pullStep step r inc) ct⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

/-- A gate that varies between the witness inputs has an absorbing cofactor. -/
theorem absorbingStep {X Y₀ Y₁ : Type} {S : Set (Wire X)} {g : Wire X}
    (step : Step S g) (r₀ : Y₀ → X) (r₁ : Y₁ → X) (a b : X)
    (pinned : ∀ w ∈ S, w a ≠ w b →
      w ∘ r₀ = (fun _ => false) ∧ w ∘ r₁ = (fun _ => true))
    (d : g a ≠ g b) :
    (∃ c : Bool, g ∘ r₀ = fun _ => c) ∨ (∃ c : Bool, g ∘ r₁ = fun _ => c) := by
  cases step with
  | @conj u v hu hv =>
    left
    refine ⟨false, ?_⟩
    by_cases du : u a=u b
    · have dv : v a≠v b := fun de => d (by simp [du,de])
      have vv := (pinned v hv dv).1
      funext y
      simp only [Function.comp_apply]
      simp [show v (r₀ y)=false from congrFun vv y]
    · have uu := (pinned u hu du).1
      funext y
      simp only [Function.comp_apply]
      simp [show u (r₀ y)=false from congrFun uu y]
  | @disj u v hu hv =>
    right
    refine ⟨true, ?_⟩
    by_cases du : u a=u b
    · have dv : v a≠v b := fun de => d (by simp [du,de])
      have vv := (pinned v hv dv).2
      funext y
      simp only [Function.comp_apply]
      simp [show v (r₁ y)=true from congrFun vv y]
    · have uu := (pinned u hu du).2
      funext y
      simp only [Function.comp_apply]
      simp [show u (r₁ y)=true from congrFun uu y]
  | @neg u hu =>
    have du : u a≠u b := fun de => d (by simp [de])
    have uu := (pinned u hu du).1
    left
    refine ⟨true, ?_⟩
    funext y
    simp only [Function.comp_apply]
    simp [show u (r₀ y)=false from congrFun uu y]

theorem pullBuild_twoSides {X Y₀ Y₁ : Type} {S : Set (Wire X)}
    {T₀ : Set (Wire Y₀)} {T₁ : Set (Wire Y₁)} {f : Wire X} {n : ℕ}
    (prog : Build S n f) (r₀ : Y₀ → X) (r₁ : Y₁ → X) (a b : X)
    (dist : f a≠f b)
    (vary₀ : ∃ y z, f (r₀ y)≠f (r₀ z)) (vary₁ : ∃ y z, f (r₁ y)≠f (r₁ z))
    (inc₀ : ∀ w ∈ S, w ∘ r₀ ∈ T₀) (inc₁ : ∀ w ∈ S, w ∘ r₁ ∈ T₁)
    (const₀ : ∀ c : Bool, (fun _ : Y₀ => c) ∈ T₀) (const₁ : ∀ c : Bool, (fun _ : Y₁ => c) ∈ T₁)
    (pinned : ∀ w ∈ S, w a≠w b → w ∘ r₀ = (fun _ => false) ∧ w ∘ r₁ = (fun _ => true)) :
    ∃ k₀ k₁ : ℕ, Build T₀ k₀ (f ∘ r₀) ∧ Build T₁ k₁ (f ∘ r₁) ∧
      k₀+1 ≤ n ∧ k₁+1 ≤ n ∧ (k₀+2≤n ∨ k₁+2≤n) := by
  induction prog generalizing T₀ T₁ with
  | here hf =>
    obtain ⟨y,z,ne⟩ := vary₀
    have h := (pinned _ hf dist).1
    exact False.elim (ne ((congrFun h y).trans (congrFun h z).symm))
  | @next S n g f step tail ih =>
    by_cases same : g a=g b
    · have incAfter {Y : Type} {r : Y → X} {T : Set (Wire Y)}
          (inc : ∀ w ∈ S, w ∘ r ∈ T) :
          ∀ w ∈ insert g S, w ∘ r ∈ insert (g ∘ r) T := by
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|inS
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (inc w inS)
      have pin w (h : w ∈ insert g S) (d : w a≠w b) :
          w ∘ r₀ = (fun _ => false) ∧ w ∘ r₁ = (fun _ => true) := by
        rcases Set.mem_insert_iff.mp h with rfl|inS
        · exact False.elim (d same)
        · exact pinned w inS d
      obtain ⟨k₀,k₁,B₀,B₁,le₀,le₁,either⟩ := ih dist vary₀ vary₁ (incAfter inc₀) (incAfter inc₁)
        (fun c => Set.mem_insert_of_mem _ (const₀ c)) (fun c => Set.mem_insert_of_mem _ (const₁ c)) pin
      exact ⟨k₀+1,k₁+1,Build.next (pullStep step r₀ inc₀) B₀,Build.next (pullStep step r₁ inc₁) B₁,
        by omega,by omega,by omega⟩
    · have oneSide {Y : Type} {r : Y → X} {T : Set (Wire Y)}
          (inc : ∀ w ∈ S, w ∘ r ∈ T) (const : ∀ c : Bool, (fun _ : Y => c) ∈ T)
          (pin : ∀ w ∈ S, w a≠w b → ∃ c : Bool, w ∘ r = fun _ => c) :
          ∀ w ∈ insert g S, w ∘ r ∈ T := by
        have folded := (foldVaryingStep step r a b inc const pin).resolve_right same
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl|inS
        · exact folded
        · exact inc w inS
      have pin₀ (w : Wire X) (h : w∈S) (d : w a≠w b) : ∃ c : Bool, w ∘ r₀ = fun _ => c :=
        ⟨false,(pinned w h d).1⟩
      have pin₁ (w : Wire X) (h : w∈S) (d : w a≠w b) : ∃ c : Bool, w ∘ r₁ = fun _ => c :=
        ⟨true,(pinned w h d).2⟩
      have extendPin {Y : Type} {r : Y → X}
          (pin : ∀ w ∈ S, w a≠w b → ∃ c : Bool, w ∘ r = fun _ => c)
          (absorbs : ∃ c : Bool, g ∘ r = fun _ => c) :
          ∀ w ∈ insert g S, w a≠w b → ∃ c : Bool, w ∘ r = fun _ => c := by
        intro w hw dw
        rcases Set.mem_insert_iff.mp hw with rfl|inS
        · exact absorbs
        · exact pin w inS dw
      have i₀ := oneSide inc₀ const₀ pin₀
      have i₁ := oneSide inc₁ const₁ pin₁
      rcases absorbingStep step r₀ r₁ a b pinned same with h|h
      · obtain ⟨k,hk,build⟩ := pullBuild_paid tail r₀ a b dist vary₀ i₀ const₀ (extendPin pin₀ h)
        exact ⟨k,n,build,pullBuild tail r₁ i₁,by omega,by omega,Or.inl (by omega)⟩
      · obtain ⟨k,hk,build⟩ := pullBuild_paid tail r₁ a b dist vary₁ i₁ const₁ (extendPin pin₁ h)
        exact ⟨n,k,pullBuild tail r₀ i₀,build,by omega,by omega,Or.inr (by omega)⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert
abbrev Row := Fin 1024
abbrev Word := BitVec 1024
def denote (w : Word) (r : Row) : Bool := w.getLsbD r.val
def avail (ws : List Word) : Set (Wire Row) := {w | ∃ z ∈ ws, w = denote z}
def nextWords (ws : List Word) : List Word :=
  ws.flatMap fun a => (~~~a) :: ws.flatMap (fun b => [a &&& b, a ||| b])
end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

theorem denote_injective : Function.Injective denote := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun eq ⟨i,hi⟩

theorem denote_mem_avail {z : Word} {ws : List Word} : denote z ∈ avail ws ↔ z ∈ ws := by
  constructor
  · rintro ⟨a,ha,h⟩
    exact denote_injective h ▸ ha
  · intro h
    exact ⟨z,h,rfl⟩

theorem avail_cons (z : Word) (ws : List Word) :
    avail (z :: ws) = insert (denote z) (avail ws) := by
  ext w
  constructor
  · rintro ⟨a,ha,eq⟩
    rcases List.mem_cons.mp ha with rfl | h
    · exact Set.mem_insert_iff.mpr (Or.inl eq)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨_,h,eq⟩)
  · intro h
    rcases Set.mem_insert_iff.mp h with eq | ⟨a,ha,eq⟩
    · exact ⟨z,List.mem_cons_self,eq⟩
    · exact ⟨a,List.mem_cons_of_mem _ ha,eq⟩

theorem stepWord {ws : List Word} {g : Wire Row} (h : Step (avail ws) g) :
    ∃ z ∈ nextWords ws, g = denote z := by
  cases h with
  | conj ha hb =>
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨b,hb,rfl⟩ := hb
    refine ⟨a &&& b, List.mem_flatMap.mpr ⟨a,ha, List.mem_cons_of_mem _ ?_⟩,?_⟩
    · exact List.mem_flatMap.mpr ⟨b,hb,by simp⟩
    · funext x; simp [denote]
  | disj ha hb =>
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨b,hb,rfl⟩ := hb
    refine ⟨a ||| b, List.mem_flatMap.mpr ⟨a,ha, List.mem_cons_of_mem _ ?_⟩,?_⟩
    · exact List.mem_flatMap.mpr ⟨b,hb,by simp⟩
    · funext x; simp [denote]
  | neg ha =>
    obtain ⟨a,ha,rfl⟩ := ha
    refine ⟨~~~a,List.mem_flatMap.mpr ⟨a,ha,List.mem_cons_self⟩,?_⟩
    funext x; simp [denote,x.isLt]

theorem zeroWord {ws : List Word} {f : Wire Row} (h : Build (avail ws) 0 f) :
    f ∈ avail ws := by
  cases h with
  | here h => exact h

theorem firstWord {ws : List Word} {f : Wire Row} {n : Nat} (h : Build (avail ws) (n+1) f) :
    ∃ z ∈ nextWords ws, Build (avail (z :: ws)) n f := by
  cases h with
  | next step tail =>
    obtain ⟨z,hz,rfl⟩ := stepWord step
    exact ⟨z,hz,avail_cons z ws ▸ tail⟩

theorem firstNewWord {ws : List Word} {f : Wire Row} {n : Nat}
    (fresh : f ∉ avail ws) (h : Build (avail ws) n f) :
    ∃ z ∈ nextWords ws, z ∉ ws ∧ ∃ k < n, Build (avail (z :: ws)) k f := by
  induction n with
  | zero => exact (fresh (zeroWord h)).elim
  | succ n ih =>
    obtain ⟨z,hz,tail⟩ := firstWord h
    by_cases old : z ∈ ws
    · have eq : avail (z::ws) = avail ws := by
        rw [avail_cons,Set.insert_eq_of_mem (denote_mem_avail.mpr old)]
      obtain ⟨u,hu,newu,k,hk,small⟩ := ih (eq ▸ tail)
      exact ⟨u,hu,newu,k,by omega,small⟩
    · exact ⟨z,hz,old,n,by omega,tail⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

theorem stepMono {X : Type} {S T : Set (Wire X)} {g : Wire X}
    (hST : S ⊆ T) (h : Step S g) : Step T g := by
  cases h with
  | conj ha hb => exact Step.conj (hST ha) (hST hb)
  | disj ha hb => exact Step.disj (hST ha) (hST hb)
  | neg ha => exact Step.neg (hST ha)

theorem buildMono {X : Type} {S T : Set (Wire X)} {n : Nat} {f : Wire X}
    (hST : S ⊆ T) (h : Build S n f) : Build T n f := by
  induction h generalizing T with
  | here hf => exact Build.here (hST hf)
  | next hs _ ih =>
    exact Build.next (stepMono hST hs) (ih (Set.insert_subset_insert hST))

theorem buildDropRedundant {X : Type} {S : Set (Wire X)} {n : Nat} {f g : Wire X}
    (hg : g ∈ S) (tail : Build (insert g S) n f) : Build S n f := by
  simpa only [Set.insert_eq_of_mem hg] using tail

theorem buildFreshFirst {X : Type} {S : Set (Wire X)} {n : Nat} {f : Wire X}
    (h : Build S (n + 1) f) (shorter : ¬ Build S n f) :
    ∃ g : Wire X, g ∉ S ∧ Step S g ∧ Build (insert g S) n f := by
  cases h with
  | next hs tail =>
    exact ⟨_, fun hg => shorter (buildDropRedundant hg tail), hs, tail⟩

theorem buildMinimumFirst {X : Type} {S : Set (Wire X)} {n : Nat} {f : Wire X}
    (h : Build S (n + 1) f) (minimum : ∀ k, Build S k f → n + 1 ≤ k) :
    ∃ g : Wire X, g ∉ S ∧ Step S g ∧ Build (insert g S) n f := by
  exact buildFreshFirst h (fun hk => Nat.not_succ_le_self n (minimum n hk))

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

theorem nextWordStep {ws : List Word} {z : Word} (h : z ∈ nextWords ws) :
    Step (avail ws) (denote z) := by
  obtain ⟨a, ha, hz⟩ := List.mem_flatMap.mp h
  have hav : denote a ∈ avail ws := ⟨a, ha, rfl⟩
  rcases List.mem_cons.mp hz with rfl | hz
  · have eq : denote (~~~a) = (fun x => !(denote a x)) := by
      funext x
      simp [denote, x.isLt]
    rw [eq]
    exact Step.neg hav
  · obtain ⟨b, hb, hz⟩ := List.mem_flatMap.mp hz
    have hbv : denote b ∈ avail ws := ⟨b, hb, rfl⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · have eq : denote (a &&& b) = (fun x => denote a x && denote b x) := by
        funext x
        simp [denote]
      rw [eq]
      exact Step.conj hav hbv
    · obtain rfl := List.mem_singleton.mp hz
      have eq : denote (a ||| b) = (fun x => denote a x || denote b x) := by
        funext x
        simp [denote]
      rw [eq]
      exact Step.disj hav hbv

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

def proj (keep ones : Nat) (i : Row) : Row :=
  ⟨((i.val &&& keep) ||| ones) % 1024, Nat.mod_lt _ (by decide)⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

private def axisMask : Fin 10 → Word := ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

private def forceAxis (j : Fin 10) (one : Bool) (w : Word) : Word :=
  let mask := axisMask j
  let stride := 2^j.val
  if one then (w &&& mask) ||| ((w >>> stride) &&& ~~~mask)
  else (w &&& ~~~mask) ||| ((w <<< stride) &&& mask)

private def forcedRow (j : Fin 10) (one : Bool) (r : BitVec 10) : BitVec 10 :=
  let b : BitVec 10 := 1 <<< j.val
  if one then r ||| b else r &&& ~~~b

set_option maxRecDepth 14000 in
set_option maxHeartbeats 4000000 in
private theorem laneIndex (j : Fin 10) (r : BitVec 10) :
    if (axisMask j).getLsbD r.toNat then
      (forcedRow j true r).toNat = r.toNat ∧ 2^j.val ≤ r.toNat ∧
        (forcedRow j false r).toNat = r.toNat - 2^j.val
    else (forcedRow j false r).toNat = r.toNat ∧
        (forcedRow j true r).toNat = 2^j.val + r.toNat := by
  have h : ∀ j : Fin 10, ∀ r : Fin 1024,
      if (axisMask j).getLsbD r.val then
        (forcedRow j true (BitVec.ofFin r)).toNat = r.val ∧ 2^j.val ≤ r.val ∧
        (forcedRow j false (BitVec.ofFin r)).toNat = r.val - 2^j.val
      else (forcedRow j false (BitVec.ofFin r)).toNat = r.val ∧
        (forcedRow j true (BitVec.ofFin r)).toNat = 2^j.val + r.val := by
    intro j
    fin_cases j <;> decide
  exact h j r.toFin

private theorem forceAxis_value (j : Fin 10) (b : Bool) (w : Word) (r : BitVec 10) :
    denote (forceAxis j b w) r.toFin = denote w (forcedRow j b r).toFin := by
  have idx := laneIndex j r
  have hr : r.toNat < 1024 := r.isLt
  cases hb : (axisMask j).getLsbD r.toNat <;>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at idx <;>
    cases b <;>
    simp only [denote, forceAxis, Bool.false_eq_true, ↓reduceIte, BitVec.val_toFin,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hb, hr, decide_true,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.true_or,
      Bool.false_or, Bool.or_true, Bool.or_false, Bool.not_true, Bool.not_false] <;>
    first | rw [idx.1] | rw [idx.2] | simp [idx.2.2,not_lt_of_ge idx.2.1]

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

def bitRow (j : Fin 10) (b : Bool) (r : Row) : Row :=
  if b then proj 1023 (2^j.val) r else proj (1023 - 2^j.val) 0 r

end PEqualNP.Outside.L_meta_1543.Cert
namespace PEqualNP.Outside.L_meta_1543.Cert

def mapBit (keep ones : Nat) (j : Fin 10) (r : Row) : Row :=
  if ones.testBit j.val then bitRow j true r
  else if keep.testBit j.val then r else bitRow j false r

def foldMap (keep ones : Nat) (js : List (Fin 10)) (r : Row) : Row :=
  js.foldr (mapBit keep ones) r

private theorem proj_bit (keep ones : Nat) (r : Row) (q : Fin 10) :
    (proj keep ones r).val.testBit q.val =
      ((r.val.testBit q.val && keep.testBit q.val) || ones.testBit q.val) := by
  change ((((r.val &&& keep) ||| ones) % 2^10).testBit q.val) = _
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_and,
    decide_eq_true q.isLt, Bool.true_and]

private theorem bitRow_bit (j q : Fin 10) (b : Bool) (r : Row) :
    (bitRow j b r).val.testBit q.val = if q = j then b else r.val.testBit q.val := by
  have masks : ∀ j q : Fin 10, (1023 : Nat).testBit q.val = true ∧
      (2^j.val : Nat).testBit q.val = decide (q = j) ∧
      (1023 - 2^j.val : Nat).testBit q.val = decide (q ≠ j) := by decide
  obtain ⟨all,set,clear⟩ := masks j q
  cases b with
  | false =>
    change (proj (1023 - 2^j.val) 0 r).val.testBit q.val = _
    rw [proj_bit,clear,Nat.zero_testBit]
    by_cases eq : q = j <;> simp [eq]
  | true =>
    change (proj 1023 (2^j.val) r).val.testBit q.val = _
    rw [proj_bit,all,set]
    by_cases eq : q = j <;> simp [eq]

private theorem foldMap_bit (keep ones : Nat) (js : List (Fin 10)) (r : Row) (q : Fin 10) :
    (foldMap keep ones js r).val.testBit q.val = if q ∈ js then
      ((r.val.testBit q.val && keep.testBit q.val) || ones.testBit q.val) else r.val.testBit q.val := by
  induction js with
  | nil => simp [foldMap]
  | cons j js ih =>
    change (mapBit keep ones j (foldMap keep ones js r)).val.testBit q.val = _
    by_cases e : q = j
    · subst j
      cases ho : ones.testBit q.val <;> cases hk : keep.testBit q.val <;>
        by_cases mem : q ∈ js <;> simp [mapBit,ho,hk,bitRow_bit,ih,mem]
    · cases ho : ones.testBit j.val <;> cases hk : keep.testBit j.val <;>
        simp [mapBit,ho,hk,bitRow_bit,e,ih]

theorem foldMap_all (keep ones : Nat) (r : Row) :
    foldMap keep ones (List.finRange 10) r = proj keep ones r := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 10
  · let q : Fin 10 := ⟨i,h⟩
    have hh := foldMap_bit keep ones (List.finRange 10) r q
    rw [if_pos (List.mem_finRange q), ←proj_bit] at hh
    exact hh
  · have pow : 1024 ≤ 2^i := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 10 ≤ i)
    have zero (z : Row) : z.val.testBit i = false := Nat.testBit_lt_two_pow (z.isLt.trans_le pow)
    rw [zero,zero]

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

private theorem rowBitVector (keep ones : Nat) (r : Row) :
    (BitVec.ofFin (proj keep ones r) : BitVec 10) =
      ((BitVec.ofFin r : BitVec 10) &&& BitVec.ofNat 10 keep) ||| BitVec.ofNat 10 ones := by
  have eq : (BitVec.ofFin r : BitVec 10) = BitVec.ofNat 10 r.val :=
    (BitVec.ofNat_finVal (w := 10) r).symm
  rw [eq, ← BitVec.ofNat_and, ← BitVec.ofNat_or]
  rfl

private theorem forcedRow_eq_bitRow (j : Fin 10) (b : Bool) (r : Row) :
    (forcedRow j b (BitVec.ofFin r)).toFin = bitRow j b r := by
  have masks : ∀ j : Fin 10,
      (↑((1 : Nat) <<< j.val) : BitVec 10) = BitVec.ofNat 10 (2^j.val) ∧
      (~~~(↑((1 : Nat) <<< j.val) : BitVec 10)) = BitVec.ofNat 10 (1023-2^j.val) := by decide
  obtain ⟨set,clear⟩ := masks j
  have full : BitVec.ofNat 10 1023 = BitVec.allOnes 10 := by decide
  change _ = (BitVec.ofFin (bitRow j b r) : BitVec 10).toFin
  congr 1
  cases b with
  | false => simp only [bitRow, Bool.false_eq_true, ↓reduceIte, rowBitVector, forcedRow, clear,
      BitVec.or_zero]
  | true => simp only [bitRow, ↓reduceIte, rowBitVector, forcedRow, set, full, BitVec.and_allOnes]

private def axisUpdate (keep ones : Nat) (w : Word) (j : Fin 10) : Word :=
  if ones.testBit j.val then forceAxis j true w
  else if keep.testBit j.val then w else forceAxis j false w

private theorem axisUpdate_sem (keep ones : Nat) (w : Word) (j : Fin 10) (r : Row) :
    denote (axisUpdate keep ones w j) r = denote w (mapBit keep ones j r) := by
  have axis (b : Bool) : denote (forceAxis j b w) r = denote w (bitRow j b r) :=
    (forceAxis_value j b w (BitVec.ofFin r)).trans (congrArg (denote w) (forcedRow_eq_bitRow j b r))
  cases h₀ : ones.testBit j.val <;> cases h₁ : keep.testBit j.val <;>
    simp only [axisUpdate, mapBit, h₀, h₁, Bool.false_eq_true, ↓reduceIte, axis]

def fastPullWord (keep ones : Nat) (w : Word) : Word :=
  (List.finRange 10).foldl (axisUpdate keep ones) w

private theorem axisFold_sem (keep ones : Nat) (js : List (Fin 10)) (w : Word) (r : Row) :
    denote (js.foldl (axisUpdate keep ones) w) r = denote w (foldMap keep ones js r) := by
  induction js generalizing w with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons,ih,axisUpdate_sem]
    rfl

theorem denote_fastPullWord (keep ones : Nat) (w : Word) :
    denote (fastPullWord keep ones w) = denote w ∘ proj keep ones := by
  funext r
  exact (axisFold_sem keep ones (List.finRange 10) w r).trans
    (congrArg (denote w) (foldMap_all keep ones r))

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

def pullWord (keep ones : Nat) (w : Word) : Word := fastPullWord keep ones w

theorem denote_pullWord (keep ones : Nat) (w : Word) :
    denote (pullWord keep ones w) = denote w ∘ proj keep ones :=
  denote_fastPullWord keep ones w

def WordLower (ws : List Word) (out : Word) (low : Nat) : Prop :=
  ∀ n, Build (avail ws) n (denote out) → low ≤ n

def mapOK (ws ts : List Word) (keep ones : Nat) : Bool :=
  ws.all fun w => ts.contains (pullWord keep ones w)

theorem mapOK_sound {ws ts : List Word} {keep ones : Nat} (h : mapOK ws ts keep ones = true) :
    ∀ w ∈ avail ws, w ∘ proj keep ones ∈ avail ts := by
  intro w hw
  obtain ⟨z,hz,e⟩ := hw
  subst w
  refine ⟨pullWord keep ones z, ?_, (denote_pullWord _ _ _).symm⟩
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h z hz)

def constOK (ts : List Word) : Bool := ts.contains 0 && ts.contains (~~~(0 : Word))

theorem denote_zero : denote 0 = fun _ : Row => false := by
  funext i
  simp [denote]

theorem denote_ones : denote (~~~(0 : Word)) = fun _ : Row => true := by
  funext i
  have z : (0 : Word).getLsbD i.val = false := congrFun denote_zero i
  simp only [denote, BitVec.getLsbD_not, z, i.isLt, decide_true, Bool.not_false, Bool.and_self]

theorem constOK_sound {ts : List Word} (h : constOK ts = true) :
    ∀ c : Bool, (fun _ : Row => c) ∈ avail ts := by
  simp only [constOK,Bool.and_eq_true] at h
  obtain ⟨hz,ho⟩ := h
  intro c
  cases c with
  | false => exact ⟨0,List.contains_iff_mem.mp hz,denote_zero.symm⟩
  | true => exact ⟨~~~(0 : Word),List.contains_iff_mem.mp ho,denote_ones.symm⟩

theorem wordDenoteInjective : Function.Injective denote := by
  intro u v h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun h ⟨i,hi⟩

def wordNC (w : Word) : Bool := (w != 0) && (w != ~~~(0 : Word))

theorem wordNC_sound {w : Word} (h : wordNC w = true) :
    ∃ a b, denote w a ≠ denote w b := by
  simp only [wordNC,Bool.and_eq_true] at h
  obtain ⟨hz,ho⟩ := h
  by_contra! same
  cases t : denote w 0 with
  | false =>
    have eq : w = 0 := wordDenoteInjective (by funext i; rw [denote_zero]; exact (same i 0).trans t)
    simp [eq] at hz
  | true =>
    have eq : w = ~~~(0 : Word) := wordDenoteInjective (by funext i; rw [denote_ones]; exact (same i 0).trans t)
    simp [eq] at ho

def flipAt (w : Word) (p : Row × Row) : Bool := denote w p.1 != denote w p.2

def srcOK (pairs : List (Row × Row)) (keep ones : Nat) (w : Word) : Bool :=
  pairs.all fun i => !(flipAt w i) ||
    (!(wordNC (pullWord keep ones w)) && (pairs.all fun j => !(flipAt w j) || (i == j)))

theorem srcOK_sound {pairs : List (Row × Row)} {keep ones : Nat} {w : Word}
    (h : srcOK pairs keep ones w = true) {i : Row × Row} (hi : i ∈ pairs) (di : flipAt w i = true) :
    wordNC (pullWord keep ones w) = false ∧ ∀ j ∈ pairs, flipAt w j = true → i = j := by
  have atI := List.all_eq_true.mp h i hi
  simp only [di, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true] at atI
  refine ⟨atI.1, ?_⟩
  intro j hj dj
  simpa [dj] using atI.2 j hj

def cutOK (ws ts : List Word) (out child : Word) (keep ones : Nat) (pairs : List (Row × Row)) : Bool :=
  mapOK ws ts keep ones && constOK ts && wordNC child &&
    (pullWord keep ones out == child) && decide pairs.Nodup &&
    pairs.all (flipAt out) && ws.all (srcOK pairs keep ones)

theorem cutLower {ws ts : List Word} {out child : Word} {keep ones low : Nat}
    {pairs : List (Row × Row)} (pass : cutOK ws ts out child keep ones pairs = true)
    (h : WordLower ts child low) : WordLower ws out (pairs.length + low) := by
  simp only [cutOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at pass
  obtain ⟨⟨⟨⟨⟨⟨maps,constants⟩,nc⟩,childEq⟩,nodup⟩,diff⟩,source⟩ := pass
  have childSem : denote out ∘ proj keep ones = denote child := by
    rw [← denote_pullWord, childEq]
  intro n build
  have sg (w : Word) (hw : w ∈ ws) := source w hw
  obtain ⟨k,hk,program⟩ := pullBuild_multi build (proj keep ones) Prod.fst Prod.snd pairs.toFinset
    (fun i hi => by simpa [ChangesOn,flipAt] using diff i (List.mem_toFinset.mp hi))
    (by obtain ⟨a,b,hab⟩ := wordNC_sound nc; exact ⟨a,b,by
          change (denote out ∘ proj keep ones) a ≠ (denote out ∘ proj keep ones) b
          rwa [childSem]⟩)
    (mapOK_sound maps) (constOK_sound constants)
    (by
      intro _ hx i hi j hj di dj
      obtain ⟨w,hw,rfl⟩ := hx
      have ci := srcOK_sound (sg w hw) (List.mem_toFinset.mp hi)
        (by simpa [ChangesOn,flipAt] using di)
      exact ci.2 j (List.mem_toFinset.mp hj) (by simpa [ChangesOn,flipAt] using dj))
    (by
      intro _ hx i hi di
      obtain ⟨w,hw,rfl⟩ := hx
      have van := (srcOK_sound (sg w hw) (List.mem_toFinset.mp hi)
        (by simpa [ChangesOn,flipAt] using di)).1
      by_cases hz : pullWord keep ones w = 0
      · exact ⟨false, by rw [← denote_pullWord, hz, denote_zero]⟩
      · have ho : pullWord keep ones w = ~~~(0 : Word) := by
          have imp : pullWord keep ones w ≠ 0 → pullWord keep ones w = ~~~(0 : Word) := by
            simpa [wordNC] using van
          exact imp hz
        exact ⟨true, by rw [← denote_pullWord, ho, denote_ones]⟩)
  rw [childSem] at program
  have childLow := h k program
  rw [List.toFinset_card_of_nodup nodup] at hk
  omega

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

def supplyCost (rich need : List Word) : Option Nat :=
  match need with
  | [] => some 0
  | z :: zs =>
    if z ∈ rich then supplyCost rich zs
    else if z ∈ nextWords rich then (supplyCost (z::rich) zs).map (fun c => c+1)
    else none

theorem avail_inclusion {xs ys : List Word} (h : ∀ z ∈ xs, z ∈ ys) : avail xs ⊆ avail ys :=
  fun _ ⟨z,hz,eq⟩ => ⟨z,h z hz,eq⟩

theorem supplyBuild {rich need : List Word} {f : Wire Row} {c n : Nat}
    (hc : supplyCost rich need = some c) (tail : Build (avail (rich ++ need)) n f) :
    Build (avail rich) (n+c) f := by
  induction need generalizing rich c with
  | nil =>
    have eq : c=0 := by simpa [supplyCost] using hc.symm
    simpa [eq] using tail
  | cons z zs ih =>
    by_cases old : z ∈ rich
    · have cost : supplyCost rich zs = some c := by simpa [supplyCost,old] using hc
      apply ih cost
      apply buildMono (T:=avail (rich ++ zs)) _ tail
      apply avail_inclusion
      intro w h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_append_left _ old
        · exact List.mem_append_right _ h
    by_cases valid : z ∈ nextWords rich
    · cases sc : supplyCost (z::rich) zs with
      | none => simp [supplyCost,old,valid,sc] at hc
      | some d =>
        have eq : d+1=c := by simpa [supplyCost,old,valid,sc] using hc
        have expanded : Build (avail ((z::rich) ++ zs)) n f := by
          apply buildMono _ tail
          apply avail_inclusion
          intro w h
          rcases List.mem_append.mp h with h | h
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.mp h with rfl | h
            · exact List.mem_append_left _ List.mem_cons_self
            · exact List.mem_append_right _ h
        have rest := ih sc expanded
        rw [avail_cons] at rest
        have result := Build.next (nextWordStep valid) rest
        convert result using 1 <;> omega
    · simp [supplyCost,old,valid] at hc

theorem transportLower {rich need : List Word} {out : Word} {k c : Nat}
    (lower : WordLower rich out k) (cost : supplyCost rich need = some c) :
    WordLower need out (k-c) := by
  intro n h
  have bigger : Build (avail (rich ++ need)) n (denote out) :=
    buildMono (avail_inclusion (fun _ h => List.mem_append_right _ h)) h
  have bound := lower (n+c) (supplyBuild cost bigger)
  omega

theorem splitLower {ws : List Word} {out : Word} {parentLow : Nat} (absent : out ∉ ws)
    (children : ∀ z ∈ nextWords ws, z ∉ ws →
      ∃ (ys : List Word) (hLow c : Nat), WordLower ys out hLow ∧
        supplyCost ys (ws ++ [z]) = some c ∧ parentLow-1+c ≤ hLow) :
    WordLower ws out parentLow := by
  intro n h
  obtain ⟨z,hz,fresh,k,small,tail⟩ := firstNewWord (fun hm => absent (denote_mem_avail.mp hm)) h
  obtain ⟨ys,hLow,c,low,sc,budget⟩ := children z hz fresh
  have tail' : Build (avail (ws ++ [z])) k (denote out) := by
    apply buildMono _ tail
    apply avail_inclusion
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ hw
  have bound := transportLower low sc k tail'
  omega

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

/-- Every source that separates the witness pair is fixed at zero and one
on the respective projections. -/
def twoPinsOK (ws : List Word) (keep₀ ones₀ keep₁ ones₁ : Nat) (a b : Row) : Bool :=
  ws.all fun z => decide (denote z a = denote z b) ||
    (decide (pullWord keep₀ ones₀ z = 0) &&
     decide (pullWord keep₁ ones₁ z = ~~~(0 : Word)))

theorem twoPinsOK_sound {ws : List Word} {keep₀ ones₀ keep₁ ones₁ : Nat} {a b : Row}
    (h : twoPinsOK ws keep₀ ones₀ keep₁ ones₁ a b = true) :
    ∀ w ∈ avail ws, w a ≠ w b →
      w ∘ proj keep₀ ones₀ = (fun _ => false) ∧
      w ∘ proj keep₁ ones₁ = (fun _ => true) := by
  intro w hw diff
  obtain ⟨z,hz,rfl⟩ := hw
  have row := (List.all_eq_true.mp h) z hz
  simp only [diff,decide_false,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] at row
  rw [← denote_pullWord,← denote_pullWord,row.1,row.2]
  exact ⟨denote_zero,denote_ones⟩

/-- Finite checks for the two restrictions, including target separation,
nonconstancy, and availability of all pulled wires and both constants. -/
def twoSidesOK (ws : List Word) (out : Word) (ts₀ ts₁ : List Word)
    (keep₀ ones₀ keep₁ ones₁ : Nat) (a b : Row) : Bool :=
  mapOK ws ts₀ keep₀ ones₀ && (mapOK ws ts₁ keep₁ ones₁ &&
  (constOK ts₀ && (constOK ts₁ &&
  (decide (denote out a ≠ denote out b) &&
  (wordNC (pullWord keep₀ ones₀ out) && (wordNC (pullWord keep₁ ones₁ out) &&
   twoPinsOK ws keep₀ ones₀ keep₁ ones₁ a b))))))

theorem tableTwoSides {ws ts₀ ts₁ : List Word} {out : Word}
    {keep₀ ones₀ keep₁ ones₁ : Nat} {a b : Row} {A B : Nat}
    (ok : twoSidesOK ws out ts₀ ts₁ keep₀ ones₀ keep₁ ones₁ a b = true)
    (low₀ : WordLower ts₀ (pullWord keep₀ ones₀ out) A)
    (low₁ : WordLower ts₁ (pullWord keep₁ ones₁ out) B) :
    WordLower ws out (min (max (A+2) (B+1)) (max (A+1) (B+2))) := by
  simp only [twoSidesOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨m₀,m₁,c₀,c₁,d,v₀,v₁,p⟩ := ok
  intro n full
  have v₀' : ∃ y z, denote out (proj keep₀ ones₀ y) ≠ denote out (proj keep₀ ones₀ z) := by
    simpa only [denote_pullWord,Function.comp_apply] using wordNC_sound v₀
  have v₁' : ∃ y z, denote out (proj keep₁ ones₁ y) ≠ denote out (proj keep₁ ones₁ z) := by
    simpa only [denote_pullWord,Function.comp_apply] using wordNC_sound v₁
  obtain ⟨s,t,build₀,build₁,paid₀,paid₁,extra⟩ :=
    pullBuild_twoSides full (proj keep₀ ones₀) (proj keep₁ ones₁) a b d v₀' v₁'
      (mapOK_sound m₀) (mapOK_sound m₁) (constOK_sound c₀) (constOK_sound c₁) (twoPinsOK_sound p)
  have hs := low₀ s (by simpa only [denote_pullWord] using build₀)
  have ht := low₁ t (by simpa only [denote_pullWord] using build₁)
  rcases extra with h|h
  · exact (min_le_left _ _).trans (max_le (by omega) (by omega))
  · exact (min_le_right _ _).trans (max_le (by omega) (by omega))

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert
open PEqualNP.MetaComplexity

/-- Little-endian truth table for an input wire in ten variables. -/
def primaryWord : Nat → Word
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 8 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
  | 9 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0

def edgePairs : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0),(0,7),(1,8),(2,9)]

def targetWord (vertices literals : Nat) : Word :=
  let literalPart := (List.range 10).foldr (fun i w =>
    if literals.testBit i then primaryWord i ||| w else w) 0
  edgePairs.foldr (fun e w =>
    if vertices.testBit e.1 && vertices.testBit e.2 then
      (primaryWord e.1 &&& primaryWord e.2) ||| w else w) literalPart

def sources (vertices literals : Nat) (extra : List Word) : List Word :=
  0 :: BitVec.allOnes 1024 ::
    (((List.range 10).filter fun i => (vertices ||| literals).testBit i).map primaryWord ++ extra)

def rowInput (r : Row) (i : Fin 10) := r.val.testBit i.val

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
theorem denote_primaryWord : ∀ (i : Fin 10) (r : Row), denote (primaryWord i) r = rowInput r i := by
  intro i
  fin_cases i <;> decide

private theorem rootSources :
    sources 1023 0 [] = 0 :: BitVec.allOnes 1024 :: (List.range 10).map primaryWord := by
  rfl

private theorem rootInputsAvailable :
    ∀ w ∈ {w : Wire (Fin 10 → Bool) | w = (fun _ => false) ∨ w = (fun _ => true) ∨
      ∃ i : Fin 10, w = (fun x => x i)}, w ∘ rowInput ∈ avail (sources 1023 0 []) := by
  intro w hw
  rw [rootSources]
  rcases hw with rfl | rfl | ⟨i,rfl⟩
  · exact ⟨0, List.mem_cons_self, by funext r; simp [denote]⟩
  · exact ⟨BitVec.allOnes _, List.mem_cons_of_mem _ List.mem_cons_self, by
      funext r
      change true = (BitVec.allOnes 1024).getLsbD r.val
      rw [BitVec.getLsbD_allOnes, decide_eq_true r.isLt]⟩
  · refine ⟨primaryWord i, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_), ?_⟩
    · exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    · exact funext fun r => (denote_primaryWord i r).symm

private def fullEdgeWord : Word :=
  (primaryWord 0 &&& primaryWord 1) ||| ((primaryWord 1 &&& primaryWord 2) ||| ((primaryWord 2 &&& primaryWord 3) ||| ((primaryWord 3 &&& primaryWord 4) ||| ((primaryWord 4 &&& primaryWord 5) ||| ((primaryWord 5 &&& primaryWord 6) ||| ((primaryWord 6 &&& primaryWord 0) ||| ((primaryWord 0 &&& primaryWord 7) ||| ((primaryWord 1 &&& primaryWord 8) ||| ((primaryWord 2 &&& primaryWord 9) ||| (0))))))))))

private theorem rootTarget : targetWord 1023 0 = fullEdgeWord := by rfl

theorem rootFromWordLower (lower : WordLower (sources 1023 0 []) (targetWord 1023 0) 14) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (2, 9)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) s → 14 ≤ s := by
  intro s hs
  obtain ⟨k,hks,proof⟩ := buildOfHasCircuitSize hs
  have pulled := pullBuild proof rowInput rootInputsAvailable
  apply le_trans (lower k ?_) hks
  rw [rootTarget]
  have funEq : denote fullEdgeWord =
      ((fun x : Fin 10 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,0),(0,7),(1,8),(2,9)] : List (Fin 10 × Fin 10)).any
          (fun e => x e.1 && x e.2)) ∘ rowInput) := by
    funext r
    have h (i : Fin 10) : (primaryWord i).getLsbD r.val = rowInput r i := denote_primaryWord i r
    have hz : (0 : Word).getLsbD r.val = false := by simp
    simp only [fullEdgeWord, denote, BitVec.getLsbD_or, BitVec.getLsbD_and, hz,
      Bool.or_false, List.any_cons, List.any_nil, Function.comp_apply]
    rw [← h 0,← h 1,← h 2,← h 3,← h 4,← h 5,← h 6,← h 7,← h 8,← h 9]
    rfl
  exact funEq.symm ▸ pulled

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

structure Bound where
  inputs : List Word
  output : Word
  low : Nat

def state (vertices literals : Nat) (extra : List Word) (low : Nat) : Bound :=
  ⟨sources vertices literals extra,targetWord vertices literals,low⟩

def Good (p : Bound) : Prop := WordLower p.inputs p.output p.low

theorem goodZero (p : Bound) (h : p.low = 0) : Good p :=
  fun n _ => h ▸ Nat.zero_le n

theorem goodOne (p : Bound) (h : p.output ∉ p.inputs ∧ p.low ≤ 1) : Good p := by
  intro n hp
  cases n with
  | zero => exact (h.1 (denote_mem_avail.mp (zeroWord hp))).elim
  | succ k => omega

theorem goodCut {p c : Bound} (child : Good c) (keep ones : Nat) (pairs : List (Row × Row))
    (check : cutOK p.inputs c.inputs p.output c.output keep ones pairs = true ∧
       p.low ≤ pairs.length+c.low) : Good p :=
  fun n h => check.2.trans (cutLower check.1 child n h)

theorem goodBoth {p a b : Bound} (ha : Good a) (hb : Good b)
    (k₀ o₀ k₁ o₁ : Nat) (x y : Row)
    (check : twoSidesOK p.inputs p.output a.inputs b.inputs k₀ o₀ k₁ o₁ x y = true ∧
       a.output = pullWord k₀ o₀ p.output ∧ b.output = pullWord k₁ o₁ p.output ∧
       p.low ≤ min (max (a.low+2) (b.low+1)) (max (a.low+1) (b.low+2))) : Good p := by
  obtain ⟨ok, e₀, e₁, order⟩ := check
  have ca : WordLower a.inputs (pullWord k₀ o₀ p.output) a.low := e₀ ▸ ha
  have cb : WordLower b.inputs (pullWord k₁ o₁ p.output) b.low := e₁ ▸ hb
  exact fun n h => order.trans (tableTwoSides ok ca cb n h)

structure Checked where
  bound : Bound
  proof : Good bound

def checked {b : Bound} (h : Good b) : Checked := ⟨b,h⟩

def freshWords (ws : List Word) : List Word :=
  ((nextWords ws).eraseDups).filter fun x => !(ws.contains x)

def covers (p : Bound) (z : Word) (c : Checked) : Bool :=
  (c.bound.output == p.output) &&
  match supplyCost c.bound.inputs (p.inputs ++ [z]) with
  | none => false
  | some t => decide (p.low-1+t ≤ c.bound.low)

def auditRows (p : Bound) : List Word → List Checked → Bool
  | [],[] => true
  | z :: zs,c :: cs => covers p z c && auditRows p zs cs
  | _,_ => false

theorem rowCovered (p : Bound) {zs : List Word} {cs : List Checked}
    (h : auditRows p zs cs = true) {z : Word} (hz : z ∈ zs) :
    ∃ c, covers p z c = true := by
  induction zs generalizing cs with
  | nil => simp at hz
  | cons w ws ih =>
    cases cs with
    | nil => simp [auditRows] at h
    | cons c rest =>
      simp only [auditRows, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hz with rfl|tail
      · exact ⟨c,h.1⟩
      · exact ih h.2 tail

theorem goodSplit (p : Bound) (cs : List Checked)
    (h : p.output ∉ p.inputs ∧ auditRows p (freshWords p.inputs) cs = true) : Good p := by
  apply splitLower h.1
  intro z hz fresh
  have ok : z ∈ freshWords p.inputs := by simpa [freshWords,hz,fresh]
  obtain ⟨c,hc⟩ := rowCovered p h.2 ok
  simp only [covers, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨eq, pass⟩ := hc
  cases cost : supplyCost c.bound.inputs (p.inputs ++ [z]) with
  | none => simp [cost] at pass
  | some t =>
    refine ⟨c.bound.inputs,c.bound.low,t,?_,cost,?_⟩
    · exact eq ▸ c.proof
    · simpa [cost] using pass

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert
def supplyValue (rich : List Word) (code : Nat) : Option Word := do
  let a ← rich[code % 32]?
  if code / 1024 % 4 = 0 then return ~~~a
  let b ← rich[code / 32 % 32]?
  if code / 1024 % 4 = 1 then return a &&& b else return a ||| b

def citedCost (rich need : List Word) (hints : Nat) : Option Nat :=
  match need with
  | [] => some 0
  | z :: zs =>
    if z ∈ rich then citedCost rich zs hints
    else if supplyValue rich (hints % 4096) = some z then
      (citedCost (z::rich) zs (hints/4096)).map (fun c => c+1)
    else none

theorem mem_next_supply {ws : List Word} {c : Nat} {z : Word}
    (hv : supplyValue ws c = some z) : z ∈ nextWords ws := by
  cases ha : ws[c % 32]? with
  | none => simp [supplyValue,ha] at hv
  | some a =>
    have am := List.mem_of_getElem? ha
    by_cases neg : c/1024 % 4=0
    · simp [supplyValue,ha,neg] at hv
      subst z
      exact List.mem_flatMap.mpr ⟨a,am,List.mem_cons_self⟩
    · cases hb : ws[c/32 % 32]? with
      | none => simp [supplyValue,ha,neg,hb] at hv
      | some b =>
        have bm := List.mem_of_getElem? hb
        by_cases conj : c/1024 % 4=1
        · simp [supplyValue,ha,neg,hb,conj] at hv
          subst z
          exact List.mem_flatMap.mpr ⟨a,am,List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,bm,by simp⟩)⟩
        · simp [supplyValue,ha,neg,hb,conj] at hv
          subst z
          exact List.mem_flatMap.mpr ⟨a,am,List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,bm,by simp⟩)⟩

theorem citedCost_sound {rich need : List Word} {hints cost : Nat}
    (h : citedCost rich need hints = some cost) : supplyCost rich need = some cost := by
  induction need generalizing rich hints cost with
  | nil => simpa [citedCost,supplyCost] using h
  | cons z zs ih =>
    by_cases old : z ∈ rich
    · have tail : citedCost rich zs hints = some cost := by simpa only [citedCost,ite_eq_left old] using h
      simpa only [supplyCost,ite_eq_left old] using ih tail
    by_cases exactGate : supplyValue rich (hints % 4096) = some z
    · have hz := mem_next_supply exactGate
      simp only [citedCost,ite_eq_right old,ite_eq_left exactGate] at h
      simp only [supplyCost,ite_eq_right old,ite_eq_left hz]
      cases next : citedCost (z::rich) zs (hints/4096) with
      | none => simp [next] at h
      | some d => rw [ih next]; simpa [next] using h
    · simp [citedCost,old,exactGate] at h

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert

def fastCovers (p : Bound) (z : Word) (c : Checked) (hints : Nat) : Bool :=
  (c.bound.output == p.output) &&
  match citedCost c.bound.inputs (p.inputs ++ [z]) hints with
  | none => false
  | some t => decide (p.low-1+t ≤ c.bound.low)

theorem fastCovers_sound {p : Bound} {z : Word} {c : Checked} {hints : Nat}
    (h : fastCovers p z c hints = true) : covers p z c = true := by
  cases hc : citedCost c.bound.inputs (p.inputs ++ [z]) hints with
  | none => simp [fastCovers,hc] at h
  | some t => unfold covers
              rw [citedCost_sound hc]
              simpa only [fastCovers,hc] using h

def fastAuditRows (p : Bound) : List Word → List Checked → List Nat → Bool
  | [], [], [] => true
  | z :: zs, c :: cs, hints :: rest =>
    fastCovers p z c hints && fastAuditRows p zs cs rest
  | _, _, _ => false

theorem fastAuditRows_sound {p : Bound} {zs : List Word} {cs : List Checked} {digits : List Nat}
    (h : fastAuditRows p zs cs digits = true) : auditRows p zs cs = true := by
  induction zs generalizing cs digits with
  | nil => cases cs <;> cases digits <;> simpa [fastAuditRows,auditRows] using h
  | cons z zs ih =>
    cases cs with
    | nil => simp [fastAuditRows] at h
    | cons c cs =>
      cases digits with
      | nil => simp [fastAuditRows] at h
      | cons d ds =>
        simp only [fastAuditRows, Bool.and_eq_true] at h
        simp only [auditRows, Bool.and_eq_true]
        exact ⟨fastCovers_sound h.1, ih h.2⟩

theorem fastGoodSplit (p : Bound) (cs : List Checked) (digits : List Nat)
    (h : p.output ∉ p.inputs ∧ fastAuditRows p (freshWords p.inputs) cs digits = true) : Good p :=
  goodSplit p cs ⟨h.1,fastAuditRows_sound h.2⟩

end PEqualNP.Outside.L_meta_1543.Cert

namespace PEqualNP.Outside.L_meta_1543.Cert
private def row0 := state 0 4 [] 0
set_option maxRecDepth 8192 in
private theorem h0 : Good row0 :=
  goodZero row0 rfl

private def row1 := state 518 0 [] 2
set_option maxRecDepth 8192 in
private theorem h1 : Good row1 :=
  goodCut h0 4 2 [(4,6), (4,516)] (by decide)

private def row2 := state 0 2 [] 0
set_option maxRecDepth 8192 in
private theorem h2 : Good row2 :=
  goodZero row2 rfl

private def row3 := state 516 2 [] 2
set_option maxRecDepth 8192 in
private theorem h3 : Good row3 :=
  goodCut h2 2 0 [(512,516), (4,516)] (by decide)

private def row4 := state 774 0 [] 4
set_option maxRecDepth 8192 in
private theorem h4 : Good row4 :=
  goodBoth h1 h3 518 0 518 256 2 258 (by decide)

private def row5 := state 782 0 [] 5
set_option maxRecDepth 8192 in
private theorem h5 : Good row5 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row6 := state 774 8 [] 5
set_option maxRecDepth 8192 in
private theorem h6 : Good row6 :=
  goodCut h4 774 0 [(0,8)] (by decide)

private def row7 := state 798 0 [] 7
set_option maxRecDepth 8192 in
private theorem h7 : Good row7 :=
  goodBoth h5 h6 782 0 782 16 8 24 (by decide)

private def row8 := state 830 0 [] 8
set_option maxRecDepth 8192 in
private theorem h8 : Good row8 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row9 := state 798 32 [] 8
set_option maxRecDepth 8192 in
private theorem h9 : Good row9 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row10 := state 894 0 [] 10
set_option maxRecDepth 8192 in
private theorem h10 : Good row10 :=
  goodBoth h8 h9 830 0 830 64 32 96 (by decide)

private def row11 := state 895 0 [(primaryWord 0 &&& primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h11 : Good row11 :=
  goodCut h10 894 0 [(64,65)] (by decide)

private def row12 := state 894 1 [(primaryWord 0 &&& primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h12 : Good row12 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row13 := state 1023 0 [(primaryWord 0 &&& primaryWord 1)] 13
set_option maxRecDepth 8192 in
private theorem h13 : Good row13 :=
  goodBoth h11 h12 895 0 895 128 1 129 (by decide)

private def row14 := state 895 0 [(primaryWord 0 ||| primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h14 : Good row14 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row15 := state 894 1 [(primaryWord 0 ||| primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h15 : Good row15 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row16 := state 1023 0 [(primaryWord 0 ||| primaryWord 1)] 13
set_option maxRecDepth 8192 in
private theorem h16 : Good row16 :=
  goodBoth h14 h15 895 0 895 128 1 129 (by decide)

private def row17 := state 895 0 [(primaryWord 0 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h17 : Good row17 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row18 := state 894 1 [(primaryWord 0 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h18 : Good row18 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row19 := state 1023 0 [(primaryWord 0 &&& primaryWord 2)] 13
set_option maxRecDepth 8192 in
private theorem h19 : Good row19 :=
  goodBoth h17 h18 895 0 895 128 1 129 (by decide)

private def row20 := state 895 0 [(primaryWord 0 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h20 : Good row20 :=
  goodCut h10 894 0 [(68,69)] (by decide)

private def row21 := state 894 1 [(primaryWord 0 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h21 : Good row21 :=
  goodCut h10 894 0 [(4,5)] (by decide)

private def row22 := state 1023 0 [(primaryWord 0 ||| primaryWord 2)] 13
set_option maxRecDepth 8192 in
private theorem h22 : Good row22 :=
  goodBoth h20 h21 895 0 895 128 1 129 (by decide)

private def row23 := state 895 0 [(primaryWord 0 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h23 : Good row23 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row24 := state 894 1 [(primaryWord 0 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h24 : Good row24 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row25 := state 1023 0 [(primaryWord 0 &&& primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h25 : Good row25 :=
  goodBoth h23 h24 895 0 895 128 1 129 (by decide)

private def row26 := state 895 0 [(primaryWord 0 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h26 : Good row26 :=
  goodCut h10 894 0 [(10,11)] (by decide)

private def row27 := state 894 1 [(primaryWord 0 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h27 : Good row27 :=
  goodCut h10 894 0 [(8,9)] (by decide)

private def row28 := state 1023 0 [(primaryWord 0 ||| primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h28 : Good row28 :=
  goodBoth h26 h27 895 0 895 128 1 129 (by decide)

private def row29 := state 895 0 [(primaryWord 0 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h29 : Good row29 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row30 := state 894 1 [(primaryWord 0 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h30 : Good row30 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row31 := state 1023 0 [(primaryWord 0 &&& primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h31 : Good row31 :=
  goodBoth h29 h30 895 0 895 128 1 129 (by decide)

private def row32 := state 895 0 [(primaryWord 0 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h32 : Good row32 :=
  goodCut h10 894 0 [(18,19)] (by decide)

private def row33 := state 894 1 [(primaryWord 0 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h33 : Good row33 :=
  goodCut h10 894 0 [(16,17)] (by decide)

private def row34 := state 1023 0 [(primaryWord 0 ||| primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h34 : Good row34 :=
  goodBoth h32 h33 895 0 895 128 1 129 (by decide)

private def row35 := state 895 0 [(primaryWord 0 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h35 : Good row35 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row36 := state 894 1 [(primaryWord 0 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h36 : Good row36 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row37 := state 1023 0 [(primaryWord 0 &&& primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h37 : Good row37 :=
  goodBoth h35 h36 895 0 895 128 1 129 (by decide)

private def row38 := state 895 0 [(primaryWord 0 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h38 : Good row38 :=
  goodCut h10 894 0 [(34,35)] (by decide)

private def row39 := state 894 1 [(primaryWord 0 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h39 : Good row39 :=
  goodCut h10 894 0 [(32,33)] (by decide)

private def row40 := state 1023 0 [(primaryWord 0 ||| primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h40 : Good row40 :=
  goodBoth h38 h39 895 0 895 128 1 129 (by decide)

private def row41 := state 895 0 [(primaryWord 0 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h41 : Good row41 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row42 := state 894 1 [(primaryWord 0 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h42 : Good row42 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row43 := state 1023 0 [(primaryWord 0 &&& primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h43 : Good row43 :=
  goodBoth h41 h42 895 0 895 128 1 129 (by decide)

private def row44 := state 895 0 [(primaryWord 0 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h44 : Good row44 :=
  goodCut h10 894 0 [(64,65)] (by decide)

private def row45 := state 894 1 [(primaryWord 0 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h45 : Good row45 :=
  goodCut h10 894 0 [(64,65)] (by decide)

private def row46 := state 1023 0 [(primaryWord 0 ||| primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h46 : Good row46 :=
  goodBoth h44 h45 895 0 895 128 1 129 (by decide)

private def row47 := state 895 0 [(primaryWord 0 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h47 : Good row47 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row48 := state 895 0 [(primaryWord 0 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h48 : Good row48 :=
  goodCut h10 894 0 [(320,321)] (by decide)

private def row49 := state 895 0 [(primaryWord 0 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h49 : Good row49 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row50 := state 895 0 [(primaryWord 0 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h50 : Good row50 :=
  goodCut h10 894 0 [(514,515)] (by decide)

private def row51 := state 518 0 [(primaryWord 1 &&& primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h51 : Good row51 :=
  goodCut h0 4 512 [(4,6), (4,516)] (by decide)

private def row52 := state 516 2 [(primaryWord 1 &&& primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h52 : Good row52 :=
  goodCut h2 2 0 [(512,516), (4,516)] (by decide)

private def row53 := state 774 0 [(primaryWord 1 &&& primaryWord 2)] 4
set_option maxRecDepth 8192 in
private theorem h53 : Good row53 :=
  goodBoth h51 h52 518 0 518 256 2 258 (by decide)

private def row54 := state 782 0 [(primaryWord 1 &&& primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h54 : Good row54 :=
  goodCut h53 774 0 [(4,12)] (by decide)

private def row55 := state 774 8 [(primaryWord 1 &&& primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h55 : Good row55 :=
  goodCut h53 774 0 [(0,8)] (by decide)

private def row56 := state 798 0 [(primaryWord 1 &&& primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h56 : Good row56 :=
  goodBoth h54 h55 782 0 782 16 8 24 (by decide)

private def row57 := state 830 0 [(primaryWord 1 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h57 : Good row57 :=
  goodCut h56 798 0 [(16,48)] (by decide)

private def row58 := state 798 32 [(primaryWord 1 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h58 : Good row58 :=
  goodCut h56 798 0 [(0,32)] (by decide)

private def row59 := state 894 0 [(primaryWord 1 &&& primaryWord 2)] 10
set_option maxRecDepth 8192 in
private theorem h59 : Good row59 :=
  goodBoth h57 h58 830 0 830 64 32 96 (by decide)

private def row60 := state 895 0 [(primaryWord 1 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h60 : Good row60 :=
  goodCut h59 894 0 [(2,3)] (by decide)

private def row61 := state 518 0 [(primaryWord 1 ||| primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h61 : Good row61 :=
  goodCut h0 4 2 [(4,6), (4,516)] (by decide)

private def row62 := state 516 2 [(primaryWord 1 ||| primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h62 : Good row62 :=
  goodCut h2 2 4 [(512,516), (4,516)] (by decide)

private def row63 := state 774 0 [(primaryWord 1 ||| primaryWord 2)] 4
set_option maxRecDepth 8192 in
private theorem h63 : Good row63 :=
  goodBoth h61 h62 518 0 518 256 2 258 (by decide)

private def row64 := state 782 0 [(primaryWord 1 ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h64 : Good row64 :=
  goodCut h63 774 0 [(4,12)] (by decide)

private def row65 := state 774 8 [(primaryWord 1 ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h65 : Good row65 :=
  goodCut h63 774 0 [(0,8)] (by decide)

private def row66 := state 798 0 [(primaryWord 1 ||| primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h66 : Good row66 :=
  goodBoth h64 h65 782 0 782 16 8 24 (by decide)

private def row67 := state 830 0 [(primaryWord 1 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h67 : Good row67 :=
  goodCut h66 798 0 [(16,48)] (by decide)

private def row68 := state 798 32 [(primaryWord 1 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h68 : Good row68 :=
  goodCut h66 798 0 [(0,32)] (by decide)

private def row69 := state 894 0 [(primaryWord 1 ||| primaryWord 2)] 10
set_option maxRecDepth 8192 in
private theorem h69 : Good row69 :=
  goodBoth h67 h68 830 0 830 64 32 96 (by decide)

private def row70 := state 895 0 [(primaryWord 1 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h70 : Good row70 :=
  goodCut h69 894 0 [(2,3)] (by decide)

private def row71 := state 775 0 [] 5
set_option maxRecDepth 8192 in
private theorem h71 : Good row71 :=
  goodCut h4 774 0 [(2,3)] (by decide)

private def row72 := state 774 1 [] 5
set_option maxRecDepth 8192 in
private theorem h72 : Good row72 :=
  goodCut h4 774 0 [(0,1)] (by decide)

private def row73 := state 839 0 [] 7
set_option maxRecDepth 8192 in
private theorem h73 : Good row73 :=
  goodBoth h71 h72 775 0 775 64 1 65 (by decide)

private def row74 := state 871 0 [] 8
set_option maxRecDepth 8192 in
private theorem h74 : Good row74 :=
  goodCut h73 839 0 [(64,96)] (by decide)

private def row75 := state 839 32 [] 8
set_option maxRecDepth 8192 in
private theorem h75 : Good row75 :=
  goodCut h73 839 0 [(0,32)] (by decide)

private def row76 := state 887 0 [] 10
set_option maxRecDepth 8192 in
private theorem h76 : Good row76 :=
  goodBoth h74 h75 871 0 871 16 32 48 (by decide)

private def row77 := state 895 0 [(primaryWord 1 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h77 : Good row77 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row78 := state 895 0 [(primaryWord 1 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h78 : Good row78 :=
  goodCut h76 887 0 [(18,26)] (by decide)

private def row79 := state 879 0 [] 9
set_option maxRecDepth 8192 in
private theorem h79 : Good row79 :=
  goodCut h74 871 0 [(4,12)] (by decide)

private def row80 := state 839 40 [] 9
set_option maxRecDepth 8192 in
private theorem h80 : Good row80 :=
  goodCut h75 871 0 [(0,8)] (by decide)

private def row81 := state 895 0 [(primaryWord 1 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h81 : Good row81 :=
  goodBoth h79 h80 879 0 879 16 8 24 (by decide)

private def row82 := state 895 0 [(primaryWord 1 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h82 : Good row82 :=
  goodBoth h79 h80 879 0 879 16 10 26 (by decide)

private def row83 := state 847 0 [] 8
set_option maxRecDepth 8192 in
private theorem h83 : Good row83 :=
  goodCut h73 839 0 [(4,12)] (by decide)

private def row84 := state 839 8 [] 8
set_option maxRecDepth 8192 in
private theorem h84 : Good row84 :=
  goodCut h73 839 0 [(0,8)] (by decide)

private def row85 := state 863 0 [] 10
set_option maxRecDepth 8192 in
private theorem h85 : Good row85 :=
  goodBoth h83 h84 847 0 847 16 8 24 (by decide)

private def row86 := state 895 0 [(primaryWord 1 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h86 : Good row86 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row87 := state 895 0 [(primaryWord 1 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h87 : Good row87 :=
  goodCut h85 863 0 [(18,50)] (by decide)

private def row88 := state 831 0 [] 9
set_option maxRecDepth 8192 in
private theorem h88 : Good row88 :=
  goodCut h8 830 0 [(2,3)] (by decide)

private def row89 := state 798 33 [] 9
set_option maxRecDepth 8192 in
private theorem h89 : Good row89 :=
  goodCut h9 830 0 [(0,1)] (by decide)

private def row90 := state 895 0 [(primaryWord 1 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h90 : Good row90 :=
  goodBoth h88 h89 831 0 831 64 1 65 (by decide)

private def row91 := state 895 0 [(primaryWord 1 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h91 : Good row91 :=
  goodBoth h88 h89 831 0 831 64 34 98 (by decide)

private def row92 := state 0 32 [] 0
set_option maxRecDepth 8192 in
private theorem h92 : Good row92 :=
  goodZero row92 rfl

private def row93 := state 112 0 [] 2
set_option maxRecDepth 8192 in
private theorem h93 : Good row93 :=
  goodCut h92 32 16 [(32,48), (32,96)] (by decide)

private def row94 := state 0 16 [] 0
set_option maxRecDepth 8192 in
private theorem h94 : Good row94 :=
  goodZero row94 rfl

private def row95 := state 96 16 [] 2
set_option maxRecDepth 8192 in
private theorem h95 : Good row95 :=
  goodCut h94 16 0 [(64,96), (32,96)] (by decide)

private def row96 := state 120 0 [] 4
set_option maxRecDepth 8192 in
private theorem h96 : Good row96 :=
  goodBoth h93 h95 112 0 112 8 16 24 (by decide)

private def row97 := state 124 0 [] 5
set_option maxRecDepth 8192 in
private theorem h97 : Good row97 :=
  goodCut h96 120 0 [(8,12)] (by decide)

private def row98 := state 120 4 [] 5
set_option maxRecDepth 8192 in
private theorem h98 : Good row98 :=
  goodCut h96 120 0 [(0,4)] (by decide)

private def row99 := state 126 0 [] 7
set_option maxRecDepth 8192 in
private theorem h99 : Good row99 :=
  goodBoth h97 h98 124 0 124 2 4 6 (by decide)

private def row100 := state 127 0 [(primaryWord 0 &&& primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h100 : Good row100 :=
  goodCut h99 126 0 [(64,65)] (by decide)

private def row101 := state 127 0 [(primaryWord 0 ||| primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h101 : Good row101 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row102 := state 127 0 [(primaryWord 0 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h102 : Good row102 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row103 := state 127 0 [(primaryWord 0 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h103 : Good row103 :=
  goodCut h99 126 0 [(68,69)] (by decide)

private def row104 := state 127 0 [(primaryWord 0 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h104 : Good row104 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row105 := state 127 0 [(primaryWord 0 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h105 : Good row105 :=
  goodCut h99 126 0 [(10,11)] (by decide)

private def row106 := state 127 0 [(primaryWord 0 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h106 : Good row106 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row107 := state 127 0 [(primaryWord 0 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h107 : Good row107 :=
  goodCut h99 126 0 [(18,19)] (by decide)

private def row108 := state 127 0 [(primaryWord 0 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h108 : Good row108 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row109 := state 127 0 [(primaryWord 0 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h109 : Good row109 :=
  goodCut h99 126 0 [(34,35)] (by decide)

private def row110 := state 127 0 [(primaryWord 0 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h110 : Good row110 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row111 := state 127 0 [(primaryWord 0 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h111 : Good row111 :=
  goodCut h99 126 0 [(64,65)] (by decide)

private def row112 := state 56 0 [] 2
set_option maxRecDepth 8192 in
private theorem h112 : Good row112 :=
  goodCut h94 16 8 [(16,24), (16,48)] (by decide)

private def row113 := state 0 8 [] 0
set_option maxRecDepth 8192 in
private theorem h113 : Good row113 :=
  goodZero row113 rfl

private def row114 := state 48 8 [] 2
set_option maxRecDepth 8192 in
private theorem h114 : Good row114 :=
  goodCut h113 8 0 [(32,48), (16,48)] (by decide)

private def row115 := state 60 0 [] 4
set_option maxRecDepth 8192 in
private theorem h115 : Good row115 :=
  goodBoth h112 h114 56 0 56 4 8 12 (by decide)

private def row116 := state 60 64 [] 5
set_option maxRecDepth 8192 in
private theorem h116 : Good row116 :=
  goodCut h115 60 0 [(0,64)] (by decide)

private def row117 := state 125 0 [] 7
set_option maxRecDepth 8192 in
private theorem h117 : Good row117 :=
  goodBoth h97 h116 124 0 124 1 64 65 (by decide)

private def row118 := state 127 0 [(primaryWord 1 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h118 : Good row118 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row119 := state 127 0 [(primaryWord 1 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h119 : Good row119 :=
  goodCut h117 125 0 [(4,6)] (by decide)

private def row120 := state 127 0 [(primaryWord 1 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h120 : Good row120 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row121 := state 127 0 [(primaryWord 1 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h121 : Good row121 :=
  goodCut h117 125 0 [(9,11)] (by decide)

private def row122 := state 127 0 [(primaryWord 1 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h122 : Good row122 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row123 := state 127 0 [(primaryWord 1 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h123 : Good row123 :=
  goodCut h117 125 0 [(17,19)] (by decide)

private def row124 := state 127 0 [(primaryWord 1 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h124 : Good row124 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row125 := state 127 0 [(primaryWord 1 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h125 : Good row125 :=
  goodCut h117 125 0 [(33,35)] (by decide)

private def row126 := state 127 0 [(primaryWord 1 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h126 : Good row126 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row127 := state 127 0 [(primaryWord 1 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h127 : Good row127 :=
  goodCut h117 125 0 [(68,70)] (by decide)

private def row128 := state 121 0 [] 5
set_option maxRecDepth 8192 in
private theorem h128 : Good row128 :=
  goodCut h96 120 0 [(64,65)] (by decide)

private def row129 := state 120 1 [] 5
set_option maxRecDepth 8192 in
private theorem h129 : Good row129 :=
  goodCut h96 120 0 [(0,1)] (by decide)

private def row130 := state 123 0 [] 7
set_option maxRecDepth 8192 in
private theorem h130 : Good row130 :=
  goodBoth h128 h129 121 0 121 2 1 3 (by decide)

private def row131 := state 127 0 [(primaryWord 2 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h131 : Good row131 :=
  goodCut h130 123 0 [(2,6)] (by decide)

private def row132 := state 127 0 [(primaryWord 2 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h132 : Good row132 :=
  goodCut h130 123 0 [(8,12)] (by decide)

private def row133 := state 127 0 [(primaryWord 2 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h133 : Good row133 :=
  goodCut h130 123 0 [(2,6)] (by decide)

private def row134 := state 127 0 [(primaryWord 2 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h134 : Good row134 :=
  goodCut h130 123 0 [(18,22)] (by decide)

private def row135 := state 127 0 [(primaryWord 2 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h135 : Good row135 :=
  goodCut h130 123 0 [(2,6)] (by decide)

private def row136 := state 127 0 [(primaryWord 2 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h136 : Good row136 :=
  goodCut h130 123 0 [(34,38)] (by decide)

private def row137 := state 127 0 [(primaryWord 2 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h137 : Good row137 :=
  goodCut h130 123 0 [(2,6)] (by decide)

private def row138 := state 127 0 [(primaryWord 2 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h138 : Good row138 :=
  goodCut h130 123 0 [(66,70)] (by decide)

private def row139 := state 0 64 [] 0
set_option maxRecDepth 8192 in
private theorem h139 : Good row139 :=
  goodZero row139 rfl

private def row140 := state 48 64 [] 2
set_option maxRecDepth 8192 in
private theorem h140 : Good row140 :=
  goodCut h139 64 0 [(32,48), (16,48)] (by decide)

private def row141 := state 113 0 [] 4
set_option maxRecDepth 8192 in
private theorem h141 : Good row141 :=
  goodBoth h93 h140 112 0 112 1 64 65 (by decide)

private def row142 := state 115 0 [] 5
set_option maxRecDepth 8192 in
private theorem h142 : Good row142 :=
  goodCut h141 113 0 [(1,3)] (by decide)

private def row143 := state 113 2 [] 5
set_option maxRecDepth 8192 in
private theorem h143 : Good row143 :=
  goodCut h141 113 0 [(0,2)] (by decide)

private def row144 := state 119 0 [] 7
set_option maxRecDepth 8192 in
private theorem h144 : Good row144 :=
  goodBoth h142 h143 115 0 115 4 2 6 (by decide)

private def row145 := state 127 0 [(primaryWord 3 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h145 : Good row145 :=
  goodCut h144 119 0 [(4,12)] (by decide)

private def row146 := state 127 0 [(primaryWord 3 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h146 : Good row146 :=
  goodCut h144 119 0 [(16,24)] (by decide)

private def row147 := state 127 0 [(primaryWord 3 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h147 : Good row147 :=
  goodCut h144 119 0 [(4,12)] (by decide)

private def row148 := state 127 0 [(primaryWord 3 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h148 : Good row148 :=
  goodCut h144 119 0 [(36,44)] (by decide)

private def row149 := state 127 0 [(primaryWord 3 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h149 : Good row149 :=
  goodCut h144 119 0 [(4,12)] (by decide)

private def row150 := state 127 0 [(primaryWord 3 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h150 : Good row150 :=
  goodCut h144 119 0 [(68,76)] (by decide)

private def row151 := state 97 0 [] 2
set_option maxRecDepth 8192 in
private theorem h151 : Good row151 :=
  goodCut h139 64 1 [(64,65), (64,96)] (by decide)

private def row152 := state 0 1 [] 0
set_option maxRecDepth 8192 in
private theorem h152 : Good row152 :=
  goodZero row152 rfl

private def row153 := state 96 1 [] 2
set_option maxRecDepth 8192 in
private theorem h153 : Good row153 :=
  goodCut h152 1 0 [(64,96), (32,96)] (by decide)

private def row154 := state 99 0 [] 4
set_option maxRecDepth 8192 in
private theorem h154 : Good row154 :=
  goodBoth h151 h153 97 0 97 2 1 3 (by decide)

private def row155 := state 103 0 [] 5
set_option maxRecDepth 8192 in
private theorem h155 : Good row155 :=
  goodCut h154 99 0 [(2,6)] (by decide)

private def row156 := state 99 4 [] 5
set_option maxRecDepth 8192 in
private theorem h156 : Good row156 :=
  goodCut h154 99 0 [(0,4)] (by decide)

private def row157 := state 111 0 [] 7
set_option maxRecDepth 8192 in
private theorem h157 : Good row157 :=
  goodBoth h155 h156 103 0 103 8 4 12 (by decide)

private def row158 := state 127 0 [(primaryWord 4 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h158 : Good row158 :=
  goodCut h157 111 0 [(8,24)] (by decide)

private def row159 := state 127 0 [(primaryWord 4 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h159 : Good row159 :=
  goodCut h157 111 0 [(32,48)] (by decide)

private def row160 := state 127 0 [(primaryWord 4 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h160 : Good row160 :=
  goodCut h157 111 0 [(8,24)] (by decide)

private def row161 := state 127 0 [(primaryWord 4 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h161 : Good row161 :=
  goodCut h157 111 0 [(72,88)] (by decide)

private def row162 := state 67 0 [] 2
set_option maxRecDepth 8192 in
private theorem h162 : Good row162 :=
  goodCut h152 1 2 [(1,3), (1,65)] (by decide)

private def row163 := state 65 2 [] 2
set_option maxRecDepth 8192 in
private theorem h163 : Good row163 :=
  goodCut h2 2 0 [(64,65), (1,65)] (by decide)

private def row164 := state 71 0 [] 4
set_option maxRecDepth 8192 in
private theorem h164 : Good row164 :=
  goodBoth h162 h163 67 0 67 4 2 6 (by decide)

private def row165 := state 79 0 [] 5
set_option maxRecDepth 8192 in
private theorem h165 : Good row165 :=
  goodCut h164 71 0 [(4,12)] (by decide)

private def row166 := state 71 8 [] 5
set_option maxRecDepth 8192 in
private theorem h166 : Good row166 :=
  goodCut h164 71 0 [(0,8)] (by decide)

private def row167 := state 95 0 [] 7
set_option maxRecDepth 8192 in
private theorem h167 : Good row167 :=
  goodBoth h165 h166 79 0 79 16 8 24 (by decide)

private def row168 := state 127 0 [(primaryWord 5 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h168 : Good row168 :=
  goodCut h167 95 0 [(16,48)] (by decide)

private def row169 := state 127 0 [(primaryWord 5 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h169 : Good row169 :=
  goodCut h167 95 0 [(64,96)] (by decide)

private def row170 := state 127 0 [(~~~(primaryWord 0))] 8
set_option maxRecDepth 8192 in
private theorem h170 : Good row170 :=
  goodCut h99 126 0 [(2,3)] (by decide)

private def row171 := state 127 0 [(~~~(primaryWord 1))] 8
set_option maxRecDepth 8192 in
private theorem h171 : Good row171 :=
  goodCut h117 125 0 [(1,3)] (by decide)

private def row172 := state 127 0 [(~~~(primaryWord 2))] 8
set_option maxRecDepth 8192 in
private theorem h172 : Good row172 :=
  goodCut h130 123 0 [(2,6)] (by decide)

private def row173 := state 127 0 [(~~~(primaryWord 3))] 8
set_option maxRecDepth 8192 in
private theorem h173 : Good row173 :=
  goodCut h144 119 0 [(4,12)] (by decide)

private def row174 := state 127 0 [(~~~(primaryWord 4))] 8
set_option maxRecDepth 8192 in
private theorem h174 : Good row174 :=
  goodCut h157 111 0 [(8,24)] (by decide)

private def row175 := state 127 0 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h175 : Good row175 :=
  goodCut h167 95 0 [(16,48)] (by decide)

private def row176 := state 62 0 [] 5
set_option maxRecDepth 8192 in
private theorem h176 : Good row176 :=
  goodCut h115 60 0 [(4,6)] (by decide)

private def row177 := state 60 2 [] 5
set_option maxRecDepth 8192 in
private theorem h177 : Good row177 :=
  goodCut h115 60 0 [(0,2)] (by decide)

private def row178 := state 63 0 [] 7
set_option maxRecDepth 8192 in
private theorem h178 : Good row178 :=
  goodBoth h176 h177 62 0 62 1 2 3 (by decide)

private def row179 := state 127 0 [(~~~(primaryWord 6))] 8
set_option maxRecDepth 8192 in
private theorem h179 : Good row179 :=
  goodCut h178 63 0 [(1,65)] (by decide)

private def row180 := state 127 0 [] 9
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h180 : Good row180 :=
  fastGoodSplit row180 [
  checked h170, checked h100, checked h101, checked h102, checked h103, checked h104, checked h105, checked h106,
  checked h107, checked h108, checked h109, checked h110, checked h111, checked h171, checked h118, checked h119,
  checked h120, checked h121, checked h122, checked h123, checked h124, checked h125, checked h126, checked h127,
  checked h172, checked h131, checked h132, checked h133, checked h134, checked h135, checked h136, checked h137,
  checked h138, checked h173, checked h145, checked h146, checked h147, checked h148, checked h149, checked h150,
  checked h174, checked h158, checked h159, checked h160, checked h161, checked h175, checked h168, checked h169,
  checked h179
  ] [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0
  ] (by decide)

private def row181 := state 639 0 [] 10
set_option maxRecDepth 8192 in
private theorem h181 : Good row181 :=
  goodCut h180 127 0 [(4,516)] (by decide)

private def row182 := state 895 0 [(primaryWord 1 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h182 : Good row182 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row183 := state 895 0 [(primaryWord 1 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h183 : Good row183 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row184 := state 383 0 [] 10
set_option maxRecDepth 8192 in
private theorem h184 : Good row184 :=
  goodCut h180 127 0 [(2,258)] (by decide)

private def row185 := state 895 0 [(primaryWord 1 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h185 : Good row185 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row186 := state 639 0 [(primaryWord 1 ||| primaryWord 9)] 9
set_option maxRecDepth 8192 in
private theorem h186 : Good row186 :=
  goodCut h130 123 512 [(2,6), (4,516)] (by decide)

private def row187 := state 524 0 [] 2
set_option maxRecDepth 8192 in
private theorem h187 : Good row187 :=
  goodCut h0 4 8 [(4,12), (4,516)] (by decide)

private def row188 := state 516 8 [] 2
set_option maxRecDepth 8192 in
private theorem h188 : Good row188 :=
  goodCut h113 8 0 [(512,516), (4,516)] (by decide)

private def row189 := state 540 0 [] 4
set_option maxRecDepth 8192 in
private theorem h189 : Good row189 :=
  goodBoth h187 h188 524 0 524 16 8 24 (by decide)

private def row190 := state 572 0 [] 5
set_option maxRecDepth 8192 in
private theorem h190 : Good row190 :=
  goodCut h189 540 0 [(16,48)] (by decide)

private def row191 := state 540 32 [] 5
set_option maxRecDepth 8192 in
private theorem h191 : Good row191 :=
  goodCut h189 540 0 [(0,32)] (by decide)

private def row192 := state 636 0 [] 7
set_option maxRecDepth 8192 in
private theorem h192 : Good row192 :=
  goodBoth h190 h191 572 0 572 64 32 96 (by decide)

private def row193 := state 637 0 [] 8
set_option maxRecDepth 8192 in
private theorem h193 : Good row193 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row194 := state 637 2 [(primaryWord 1 ||| primaryWord 9)] 9
set_option maxRecDepth 8192 in
private theorem h194 : Good row194 :=
  goodCut h193 637 0 [(512,514)] (by decide)

private def row195 := state 895 0 [(primaryWord 1 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h195 : Good row195 :=
  goodBoth h186 h194 639 0 639 256 2 258 (by decide)

private def row196 := state 895 0 [(primaryWord 2 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h196 : Good row196 :=
  goodCut h76 887 0 [(16,24)] (by decide)

private def row197 := state 895 0 [(primaryWord 2 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h197 : Good row197 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row198 := state 895 0 [(primaryWord 2 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h198 : Good row198 :=
  goodBoth h79 h80 879 0 879 16 8 24 (by decide)

private def row199 := state 895 0 [(primaryWord 2 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h199 : Good row199 :=
  goodBoth h79 h80 879 0 879 16 36 52 (by decide)

private def row200 := state 895 0 [(primaryWord 2 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h200 : Good row200 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row201 := state 895 0 [(primaryWord 2 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h201 : Good row201 :=
  goodCut h85 863 0 [(20,52)] (by decide)

private def row202 := state 895 0 [(primaryWord 2 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h202 : Good row202 :=
  goodBoth h88 h89 831 0 831 64 1 65 (by decide)

private def row203 := state 895 0 [(primaryWord 2 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h203 : Good row203 :=
  goodBoth h88 h89 831 0 831 64 5 69 (by decide)

private def row204 := state 895 0 [(primaryWord 2 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h204 : Good row204 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row205 := state 383 0 [(primaryWord 2 ||| primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h205 : Good row205 :=
  goodCut h117 125 256 [(1,3), (2,258)] (by decide)

private def row206 := state 259 0 [] 2
set_option maxRecDepth 8192 in
private theorem h206 : Good row206 :=
  goodCut h2 2 1 [(2,3), (2,258)] (by decide)

private def row207 := state 258 1 [] 2
set_option maxRecDepth 8192 in
private theorem h207 : Good row207 :=
  goodCut h152 1 0 [(256,258), (2,258)] (by decide)

private def row208 := state 323 0 [] 4
set_option maxRecDepth 8192 in
private theorem h208 : Good row208 :=
  goodBoth h206 h207 259 0 259 64 1 65 (by decide)

private def row209 := state 355 0 [] 5
set_option maxRecDepth 8192 in
private theorem h209 : Good row209 :=
  goodCut h208 323 0 [(64,96)] (by decide)

private def row210 := state 323 32 [] 5
set_option maxRecDepth 8192 in
private theorem h210 : Good row210 :=
  goodCut h208 323 0 [(0,32)] (by decide)

private def row211 := state 371 0 [] 7
set_option maxRecDepth 8192 in
private theorem h211 : Good row211 :=
  goodBoth h209 h210 355 0 355 16 32 48 (by decide)

private def row212 := state 379 0 [] 8
set_option maxRecDepth 8192 in
private theorem h212 : Good row212 :=
  goodCut h211 371 0 [(16,24)] (by decide)

private def row213 := state 379 4 [(primaryWord 2 ||| primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h213 : Good row213 :=
  goodCut h212 379 0 [(256,260)] (by decide)

private def row214 := state 895 0 [(primaryWord 2 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h214 : Good row214 :=
  goodBoth h205 h213 383 0 383 512 4 516 (by decide)

private def row215 := state 895 0 [(primaryWord 2 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h215 : Good row215 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row216 := state 895 0 [(primaryWord 2 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h216 : Good row216 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row217 := state 895 0 [(primaryWord 3 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h217 : Good row217 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row218 := state 895 0 [(primaryWord 3 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h218 : Good row218 :=
  goodCut h76 887 0 [(16,24)] (by decide)

private def row219 := state 895 0 [(primaryWord 3 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h219 : Good row219 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row220 := state 895 0 [(primaryWord 3 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h220 : Good row220 :=
  goodCut h76 887 0 [(36,44)] (by decide)

private def row221 := state 895 0 [(primaryWord 3 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h221 : Good row221 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row222 := state 895 0 [(primaryWord 3 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h222 : Good row222 :=
  goodCut h76 887 0 [(68,76)] (by decide)

private def row223 := state 895 0 [(primaryWord 3 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h223 : Good row223 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row224 := state 895 0 [(primaryWord 3 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h224 : Good row224 :=
  goodCut h76 887 0 [(260,268)] (by decide)

private def row225 := state 895 0 [(primaryWord 3 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h225 : Good row225 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row226 := state 895 0 [(primaryWord 3 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h226 : Good row226 :=
  goodCut h76 887 0 [(528,536)] (by decide)

private def row227 := state 895 0 [(primaryWord 4 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h227 : Good row227 :=
  goodCut h85 863 0 [(64,96)] (by decide)

private def row228 := state 895 0 [(primaryWord 4 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h228 : Good row228 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row229 := state 895 0 [(primaryWord 4 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h229 : Good row229 :=
  goodBoth h79 h80 879 0 879 16 8 24 (by decide)

private def row230 := state 895 0 [(primaryWord 4 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h230 : Good row230 :=
  goodBoth h79 h80 879 0 879 16 72 88 (by decide)

private def row231 := state 895 0 [(primaryWord 4 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h231 : Good row231 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row232 := state 895 0 [(primaryWord 4 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h232 : Good row232 :=
  goodCut h181 639 0 [(18,274)] (by decide)

private def row233 := state 895 0 [(primaryWord 4 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h233 : Good row233 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row234 := state 895 0 [(primaryWord 4 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h234 : Good row234 :=
  goodCut h184 383 0 [(20,532)] (by decide)

private def row235 := state 895 0 [(primaryWord 5 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h235 : Good row235 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row236 := state 895 0 [(primaryWord 5 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h236 : Good row236 :=
  goodCut h85 863 0 [(64,96)] (by decide)

private def row237 := state 895 0 [(primaryWord 5 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h237 : Good row237 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row238 := state 895 0 [(primaryWord 5 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h238 : Good row238 :=
  goodCut h85 863 0 [(272,304)] (by decide)

private def row239 := state 895 0 [(primaryWord 5 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h239 : Good row239 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row240 := state 895 0 [(primaryWord 5 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h240 : Good row240 :=
  goodCut h85 863 0 [(528,560)] (by decide)

private def row241 := state 895 0 [(primaryWord 6 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h241 : Good row241 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row242 := state 895 0 [(primaryWord 6 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h242 : Good row242 :=
  goodCut h181 639 0 [(66,322)] (by decide)

private def row243 := state 895 0 [(primaryWord 6 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h243 : Good row243 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row244 := state 895 0 [(primaryWord 6 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h244 : Good row244 :=
  goodCut h184 383 0 [(68,580)] (by decide)

private def row245 := state 895 0 [(primaryWord 8 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h245 : Good row245 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row246 := state 895 0 [(primaryWord 8 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h246 : Good row246 :=
  goodCut h181 639 0 [(514,770)] (by decide)

private def row247 := state 895 0 [(~~~(primaryWord 0))] 11
set_option maxRecDepth 8192 in
private theorem h247 : Good row247 :=
  goodCut h10 894 0 [(2,3)] (by decide)

private def row248 := state 518 0 [(~~~(primaryWord 1))] 2
set_option maxRecDepth 8192 in
private theorem h248 : Good row248 :=
  goodCut h0 4 2 [(4,6), (4,516)] (by decide)

private def row249 := state 0 2 [(~~~(primaryWord 1))] 0
set_option maxRecDepth 8192 in
private theorem h249 : Good row249 :=
  goodZero row249 rfl

private def row250 := state 516 2 [(~~~(primaryWord 1))] 2
set_option maxRecDepth 8192 in
private theorem h250 : Good row250 :=
  goodCut h249 2 0 [(512,516), (4,516)] (by decide)

private def row251 := state 774 0 [(~~~(primaryWord 1))] 4
set_option maxRecDepth 8192 in
private theorem h251 : Good row251 :=
  goodBoth h248 h250 518 0 518 256 2 258 (by decide)

private def row252 := state 782 0 [(~~~(primaryWord 1))] 5
set_option maxRecDepth 8192 in
private theorem h252 : Good row252 :=
  goodCut h251 774 0 [(4,12)] (by decide)

private def row253 := state 774 8 [(~~~(primaryWord 1))] 5
set_option maxRecDepth 8192 in
private theorem h253 : Good row253 :=
  goodCut h251 774 0 [(0,8)] (by decide)

private def row254 := state 798 0 [(~~~(primaryWord 1))] 7
set_option maxRecDepth 8192 in
private theorem h254 : Good row254 :=
  goodBoth h252 h253 782 0 782 16 8 24 (by decide)

private def row255 := state 830 0 [(~~~(primaryWord 1))] 8
set_option maxRecDepth 8192 in
private theorem h255 : Good row255 :=
  goodCut h254 798 0 [(16,48)] (by decide)

private def row256 := state 798 32 [(~~~(primaryWord 1))] 8
set_option maxRecDepth 8192 in
private theorem h256 : Good row256 :=
  goodCut h254 798 0 [(0,32)] (by decide)

private def row257 := state 894 0 [(~~~(primaryWord 1))] 10
set_option maxRecDepth 8192 in
private theorem h257 : Good row257 :=
  goodBoth h255 h256 830 0 830 64 32 96 (by decide)

private def row258 := state 895 0 [(~~~(primaryWord 1))] 11
set_option maxRecDepth 8192 in
private theorem h258 : Good row258 :=
  goodCut h257 894 0 [(2,3)] (by decide)

private def row259 := state 0 4 [(~~~(primaryWord 2))] 0
set_option maxRecDepth 8192 in
private theorem h259 : Good row259 :=
  goodZero row259 rfl

private def row260 := state 518 0 [(~~~(primaryWord 2))] 2
set_option maxRecDepth 8192 in
private theorem h260 : Good row260 :=
  goodCut h259 4 2 [(4,6), (4,516)] (by decide)

private def row261 := state 516 2 [(~~~(primaryWord 2))] 2
set_option maxRecDepth 8192 in
private theorem h261 : Good row261 :=
  goodCut h2 2 0 [(512,516), (4,516)] (by decide)

private def row262 := state 774 0 [(~~~(primaryWord 2))] 4
set_option maxRecDepth 8192 in
private theorem h262 : Good row262 :=
  goodBoth h260 h261 518 0 518 256 2 258 (by decide)

private def row263 := state 782 0 [(~~~(primaryWord 2))] 5
set_option maxRecDepth 8192 in
private theorem h263 : Good row263 :=
  goodCut h262 774 0 [(4,12)] (by decide)

private def row264 := state 774 8 [(~~~(primaryWord 2))] 5
set_option maxRecDepth 8192 in
private theorem h264 : Good row264 :=
  goodCut h262 774 0 [(0,8)] (by decide)

private def row265 := state 798 0 [(~~~(primaryWord 2))] 7
set_option maxRecDepth 8192 in
private theorem h265 : Good row265 :=
  goodBoth h263 h264 782 0 782 16 8 24 (by decide)

private def row266 := state 830 0 [(~~~(primaryWord 2))] 8
set_option maxRecDepth 8192 in
private theorem h266 : Good row266 :=
  goodCut h265 798 0 [(16,48)] (by decide)

private def row267 := state 798 32 [(~~~(primaryWord 2))] 8
set_option maxRecDepth 8192 in
private theorem h267 : Good row267 :=
  goodCut h265 798 0 [(0,32)] (by decide)

private def row268 := state 894 0 [(~~~(primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h268 : Good row268 :=
  goodBoth h266 h267 830 0 830 64 32 96 (by decide)

private def row269 := state 895 0 [(~~~(primaryWord 2))] 11
set_option maxRecDepth 8192 in
private theorem h269 : Good row269 :=
  goodCut h268 894 0 [(2,3)] (by decide)

private def row270 := state 895 0 [(~~~(primaryWord 3))] 11
set_option maxRecDepth 8192 in
private theorem h270 : Good row270 :=
  goodCut h76 887 0 [(4,12)] (by decide)

private def row271 := state 28 0 [(~~~(primaryWord 4))] 2
set_option maxRecDepth 8192 in
private theorem h271 : Good row271 :=
  goodCut h113 8 4 [(8,12), (8,24)] (by decide)

private def row272 := state 24 4 [(~~~(primaryWord 4))] 2
set_option maxRecDepth 8192 in
private theorem h272 : Good row272 :=
  goodCut h0 4 0 [(16,24), (8,24)] (by decide)

private def row273 := state 540 0 [(~~~(primaryWord 4))] 4
set_option maxRecDepth 8192 in
private theorem h273 : Good row273 :=
  goodBoth h271 h272 28 0 28 512 4 516 (by decide)

private def row274 := state 542 0 [(~~~(primaryWord 4))] 5
set_option maxRecDepth 8192 in
private theorem h274 : Good row274 :=
  goodCut h273 540 0 [(4,6)] (by decide)

private def row275 := state 540 2 [(~~~(primaryWord 4))] 5
set_option maxRecDepth 8192 in
private theorem h275 : Good row275 :=
  goodCut h273 540 0 [(0,2)] (by decide)

private def row276 := state 798 0 [(~~~(primaryWord 4))] 7
set_option maxRecDepth 8192 in
private theorem h276 : Good row276 :=
  goodBoth h274 h275 542 0 542 256 2 258 (by decide)

private def row277 := state 830 0 [(~~~(primaryWord 4))] 8
set_option maxRecDepth 8192 in
private theorem h277 : Good row277 :=
  goodCut h276 798 0 [(16,48)] (by decide)

private def row278 := state 798 32 [(~~~(primaryWord 4))] 8
set_option maxRecDepth 8192 in
private theorem h278 : Good row278 :=
  goodCut h276 798 0 [(0,32)] (by decide)

private def row279 := state 894 0 [(~~~(primaryWord 4))] 10
set_option maxRecDepth 8192 in
private theorem h279 : Good row279 :=
  goodBoth h277 h278 830 0 830 64 32 96 (by decide)

private def row280 := state 895 0 [(~~~(primaryWord 4))] 11
set_option maxRecDepth 8192 in
private theorem h280 : Good row280 :=
  goodCut h279 894 0 [(2,3)] (by decide)

private def row281 := state 895 0 [(~~~(primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h281 : Good row281 :=
  goodCut h85 863 0 [(16,48)] (by decide)

private def row282 := state 124 0 [(~~~(primaryWord 6))] 5
set_option maxRecDepth 8192 in
private theorem h282 : Good row282 :=
  goodCut h115 60 0 [(32,96)] (by decide)

private def row283 := state 112 0 [(~~~(primaryWord 6))] 2
set_option maxRecDepth 8192 in
private theorem h283 : Good row283 :=
  goodCut h92 32 16 [(32,48), (32,96)] (by decide)

private def row284 := state 96 16 [(~~~(primaryWord 6))] 2
set_option maxRecDepth 8192 in
private theorem h284 : Good row284 :=
  goodCut h94 16 0 [(64,96), (32,96)] (by decide)

private def row285 := state 120 0 [(~~~(primaryWord 6))] 4
set_option maxRecDepth 8192 in
private theorem h285 : Good row285 :=
  goodBoth h283 h284 112 0 112 8 16 24 (by decide)

private def row286 := state 120 4 [(~~~(primaryWord 6))] 5
set_option maxRecDepth 8192 in
private theorem h286 : Good row286 :=
  goodCut h285 120 0 [(0,4)] (by decide)

private def row287 := state 636 0 [(~~~(primaryWord 6))] 7
set_option maxRecDepth 8192 in
private theorem h287 : Good row287 :=
  goodBoth h282 h286 124 0 124 512 4 516 (by decide)

private def row288 := state 638 0 [(~~~(primaryWord 6))] 8
set_option maxRecDepth 8192 in
private theorem h288 : Good row288 :=
  goodCut h287 636 0 [(4,6)] (by decide)

private def row289 := state 636 2 [(~~~(primaryWord 6))] 8
set_option maxRecDepth 8192 in
private theorem h289 : Good row289 :=
  goodCut h287 636 0 [(0,2)] (by decide)

private def row290 := state 894 0 [(~~~(primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h290 : Good row290 :=
  goodBoth h288 h289 638 0 638 256 2 258 (by decide)

private def row291 := state 895 0 [(~~~(primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h291 : Good row291 :=
  goodCut h290 894 0 [(2,3)] (by decide)

private def row292 := state 895 0 [(~~~(primaryWord 8))] 11
set_option maxRecDepth 8192 in
private theorem h292 : Good row292 :=
  goodCut h181 639 0 [(2,258)] (by decide)

private def row293 := state 895 0 [(~~~(primaryWord 9))] 11
set_option maxRecDepth 8192 in
private theorem h293 : Good row293 :=
  goodCut h184 383 0 [(4,516)] (by decide)

private def row294 := state 895 0 [] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h294 : Good row294 :=
  fastGoodSplit row294 [
  checked h247, checked h11, checked h14, checked h17, checked h20, checked h23, checked h26, checked h29,
  checked h32, checked h35, checked h38, checked h41, checked h44, checked h47, checked h48, checked h49,
  checked h50, checked h258, checked h60, checked h70, checked h77, checked h78, checked h81, checked h82,
  checked h86, checked h87, checked h90, checked h91, checked h182, checked h183, checked h185, checked h195,
  checked h269, checked h196, checked h197, checked h198, checked h199, checked h200, checked h201, checked h202,
  checked h203, checked h204, checked h214, checked h215, checked h216, checked h270, checked h217, checked h218,
  checked h219, checked h220, checked h221, checked h222, checked h223, checked h224, checked h225, checked h226,
  checked h280, checked h227, checked h228, checked h229, checked h230, checked h231, checked h232, checked h233,
  checked h234, checked h281, checked h235, checked h236, checked h237, checked h238, checked h239, checked h240,
  checked h291, checked h241, checked h242, checked h243, checked h244, checked h292, checked h245, checked h246,
  checked h293
  ] [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ] (by decide)

private def row295 := state 1023 0 [(primaryWord 0 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h295 : Good row295 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row296 := state 1023 0 [(primaryWord 0 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h296 : Good row296 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row297 := state 636 1 [] 8
set_option maxRecDepth 8192 in
private theorem h297 : Good row297 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row298 := state 765 0 [] 10
set_option maxRecDepth 8192 in
private theorem h298 : Good row298 :=
  goodBoth h193 h297 637 0 637 128 1 129 (by decide)

private def row299 := state 767 0 [] 11
set_option maxRecDepth 8192 in
private theorem h299 : Good row299 :=
  goodCut h298 765 0 [(1,3)] (by decide)

private def row300 := state 765 2 [] 11
set_option maxRecDepth 8192 in
private theorem h300 : Good row300 :=
  goodCut h298 765 0 [(0,2)] (by decide)

private def row301 := state 1023 0 [(primaryWord 0 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h301 : Good row301 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row302 := state 894 1 [(primaryWord 0 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h302 : Good row302 :=
  goodCut h10 894 0 [(256,257)] (by decide)

private def row303 := state 1023 0 [(primaryWord 0 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h303 : Good row303 :=
  goodBoth h48 h302 895 0 895 128 1 129 (by decide)

private def row304 := state 259 0 [(primaryWord 0 &&& primaryWord 1)] 2
set_option maxRecDepth 8192 in
private theorem h304 : Good row304 :=
  goodCut h2 2 256 [(2,3), (2,258)] (by decide)

private def row305 := state 258 1 [(primaryWord 0 &&& primaryWord 1)] 2
set_option maxRecDepth 8192 in
private theorem h305 : Good row305 :=
  goodCut h152 1 0 [(256,258), (2,258)] (by decide)

private def row306 := state 387 0 [(primaryWord 0 &&& primaryWord 1)] 4
set_option maxRecDepth 8192 in
private theorem h306 : Good row306 :=
  goodBoth h304 h305 259 0 259 128 1 129 (by decide)

private def row307 := state 451 0 [(primaryWord 0 &&& primaryWord 1)] 5
set_option maxRecDepth 8192 in
private theorem h307 : Good row307 :=
  goodCut h306 387 0 [(1,65)] (by decide)

private def row308 := state 387 64 [(primaryWord 0 &&& primaryWord 1)] 5
set_option maxRecDepth 8192 in
private theorem h308 : Good row308 :=
  goodCut h306 387 0 [(0,64)] (by decide)

private def row309 := state 483 0 [(primaryWord 0 &&& primaryWord 1)] 7
set_option maxRecDepth 8192 in
private theorem h309 : Good row309 :=
  goodBoth h307 h308 451 0 451 32 64 96 (by decide)

private def row310 := state 499 0 [(primaryWord 0 &&& primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h310 : Good row310 :=
  goodCut h309 483 0 [(32,48)] (by decide)

private def row311 := state 483 16 [(primaryWord 0 &&& primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h311 : Good row311 :=
  goodCut h309 483 0 [(0,16)] (by decide)

private def row312 := state 507 0 [(primaryWord 0 &&& primaryWord 1)] 10
set_option maxRecDepth 8192 in
private theorem h312 : Good row312 :=
  goodBoth h310 h311 499 0 499 8 16 24 (by decide)

private def row313 := state 511 0 [(primaryWord 0 &&& primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h313 : Good row313 :=
  goodCut h312 507 0 [(2,6)] (by decide)

private def row314 := state 259 0 [(primaryWord 0 ||| primaryWord 1)] 2
set_option maxRecDepth 8192 in
private theorem h314 : Good row314 :=
  goodCut h2 2 1 [(2,3), (2,258)] (by decide)

private def row315 := state 258 1 [(primaryWord 0 ||| primaryWord 1)] 2
set_option maxRecDepth 8192 in
private theorem h315 : Good row315 :=
  goodCut h152 1 2 [(256,258), (2,258)] (by decide)

private def row316 := state 387 0 [(primaryWord 0 ||| primaryWord 1)] 4
set_option maxRecDepth 8192 in
private theorem h316 : Good row316 :=
  goodBoth h314 h315 259 0 259 128 1 129 (by decide)

private def row317 := state 451 0 [(primaryWord 0 ||| primaryWord 1)] 5
set_option maxRecDepth 8192 in
private theorem h317 : Good row317 :=
  goodCut h316 387 0 [(1,65)] (by decide)

private def row318 := state 387 64 [(primaryWord 0 ||| primaryWord 1)] 5
set_option maxRecDepth 8192 in
private theorem h318 : Good row318 :=
  goodCut h316 387 0 [(0,64)] (by decide)

private def row319 := state 483 0 [(primaryWord 0 ||| primaryWord 1)] 7
set_option maxRecDepth 8192 in
private theorem h319 : Good row319 :=
  goodBoth h317 h318 451 0 451 32 64 96 (by decide)

private def row320 := state 499 0 [(primaryWord 0 ||| primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h320 : Good row320 :=
  goodCut h319 483 0 [(32,48)] (by decide)

private def row321 := state 483 16 [(primaryWord 0 ||| primaryWord 1)] 8
set_option maxRecDepth 8192 in
private theorem h321 : Good row321 :=
  goodCut h319 483 0 [(0,16)] (by decide)

private def row322 := state 507 0 [(primaryWord 0 ||| primaryWord 1)] 10
set_option maxRecDepth 8192 in
private theorem h322 : Good row322 :=
  goodBoth h320 h321 499 0 499 8 16 24 (by decide)

private def row323 := state 511 0 [(primaryWord 0 ||| primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h323 : Good row323 :=
  goodCut h322 507 0 [(2,6)] (by decide)

private def row324 := state 387 0 [] 4
set_option maxRecDepth 8192 in
private theorem h324 : Good row324 :=
  goodBoth h206 h207 259 0 259 128 1 129 (by decide)

private def row325 := state 451 0 [] 5
set_option maxRecDepth 8192 in
private theorem h325 : Good row325 :=
  goodCut h324 387 0 [(1,65)] (by decide)

private def row326 := state 387 64 [] 5
set_option maxRecDepth 8192 in
private theorem h326 : Good row326 :=
  goodCut h324 387 0 [(0,64)] (by decide)

private def row327 := state 483 0 [] 7
set_option maxRecDepth 8192 in
private theorem h327 : Good row327 :=
  goodBoth h325 h326 451 0 451 32 64 96 (by decide)

private def row328 := state 499 0 [] 8
set_option maxRecDepth 8192 in
private theorem h328 : Good row328 :=
  goodCut h327 483 0 [(32,48)] (by decide)

private def row329 := state 483 16 [] 8
set_option maxRecDepth 8192 in
private theorem h329 : Good row329 :=
  goodCut h327 483 0 [(0,16)] (by decide)

private def row330 := state 507 0 [] 10
set_option maxRecDepth 8192 in
private theorem h330 : Good row330 :=
  goodBoth h328 h329 499 0 499 8 16 24 (by decide)

private def row331 := state 511 0 [(primaryWord 0 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h331 : Good row331 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row332 := state 511 0 [(primaryWord 0 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h332 : Good row332 :=
  goodCut h330 507 0 [(9,13)] (by decide)

private def row333 := state 503 0 [] 9
set_option maxRecDepth 8192 in
private theorem h333 : Good row333 :=
  goodCut h328 499 0 [(2,6)] (by decide)

private def row334 := state 483 20 [] 9
set_option maxRecDepth 8192 in
private theorem h334 : Good row334 :=
  goodCut h329 499 0 [(0,4)] (by decide)

private def row335 := state 511 0 [(primaryWord 0 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h335 : Good row335 :=
  goodBoth h333 h334 503 0 503 8 4 12 (by decide)

private def row336 := state 511 0 [(primaryWord 0 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h336 : Good row336 :=
  goodBoth h333 h334 503 0 503 8 5 13 (by decide)

private def row337 := state 487 0 [] 8
set_option maxRecDepth 8192 in
private theorem h337 : Good row337 :=
  goodCut h327 483 0 [(2,6)] (by decide)

private def row338 := state 483 4 [] 8
set_option maxRecDepth 8192 in
private theorem h338 : Good row338 :=
  goodCut h327 483 0 [(0,4)] (by decide)

private def row339 := state 495 0 [] 10
set_option maxRecDepth 8192 in
private theorem h339 : Good row339 :=
  goodBoth h337 h338 487 0 487 8 4 12 (by decide)

private def row340 := state 511 0 [(primaryWord 0 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h340 : Good row340 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row341 := state 511 0 [(primaryWord 0 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h341 : Good row341 :=
  goodCut h339 495 0 [(9,25)] (by decide)

private def row342 := state 391 0 [] 5
set_option maxRecDepth 8192 in
private theorem h342 : Good row342 :=
  goodCut h324 387 0 [(2,6)] (by decide)

private def row343 := state 387 4 [] 5
set_option maxRecDepth 8192 in
private theorem h343 : Good row343 :=
  goodCut h324 387 0 [(0,4)] (by decide)

private def row344 := state 399 0 [] 7
set_option maxRecDepth 8192 in
private theorem h344 : Good row344 :=
  goodBoth h342 h343 391 0 391 8 4 12 (by decide)

private def row345 := state 463 0 [] 8
set_option maxRecDepth 8192 in
private theorem h345 : Good row345 :=
  goodCut h344 399 0 [(1,65)] (by decide)

private def row346 := state 479 0 [] 9
set_option maxRecDepth 8192 in
private theorem h346 : Good row346 :=
  goodCut h345 463 0 [(8,24)] (by decide)

private def row347 := state 399 64 [] 8
set_option maxRecDepth 8192 in
private theorem h347 : Good row347 :=
  goodCut h344 399 0 [(0,64)] (by decide)

private def row348 := state 399 80 [] 9
set_option maxRecDepth 8192 in
private theorem h348 : Good row348 :=
  goodCut h347 463 0 [(0,16)] (by decide)

private def row349 := state 511 0 [(primaryWord 0 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h349 : Good row349 :=
  goodBoth h346 h348 479 0 479 32 16 48 (by decide)

private def row350 := state 511 0 [(primaryWord 0 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h350 : Good row350 :=
  goodBoth h346 h348 479 0 479 32 17 49 (by decide)

private def row351 := state 415 0 [] 8
set_option maxRecDepth 8192 in
private theorem h351 : Good row351 :=
  goodCut h344 399 0 [(8,24)] (by decide)

private def row352 := state 399 16 [] 8
set_option maxRecDepth 8192 in
private theorem h352 : Good row352 :=
  goodCut h344 399 0 [(0,16)] (by decide)

private def row353 := state 447 0 [] 10
set_option maxRecDepth 8192 in
private theorem h353 : Good row353 :=
  goodBoth h351 h352 415 0 415 32 16 48 (by decide)

private def row354 := state 511 0 [(primaryWord 0 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h354 : Good row354 :=
  goodCut h353 447 0 [(32,96)] (by decide)

private def row355 := state 511 0 [(primaryWord 0 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h355 : Good row355 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row356 := state 511 0 [(primaryWord 0 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h356 : Good row356 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row357 := state 511 0 [(primaryWord 0 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h357 : Good row357 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row358 := state 255 0 [] 10
set_option maxRecDepth 8192 in
private theorem h358 : Good row358 :=
  goodCut h180 127 0 [(1,129)] (by decide)

private def row359 := state 511 0 [(primaryWord 0 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h359 : Good row359 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row360 := state 383 0 [(primaryWord 0 ||| primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h360 : Good row360 :=
  goodCut h117 125 256 [(1,3), (2,258)] (by decide)

private def row361 := state 262 0 [] 2
set_option maxRecDepth 8192 in
private theorem h361 : Good row361 :=
  goodCut h2 2 4 [(2,6), (2,258)] (by decide)

private def row362 := state 258 4 [] 2
set_option maxRecDepth 8192 in
private theorem h362 : Good row362 :=
  goodCut h0 4 0 [(256,258), (2,258)] (by decide)

private def row363 := state 270 0 [] 4
set_option maxRecDepth 8192 in
private theorem h363 : Good row363 :=
  goodBoth h361 h362 262 0 262 8 4 12 (by decide)

private def row364 := state 286 0 [] 5
set_option maxRecDepth 8192 in
private theorem h364 : Good row364 :=
  goodCut h363 270 0 [(8,24)] (by decide)

private def row365 := state 270 16 [] 5
set_option maxRecDepth 8192 in
private theorem h365 : Good row365 :=
  goodCut h363 270 0 [(0,16)] (by decide)

private def row366 := state 318 0 [] 7
set_option maxRecDepth 8192 in
private theorem h366 : Good row366 :=
  goodBoth h364 h365 286 0 286 32 16 48 (by decide)

private def row367 := state 382 0 [] 8
set_option maxRecDepth 8192 in
private theorem h367 : Good row367 :=
  goodCut h366 318 0 [(32,96)] (by decide)

private def row368 := state 382 1 [(primaryWord 0 ||| primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h368 : Good row368 :=
  goodCut h367 382 0 [(256,257)] (by decide)

private def row369 := state 511 0 [(primaryWord 0 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h369 : Good row369 :=
  goodBoth h360 h368 383 0 383 128 1 129 (by decide)

private def row370 := state 511 0 [(primaryWord 1 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h370 : Good row370 :=
  goodCut h330 507 0 [(8,12)] (by decide)

private def row371 := state 511 0 [(primaryWord 1 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h371 : Good row371 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row372 := state 511 0 [(primaryWord 1 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h372 : Good row372 :=
  goodBoth h333 h334 503 0 503 8 4 12 (by decide)

private def row373 := state 511 0 [(primaryWord 1 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h373 : Good row373 :=
  goodBoth h333 h334 503 0 503 8 18 26 (by decide)

private def row374 := state 511 0 [(primaryWord 1 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h374 : Good row374 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row375 := state 511 0 [(primaryWord 1 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h375 : Good row375 :=
  goodCut h339 495 0 [(10,26)] (by decide)

private def row376 := state 511 0 [(primaryWord 1 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h376 : Good row376 :=
  goodBoth h346 h348 479 0 479 32 16 48 (by decide)

private def row377 := state 511 0 [(primaryWord 1 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h377 : Good row377 :=
  goodBoth h346 h348 479 0 479 32 18 50 (by decide)

private def row378 := state 511 0 [(primaryWord 1 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h378 : Good row378 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row379 := state 511 0 [(primaryWord 1 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h379 : Good row379 :=
  goodCut h353 447 0 [(34,98)] (by decide)

private def row380 := state 511 0 [(primaryWord 1 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h380 : Good row380 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row381 := state 255 0 [(primaryWord 1 ||| primaryWord 7)] 9
set_option maxRecDepth 8192 in
private theorem h381 : Good row381 :=
  goodCut h99 126 128 [(2,3), (1,129)] (by decide)

private def row382 := state 193 0 [] 2
set_option maxRecDepth 8192 in
private theorem h382 : Good row382 :=
  goodCut h152 1 64 [(1,65), (1,129)] (by decide)

private def row383 := state 129 64 [] 2
set_option maxRecDepth 8192 in
private theorem h383 : Good row383 :=
  goodCut h139 64 0 [(128,129), (1,129)] (by decide)

private def row384 := state 225 0 [] 4
set_option maxRecDepth 8192 in
private theorem h384 : Good row384 :=
  goodBoth h382 h383 193 0 193 32 64 96 (by decide)

private def row385 := state 241 0 [] 5
set_option maxRecDepth 8192 in
private theorem h385 : Good row385 :=
  goodCut h384 225 0 [(32,48)] (by decide)

private def row386 := state 225 16 [] 5
set_option maxRecDepth 8192 in
private theorem h386 : Good row386 :=
  goodCut h384 225 0 [(0,16)] (by decide)

private def row387 := state 249 0 [] 7
set_option maxRecDepth 8192 in
private theorem h387 : Good row387 :=
  goodBoth h385 h386 241 0 241 8 16 24 (by decide)

private def row388 := state 253 0 [] 8
set_option maxRecDepth 8192 in
private theorem h388 : Good row388 :=
  goodCut h387 249 0 [(8,12)] (by decide)

private def row389 := state 253 2 [(primaryWord 1 ||| primaryWord 7)] 9
set_option maxRecDepth 8192 in
private theorem h389 : Good row389 :=
  goodCut h388 253 0 [(128,130)] (by decide)

private def row390 := state 511 0 [(primaryWord 1 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h390 : Good row390 :=
  goodBoth h381 h389 255 0 255 256 2 258 (by decide)

private def row391 := state 511 0 [(primaryWord 1 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h391 : Good row391 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row392 := state 511 0 [(primaryWord 1 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h392 : Good row392 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row393 := state 511 0 [(primaryWord 2 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h393 : Good row393 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row394 := state 511 0 [(primaryWord 2 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h394 : Good row394 :=
  goodCut h330 507 0 [(8,12)] (by decide)

private def row395 := state 511 0 [(primaryWord 2 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h395 : Good row395 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row396 := state 511 0 [(primaryWord 2 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h396 : Good row396 :=
  goodCut h330 507 0 [(18,22)] (by decide)

private def row397 := state 511 0 [(primaryWord 2 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h397 : Good row397 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row398 := state 511 0 [(primaryWord 2 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h398 : Good row398 :=
  goodCut h330 507 0 [(34,38)] (by decide)

private def row399 := state 511 0 [(primaryWord 2 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h399 : Good row399 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row400 := state 511 0 [(primaryWord 2 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h400 : Good row400 :=
  goodCut h330 507 0 [(66,70)] (by decide)

private def row401 := state 511 0 [(primaryWord 2 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h401 : Good row401 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row402 := state 511 0 [(primaryWord 2 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h402 : Good row402 :=
  goodCut h330 507 0 [(130,134)] (by decide)

private def row403 := state 511 0 [(primaryWord 2 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h403 : Good row403 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row404 := state 511 0 [(primaryWord 2 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h404 : Good row404 :=
  goodCut h330 507 0 [(264,268)] (by decide)

private def row405 := state 511 0 [(primaryWord 3 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h405 : Good row405 :=
  goodCut h339 495 0 [(32,48)] (by decide)

private def row406 := state 511 0 [(primaryWord 3 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h406 : Good row406 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row407 := state 511 0 [(primaryWord 3 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h407 : Good row407 :=
  goodBoth h333 h334 503 0 503 8 4 12 (by decide)

private def row408 := state 511 0 [(primaryWord 3 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h408 : Good row408 :=
  goodBoth h333 h334 503 0 503 8 36 44 (by decide)

private def row409 := state 511 0 [(primaryWord 3 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h409 : Good row409 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row410 := state 511 0 [(primaryWord 3 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h410 : Good row410 :=
  goodCut h353 447 0 [(9,73)] (by decide)

private def row411 := state 511 0 [(primaryWord 3 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h411 : Good row411 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row412 := state 511 0 [(primaryWord 3 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h412 : Good row412 :=
  goodCut h184 383 0 [(9,137)] (by decide)

private def row413 := state 511 0 [(primaryWord 3 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h413 : Good row413 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row414 := state 511 0 [(primaryWord 3 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h414 : Good row414 :=
  goodCut h358 255 0 [(10,266)] (by decide)

private def row415 := state 511 0 [(primaryWord 4 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h415 : Good row415 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row416 := state 511 0 [(primaryWord 4 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h416 : Good row416 :=
  goodCut h339 495 0 [(32,48)] (by decide)

private def row417 := state 511 0 [(primaryWord 4 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h417 : Good row417 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row418 := state 511 0 [(primaryWord 4 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h418 : Good row418 :=
  goodCut h339 495 0 [(72,88)] (by decide)

private def row419 := state 511 0 [(primaryWord 4 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h419 : Good row419 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row420 := state 511 0 [(primaryWord 4 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h420 : Good row420 :=
  goodCut h339 495 0 [(136,152)] (by decide)

private def row421 := state 511 0 [(primaryWord 4 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h421 : Good row421 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row422 := state 511 0 [(primaryWord 4 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h422 : Good row422 :=
  goodCut h339 495 0 [(264,280)] (by decide)

private def row423 := state 511 0 [(primaryWord 5 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h423 : Good row423 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row424 := state 511 0 [(primaryWord 5 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h424 : Good row424 :=
  goodCut h353 447 0 [(32,96)] (by decide)

private def row425 := state 511 0 [(primaryWord 5 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h425 : Good row425 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row426 := state 511 0 [(primaryWord 5 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h426 : Good row426 :=
  goodCut h184 383 0 [(33,161)] (by decide)

private def row427 := state 511 0 [(primaryWord 5 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h427 : Good row427 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row428 := state 511 0 [(primaryWord 5 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h428 : Good row428 :=
  goodCut h358 255 0 [(34,290)] (by decide)

private def row429 := state 511 0 [(primaryWord 6 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h429 : Good row429 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row430 := state 511 0 [(primaryWord 6 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h430 : Good row430 :=
  goodCut h353 447 0 [(160,224)] (by decide)

private def row431 := state 511 0 [(primaryWord 6 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h431 : Good row431 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row432 := state 511 0 [(primaryWord 6 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h432 : Good row432 :=
  goodCut h353 447 0 [(257,321)] (by decide)

private def row433 := state 511 0 [(primaryWord 7 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h433 : Good row433 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row434 := state 511 0 [(primaryWord 7 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h434 : Good row434 :=
  goodCut h184 383 0 [(257,385)] (by decide)

private def row435 := state 259 0 [(~~~(primaryWord 0))] 2
set_option maxRecDepth 8192 in
private theorem h435 : Good row435 :=
  goodCut h2 2 1 [(2,3), (2,258)] (by decide)

private def row436 := state 0 1 [(~~~(primaryWord 0))] 0
set_option maxRecDepth 8192 in
private theorem h436 : Good row436 :=
  goodZero row436 rfl

private def row437 := state 258 1 [(~~~(primaryWord 0))] 2
set_option maxRecDepth 8192 in
private theorem h437 : Good row437 :=
  goodCut h436 1 0 [(256,258), (2,258)] (by decide)

private def row438 := state 387 0 [(~~~(primaryWord 0))] 4
set_option maxRecDepth 8192 in
private theorem h438 : Good row438 :=
  goodBoth h435 h437 259 0 259 128 1 129 (by decide)

private def row439 := state 451 0 [(~~~(primaryWord 0))] 5
set_option maxRecDepth 8192 in
private theorem h439 : Good row439 :=
  goodCut h438 387 0 [(1,65)] (by decide)

private def row440 := state 387 64 [(~~~(primaryWord 0))] 5
set_option maxRecDepth 8192 in
private theorem h440 : Good row440 :=
  goodCut h438 387 0 [(0,64)] (by decide)

private def row441 := state 483 0 [(~~~(primaryWord 0))] 7
set_option maxRecDepth 8192 in
private theorem h441 : Good row441 :=
  goodBoth h439 h440 451 0 451 32 64 96 (by decide)

private def row442 := state 499 0 [(~~~(primaryWord 0))] 8
set_option maxRecDepth 8192 in
private theorem h442 : Good row442 :=
  goodCut h441 483 0 [(32,48)] (by decide)

private def row443 := state 483 16 [(~~~(primaryWord 0))] 8
set_option maxRecDepth 8192 in
private theorem h443 : Good row443 :=
  goodCut h441 483 0 [(0,16)] (by decide)

private def row444 := state 507 0 [(~~~(primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h444 : Good row444 :=
  goodBoth h442 h443 499 0 499 8 16 24 (by decide)

private def row445 := state 511 0 [(~~~(primaryWord 0))] 11
set_option maxRecDepth 8192 in
private theorem h445 : Good row445 :=
  goodCut h444 507 0 [(2,6)] (by decide)

private def row446 := state 259 0 [(~~~(primaryWord 1))] 2
set_option maxRecDepth 8192 in
private theorem h446 : Good row446 :=
  goodCut h249 2 1 [(2,3), (2,258)] (by decide)

private def row447 := state 258 1 [(~~~(primaryWord 1))] 2
set_option maxRecDepth 8192 in
private theorem h447 : Good row447 :=
  goodCut h152 1 0 [(256,258), (2,258)] (by decide)

private def row448 := state 387 0 [(~~~(primaryWord 1))] 4
set_option maxRecDepth 8192 in
private theorem h448 : Good row448 :=
  goodBoth h446 h447 259 0 259 128 1 129 (by decide)

private def row449 := state 451 0 [(~~~(primaryWord 1))] 5
set_option maxRecDepth 8192 in
private theorem h449 : Good row449 :=
  goodCut h448 387 0 [(1,65)] (by decide)

private def row450 := state 387 64 [(~~~(primaryWord 1))] 5
set_option maxRecDepth 8192 in
private theorem h450 : Good row450 :=
  goodCut h448 387 0 [(0,64)] (by decide)

private def row451 := state 483 0 [(~~~(primaryWord 1))] 7
set_option maxRecDepth 8192 in
private theorem h451 : Good row451 :=
  goodBoth h449 h450 451 0 451 32 64 96 (by decide)

private def row452 := state 499 0 [(~~~(primaryWord 1))] 8
set_option maxRecDepth 8192 in
private theorem h452 : Good row452 :=
  goodCut h451 483 0 [(32,48)] (by decide)

private def row453 := state 483 16 [(~~~(primaryWord 1))] 8
set_option maxRecDepth 8192 in
private theorem h453 : Good row453 :=
  goodCut h451 483 0 [(0,16)] (by decide)

private def row454 := state 507 0 [(~~~(primaryWord 1))] 10
set_option maxRecDepth 8192 in
private theorem h454 : Good row454 :=
  goodBoth h452 h453 499 0 499 8 16 24 (by decide)

private def row455 := state 511 0 [(~~~(primaryWord 1))] 11
set_option maxRecDepth 8192 in
private theorem h455 : Good row455 :=
  goodCut h454 507 0 [(2,6)] (by decide)

private def row456 := state 511 0 [(~~~(primaryWord 2))] 11
set_option maxRecDepth 8192 in
private theorem h456 : Good row456 :=
  goodCut h330 507 0 [(2,6)] (by decide)

private def row457 := state 121 0 [(~~~(primaryWord 3))] 5
set_option maxRecDepth 8192 in
private theorem h457 : Good row457 :=
  goodCut h141 113 0 [(16,24)] (by decide)

private def row458 := state 56 0 [(~~~(primaryWord 3))] 2
set_option maxRecDepth 8192 in
private theorem h458 : Good row458 :=
  goodCut h94 16 8 [(16,24), (16,48)] (by decide)

private def row459 := state 24 32 [(~~~(primaryWord 3))] 2
set_option maxRecDepth 8192 in
private theorem h459 : Good row459 :=
  goodCut h92 32 0 [(16,24), (8,24)] (by decide)

private def row460 := state 120 0 [(~~~(primaryWord 3))] 4
set_option maxRecDepth 8192 in
private theorem h460 : Good row460 :=
  goodBoth h458 h459 56 0 56 64 32 96 (by decide)

private def row461 := state 120 1 [(~~~(primaryWord 3))] 5
set_option maxRecDepth 8192 in
private theorem h461 : Good row461 :=
  goodCut h460 120 0 [(0,1)] (by decide)

private def row462 := state 249 0 [(~~~(primaryWord 3))] 7
set_option maxRecDepth 8192 in
private theorem h462 : Good row462 :=
  goodBoth h457 h461 121 0 121 128 1 129 (by decide)

private def row463 := state 251 0 [(~~~(primaryWord 3))] 8
set_option maxRecDepth 8192 in
private theorem h463 : Good row463 :=
  goodCut h462 249 0 [(1,3)] (by decide)

private def row464 := state 249 2 [(~~~(primaryWord 3))] 8
set_option maxRecDepth 8192 in
private theorem h464 : Good row464 :=
  goodCut h462 249 0 [(0,2)] (by decide)

private def row465 := state 507 0 [(~~~(primaryWord 3))] 10
set_option maxRecDepth 8192 in
private theorem h465 : Good row465 :=
  goodBoth h463 h464 251 0 251 256 2 258 (by decide)

private def row466 := state 511 0 [(~~~(primaryWord 3))] 11
set_option maxRecDepth 8192 in
private theorem h466 : Good row466 :=
  goodCut h465 507 0 [(2,6)] (by decide)

private def row467 := state 511 0 [(~~~(primaryWord 4))] 11
set_option maxRecDepth 8192 in
private theorem h467 : Good row467 :=
  goodCut h339 495 0 [(8,24)] (by decide)

private def row468 := state 97 0 [(~~~(primaryWord 5))] 2
set_option maxRecDepth 8192 in
private theorem h468 : Good row468 :=
  goodCut h139 64 1 [(64,65), (64,96)] (by decide)

private def row469 := state 96 1 [(~~~(primaryWord 5))] 2
set_option maxRecDepth 8192 in
private theorem h469 : Good row469 :=
  goodCut h152 1 0 [(64,96), (32,96)] (by decide)

private def row470 := state 225 0 [(~~~(primaryWord 5))] 4
set_option maxRecDepth 8192 in
private theorem h470 : Good row470 :=
  goodBoth h468 h469 97 0 97 128 1 129 (by decide)

private def row471 := state 227 0 [(~~~(primaryWord 5))] 5
set_option maxRecDepth 8192 in
private theorem h471 : Good row471 :=
  goodCut h470 225 0 [(1,3)] (by decide)

private def row472 := state 225 2 [(~~~(primaryWord 5))] 5
set_option maxRecDepth 8192 in
private theorem h472 : Good row472 :=
  goodCut h470 225 0 [(0,2)] (by decide)

private def row473 := state 483 0 [(~~~(primaryWord 5))] 7
set_option maxRecDepth 8192 in
private theorem h473 : Good row473 :=
  goodBoth h471 h472 227 0 227 256 2 258 (by decide)

private def row474 := state 499 0 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h474 : Good row474 :=
  goodCut h473 483 0 [(32,48)] (by decide)

private def row475 := state 483 16 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h475 : Good row475 :=
  goodCut h473 483 0 [(0,16)] (by decide)

private def row476 := state 507 0 [(~~~(primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h476 : Good row476 :=
  goodBoth h474 h475 499 0 499 8 16 24 (by decide)

private def row477 := state 511 0 [(~~~(primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h477 : Good row477 :=
  goodCut h476 507 0 [(2,6)] (by decide)

private def row478 := state 511 0 [(~~~(primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h478 : Good row478 :=
  goodCut h353 447 0 [(1,65)] (by decide)

private def row479 := state 511 0 [(~~~(primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h479 : Good row479 :=
  goodCut h184 383 0 [(1,129)] (by decide)

private def row480 := state 511 0 [(~~~(primaryWord 8))] 11
set_option maxRecDepth 8192 in
private theorem h480 : Good row480 :=
  goodCut h358 255 0 [(2,258)] (by decide)

private def row481 := state 511 0 [] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h481 : Good row481 :=
  fastGoodSplit row481 [
  checked h445, checked h313, checked h323, checked h331, checked h332, checked h335, checked h336, checked h340,
  checked h341, checked h349, checked h350, checked h354, checked h355, checked h356, checked h357, checked h359,
  checked h369, checked h455, checked h370, checked h371, checked h372, checked h373, checked h374, checked h375,
  checked h376, checked h377, checked h378, checked h379, checked h380, checked h390, checked h391, checked h392,
  checked h456, checked h393, checked h394, checked h395, checked h396, checked h397, checked h398, checked h399,
  checked h400, checked h401, checked h402, checked h403, checked h404, checked h466, checked h405, checked h406,
  checked h407, checked h408, checked h409, checked h410, checked h411, checked h412, checked h413, checked h414,
  checked h467, checked h415, checked h416, checked h417, checked h418, checked h419, checked h420, checked h421,
  checked h422, checked h477, checked h423, checked h424, checked h425, checked h426, checked h427, checked h428,
  checked h478, checked h429, checked h430, checked h431, checked h432, checked h479, checked h433, checked h434,
  checked h480
  ] [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ] (by decide)

private def row482 := state 1023 0 [(primaryWord 0 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h482 : Good row482 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row483 := state 1023 0 [(primaryWord 0 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h483 : Good row483 :=
  goodCut h481 511 0 [(5,517)] (by decide)

private def row484 := state 894 1 [(primaryWord 1 &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h484 : Good row484 :=
  goodCut h59 894 0 [(0,1)] (by decide)

private def row485 := state 1023 0 [(primaryWord 1 &&& primaryWord 2)] 13
set_option maxRecDepth 8192 in
private theorem h485 : Good row485 :=
  goodBoth h60 h484 895 0 895 128 1 129 (by decide)

private def row486 := state 894 1 [(primaryWord 1 ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h486 : Good row486 :=
  goodCut h69 894 0 [(0,1)] (by decide)

private def row487 := state 1023 0 [(primaryWord 1 ||| primaryWord 2)] 13
set_option maxRecDepth 8192 in
private theorem h487 : Good row487 :=
  goodBoth h70 h486 895 0 895 128 1 129 (by decide)

private def row488 := state 782 0 [(primaryWord 1 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h488 : Good row488 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row489 := state 774 8 [(primaryWord 1 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h489 : Good row489 :=
  goodCut h4 774 0 [(0,8)] (by decide)

private def row490 := state 798 0 [(primaryWord 1 &&& primaryWord 3)] 7
set_option maxRecDepth 8192 in
private theorem h490 : Good row490 :=
  goodBoth h488 h489 782 0 782 16 8 24 (by decide)

private def row491 := state 830 0 [(primaryWord 1 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h491 : Good row491 :=
  goodCut h490 798 0 [(16,48)] (by decide)

private def row492 := state 798 32 [(primaryWord 1 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h492 : Good row492 :=
  goodCut h490 798 0 [(0,32)] (by decide)

private def row493 := state 894 0 [(primaryWord 1 &&& primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h493 : Good row493 :=
  goodBoth h491 h492 830 0 830 64 32 96 (by decide)

private def row494 := state 894 1 [(primaryWord 1 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h494 : Good row494 :=
  goodCut h493 894 0 [(0,1)] (by decide)

private def row495 := state 1023 0 [(primaryWord 1 &&& primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h495 : Good row495 :=
  goodBoth h77 h494 895 0 895 128 1 129 (by decide)

private def row496 := state 767 0 [(primaryWord 1 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h496 : Good row496 :=
  goodCut h298 765 0 [(9,11)] (by decide)

private def row497 := state 765 2 [(primaryWord 1 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h497 : Good row497 :=
  goodCut h298 765 0 [(8,10)] (by decide)

private def row498 := state 1023 0 [(primaryWord 1 ||| primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h498 : Good row498 :=
  goodBoth h496 h497 767 0 767 256 2 258 (by decide)

private def row499 := state 798 0 [(primaryWord 1 &&& primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h499 : Good row499 :=
  goodBoth h5 h6 782 0 782 16 8 24 (by decide)

private def row500 := state 830 0 [(primaryWord 1 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h500 : Good row500 :=
  goodCut h499 798 0 [(16,48)] (by decide)

private def row501 := state 774 32 [] 5
set_option maxRecDepth 8192 in
private theorem h501 : Good row501 :=
  goodCut h4 774 0 [(0,32)] (by decide)

private def row502 := state 782 32 [] 6
set_option maxRecDepth 8192 in
private theorem h502 : Good row502 :=
  goodCut h501 806 0 [(4,12)] (by decide)

private def row503 := state 774 40 [] 6
set_option maxRecDepth 8192 in
private theorem h503 : Good row503 :=
  goodCut h501 806 0 [(0,8)] (by decide)

private def row504 := state 798 32 [(primaryWord 1 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h504 : Good row504 :=
  goodBoth h502 h503 814 0 814 16 8 24 (by decide)

private def row505 := state 894 0 [(primaryWord 1 &&& primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h505 : Good row505 :=
  goodBoth h500 h504 830 0 830 64 32 96 (by decide)

private def row506 := state 894 1 [(primaryWord 1 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h506 : Good row506 :=
  goodCut h505 894 0 [(0,1)] (by decide)

private def row507 := state 1023 0 [(primaryWord 1 &&& primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h507 : Good row507 :=
  goodBoth h81 h506 895 0 895 128 1 129 (by decide)

private def row508 := state 798 0 [(primaryWord 1 ||| primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h508 : Good row508 :=
  goodBoth h5 h6 782 0 782 16 10 26 (by decide)

private def row509 := state 830 0 [(primaryWord 1 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h509 : Good row509 :=
  goodCut h508 798 0 [(16,48)] (by decide)

private def row510 := state 798 32 [(primaryWord 1 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h510 : Good row510 :=
  goodBoth h502 h503 814 0 814 16 10 26 (by decide)

private def row511 := state 894 0 [(primaryWord 1 ||| primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h511 : Good row511 :=
  goodBoth h509 h510 830 0 830 64 32 96 (by decide)

private def row512 := state 894 1 [(primaryWord 1 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h512 : Good row512 :=
  goodCut h511 894 0 [(0,1)] (by decide)

private def row513 := state 1023 0 [(primaryWord 1 ||| primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h513 : Good row513 :=
  goodBoth h82 h512 895 0 895 128 1 129 (by decide)

private def row514 := state 830 0 [(primaryWord 1 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h514 : Good row514 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row515 := state 798 32 [(primaryWord 1 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h515 : Good row515 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row516 := state 894 0 [(primaryWord 1 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h516 : Good row516 :=
  goodBoth h514 h515 830 0 830 64 32 96 (by decide)

private def row517 := state 894 1 [(primaryWord 1 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h517 : Good row517 :=
  goodCut h516 894 0 [(0,1)] (by decide)

private def row518 := state 1023 0 [(primaryWord 1 &&& primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h518 : Good row518 :=
  goodBoth h86 h517 895 0 895 128 1 129 (by decide)

private def row519 := state 830 0 [(primaryWord 1 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h519 : Good row519 :=
  goodCut h7 798 0 [(18,50)] (by decide)

private def row520 := state 798 32 [(primaryWord 1 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h520 : Good row520 :=
  goodCut h7 798 0 [(2,34)] (by decide)

private def row521 := state 894 0 [(primaryWord 1 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h521 : Good row521 :=
  goodBoth h519 h520 830 0 830 64 32 96 (by decide)

private def row522 := state 894 1 [(primaryWord 1 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h522 : Good row522 :=
  goodCut h521 894 0 [(0,1)] (by decide)

private def row523 := state 1023 0 [(primaryWord 1 ||| primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h523 : Good row523 :=
  goodBoth h87 h522 895 0 895 128 1 129 (by decide)

private def row524 := state 830 1 [] 9
set_option maxRecDepth 8192 in
private theorem h524 : Good row524 :=
  goodCut h8 830 0 [(0,1)] (by decide)

private def row525 := state 894 1 [(primaryWord 1 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h525 : Good row525 :=
  goodBoth h524 h89 831 0 831 64 32 96 (by decide)

private def row526 := state 1023 0 [(primaryWord 1 &&& primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h526 : Good row526 :=
  goodBoth h90 h525 895 0 895 128 1 129 (by decide)

private def row527 := state 894 1 [(primaryWord 1 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h527 : Good row527 :=
  goodBoth h524 h89 831 0 831 64 34 98 (by decide)

private def row528 := state 1023 0 [(primaryWord 1 ||| primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h528 : Good row528 :=
  goodBoth h91 h527 895 0 895 128 1 129 (by decide)

private def row529 := state 1023 0 [(primaryWord 1 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h529 : Good row529 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row530 := state 767 0 [(primaryWord 1 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h530 : Good row530 :=
  goodCut h298 765 0 [(132,134)] (by decide)

private def row531 := state 765 2 [(primaryWord 1 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h531 : Good row531 :=
  goodCut h298 765 0 [(128,130)] (by decide)

private def row532 := state 1023 0 [(primaryWord 1 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h532 : Good row532 :=
  goodBoth h530 h531 767 0 767 256 2 258 (by decide)

private def row533 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h533 : Good row533 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row534 := state 1023 0 [(primaryWord 1 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h534 : Good row534 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row535 := state 1023 0 [(primaryWord 1 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h535 : Good row535 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row536 := state 767 0 [(primaryWord 1 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h536 : Good row536 :=
  goodCut h298 765 0 [(513,515)] (by decide)

private def row537 := state 765 2 [(primaryWord 1 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h537 : Good row537 :=
  goodCut h298 765 0 [(512,514)] (by decide)

private def row538 := state 1023 0 [(primaryWord 1 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h538 : Good row538 :=
  goodBoth h536 h537 767 0 767 256 2 258 (by decide)

private def row539 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h539 : Good row539 :=
  goodCut h298 765 0 [(4,6)] (by decide)

private def row540 := state 782 0 [(primaryWord 2 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h540 : Good row540 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row541 := state 774 8 [(primaryWord 2 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h541 : Good row541 :=
  goodCut h4 774 0 [(0,8)] (by decide)

private def row542 := state 798 0 [(primaryWord 2 &&& primaryWord 3)] 7
set_option maxRecDepth 8192 in
private theorem h542 : Good row542 :=
  goodBoth h540 h541 782 0 782 16 8 24 (by decide)

private def row543 := state 830 0 [(primaryWord 2 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h543 : Good row543 :=
  goodCut h542 798 0 [(16,48)] (by decide)

private def row544 := state 798 32 [(primaryWord 2 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h544 : Good row544 :=
  goodCut h542 798 0 [(0,32)] (by decide)

private def row545 := state 894 0 [(primaryWord 2 &&& primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h545 : Good row545 :=
  goodBoth h543 h544 830 0 830 64 32 96 (by decide)

private def row546 := state 894 1 [(primaryWord 2 &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h546 : Good row546 :=
  goodCut h545 894 0 [(0,1)] (by decide)

private def row547 := state 1023 0 [(primaryWord 2 &&& primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h547 : Good row547 :=
  goodBoth h196 h546 895 0 895 128 1 129 (by decide)

private def row548 := state 782 0 [(primaryWord 2 ||| primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h548 : Good row548 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row549 := state 774 8 [(primaryWord 2 ||| primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h549 : Good row549 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row550 := state 798 0 [(primaryWord 2 ||| primaryWord 3)] 7
set_option maxRecDepth 8192 in
private theorem h550 : Good row550 :=
  goodBoth h548 h549 782 0 782 16 8 24 (by decide)

private def row551 := state 830 0 [(primaryWord 2 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h551 : Good row551 :=
  goodCut h550 798 0 [(16,48)] (by decide)

private def row552 := state 798 32 [(primaryWord 2 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h552 : Good row552 :=
  goodCut h550 798 0 [(0,32)] (by decide)

private def row553 := state 894 0 [(primaryWord 2 ||| primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h553 : Good row553 :=
  goodBoth h551 h552 830 0 830 64 32 96 (by decide)

private def row554 := state 894 1 [(primaryWord 2 ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h554 : Good row554 :=
  goodCut h553 894 0 [(0,1)] (by decide)

private def row555 := state 1023 0 [(primaryWord 2 ||| primaryWord 3)] 13
set_option maxRecDepth 8192 in
private theorem h555 : Good row555 :=
  goodBoth h197 h554 895 0 895 128 1 129 (by decide)

private def row556 := state 798 0 [(primaryWord 2 &&& primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h556 : Good row556 :=
  goodBoth h5 h6 782 0 782 16 8 24 (by decide)

private def row557 := state 830 0 [(primaryWord 2 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h557 : Good row557 :=
  goodCut h556 798 0 [(16,48)] (by decide)

private def row558 := state 798 32 [(primaryWord 2 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h558 : Good row558 :=
  goodBoth h502 h503 814 0 814 16 8 24 (by decide)

private def row559 := state 894 0 [(primaryWord 2 &&& primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h559 : Good row559 :=
  goodBoth h557 h558 830 0 830 64 32 96 (by decide)

private def row560 := state 894 1 [(primaryWord 2 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h560 : Good row560 :=
  goodCut h559 894 0 [(0,1)] (by decide)

private def row561 := state 1023 0 [(primaryWord 2 &&& primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h561 : Good row561 :=
  goodBoth h198 h560 895 0 895 128 1 129 (by decide)

private def row562 := state 507 4 [(primaryWord 2 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h562 : Good row562 :=
  goodCut h330 507 0 [(16,20)] (by decide)

private def row563 := state 1023 0 [(primaryWord 2 ||| primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h563 : Good row563 :=
  goodBoth h396 h562 511 0 511 512 4 516 (by decide)

private def row564 := state 830 0 [(primaryWord 2 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h564 : Good row564 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row565 := state 798 32 [(primaryWord 2 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h565 : Good row565 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row566 := state 894 0 [(primaryWord 2 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h566 : Good row566 :=
  goodBoth h564 h565 830 0 830 64 32 96 (by decide)

private def row567 := state 894 1 [(primaryWord 2 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h567 : Good row567 :=
  goodCut h566 894 0 [(0,1)] (by decide)

private def row568 := state 1023 0 [(primaryWord 2 &&& primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h568 : Good row568 :=
  goodBoth h200 h567 895 0 895 128 1 129 (by decide)

private def row569 := state 830 0 [(primaryWord 2 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h569 : Good row569 :=
  goodCut h7 798 0 [(20,52)] (by decide)

private def row570 := state 798 32 [(primaryWord 2 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h570 : Good row570 :=
  goodCut h7 798 0 [(4,36)] (by decide)

private def row571 := state 894 0 [(primaryWord 2 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h571 : Good row571 :=
  goodBoth h569 h570 830 0 830 64 32 96 (by decide)

private def row572 := state 894 1 [(primaryWord 2 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h572 : Good row572 :=
  goodCut h571 894 0 [(0,1)] (by decide)

private def row573 := state 1023 0 [(primaryWord 2 ||| primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h573 : Good row573 :=
  goodBoth h201 h572 895 0 895 128 1 129 (by decide)

private def row574 := state 894 1 [(primaryWord 2 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h574 : Good row574 :=
  goodBoth h524 h89 831 0 831 64 32 96 (by decide)

private def row575 := state 1023 0 [(primaryWord 2 &&& primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h575 : Good row575 :=
  goodBoth h202 h574 895 0 895 128 1 129 (by decide)

private def row576 := state 894 1 [(primaryWord 2 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h576 : Good row576 :=
  goodBoth h524 h89 831 0 831 64 36 100 (by decide)

private def row577 := state 1023 0 [(primaryWord 2 ||| primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h577 : Good row577 :=
  goodBoth h203 h576 895 0 895 128 1 129 (by decide)

private def row578 := state 1023 0 [(primaryWord 2 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h578 : Good row578 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row579 := state 1023 0 [(primaryWord 2 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h579 : Good row579 :=
  goodCut h294 895 0 [(5,133)] (by decide)

private def row580 := state 1023 0 [(primaryWord 2 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h580 : Good row580 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row581 := state 507 4 [(primaryWord 2 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h581 : Good row581 :=
  goodCut h330 507 0 [(256,260)] (by decide)

private def row582 := state 1023 0 [(primaryWord 2 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h582 : Good row582 :=
  goodBoth h404 h581 511 0 511 512 4 516 (by decide)

private def row583 := state 1023 0 [(primaryWord 2 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h583 : Good row583 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row584 := state 1023 0 [(primaryWord 2 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h584 : Good row584 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row585 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h585 : Good row585 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row586 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h586 : Good row586 :=
  goodCut h298 765 0 [(1,3)] (by decide)

private def row587 := state 637 0 [(primaryWord 0 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h587 : Good row587 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row588 := state 636 1 [(primaryWord 0 &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h588 : Good row588 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row589 := state 765 0 [(primaryWord 0 &&& primaryWord 2)] 10
set_option maxRecDepth 8192 in
private theorem h589 : Good row589 :=
  goodBoth h587 h588 637 0 637 128 1 129 (by decide)

private def row590 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h590 : Good row590 :=
  goodCut h589 765 0 [(1,3)] (by decide)

private def row591 := state 637 0 [(primaryWord 0 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h591 : Good row591 :=
  goodCut h192 636 0 [(68,69)] (by decide)

private def row592 := state 636 1 [(primaryWord 0 ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h592 : Good row592 :=
  goodCut h192 636 0 [(4,5)] (by decide)

private def row593 := state 765 0 [(primaryWord 0 ||| primaryWord 2)] 10
set_option maxRecDepth 8192 in
private theorem h593 : Good row593 :=
  goodBoth h591 h592 637 0 637 128 1 129 (by decide)

private def row594 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 2)] 11
set_option maxRecDepth 8192 in
private theorem h594 : Good row594 :=
  goodCut h593 765 0 [(1,3)] (by decide)

private def row595 := state 903 0 [] 7
set_option maxRecDepth 8192 in
private theorem h595 : Good row595 :=
  goodBoth h71 h72 775 0 775 128 1 129 (by decide)

private def row596 := state 967 0 [] 8
set_option maxRecDepth 8192 in
private theorem h596 : Good row596 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row597 := state 903 64 [] 8
set_option maxRecDepth 8192 in
private theorem h597 : Good row597 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row598 := state 999 0 [] 10
set_option maxRecDepth 8192 in
private theorem h598 : Good row598 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row599 := state 1015 0 [] 11
set_option maxRecDepth 8192 in
private theorem h599 : Good row599 :=
  goodCut h598 999 0 [(32,48)] (by decide)

private def row600 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h600 : Good row600 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row601 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h601 : Good row601 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row602 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h602 : Good row602 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row603 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h603 : Good row603 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row604 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h604 : Good row604 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row605 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h605 : Good row605 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row606 := state 798 0 [(primaryWord 3 ||| primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h606 : Good row606 :=
  goodBoth h5 h6 782 0 782 16 8 24 (by decide)

private def row607 := state 830 0 [(primaryWord 3 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h607 : Good row607 :=
  goodCut h606 798 0 [(16,48)] (by decide)

private def row608 := state 798 32 [(primaryWord 3 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h608 : Good row608 :=
  goodBoth h502 h503 814 0 814 16 8 24 (by decide)

private def row609 := state 894 0 [(primaryWord 3 ||| primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h609 : Good row609 :=
  goodBoth h607 h608 830 0 830 64 32 96 (by decide)

private def row610 := state 894 1 [(primaryWord 3 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h610 : Good row610 :=
  goodCut h609 894 0 [(0,1)] (by decide)

private def row611 := state 1023 0 [(primaryWord 3 ||| primaryWord 4)] 13
set_option maxRecDepth 8192 in
private theorem h611 : Good row611 :=
  goodBoth h218 h610 895 0 895 128 1 129 (by decide)

private def row612 := state 830 0 [(primaryWord 3 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h612 : Good row612 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row613 := state 798 32 [(primaryWord 3 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h613 : Good row613 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row614 := state 894 0 [(primaryWord 3 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h614 : Good row614 :=
  goodBoth h612 h613 830 0 830 64 32 96 (by decide)

private def row615 := state 894 1 [(primaryWord 3 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h615 : Good row615 :=
  goodCut h614 894 0 [(0,1)] (by decide)

private def row616 := state 1023 0 [(primaryWord 3 &&& primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h616 : Good row616 :=
  goodBoth h219 h615 895 0 895 128 1 129 (by decide)

private def row617 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (primaryWord 3 ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h617 : Good row617 :=
  goodCut h599 1015 0 [(36,44)] (by decide)

private def row618 := state 894 1 [(primaryWord 3 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h618 : Good row618 :=
  goodBoth h524 h89 831 0 831 64 32 96 (by decide)

private def row619 := state 1023 0 [(primaryWord 3 &&& primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h619 : Good row619 :=
  goodBoth h221 h618 895 0 895 128 1 129 (by decide)

private def row620 := state 894 1 [(primaryWord 3 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h620 : Good row620 :=
  goodBoth h524 h89 831 0 831 64 40 104 (by decide)

private def row621 := state 1023 0 [(primaryWord 3 ||| primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h621 : Good row621 :=
  goodBoth h222 h620 895 0 895 128 1 129 (by decide)

private def row622 := state 1023 0 [(primaryWord 3 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h622 : Good row622 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row623 := state 1023 0 [(primaryWord 3 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h623 : Good row623 :=
  goodCut h294 895 0 [(9,137)] (by decide)

private def row624 := state 1023 0 [(primaryWord 3 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h624 : Good row624 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row625 := state 1023 0 [(primaryWord 3 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h625 : Good row625 :=
  goodBoth h299 h300 767 0 767 256 10 266 (by decide)

private def row626 := state 1023 0 [(primaryWord 3 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h626 : Good row626 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row627 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (primaryWord 3 ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h627 : Good row627 :=
  goodCut h599 1015 0 [(528,536)] (by decide)

private def row628 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h628 : Good row628 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row629 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h629 : Good row629 :=
  goodCut h298 765 0 [(1,3), (10,266)] (by decide)

private def row630 := state 637 0 [(primaryWord 0 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h630 : Good row630 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row631 := state 636 1 [(primaryWord 0 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h631 : Good row631 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row632 := state 765 0 [(primaryWord 0 &&& primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h632 : Good row632 :=
  goodBoth h630 h631 637 0 637 128 1 129 (by decide)

private def row633 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h633 : Good row633 :=
  goodCut h632 765 0 [(1,3)] (by decide)

private def row634 := state 637 0 [(primaryWord 0 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h634 : Good row634 :=
  goodCut h192 636 0 [(72,73)] (by decide)

private def row635 := state 636 1 [(primaryWord 0 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h635 : Good row635 :=
  goodCut h192 636 0 [(8,9)] (by decide)

private def row636 := state 765 0 [(primaryWord 0 ||| primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h636 : Good row636 :=
  goodBoth h634 h635 637 0 637 128 1 129 (by decide)

private def row637 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h637 : Good row637 :=
  goodCut h636 765 0 [(1,3)] (by decide)

private def row638 := state 830 0 [(primaryWord 4 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h638 : Good row638 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row639 := state 798 32 [(primaryWord 4 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h639 : Good row639 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row640 := state 894 0 [(primaryWord 4 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h640 : Good row640 :=
  goodBoth h638 h639 830 0 830 64 32 96 (by decide)

private def row641 := state 894 1 [(primaryWord 4 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h641 : Good row641 :=
  goodCut h640 894 0 [(0,1)] (by decide)

private def row642 := state 1023 0 [(primaryWord 4 &&& primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h642 : Good row642 :=
  goodBoth h227 h641 895 0 895 128 1 129 (by decide)

private def row643 := state 830 0 [(primaryWord 4 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h643 : Good row643 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row644 := state 798 32 [(primaryWord 4 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h644 : Good row644 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row645 := state 894 0 [(primaryWord 4 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h645 : Good row645 :=
  goodBoth h643 h644 830 0 830 64 32 96 (by decide)

private def row646 := state 894 1 [(primaryWord 4 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h646 : Good row646 :=
  goodCut h645 894 0 [(0,1)] (by decide)

private def row647 := state 1023 0 [(primaryWord 4 ||| primaryWord 5)] 13
set_option maxRecDepth 8192 in
private theorem h647 : Good row647 :=
  goodBoth h228 h646 895 0 895 128 1 129 (by decide)

private def row648 := state 894 1 [(primaryWord 4 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h648 : Good row648 :=
  goodBoth h524 h89 831 0 831 64 32 96 (by decide)

private def row649 := state 1023 0 [(primaryWord 4 &&& primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h649 : Good row649 :=
  goodBoth h229 h648 895 0 895 128 1 129 (by decide)

private def row650 := state 1007 0 [] 11
set_option maxRecDepth 8192 in
private theorem h650 : Good row650 :=
  goodCut h598 999 0 [(4,12)] (by decide)

private def row651 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (primaryWord 4 ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h651 : Good row651 :=
  goodCut h650 1007 0 [(72,88)] (by decide)

private def row652 := state 1023 0 [(primaryWord 4 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h652 : Good row652 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row653 := state 1023 0 [(primaryWord 4 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h653 : Good row653 :=
  goodCut h294 895 0 [(17,145)] (by decide)

private def row654 := state 1023 0 [(primaryWord 4 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h654 : Good row654 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row655 := state 1023 0 [(primaryWord 4 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h655 : Good row655 :=
  goodBoth h299 h300 767 0 767 256 18 274 (by decide)

private def row656 := state 1023 0 [(primaryWord 4 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h656 : Good row656 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row657 := state 1023 0 [(primaryWord 4 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h657 : Good row657 :=
  goodCut h481 511 0 [(20,532)] (by decide)

private def row658 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h658 : Good row658 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row659 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h659 : Good row659 :=
  goodCut h298 765 0 [(1,3), (18,274)] (by decide)

private def row660 := state 637 0 [(primaryWord 0 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h660 : Good row660 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row661 := state 636 1 [(primaryWord 0 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h661 : Good row661 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row662 := state 765 0 [(primaryWord 0 &&& primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h662 : Good row662 :=
  goodBoth h660 h661 637 0 637 128 1 129 (by decide)

private def row663 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h663 : Good row663 :=
  goodCut h662 765 0 [(1,3)] (by decide)

private def row664 := state 637 0 [(primaryWord 0 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h664 : Good row664 :=
  goodCut h192 636 0 [(80,81)] (by decide)

private def row665 := state 636 1 [(primaryWord 0 ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h665 : Good row665 :=
  goodCut h192 636 0 [(16,17)] (by decide)

private def row666 := state 765 0 [(primaryWord 0 ||| primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h666 : Good row666 :=
  goodBoth h664 h665 637 0 637 128 1 129 (by decide)

private def row667 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h667 : Good row667 :=
  goodCut h666 765 0 [(1,3)] (by decide)

private def row668 := state 871 0 [(primaryWord 5 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h668 : Good row668 :=
  goodCut h73 839 0 [(64,96)] (by decide)

private def row669 := state 839 32 [(primaryWord 5 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h669 : Good row669 :=
  goodCut h73 839 0 [(0,32)] (by decide)

private def row670 := state 887 0 [(primaryWord 5 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h670 : Good row670 :=
  goodBoth h668 h669 871 0 871 16 32 48 (by decide)

private def row671 := state 1015 0 [(primaryWord 5 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h671 : Good row671 :=
  goodCut h670 887 0 [(1,129)] (by decide)

private def row672 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (primaryWord 5 &&& primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h672 : Good row672 :=
  goodCut h671 1015 0 [(4,12)] (by decide)

private def row673 := state 894 1 [(primaryWord 5 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h673 : Good row673 :=
  goodBoth h524 h89 831 0 831 64 32 96 (by decide)

private def row674 := state 1023 0 [(primaryWord 5 ||| primaryWord 6)] 13
set_option maxRecDepth 8192 in
private theorem h674 : Good row674 :=
  goodBoth h236 h673 895 0 895 128 1 129 (by decide)

private def row675 := state 1023 0 [(primaryWord 5 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h675 : Good row675 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row676 := state 1023 0 [(primaryWord 5 ||| primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h676 : Good row676 :=
  goodCut h294 895 0 [(33,161)] (by decide)

private def row677 := state 1023 0 [(primaryWord 5 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h677 : Good row677 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row678 := state 1023 0 [(primaryWord 5 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h678 : Good row678 :=
  goodBoth h299 h300 767 0 767 256 34 290 (by decide)

private def row679 := state 1023 0 [(primaryWord 5 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h679 : Good row679 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row680 := state 1023 0 [(primaryWord 5 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h680 : Good row680 :=
  goodCut h481 511 0 [(36,548)] (by decide)

private def row681 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h681 : Good row681 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row682 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h682 : Good row682 :=
  goodCut h298 765 0 [(1,3), (34,290)] (by decide)

private def row683 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h683 : Good row683 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row684 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h684 : Good row684 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row685 := state 637 0 [(primaryWord 0 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h685 : Good row685 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row686 := state 636 1 [(primaryWord 0 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h686 : Good row686 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row687 := state 765 0 [(primaryWord 0 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h687 : Good row687 :=
  goodBoth h685 h686 637 0 637 128 1 129 (by decide)

private def row688 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h688 : Good row688 :=
  goodCut h687 765 0 [(1,3)] (by decide)

private def row689 := state 0 257 [(primaryWord 0 ||| primaryWord 8)] 0
set_option maxRecDepth 8192 in
private theorem h689 : Good row689 :=
  goodZero row689 rfl

private def row690 := state 323 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 2
set_option maxRecDepth 8192 in
private theorem h690 : Good row690 :=
  goodCut h689 257 2 [(1,3), (1,65)] (by decide)

private def row691 := state 327 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 4
set_option maxRecDepth 8192 in
private theorem h691 : Good row691 :=
  goodBoth h690 h163 323 0 67 4 2 6 (by decide)

private def row692 := state 335 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h692 : Good row692 :=
  goodCut h691 327 0 [(4,12)] (by decide)

private def row693 := state 327 8 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h693 : Good row693 :=
  goodCut h691 327 0 [(0,8)] (by decide)

private def row694 := state 351 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 7
set_option maxRecDepth 8192 in
private theorem h694 : Good row694 :=
  goodBoth h692 h693 335 0 335 16 8 24 (by decide)

private def row695 := state 383 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h695 : Good row695 :=
  goodCut h694 351 0 [(17,49)] (by decide)

private def row696 := state 124 1 [(primaryWord 0 ||| primaryWord 5)] 6
set_option maxRecDepth 8192 in
private theorem h696 : Good row696 :=
  goodCut h97 124 0 [(32,33)] (by decide)

private def row697 := state 0 321 [(primaryWord 0 ||| primaryWord 8)] 1
set_option maxRecDepth 8192 in
private theorem h697 : Good row697 :=
  goodOne row697 (by decide)

private def row698 := state 0 337 [(primaryWord 0 ||| primaryWord 8)] 2
set_option maxRecDepth 8192 in
private theorem h698 : Good row698 :=
  goodCut h697 321 0 [(0,16)] (by decide)

private def row699 := state 112 257 [(primaryWord 0 ||| primaryWord 8), ((primaryWord 0 ||| primaryWord 8) ||| primaryWord 5)] 3
set_option maxRecDepth 8192 in
private theorem h699 : Good row699 :=
  goodCut h698 337 32 [(16,48)] (by decide)

private def row700 := state 0 273 [(primaryWord 0 ||| primaryWord 8)] 1
set_option maxRecDepth 8192 in
private theorem h700 : Good row700 :=
  goodOne row700 (by decide)

private def row701 := state 96 273 [(primaryWord 0 ||| primaryWord 8), ((primaryWord 0 ||| primaryWord 8) ||| primaryWord 5)] 3
set_option maxRecDepth 8192 in
private theorem h701 : Good row701 :=
  goodCut h700 273 32 [(64,96), (32,96)] (by decide)

private def row702 := state 120 257 [(primaryWord 0 ||| primaryWord 8), ((primaryWord 0 ||| primaryWord 8) ||| primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h702 : Good row702 :=
  goodBoth h699 h701 369 0 369 8 16 24 (by decide)

private def row703 := state 120 261 [(primaryWord 0 ||| primaryWord 8), ((primaryWord 0 ||| primaryWord 8) ||| primaryWord 5)] 6
set_option maxRecDepth 8192 in
private theorem h703 : Good row703 :=
  goodCut h702 377 0 [(0,4)] (by decide)

private def row704 := state 382 1 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h704 : Good row704 :=
  goodBoth h696 h703 125 0 381 2 4 6 (by decide)

private def row705 := state 511 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h705 : Good row705 :=
  goodBoth h695 h704 383 0 383 128 1 129 (by decide)

private def row706 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h706 : Good row706 :=
  goodCut h705 511 0 [(4,516)] (by decide)

private def row707 := state 1023 0 [(primaryWord 6 &&& primaryWord 7)] 13
set_option maxRecDepth 8192 in
private theorem h707 : Good row707 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row708 := state 415 0 [(primaryWord 3 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h708 : Good row708 :=
  goodCut h344 399 0 [(8,24)] (by decide)

private def row709 := state 399 16 [(primaryWord 3 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h709 : Good row709 :=
  goodCut h344 399 0 [(0,16)] (by decide)

private def row710 := state 447 0 [(primaryWord 3 &&& primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h710 : Good row710 :=
  goodBoth h708 h709 415 0 415 32 16 48 (by decide)

private def row711 := state 959 0 [(primaryWord 3 &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h711 : Good row711 :=
  goodCut h710 447 0 [(4,516)] (by decide)

private def row712 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h712 : Good row712 :=
  goodCut h711 959 0 [(160,224)] (by decide)

private def row713 := state 1023 0 [(primaryWord 6 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h713 : Good row713 :=
  goodBoth h299 h300 767 0 767 256 2 258 (by decide)

private def row714 := state 1023 0 [(primaryWord 6 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h714 : Good row714 :=
  goodBoth h299 h300 767 0 767 256 66 322 (by decide)

private def row715 := state 1023 0 [(primaryWord 6 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h715 : Good row715 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row716 := state 1023 0 [(primaryWord 6 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h716 : Good row716 :=
  goodCut h481 511 0 [(68,580)] (by decide)

private def row717 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h717 : Good row717 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row718 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h718 : Good row718 :=
  goodCut h298 765 0 [(1,3), (66,322)] (by decide)

private def row719 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h719 : Good row719 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row720 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h720 : Good row720 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row721 := state 637 0 [(primaryWord 0 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h721 : Good row721 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row722 := state 636 1 [(primaryWord 0 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h722 : Good row722 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row723 := state 765 0 [(primaryWord 0 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h723 : Good row723 :=
  goodBoth h721 h722 637 0 637 128 1 129 (by decide)

private def row724 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h724 : Good row724 :=
  goodCut h723 765 0 [(1,3)] (by decide)

private def row725 := state 637 0 [(primaryWord 0 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h725 : Good row725 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row726 := state 636 1 [(primaryWord 0 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h726 : Good row726 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row727 := state 765 0 [(primaryWord 0 ||| primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h727 : Good row727 :=
  goodBoth h725 h726 637 0 637 128 1 129 (by decide)

private def row728 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h728 : Good row728 :=
  goodCut h727 765 0 [(1,3)] (by decide)

private def row729 := state 1023 0 [(primaryWord 7 &&& primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h729 : Good row729 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row730 := state 1023 0 [(primaryWord 7 ||| primaryWord 8)] 13
set_option maxRecDepth 8192 in
private theorem h730 : Good row730 :=
  goodCut h294 895 0 [(257,385)] (by decide)

private def row731 := state 1023 0 [(primaryWord 7 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h731 : Good row731 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row732 := state 1023 0 [(primaryWord 7 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h732 : Good row732 :=
  goodCut h294 895 0 [(513,641)] (by decide)

private def row733 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h733 : Good row733 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row734 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h734 : Good row734 :=
  goodCut h298 765 0 [(1,3), (130,386)] (by decide)

private def row735 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h735 : Good row735 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row736 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h736 : Good row736 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row737 := state 383 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h737 : Good row737 :=
  goodCut h180 127 0 [] (by decide)

private def row738 := state 895 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 10
set_option maxRecDepth 8192 in
private theorem h738 : Good row738 :=
  goodCut h737 383 0 [(4,516)] (by decide)

private def row739 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h739 : Good row739 :=
  goodCut h738 895 0 [(1,129)] (by decide)

private def row740 := state 765 0 [(primaryWord 0 ||| primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h740 : Good row740 :=
  goodBoth h193 h297 637 0 637 128 1 129 (by decide)

private def row741 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h741 : Good row741 :=
  goodCut h740 765 0 [(1,3)] (by decide)

private def row742 := state 1023 0 [(primaryWord 8 &&& primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h742 : Good row742 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row743 := state 1023 0 [(primaryWord 8 ||| primaryWord 9)] 13
set_option maxRecDepth 8192 in
private theorem h743 : Good row743 :=
  goodCut h481 511 0 [(260,772)] (by decide)

private def row744 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h744 : Good row744 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row745 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h745 : Good row745 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row746 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h746 : Good row746 :=
  goodCut h298 765 0 [(1,3)] (by decide)

private def row747 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h747 : Good row747 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row748 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h748 : Good row748 :=
  goodCut h298 765 0 [(1,3), (514,770)] (by decide)

private def row749 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h749 : Good row749 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row750 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h750 : Good row750 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row751 := state 249 4 [] 8
set_option maxRecDepth 8192 in
private theorem h751 : Good row751 :=
  goodCut h387 249 0 [(0,4)] (by decide)

private def row752 := state 765 0 [(primaryWord 0 &&& primaryWord 9)] 10
set_option maxRecDepth 8192 in
private theorem h752 : Good row752 :=
  goodBoth h388 h751 253 0 253 512 4 516 (by decide)

private def row753 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h753 : Good row753 :=
  goodCut h752 765 0 [(1,3)] (by decide)

private def row754 := state 765 0 [(primaryWord 0 ||| primaryWord 9)] 10
set_option maxRecDepth 8192 in
private theorem h754 : Good row754 :=
  goodBoth h388 h751 253 0 253 512 5 517 (by decide)

private def row755 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h755 : Good row755 :=
  goodCut h754 765 0 [(1,3)] (by decide)

private def row756 := state 56 0 [(primaryWord 3 &&& primaryWord 4)] 2
set_option maxRecDepth 8192 in
private theorem h756 : Good row756 :=
  goodCut h94 16 32 [(16,24), (16,48)] (by decide)

private def row757 := state 48 8 [(primaryWord 3 &&& primaryWord 4)] 2
set_option maxRecDepth 8192 in
private theorem h757 : Good row757 :=
  goodCut h113 8 0 [(32,48), (16,48)] (by decide)

private def row758 := state 60 0 [(primaryWord 3 &&& primaryWord 4)] 4
set_option maxRecDepth 8192 in
private theorem h758 : Good row758 :=
  goodBoth h756 h757 56 0 56 4 8 12 (by decide)

private def row759 := state 124 0 [(primaryWord 3 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h759 : Good row759 :=
  goodCut h758 60 0 [(32,96)] (by decide)

private def row760 := state 60 64 [(primaryWord 3 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h760 : Good row760 :=
  goodCut h758 60 0 [(0,64)] (by decide)

private def row761 := state 125 0 [(primaryWord 3 &&& primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h761 : Good row761 :=
  goodBoth h759 h760 124 0 124 1 64 65 (by decide)

private def row762 := state 637 0 [(primaryWord 3 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h762 : Good row762 :=
  goodCut h761 125 0 [(4,516)] (by decide)

private def row763 := state 765 0 [(primaryWord 3 &&& primaryWord 4)] 9
set_option maxRecDepth 8192 in
private theorem h763 : Good row763 :=
  goodCut h762 637 0 [(1,129)] (by decide)

private def row764 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 3 &&& primaryWord 4))] 11
set_option maxRecDepth 8192 in
private theorem h764 : Good row764 :=
  goodCut h763 765 0 [(1,3), (2,258)] (by decide)

private def row765 := state 519 0 [] 4
set_option maxRecDepth 8192 in
private theorem h765 : Good row765 :=
  goodBoth h1 h3 518 0 518 1 2 3 (by decide)

private def row766 := state 583 0 [] 5
set_option maxRecDepth 8192 in
private theorem h766 : Good row766 :=
  goodCut h765 519 0 [(1,65)] (by decide)

private def row767 := state 519 64 [] 5
set_option maxRecDepth 8192 in
private theorem h767 : Good row767 :=
  goodCut h765 519 0 [(0,64)] (by decide)

private def row768 := state 615 0 [] 7
set_option maxRecDepth 8192 in
private theorem h768 : Good row768 :=
  goodBoth h766 h767 583 0 583 32 64 96 (by decide)

private def row769 := state 743 0 [] 8
set_option maxRecDepth 8192 in
private theorem h769 : Good row769 :=
  goodCut h768 615 0 [(1,129)] (by decide)

private def row770 := state 759 0 [] 9
set_option maxRecDepth 8192 in
private theorem h770 : Good row770 :=
  goodCut h769 743 0 [(32,48)] (by decide)

private def row771 := state 1015 0 [(primaryWord 1 &&& primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h771 : Good row771 :=
  goodCut h770 759 0 [(2,258)] (by decide)

private def row772 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 3 &&& primaryWord 4))] 11
set_option maxRecDepth 8192 in
private theorem h772 : Good row772 :=
  goodCut h771 1015 0 [(4,12)] (by decide)

private def row773 := state 125 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 0)] 7
set_option maxRecDepth 8192 in
private theorem h773 : Good row773 :=
  goodBoth h759 h760 124 0 124 1 64 65 (by decide)

private def row774 := state 637 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h774 : Good row774 :=
  goodCut h773 125 0 [(4,516)] (by decide)

private def row775 := state 765 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h775 : Good row775 :=
  goodCut h774 637 0 [(1,129)] (by decide)

private def row776 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), ((primaryWord 3 &&& primaryWord 4) &&& ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h776 : Good row776 :=
  goodCut h775 765 0 [(1,3)] (by decide)

private def row777 := state 121 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h777 : Good row777 :=
  goodCut h141 113 0 [(17,25)] (by decide)

private def row778 := state 113 8 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h778 : Good row778 :=
  goodCut h141 113 0 [(0,8)] (by decide)

private def row779 := state 125 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 7
set_option maxRecDepth 8192 in
private theorem h779 : Good row779 :=
  goodBoth h777 h778 121 0 121 4 8 12 (by decide)

private def row780 := state 637 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h780 : Good row780 :=
  goodCut h779 125 0 [(4,516)] (by decide)

private def row781 := state 765 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) ||| primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h781 : Good row781 :=
  goodCut h780 637 0 [(1,129)] (by decide)

private def row782 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), ((primaryWord 3 &&& primaryWord 4) ||| ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h782 : Good row782 :=
  goodCut h781 765 0 [(1,3)] (by decide)

private def row783 := state 894 1 [(~~~(primaryWord 0))] 11
set_option maxRecDepth 8192 in
private theorem h783 : Good row783 :=
  goodCut h10 894 0 [(0,1)] (by decide)

private def row784 := state 1023 0 [(~~~(primaryWord 0))] 13
set_option maxRecDepth 8192 in
private theorem h784 : Good row784 :=
  goodBoth h247 h783 895 0 895 128 1 129 (by decide)

private def row785 := state 894 1 [(~~~(primaryWord 1))] 11
set_option maxRecDepth 8192 in
private theorem h785 : Good row785 :=
  goodCut h257 894 0 [(0,1)] (by decide)

private def row786 := state 1023 0 [(~~~(primaryWord 1))] 13
set_option maxRecDepth 8192 in
private theorem h786 : Good row786 :=
  goodBoth h258 h785 895 0 895 128 1 129 (by decide)

private def row787 := state 894 1 [(~~~(primaryWord 2))] 11
set_option maxRecDepth 8192 in
private theorem h787 : Good row787 :=
  goodCut h268 894 0 [(0,1)] (by decide)

private def row788 := state 1023 0 [(~~~(primaryWord 2))] 13
set_option maxRecDepth 8192 in
private theorem h788 : Good row788 :=
  goodBoth h269 h787 895 0 895 128 1 129 (by decide)

private def row789 := state 782 0 [(~~~(primaryWord 3))] 5
set_option maxRecDepth 8192 in
private theorem h789 : Good row789 :=
  goodCut h4 774 0 [(4,12)] (by decide)

private def row790 := state 774 8 [(~~~(primaryWord 3))] 5
set_option maxRecDepth 8192 in
private theorem h790 : Good row790 :=
  goodCut h4 774 0 [(0,8)] (by decide)

private def row791 := state 798 0 [(~~~(primaryWord 3))] 7
set_option maxRecDepth 8192 in
private theorem h791 : Good row791 :=
  goodBoth h789 h790 782 0 782 16 8 24 (by decide)

private def row792 := state 830 0 [(~~~(primaryWord 3))] 8
set_option maxRecDepth 8192 in
private theorem h792 : Good row792 :=
  goodCut h791 798 0 [(16,48)] (by decide)

private def row793 := state 798 32 [(~~~(primaryWord 3))] 8
set_option maxRecDepth 8192 in
private theorem h793 : Good row793 :=
  goodCut h791 798 0 [(0,32)] (by decide)

private def row794 := state 894 0 [(~~~(primaryWord 3))] 10
set_option maxRecDepth 8192 in
private theorem h794 : Good row794 :=
  goodBoth h792 h793 830 0 830 64 32 96 (by decide)

private def row795 := state 894 1 [(~~~(primaryWord 3))] 11
set_option maxRecDepth 8192 in
private theorem h795 : Good row795 :=
  goodCut h794 894 0 [(0,1)] (by decide)

private def row796 := state 1023 0 [(~~~(primaryWord 3))] 13
set_option maxRecDepth 8192 in
private theorem h796 : Good row796 :=
  goodBoth h270 h795 895 0 895 128 1 129 (by decide)

private def row797 := state 894 1 [(~~~(primaryWord 4))] 11
set_option maxRecDepth 8192 in
private theorem h797 : Good row797 :=
  goodCut h279 894 0 [(0,1)] (by decide)

private def row798 := state 1023 0 [(~~~(primaryWord 4))] 13
set_option maxRecDepth 8192 in
private theorem h798 : Good row798 :=
  goodBoth h280 h797 895 0 895 128 1 129 (by decide)

private def row799 := state 830 0 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h799 : Good row799 :=
  goodCut h7 798 0 [(16,48)] (by decide)

private def row800 := state 798 32 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h800 : Good row800 :=
  goodCut h7 798 0 [(0,32)] (by decide)

private def row801 := state 894 0 [(~~~(primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h801 : Good row801 :=
  goodBoth h799 h800 830 0 830 64 32 96 (by decide)

private def row802 := state 894 1 [(~~~(primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h802 : Good row802 :=
  goodCut h801 894 0 [(0,1)] (by decide)

private def row803 := state 1023 0 [(~~~(primaryWord 5))] 13
set_option maxRecDepth 8192 in
private theorem h803 : Good row803 :=
  goodBoth h281 h802 895 0 895 128 1 129 (by decide)

private def row804 := state 894 1 [(~~~(primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h804 : Good row804 :=
  goodCut h290 894 0 [(0,1)] (by decide)

private def row805 := state 1023 0 [(~~~(primaryWord 6))] 13
set_option maxRecDepth 8192 in
private theorem h805 : Good row805 :=
  goodBoth h291 h804 895 0 895 128 1 129 (by decide)

private def row806 := state 1023 0 [(~~~(primaryWord 7))] 13
set_option maxRecDepth 8192 in
private theorem h806 : Good row806 :=
  goodCut h294 895 0 [(1,129)] (by decide)

private def row807 := state 262 0 [(~~~(primaryWord 8))] 2
set_option maxRecDepth 8192 in
private theorem h807 : Good row807 :=
  goodCut h2 2 4 [(2,6), (2,258)] (by decide)

private def row808 := state 258 4 [(~~~(primaryWord 8))] 2
set_option maxRecDepth 8192 in
private theorem h808 : Good row808 :=
  goodCut h0 4 0 [(256,258), (2,258)] (by decide)

private def row809 := state 774 0 [(~~~(primaryWord 8))] 4
set_option maxRecDepth 8192 in
private theorem h809 : Good row809 :=
  goodBoth h807 h808 262 0 262 512 4 516 (by decide)

private def row810 := state 782 0 [(~~~(primaryWord 8))] 5
set_option maxRecDepth 8192 in
private theorem h810 : Good row810 :=
  goodCut h809 774 0 [(4,12)] (by decide)

private def row811 := state 774 8 [(~~~(primaryWord 8))] 5
set_option maxRecDepth 8192 in
private theorem h811 : Good row811 :=
  goodCut h809 774 0 [(0,8)] (by decide)

private def row812 := state 798 0 [(~~~(primaryWord 8))] 7
set_option maxRecDepth 8192 in
private theorem h812 : Good row812 :=
  goodBoth h810 h811 782 0 782 16 8 24 (by decide)

private def row813 := state 830 0 [(~~~(primaryWord 8))] 8
set_option maxRecDepth 8192 in
private theorem h813 : Good row813 :=
  goodCut h812 798 0 [(16,48)] (by decide)

private def row814 := state 798 32 [(~~~(primaryWord 8))] 8
set_option maxRecDepth 8192 in
private theorem h814 : Good row814 :=
  goodCut h812 798 0 [(0,32)] (by decide)

private def row815 := state 894 0 [(~~~(primaryWord 8))] 10
set_option maxRecDepth 8192 in
private theorem h815 : Good row815 :=
  goodBoth h813 h814 830 0 830 64 32 96 (by decide)

private def row816 := state 894 1 [(~~~(primaryWord 8))] 11
set_option maxRecDepth 8192 in
private theorem h816 : Good row816 :=
  goodCut h815 894 0 [(0,1)] (by decide)

private def row817 := state 1023 0 [(~~~(primaryWord 8))] 13
set_option maxRecDepth 8192 in
private theorem h817 : Good row817 :=
  goodBoth h292 h816 895 0 895 128 1 129 (by decide)

private def row818 := state 1023 0 [(~~~(primaryWord 9))] 13
set_option maxRecDepth 8192 in
private theorem h818 : Good row818 :=
  goodCut h481 511 0 [(4,516)] (by decide)

private def row819 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (~~~((primaryWord 1 &&& primaryWord 8)))] 12
set_option maxRecDepth 8192 in
private theorem h819 : Good row819 :=
  goodCut h298 765 0 [(1,3), (2,258)] (by decide)

private def row820 := state 1023 0 [(primaryWord 3 &&& primaryWord 4), (~~~((primaryWord 3 &&& primaryWord 4)))] 12
set_option maxRecDepth 8192 in
private theorem h820 : Good row820 :=
  goodCut h599 1015 0 [(4,12)] (by decide)

private def row821 := state 637 0 [(~~~(primaryWord 0))] 8
set_option maxRecDepth 8192 in
private theorem h821 : Good row821 :=
  goodCut h192 636 0 [(64,65)] (by decide)

private def row822 := state 636 1 [(~~~(primaryWord 0))] 8
set_option maxRecDepth 8192 in
private theorem h822 : Good row822 :=
  goodCut h192 636 0 [(0,1)] (by decide)

private def row823 := state 765 0 [(~~~(primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h823 : Good row823 :=
  goodBoth h821 h822 637 0 637 128 1 129 (by decide)

private def row824 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (~~~(((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)))] 11
set_option maxRecDepth 8192 in
private theorem h824 : Good row824 :=
  goodCut h823 765 0 [(1,3)] (by decide)

private def row825 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h825 : Good row825 :=
  fastGoodSplit row825 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h600, checked h601, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h602, checked h603,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h604, checked h605, checked h590, checked h594, checked h796, checked h611,
  checked h616, checked h617, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625,
  checked h626, checked h627, checked h628, checked h629, checked h633, checked h637, checked h798, checked h642,
  checked h647, checked h649, checked h651, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h663, checked h667, checked h803, checked h672, checked h674,
  checked h675, checked h676, checked h677, checked h678, checked h679, checked h680, checked h681, checked h682,
  checked h683, checked h684, checked h688, checked h706, checked h805, checked h707, checked h712, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h719, checked h720, checked h724,
  checked h728, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h735, checked h736, checked h739, checked h741, checked h817, checked h742, checked h743, checked h744,
  checked h745, checked h746, checked h818, checked h747, checked h748, checked h749, checked h750, checked h753,
  checked h755, checked h819, checked h764, checked h772, checked h820, checked h776, checked h782, checked h824
  ] [
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963,
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 8783171, 8783171, 36529136963, 36529136963,
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963,
  36529136963, 36529136963, 8783171, 8783171, 1221, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963,
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 1221, 8783171, 8783171,
  1221, 1221, 36529136963, 36529136963, 36529136963, 8783171, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963,
  36529136963, 8783171, 10106053, 10106053, 1221, 1221, 36529136963, 36529136963, 36529136963, 36529136963, 8783171, 36529136963,
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 10106053, 1221, 1221, 36529136963, 8783171, 36529136963,
  36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 10106053, 8783171, 8783171, 1221, 1221,
  36529136963, 36529136963, 8783171, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 10106053, 8783171, 8783171, 1221,
  1221, 36529136963, 36529136963, 36529136963, 36529136963, 36529136963, 10106053, 10106053, 8783171, 8783171, 1221, 1221,
  36529136963, 36529136963, 36529136963, 8783171, 8783171, 1221, 36529136963, 10106053, 10106053, 8783171, 8783171, 1221,
  1221, 10106053, 2434, 2434, 8783171, 0, 0, 1221
  ] (by decide)

private def row826 := state 999 0 [(primaryWord 0 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h826 : Good row826 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row827 := state 1015 0 [(primaryWord 0 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h827 : Good row827 :=
  goodCut h826 999 0 [(32,48)] (by decide)

private def row828 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h828 : Good row828 :=
  goodCut h827 1015 0 [(36,44)] (by decide)

private def row829 := state 999 0 [(primaryWord 0 ||| primaryWord 5)] 9
set_option maxRecDepth 8192 in
private theorem h829 : Good row829 :=
  goodCut h595 903 32 [(64,96), (1,65)] (by decide)

private def row830 := state 967 32 [(primaryWord 0 ||| primaryWord 5)] 9
set_option maxRecDepth 8192 in
private theorem h830 : Good row830 :=
  goodCut h596 967 0 [(1,33)] (by decide)

private def row831 := state 1015 0 [(primaryWord 0 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h831 : Good row831 :=
  goodBoth h829 h830 999 0 999 16 32 48 (by decide)

private def row832 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h832 : Good row832 :=
  goodCut h831 1015 0 [(36,44)] (by decide)

private def row833 := state 999 0 [(primaryWord 1 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h833 : Good row833 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row834 := state 1015 0 [(primaryWord 1 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h834 : Good row834 :=
  goodCut h833 999 0 [(32,48)] (by decide)

private def row835 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h835 : Good row835 :=
  goodCut h834 1015 0 [(36,44)] (by decide)

private def row836 := state 999 0 [(primaryWord 1 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h836 : Good row836 :=
  goodBoth h596 h597 967 0 967 32 66 98 (by decide)

private def row837 := state 1015 0 [(primaryWord 1 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h837 : Good row837 :=
  goodCut h836 999 0 [(32,48)] (by decide)

private def row838 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h838 : Good row838 :=
  goodCut h837 1015 0 [(36,44)] (by decide)

private def row839 := state 999 0 [(primaryWord 2 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h839 : Good row839 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row840 := state 1015 0 [(primaryWord 2 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h840 : Good row840 :=
  goodCut h839 999 0 [(32,48)] (by decide)

private def row841 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h841 : Good row841 :=
  goodCut h840 1015 0 [(36,44)] (by decide)

private def row842 := state 999 0 [(primaryWord 2 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h842 : Good row842 :=
  goodBoth h596 h597 967 0 967 32 68 100 (by decide)

private def row843 := state 1015 0 [(primaryWord 2 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h843 : Good row843 :=
  goodCut h842 999 0 [(32,48)] (by decide)

private def row844 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h844 : Good row844 :=
  goodCut h843 1015 0 [(36,44)] (by decide)

private def row845 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h845 : Good row845 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row846 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h846 : Good row846 :=
  goodCut h330 507 512 [(2,6), (5,517)] (by decide)

private def row847 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h847 : Good row847 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row848 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h848 : Good row848 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row849 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h849 : Good row849 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row850 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h850 : Good row850 :=
  goodCut h330 507 512 [(8,12), (4,516)] (by decide)

private def row851 := state 1007 0 [(primaryWord 3 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h851 : Good row851 :=
  goodCut h598 999 0 [(36,44)] (by decide)

private def row852 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), (primaryWord 4 ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h852 : Good row852 :=
  goodCut h851 1007 0 [(72,88)] (by decide)

private def row853 := state 1015 0 [(primaryWord 4 &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h853 : Good row853 :=
  goodCut h598 999 0 [(32,48)] (by decide)

private def row854 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h854 : Good row854 :=
  goodCut h853 1015 0 [(36,44)] (by decide)

private def row855 := state 1015 0 [(primaryWord 4 ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h855 : Good row855 :=
  goodCut h598 999 0 [(32,48)] (by decide)

private def row856 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h856 : Good row856 :=
  goodCut h855 1015 0 [(36,44)] (by decide)

private def row857 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h857 : Good row857 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row858 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h858 : Good row858 :=
  goodCut h330 507 512 [(2,6), (20,532)] (by decide)

private def row859 := state 911 0 [] 8
set_option maxRecDepth 8192 in
private theorem h859 : Good row859 :=
  goodCut h595 903 0 [(4,12)] (by decide)

private def row860 := state 903 8 [] 8
set_option maxRecDepth 8192 in
private theorem h860 : Good row860 :=
  goodCut h595 903 0 [(0,8)] (by decide)

private def row861 := state 927 0 [] 10
set_option maxRecDepth 8192 in
private theorem h861 : Good row861 :=
  goodBoth h859 h860 911 0 911 16 8 24 (by decide)

private def row862 := state 991 0 [] 11
set_option maxRecDepth 8192 in
private theorem h862 : Good row862 :=
  goodCut h861 927 0 [(1,65)] (by decide)

private def row863 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), (primaryWord 3 ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h863 : Good row863 :=
  goodCut h862 991 0 [(72,104)] (by decide)

private def row864 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h864 : Good row864 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row865 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h865 : Good row865 :=
  goodCut h330 507 512 [(2,6), (36,548)] (by decide)

private def row866 := state 195 0 [(primaryWord 6 ||| primaryWord 7)] 2
set_option maxRecDepth 8192 in
private theorem h866 : Good row866 :=
  goodCut h152 1 2 [(1,3), (1,65)] (by decide)

private def row867 := state 193 2 [(primaryWord 6 ||| primaryWord 7)] 2
set_option maxRecDepth 8192 in
private theorem h867 : Good row867 :=
  goodCut h2 2 0 [(64,65), (1,65)] (by decide)

private def row868 := state 451 0 [(primaryWord 6 ||| primaryWord 7)] 4
set_option maxRecDepth 8192 in
private theorem h868 : Good row868 :=
  goodBoth h866 h867 195 0 195 256 2 258 (by decide)

private def row869 := state 455 0 [(primaryWord 6 ||| primaryWord 7)] 5
set_option maxRecDepth 8192 in
private theorem h869 : Good row869 :=
  goodCut h868 451 0 [(2,6)] (by decide)

private def row870 := state 451 4 [(primaryWord 6 ||| primaryWord 7)] 5
set_option maxRecDepth 8192 in
private theorem h870 : Good row870 :=
  goodCut h868 451 0 [(0,4)] (by decide)

private def row871 := state 967 0 [(primaryWord 6 ||| primaryWord 7)] 7
set_option maxRecDepth 8192 in
private theorem h871 : Good row871 :=
  goodBoth h869 h870 455 0 455 512 4 516 (by decide)

private def row872 := state 975 0 [(primaryWord 6 ||| primaryWord 7)] 8
set_option maxRecDepth 8192 in
private theorem h872 : Good row872 :=
  goodCut h871 967 0 [(4,12)] (by decide)

private def row873 := state 967 8 [(primaryWord 6 ||| primaryWord 7)] 8
set_option maxRecDepth 8192 in
private theorem h873 : Good row873 :=
  goodCut h871 967 0 [(0,8)] (by decide)

private def row874 := state 991 0 [(primaryWord 6 ||| primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h874 : Good row874 :=
  goodBoth h872 h873 975 0 975 16 8 24 (by decide)

private def row875 := state 903 16 [] 8
set_option maxRecDepth 8192 in
private theorem h875 : Good row875 :=
  goodCut h595 903 0 [(0,16)] (by decide)

private def row876 := state 911 16 [] 9
set_option maxRecDepth 8192 in
private theorem h876 : Good row876 :=
  goodCut h875 919 0 [(4,12)] (by decide)

private def row877 := state 911 80 [(primaryWord 6 ||| primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h877 : Good row877 :=
  goodCut h876 927 0 [(128,192)] (by decide)

private def row878 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h878 : Good row878 :=
  goodBoth h874 h877 991 0 991 32 72 104 (by decide)

private def row879 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h879 : Good row879 :=
  goodCut h671 1015 0 [(36,44)] (by decide)

private def row880 := state 999 0 [(primaryWord 5 ||| primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h880 : Good row880 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row881 := state 1015 0 [(primaryWord 5 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h881 : Good row881 :=
  goodCut h880 999 0 [(32,48)] (by decide)

private def row882 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h882 : Good row882 :=
  goodCut h881 1015 0 [(36,44)] (by decide)

private def row883 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h883 : Good row883 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row884 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h884 : Good row884 :=
  goodCut h330 507 512 [(2,6), (68,580)] (by decide)

private def row885 := state 1015 0 [(primaryWord 5 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h885 : Good row885 :=
  goodCut h76 887 0 [(1,129)] (by decide)

private def row886 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h886 : Good row886 :=
  goodCut h885 1015 0 [(36,44)] (by decide)

private def row887 := state 1015 0 [(primaryWord 5 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h887 : Good row887 :=
  goodCut h76 887 0 [(33,161)] (by decide)

private def row888 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h888 : Good row888 :=
  goodCut h887 1015 0 [(36,44)] (by decide)

private def row889 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h889 : Good row889 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row890 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h890 : Good row890 :=
  goodCut h330 507 512 [(2,6), (132,644)] (by decide)

private def row891 := state 999 0 [(primaryWord 5 &&& primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h891 : Good row891 :=
  goodBoth h596 h597 967 0 967 32 64 96 (by decide)

private def row892 := state 1015 0 [(primaryWord 5 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h892 : Good row892 :=
  goodCut h891 999 0 [(32,48)] (by decide)

private def row893 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h893 : Good row893 :=
  goodCut h892 1015 0 [(36,44)] (by decide)

private def row894 := state 999 0 [(primaryWord 5 ||| primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h894 : Good row894 :=
  goodBoth h596 h597 967 0 967 32 320 352 (by decide)

private def row895 := state 1015 0 [(primaryWord 5 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h895 : Good row895 :=
  goodCut h894 999 0 [(32,48)] (by decide)

private def row896 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h896 : Good row896 :=
  goodCut h895 1015 0 [(36,44)] (by decide)

private def row897 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h897 : Good row897 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row898 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 9) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h898 : Good row898 :=
  goodCut h330 507 512 [(2,6), (260,772)] (by decide)

private def row899 := state 499 4 [] 9
set_option maxRecDepth 8192 in
private theorem h899 : Good row899 :=
  goodCut h328 499 0 [(0,4)] (by decide)

private def row900 := state 1015 0 [(primaryWord 5 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h900 : Good row900 :=
  goodBoth h333 h899 503 0 503 512 4 516 (by decide)

private def row901 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h901 : Good row901 :=
  goodCut h900 1015 0 [(36,44)] (by decide)

private def row902 := state 249 0 [(primaryWord 3 ||| primaryWord 5)] 6
set_option maxRecDepth 8192 in
private theorem h902 : Good row902 :=
  goodCut h384 225 8 [(16,24), (8,24)] (by decide)

private def row903 := state 241 8 [(primaryWord 3 ||| primaryWord 5)] 6
set_option maxRecDepth 8192 in
private theorem h903 : Good row903 :=
  goodCut h385 241 0 [(32,40)] (by decide)

private def row904 := state 253 0 [(primaryWord 3 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h904 : Good row904 :=
  goodBoth h902 h903 249 0 249 4 8 12 (by decide)

private def row905 := state 765 0 [(primaryWord 3 ||| primaryWord 5)] 9
set_option maxRecDepth 8192 in
private theorem h905 : Good row905 :=
  goodCut h904 253 0 [(4,516)] (by decide)

private def row906 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 3 ||| primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h906 : Good row906 :=
  goodCut h905 765 0 [(1,3), (2,258)] (by decide)

private def row907 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 3 ||| primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h907 : Good row907 :=
  goodCut h905 765 0 [(1,3), (10,266)] (by decide)

private def row908 := state 765 0 [(primaryWord 3 ||| primaryWord 9)] 9
set_option maxRecDepth 8192 in
private theorem h908 : Good row908 :=
  goodCut h387 249 512 [(8,12), (4,516)] (by decide)

private def row909 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 3 ||| primaryWord 9))] 11
set_option maxRecDepth 8192 in
private theorem h909 : Good row909 :=
  goodCut h908 765 0 [(1,3), (2,258)] (by decide)

private def row910 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 3 ||| primaryWord 9))] 11
set_option maxRecDepth 8192 in
private theorem h910 : Good row910 :=
  goodCut h908 765 0 [(1,3), (10,266)] (by decide)

private def row911 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), (primaryWord 3 ||| primaryWord 9), ((primaryWord 3 ||| primaryWord 5) &&& (primaryWord 3 ||| primaryWord 9))] 11
set_option maxRecDepth 8192 in
private theorem h911 : Good row911 :=
  goodCut h334 503 8 [(528,536), (4,516)] (by decide)

private def row912 := state 249 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h912 : Good row912 :=
  goodCut h384 225 8 [(16,24), (8,24)] (by decide)

private def row913 := state 225 0 [(primaryWord 0 &&& primaryWord 5)] 4
set_option maxRecDepth 8192 in
private theorem h913 : Good row913 :=
  goodBoth h382 h383 193 0 193 32 64 96 (by decide)

private def row914 := state 241 0 [(primaryWord 0 &&& primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h914 : Good row914 :=
  goodCut h913 225 0 [(32,48)] (by decide)

private def row915 := state 241 8 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h915 : Good row915 :=
  goodCut h914 241 0 [(32,40)] (by decide)

private def row916 := state 253 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h916 : Good row916 :=
  goodBoth h912 h915 249 0 249 4 8 12 (by decide)

private def row917 := state 765 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h917 : Good row917 :=
  goodCut h916 253 0 [(4,516)] (by decide)

private def row918 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& (primaryWord 3 ||| primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h918 : Good row918 :=
  goodCut h917 765 0 [(1,3)] (by decide)

private def row919 := state 249 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h919 : Good row919 :=
  goodCut h384 225 8 [(17,25), (8,24)] (by decide)

private def row920 := state 96 0 [] 1
set_option maxRecDepth 8192 in
private theorem h920 : Good row920 :=
  goodOne row920 (by decide)

private def row921 := state 225 0 [(primaryWord 0 ||| primaryWord 5)] 3
set_option maxRecDepth 8192 in
private theorem h921 : Good row921 :=
  goodCut h920 96 0 [(160,161), (1,129)] (by decide)

private def row922 := state 0 192 [] 1
set_option maxRecDepth 8192 in
private theorem h922 : Good row922 :=
  goodOne row922 (by decide)

private def row923 := state 0 224 [] 2
set_option maxRecDepth 8192 in
private theorem h923 : Good row923 :=
  goodCut h922 192 0 [(0,32)] (by decide)

private def row924 := state 193 32 [(primaryWord 0 ||| primaryWord 5)] 3
set_option maxRecDepth 8192 in
private theorem h924 : Good row924 :=
  goodCut h923 224 1 [(64,65)] (by decide)

private def row925 := state 241 0 [(primaryWord 0 ||| primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h925 : Good row925 :=
  goodBoth h921 h924 225 0 225 16 32 48 (by decide)

private def row926 := state 241 8 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h926 : Good row926 :=
  goodCut h925 241 0 [(32,40)] (by decide)

private def row927 := state 253 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h927 : Good row927 :=
  goodBoth h919 h926 249 0 249 4 8 12 (by decide)

private def row928 := state 765 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h928 : Good row928 :=
  goodCut h927 253 0 [(4,516)] (by decide)

private def row929 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| (primaryWord 3 ||| primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h929 : Good row929 :=
  goodCut h928 765 0 [(1,3)] (by decide)

private def row930 := state 507 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h930 : Good row930 :=
  goodCut h387 249 0 [(1,3)] (by decide)

private def row931 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& (primaryWord 3 ||| primaryWord 9))] 10
set_option maxRecDepth 8192 in
private theorem h931 : Good row931 :=
  goodCut h930 507 512 [(2,6), (4,516)] (by decide)

private def row932 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| (primaryWord 3 ||| primaryWord 9))] 10
set_option maxRecDepth 8192 in
private theorem h932 : Good row932 :=
  goodCut h930 507 512 [(2,6), (5,517)] (by decide)

private def row933 := state 487 0 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h933 : Good row933 :=
  goodCut h473 483 0 [(2,6)] (by decide)

private def row934 := state 483 4 [(~~~(primaryWord 5))] 8
set_option maxRecDepth 8192 in
private theorem h934 : Good row934 :=
  goodCut h473 483 0 [(0,4)] (by decide)

private def row935 := state 999 0 [(~~~(primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h935 : Good row935 :=
  goodBoth h933 h934 487 0 487 512 4 516 (by decide)

private def row936 := state 1015 0 [(~~~(primaryWord 5))] 11
set_option maxRecDepth 8192 in
private theorem h936 : Good row936 :=
  goodCut h935 999 0 [(32,48)] (by decide)

private def row937 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), (~~~((primaryWord 3 ||| primaryWord 5)))] 12
set_option maxRecDepth 8192 in
private theorem h937 : Good row937 :=
  goodCut h936 1015 0 [(36,44)] (by decide)

private def row938 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), (~~~((primaryWord 3 ||| primaryWord 9)))] 12
set_option maxRecDepth 8192 in
private theorem h938 : Good row938 :=
  goodCut h330 507 512 [(2,6), (4,516)] (by decide)

private def row939 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h939 : Good row939 :=
  fastGoodSplit row939 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h828, checked h832, checked h845, checked h846,
  checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518,
  checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538,
  checked h835, checked h838, checked h847, checked h848, checked h539, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h586, checked h841, checked h844,
  checked h849, checked h850, checked h590, checked h594, checked h796, checked h617, checked h611, checked h616,
  checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h628,
  checked h629, checked h633, checked h637, checked h798, checked h642, checked h647, checked h649, checked h852,
  checked h652, checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659,
  checked h854, checked h856, checked h857, checked h858, checked h663, checked h667, checked h803, checked h863,
  checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680, checked h681,
  checked h682, checked h864, checked h865, checked h688, checked h706, checked h805, checked h707, checked h878,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882,
  checked h883, checked h884, checked h724, checked h728, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h733, checked h734, checked h886, checked h888, checked h889, checked h890, checked h739,
  checked h741, checked h817, checked h742, checked h743, checked h893, checked h896, checked h897, checked h898,
  checked h746, checked h818, checked h747, checked h748, checked h901, checked h753, checked h755, checked h819,
  checked h906, checked h907, checked h909, checked h910, checked h937, checked h911, checked h918, checked h929,
  checked h938, checked h931, checked h932, checked h824
  ] [
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 41953028325, 36533986627, 36533986627, 36533462339, 36533462339,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 36533986627, 36533986627, 36533462339, 36533462339, 9988325, 151911509550403, 151911509550403, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403,
  41953028325, 9988325, 36533986627, 36533986627, 36533462339, 36533462339, 9988325, 9988325, 151911509550403, 36533986627, 151911509550403, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 41953028325, 41953028325, 9988325, 9988325, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 36533986627, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 41953028325, 41953028325,
  36533986627, 36533986627, 36533462339, 36533462339, 9988325, 9988325, 151911509550403, 36533986627, 151911509550403, 151911509550403, 151911509550403, 151911509550403,
  151911509550403, 151911509550403, 151911509550403, 41953028325, 41953028325, 36533462339, 36533462339, 9988325, 9988325, 151911509550403, 151911509550403, 36533986627,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 41953028325, 41953028325, 36533986627, 36533986627, 36533462339, 36533462339, 9988325, 9988325,
  151911509550403, 151911509550403, 151911509550403, 151911509550403, 151911509550403, 41953028325, 41953028325, 36533986627, 36533986627, 36533462339, 36533462339, 9988325,
  9988325, 151911509550403, 151911509550403, 151911509550403, 36533986627, 36533986627, 36533462339, 36533462339, 9988325, 151911509550403, 41953028325, 41953028325,
  36533986627, 9988325, 9988325, 41953028325, 10107237, 10107237, 10107109, 10107109, 36533986627, 8783171, 2405, 2405,
  36533462339, 2277, 2277, 9988325
  ] (by decide)

private def row940 := state 1015 0 [(primaryWord 5 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h940 : Good row940 :=
  goodBoth h333 h899 503 0 503 512 36 548 (by decide)

private def row941 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h941 : Good row941 :=
  goodCut h940 1015 0 [(36,44)] (by decide)

private def row942 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h942 : Good row942 :=
  fastGoodSplit row942 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h828, checked h832, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h835, checked h838,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h841, checked h844, checked h590, checked h594, checked h796, checked h617,
  checked h611, checked h616, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625,
  checked h626, checked h939, checked h628, checked h629, checked h633, checked h637, checked h798, checked h642,
  checked h647, checked h649, checked h852, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h854, checked h856, checked h663, checked h667, checked h803,
  checked h863, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h688, checked h706, checked h805, checked h707, checked h878, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882, checked h724,
  checked h728, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h886, checked h888, checked h739, checked h741, checked h817, checked h742, checked h743, checked h893,
  checked h896, checked h746, checked h818, checked h747, checked h748, checked h901, checked h941, checked h753,
  checked h755, checked h819, checked h906, checked h907, checked h937, checked h918, checked h929, checked h824
  ] [
  36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339,
  36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 8783171, 8783171, 36533462339, 36533462339,
  36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339,
  36533462339, 36533462339, 8783171, 8783171, 2277, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339,
  36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 2277, 8783171, 8783171,
  2277, 2277, 36533462339, 8783171, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339,
  36533462339, 0, 10107109, 10107109, 2277, 2277, 36533462339, 36533462339, 36533462339, 36533462339, 8783171, 36533462339,
  36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 10107109, 8783171, 8783171, 2277, 2277, 36533462339,
  8783171, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 10107109, 2277, 2277,
  36533462339, 36533462339, 8783171, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 10107109, 8783171, 8783171, 2277,
  2277, 36533462339, 36533462339, 36533462339, 36533462339, 36533462339, 10107109, 10107109, 8783171, 8783171, 2277, 2277,
  36533462339, 36533462339, 36533462339, 8783171, 8783171, 2277, 36533462339, 10107109, 10107109, 8783171, 8783171, 2277,
  2277, 10107109, 2434, 2434, 8783171, 0, 0, 2277
  ] (by decide)

private def row943 := state 526 0 [(primaryWord 3 ||| primaryWord 9)] 2
set_option maxRecDepth 8192 in
private theorem h943 : Good row943 :=
  goodCut h0 4 2 [(4,6), (4,12)] (by decide)

private def row944 := state 524 2 [(primaryWord 3 ||| primaryWord 9)] 2
set_option maxRecDepth 8192 in
private theorem h944 : Good row944 :=
  goodCut h2 2 0 [(8,12), (4,12)] (by decide)

private def row945 := state 782 0 [(primaryWord 3 ||| primaryWord 9)] 4
set_option maxRecDepth 8192 in
private theorem h945 : Good row945 :=
  goodBoth h943 h944 526 0 526 256 2 258 (by decide)

private def row946 := state 783 0 [(primaryWord 3 ||| primaryWord 9)] 5
set_option maxRecDepth 8192 in
private theorem h946 : Good row946 :=
  goodCut h945 782 0 [(2,3)] (by decide)

private def row947 := state 782 1 [(primaryWord 3 ||| primaryWord 9)] 5
set_option maxRecDepth 8192 in
private theorem h947 : Good row947 :=
  goodCut h945 782 0 [(0,1)] (by decide)

private def row948 := state 911 0 [(primaryWord 3 ||| primaryWord 9)] 7
set_option maxRecDepth 8192 in
private theorem h948 : Good row948 :=
  goodBoth h946 h947 783 0 783 128 1 129 (by decide)

private def row949 := state 975 0 [(primaryWord 3 ||| primaryWord 9)] 8
set_option maxRecDepth 8192 in
private theorem h949 : Good row949 :=
  goodCut h948 911 0 [(1,65)] (by decide)

private def row950 := state 911 64 [(primaryWord 3 ||| primaryWord 9)] 8
set_option maxRecDepth 8192 in
private theorem h950 : Good row950 :=
  goodCut h948 911 0 [(0,64)] (by decide)

private def row951 := state 1007 0 [(primaryWord 3 ||| primaryWord 9)] 10
set_option maxRecDepth 8192 in
private theorem h951 : Good row951 :=
  goodBoth h949 h950 975 0 975 32 64 96 (by decide)

private def row952 := state 967 32 [] 9
set_option maxRecDepth 8192 in
private theorem h952 : Good row952 :=
  goodCut h596 967 0 [(0,32)] (by decide)

private def row953 := state 967 40 [(primaryWord 3 ||| primaryWord 9)] 10
set_option maxRecDepth 8192 in
private theorem h953 : Good row953 :=
  goodCut h952 999 0 [(512,520)] (by decide)

private def row954 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), (primaryWord 4 ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h954 : Good row954 :=
  goodBoth h951 h953 1007 0 1007 16 72 88 (by decide)

private def row955 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), (primaryWord 3 ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h955 : Good row955 :=
  goodCut h671 1015 0 [(528,536)] (by decide)

private def row956 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h956 : Good row956 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row957 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h957 : Good row957 :=
  goodCut h10 894 128 [(64,65), (1,129)] (by decide)

private def row958 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h958 : Good row958 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row959 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h959 : Good row959 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row960 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h960 : Good row960 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row961 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h961 : Good row961 :=
  goodCut h10 894 128 [(2,3), (5,133)] (by decide)

private def row962 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h962 : Good row962 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row963 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h963 : Good row963 :=
  goodCut h10 894 128 [(2,3), (9,137)] (by decide)

private def row964 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h964 : Good row964 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row965 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h965 : Good row965 :=
  goodCut h10 894 128 [(2,3), (17,145)] (by decide)

private def row966 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h966 : Good row966 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row967 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h967 : Good row967 :=
  goodCut h10 894 128 [(2,3), (33,161)] (by decide)

private def row968 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h968 : Good row968 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row969 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h969 : Good row969 :=
  goodCut h10 894 128 [(2,3), (257,385)] (by decide)

private def row970 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h970 : Good row970 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row971 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), ((primaryWord 6 ||| primaryWord 7) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h971 : Good row971 :=
  goodCut h10 894 128 [(2,3), (513,641)] (by decide)

private def row972 := state 894 0 [(primaryWord 1 &&& primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h972 : Good row972 :=
  goodCut h192 636 0 [(4,6), (2,258)] (by decide)

private def row973 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 6 ||| primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h973 : Good row973 :=
  goodCut h972 894 128 [(2,3), (1,129)] (by decide)

private def row974 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 6 ||| primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h974 : Good row974 :=
  goodCut h972 894 128 [(2,3), (1,129)] (by decide)

private def row975 := state 822 0 [] 6
set_option maxRecDepth 8192 in
private theorem h975 : Good row975 :=
  goodCut h4 774 0 [(32,48), (16,48)] (by decide)

private def row976 := state 830 0 [(primaryWord 3 ||| primaryWord 9)] 7
set_option maxRecDepth 8192 in
private theorem h976 : Good row976 :=
  goodCut h975 822 0 [(528,536)] (by decide)

private def row977 := state 798 32 [(primaryWord 3 ||| primaryWord 9)] 7
set_option maxRecDepth 8192 in
private theorem h977 : Good row977 :=
  goodCut h501 806 0 [(528,536), (8,24)] (by decide)

private def row978 := state 894 0 [(primaryWord 3 ||| primaryWord 9)] 9
set_option maxRecDepth 8192 in
private theorem h978 : Good row978 :=
  goodBoth h976 h977 830 0 830 64 32 96 (by decide)

private def row979 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7), ((primaryWord 3 ||| primaryWord 9) &&& (primaryWord 6 ||| primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h979 : Good row979 :=
  goodCut h978 894 128 [(2,3), (1,129)] (by decide)

private def row980 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7), ((primaryWord 3 ||| primaryWord 9) ||| (primaryWord 6 ||| primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h980 : Good row980 :=
  goodCut h978 894 128 [(2,3), (9,137)] (by decide)

private def row981 := state 263 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 2
set_option maxRecDepth 8192 in
private theorem h981 : Good row981 :=
  goodCut h2 2 1 [(2,3), (2,6)] (by decide)

private def row982 := state 259 4 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 2
set_option maxRecDepth 8192 in
private theorem h982 : Good row982 :=
  goodCut h0 4 0 [(2,3), (1,3)] (by decide)

private def row983 := state 775 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 4
set_option maxRecDepth 8192 in
private theorem h983 : Good row983 :=
  goodBoth h981 h982 263 0 263 512 4 516 (by decide)

private def row984 := state 783 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h984 : Good row984 :=
  goodCut h983 775 0 [(4,12)] (by decide)

private def row985 := state 775 8 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h985 : Good row985 :=
  goodCut h983 775 0 [(0,8)] (by decide)

private def row986 := state 799 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 7
set_option maxRecDepth 8192 in
private theorem h986 : Good row986 :=
  goodBoth h984 h985 783 0 783 16 8 24 (by decide)

private def row987 := state 831 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h987 : Good row987 :=
  goodCut h986 799 0 [(16,48)] (by decide)

private def row988 := state 959 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& primaryWord 7)] 9
set_option maxRecDepth 8192 in
private theorem h988 : Good row988 :=
  goodCut h987 831 0 [(1,129)] (by decide)

private def row989 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& (primaryWord 6 ||| primaryWord 7))] 10
set_option maxRecDepth 8192 in
private theorem h989 : Good row989 :=
  goodCut h988 959 0 [(160,224)] (by decide)

private def row990 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| (primaryWord 6 ||| primaryWord 7))] 10
set_option maxRecDepth 8192 in
private theorem h990 : Good row990 :=
  goodCut h972 894 128 [(1,129)] (by decide)

private def row991 := state 1023 0 [(primaryWord 6 ||| primaryWord 7), (~~~((primaryWord 6 ||| primaryWord 7)))] 12
set_option maxRecDepth 8192 in
private theorem h991 : Good row991 :=
  goodCut h10 894 128 [(2,3), (1,129)] (by decide)

private def row992 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h992 : Good row992 :=
  fastGoodSplit row992 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h845, checked h846, checked h956, checked h957,
  checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518,
  checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538,
  checked h847, checked h848, checked h958, checked h959, checked h539, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h586, checked h849, checked h850,
  checked h960, checked h961, checked h590, checked h594, checked h796, checked h627, checked h611, checked h616,
  checked h878, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h628, checked h629, checked h962, checked h963, checked h633, checked h637, checked h798, checked h642,
  checked h647, checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h857, checked h858, checked h964, checked h965, checked h663,
  checked h667, checked h803, checked h955, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h864, checked h865, checked h966, checked h967,
  checked h688, checked h706, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h883, checked h884, checked h724, checked h728, checked h806, checked h729,
  checked h730, checked h731, checked h732, checked h733, checked h734, checked h889, checked h890, checked h739,
  checked h741, checked h817, checked h742, checked h743, checked h897, checked h898, checked h968, checked h969,
  checked h746, checked h818, checked h747, checked h748, checked h970, checked h971, checked h753, checked h755,
  checked h819, checked h909, checked h910, checked h973, checked h974, checked h938, checked h979, checked h980,
  checked h931, checked h932, checked h991, checked h989, checked h990, checked h824
  ] [
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515,
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 41952778597, 36533736771, 36533736771, 36533986627, 36533986627,
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515,
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 36533736771, 36533736771, 36533986627, 36533986627, 9738597, 151910486664515, 151910486664515, 151910486664515,
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515,
  41952778597, 9738597, 36533736771, 36533736771, 36533986627, 36533986627, 9738597, 9738597, 151910486664515, 36533736771, 151910486664515, 151910486664515,
  36533986627, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 41952778597, 41952778597, 36533986627, 36533986627,
  9738597, 9738597, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 36533736771, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515,
  151910486664515, 41952778597, 41952778597, 36533736771, 36533736771, 36533986627, 36533986627, 9738597, 9738597, 151910486664515, 36533736771, 151910486664515,
  151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 41952778597, 41952778597, 36533736771, 36533736771, 36533986627, 36533986627,
  9738597, 9738597, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 41952778597, 41952778597, 36533736771, 36533736771,
  9738597, 9738597, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 151910486664515, 41952778597, 41952778597, 36533736771, 36533736771, 9738597,
  9738597, 151910486664515, 151910486664515, 151910486664515, 36533736771, 36533736771, 36533986627, 36533986627, 9738597, 151910486664515, 41952778597, 41952778597,
  36533986627, 36533986627, 9738597, 9738597, 41952778597, 10107176, 10107176, 10107237, 10107237, 36533736771, 8783171, 8783171,
  2344, 2344, 36533986627, 2405, 2405, 9738597
  ] (by decide)

private def row993 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h993 : Good row993 :=
  fastGoodSplit row993 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h845, checked h846, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h847, checked h848,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h849, checked h850, checked h590, checked h594, checked h796, checked h627,
  checked h611, checked h616, checked h939, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h628, checked h629, checked h633, checked h637, checked h798, checked h642,
  checked h647, checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h857, checked h858, checked h663, checked h667, checked h803,
  checked h955, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h864, checked h865, checked h688, checked h706, checked h805, checked h707,
  checked h992, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h883,
  checked h884, checked h724, checked h728, checked h806, checked h729, checked h730, checked h731, checked h732,
  checked h733, checked h734, checked h889, checked h890, checked h739, checked h741, checked h817, checked h742,
  checked h743, checked h897, checked h898, checked h746, checked h818, checked h747, checked h748, checked h753,
  checked h755, checked h819, checked h909, checked h910, checked h938, checked h931, checked h932, checked h824
  ] [
  36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627,
  36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 8783171, 8783171, 36533986627, 36533986627,
  36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627,
  36533986627, 36533986627, 8783171, 8783171, 2405, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627,
  36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 2405, 8783171, 8783171,
  2405, 2405, 36533986627, 8783171, 36533986627, 36533986627, 0, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627,
  36533986627, 36533986627, 10107237, 10107237, 2405, 2405, 36533986627, 36533986627, 36533986627, 36533986627, 8783171, 36533986627,
  36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 10107237, 8783171, 8783171, 2405, 2405, 36533986627,
  8783171, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 10107237, 8783171, 8783171,
  2405, 2405, 36533986627, 36533986627, 0, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 10107237, 8783171,
  8783171, 2405, 2405, 36533986627, 36533986627, 36533986627, 36533986627, 36533986627, 10107237, 10107237, 8783171, 8783171,
  2405, 2405, 36533986627, 36533986627, 36533986627, 8783171, 8783171, 2405, 36533986627, 10107237, 10107237, 2405,
  2405, 10107237, 2434, 2434, 8783171, 0, 0, 2405
  ] (by decide)

private def row994 := state 967 0 [(primaryWord 0 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h994 : Good row994 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row995 := state 903 64 [(primaryWord 0 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h995 : Good row995 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row996 := state 999 0 [(primaryWord 0 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h996 : Good row996 :=
  goodBoth h994 h995 967 0 967 32 64 96 (by decide)

private def row997 := state 1007 0 [(primaryWord 0 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h997 : Good row997 :=
  goodCut h996 999 0 [(4,12)] (by decide)

private def row998 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h998 : Good row998 :=
  goodCut h997 1007 0 [(72,88)] (by decide)

private def row999 := state 967 0 [(primaryWord 0 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h999 : Good row999 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1000 := state 903 64 [(primaryWord 0 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1000 : Good row1000 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1001 := state 999 0 [(primaryWord 0 ||| primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1001 : Good row1001 :=
  goodBoth h999 h1000 967 0 967 32 64 96 (by decide)

private def row1002 := state 1007 0 [(primaryWord 0 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1002 : Good row1002 :=
  goodCut h1001 999 0 [(4,12)] (by decide)

private def row1003 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h1003 : Good row1003 :=
  goodCut h1002 1007 0 [(72,88)] (by decide)

private def row1004 := state 967 0 [(primaryWord 1 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1004 : Good row1004 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1005 := state 903 64 [(primaryWord 1 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1005 : Good row1005 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row1006 := state 999 0 [(primaryWord 1 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1006 : Good row1006 :=
  goodBoth h1004 h1005 967 0 967 32 64 96 (by decide)

private def row1007 := state 1007 0 [(primaryWord 1 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1007 : Good row1007 :=
  goodCut h1006 999 0 [(4,12)] (by decide)

private def row1008 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h1008 : Good row1008 :=
  goodCut h1007 1007 0 [(72,88)] (by decide)

private def row1009 := state 927 0 [(primaryWord 1 ||| primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h1009 : Good row1009 :=
  goodBoth h859 h860 911 0 911 16 10 26 (by decide)

private def row1010 := state 959 0 [(primaryWord 1 ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h1010 : Good row1010 :=
  goodCut h1009 927 0 [(16,48)] (by decide)

private def row1011 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h1011 : Good row1011 :=
  goodCut h1010 959 0 [(17,81)] (by decide)

private def row1012 := state 967 0 [(primaryWord 2 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1012 : Good row1012 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1013 := state 903 64 [(primaryWord 2 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1013 : Good row1013 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row1014 := state 999 0 [(primaryWord 2 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1014 : Good row1014 :=
  goodBoth h1012 h1013 967 0 967 32 64 96 (by decide)

private def row1015 := state 1007 0 [(primaryWord 2 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1015 : Good row1015 :=
  goodCut h1014 999 0 [(4,12)] (by decide)

private def row1016 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h1016 : Good row1016 :=
  goodCut h1015 1007 0 [(72,88)] (by decide)

private def row1017 := state 967 0 [(primaryWord 2 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1017 : Good row1017 :=
  goodCut h595 903 0 [(5,69)] (by decide)

private def row1018 := state 903 64 [(primaryWord 2 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1018 : Good row1018 :=
  goodCut h595 903 0 [(4,68)] (by decide)

private def row1019 := state 999 0 [(primaryWord 2 ||| primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1019 : Good row1019 :=
  goodBoth h1017 h1018 967 0 967 32 64 96 (by decide)

private def row1020 := state 1007 0 [(primaryWord 2 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1020 : Good row1020 :=
  goodCut h1019 999 0 [(4,12)] (by decide)

private def row1021 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h1021 : Good row1021 :=
  goodCut h1020 1007 0 [(72,88)] (by decide)

private def row1022 := state 1007 0 [(primaryWord 3 &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1022 : Good row1022 :=
  goodCut h598 999 0 [(4,12)] (by decide)

private def row1023 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h1023 : Good row1023 :=
  goodCut h1022 1007 0 [(72,88)] (by decide)

private def row1024 := state 1007 0 [(primaryWord 3 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1024 : Good row1024 :=
  goodCut h598 999 0 [(68,76)] (by decide)

private def row1025 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h1025 : Good row1025 :=
  goodCut h1024 1007 0 [(72,88)] (by decide)

private def row1026 := state 959 0 [] 11
set_option maxRecDepth 8192 in
private theorem h1026 : Good row1026 :=
  goodCut h861 927 0 [(16,48)] (by decide)

private def row1027 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), (primaryWord 4 ||| primaryWord 6)] 12
set_option maxRecDepth 8192 in
private theorem h1027 : Good row1027 :=
  goodCut h1026 959 0 [(17,81)] (by decide)

private def row1028 := state 991 0 [(primaryWord 4 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1028 : Good row1028 :=
  goodCut h861 927 0 [(17,81)] (by decide)

private def row1029 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h1029 : Good row1029 :=
  goodCut h1028 991 0 [(16,48)] (by decide)

private def row1030 := state 975 0 [] 9
set_option maxRecDepth 8192 in
private theorem h1030 : Good row1030 :=
  goodCut h596 967 0 [(4,12)] (by decide)

private def row1031 := state 911 64 [] 9
set_option maxRecDepth 8192 in
private theorem h1031 : Good row1031 :=
  goodCut h597 967 0 [(4,12)] (by decide)

private def row1032 := state 1007 0 [(primaryWord 5 ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1032 : Good row1032 :=
  goodBoth h1030 h1031 975 0 975 32 64 96 (by decide)

private def row1033 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 5)] 12
set_option maxRecDepth 8192 in
private theorem h1033 : Good row1033 :=
  goodCut h1032 1007 0 [(72,88)] (by decide)

private def row1034 := state 967 0 [(primaryWord 6 &&& primaryWord 7)] 8
set_option maxRecDepth 8192 in
private theorem h1034 : Good row1034 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1035 := state 903 64 [(primaryWord 6 &&& primaryWord 7)] 8
set_option maxRecDepth 8192 in
private theorem h1035 : Good row1035 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row1036 := state 999 0 [(primaryWord 6 &&& primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h1036 : Good row1036 :=
  goodBoth h1034 h1035 967 0 967 32 64 96 (by decide)

private def row1037 := state 1007 0 [(primaryWord 6 &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h1037 : Good row1037 :=
  goodCut h1036 999 0 [(4,12)] (by decide)

private def row1038 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h1038 : Good row1038 :=
  goodCut h1037 1007 0 [(72,88)] (by decide)

private def row1039 := state 967 0 [(primaryWord 6 &&& primaryWord 8)] 8
set_option maxRecDepth 8192 in
private theorem h1039 : Good row1039 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1040 := state 903 64 [(primaryWord 6 &&& primaryWord 8)] 8
set_option maxRecDepth 8192 in
private theorem h1040 : Good row1040 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row1041 := state 999 0 [(primaryWord 6 &&& primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h1041 : Good row1041 :=
  goodBoth h1039 h1040 967 0 967 32 64 96 (by decide)

private def row1042 := state 1007 0 [(primaryWord 6 &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h1042 : Good row1042 :=
  goodCut h1041 999 0 [(4,12)] (by decide)

private def row1043 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h1043 : Good row1043 :=
  goodCut h1042 1007 0 [(72,88)] (by decide)

private def row1044 := state 967 0 [(primaryWord 6 ||| primaryWord 8)] 8
set_option maxRecDepth 8192 in
private theorem h1044 : Good row1044 :=
  goodCut h595 903 0 [(257,321)] (by decide)

private def row1045 := state 903 64 [(primaryWord 6 ||| primaryWord 8)] 8
set_option maxRecDepth 8192 in
private theorem h1045 : Good row1045 :=
  goodCut h595 903 0 [(256,320)] (by decide)

private def row1046 := state 999 0 [(primaryWord 6 ||| primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h1046 : Good row1046 :=
  goodBoth h1044 h1045 967 0 967 32 64 96 (by decide)

private def row1047 := state 1007 0 [(primaryWord 6 ||| primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h1047 : Good row1047 :=
  goodCut h1046 999 0 [(4,12)] (by decide)

private def row1048 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h1048 : Good row1048 :=
  goodCut h1047 1007 0 [(72,88)] (by decide)

private def row1049 := state 1007 0 [(primaryWord 6 &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h1049 : Good row1049 :=
  goodCut h339 495 0 [(4,516)] (by decide)

private def row1050 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h1050 : Good row1050 :=
  goodCut h1049 1007 0 [(72,88)] (by decide)

private def row1051 := state 1007 0 [(primaryWord 6 ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h1051 : Good row1051 :=
  goodCut h339 495 0 [(68,580)] (by decide)

private def row1052 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h1052 : Good row1052 :=
  goodCut h1051 1007 0 [(72,88)] (by decide)

private def row1053 := state 636 0 [(primaryWord 4 ||| primaryWord 6)] 6
set_option maxRecDepth 8192 in
private theorem h1053 : Good row1053 :=
  goodCut h189 540 64 [(16,48), (32,96)] (by decide)

private def row1054 := state 572 64 [(primaryWord 4 ||| primaryWord 6)] 6
set_option maxRecDepth 8192 in
private theorem h1054 : Good row1054 :=
  goodCut h190 572 0 [(16,80)] (by decide)

private def row1055 := state 637 0 [(primaryWord 4 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1055 : Good row1055 :=
  goodBoth h1053 h1054 636 0 636 1 64 65 (by decide)

private def row1056 := state 765 0 [(primaryWord 4 ||| primaryWord 6)] 9
set_option maxRecDepth 8192 in
private theorem h1056 : Good row1056 :=
  goodCut h1055 637 0 [(1,129)] (by decide)

private def row1057 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 4 ||| primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h1057 : Good row1057 :=
  goodCut h1056 765 0 [(1,3), (2,258)] (by decide)

private def row1058 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 4 ||| primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h1058 : Good row1058 :=
  goodCut h1056 765 0 [(1,3), (18,274)] (by decide)

private def row1059 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), (primaryWord 6 ||| primaryWord 7), ((primaryWord 4 ||| primaryWord 6) &&& (primaryWord 6 ||| primaryWord 7))] 11
set_option maxRecDepth 8192 in
private theorem h1059 : Good row1059 :=
  goodCut h89 831 64 [(160,224), (1,129)] (by decide)

private def row1060 := state 125 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h1060 : Good row1060 :=
  goodCut h115 60 0 [(64,65), (17,81)] (by decide)

private def row1061 := state 65 0 [] 1
set_option maxRecDepth 8192 in
private theorem h1061 : Good row1061 :=
  goodOne row1061 (by decide)

private def row1062 := state 113 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 3
set_option maxRecDepth 8192 in
private theorem h1062 : Good row1062 :=
  goodCut h1061 65 16 [(32,48), (16,48)] (by decide)

private def row1063 := state 0 48 [] 1
set_option maxRecDepth 8192 in
private theorem h1063 : Good row1063 :=
  goodOne row1063 (by decide)

private def row1064 := state 0 49 [] 2
set_option maxRecDepth 8192 in
private theorem h1064 : Good row1064 :=
  goodCut h1063 48 0 [(0,1)] (by decide)

private def row1065 := state 97 16 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 3
set_option maxRecDepth 8192 in
private theorem h1065 : Good row1065 :=
  goodCut h1064 49 64 [(32,96)] (by decide)

private def row1066 := state 121 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 5
set_option maxRecDepth 8192 in
private theorem h1066 : Good row1066 :=
  goodBoth h1062 h1065 113 0 113 8 16 24 (by decide)

private def row1067 := state 121 4 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 6
set_option maxRecDepth 8192 in
private theorem h1067 : Good row1067 :=
  goodCut h1066 121 0 [(0,4)] (by decide)

private def row1068 := state 637 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h1068 : Good row1068 :=
  goodBoth h1060 h1067 125 0 125 512 4 516 (by decide)

private def row1069 := state 765 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h1069 : Good row1069 :=
  goodCut h1068 637 0 [(1,129)] (by decide)

private def row1070 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) &&& (primaryWord 4 ||| primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h1070 : Good row1070 :=
  goodCut h1069 765 0 [(1,3)] (by decide)

private def row1071 := state 637 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h1071 : Good row1071 :=
  goodBoth h1053 h1054 636 0 636 1 64 65 (by decide)

private def row1072 := state 765 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h1072 : Good row1072 :=
  goodCut h1071 637 0 [(1,129)] (by decide)

private def row1073 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0) ||| (primaryWord 4 ||| primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h1073 : Good row1073 :=
  goodCut h1072 765 0 [(1,3)] (by decide)

private def row1074 := state 967 0 [(~~~(primaryWord 6))] 8
set_option maxRecDepth 8192 in
private theorem h1074 : Good row1074 :=
  goodCut h595 903 0 [(1,65)] (by decide)

private def row1075 := state 903 64 [(~~~(primaryWord 6))] 8
set_option maxRecDepth 8192 in
private theorem h1075 : Good row1075 :=
  goodCut h595 903 0 [(0,64)] (by decide)

private def row1076 := state 999 0 [(~~~(primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h1076 : Good row1076 :=
  goodBoth h1074 h1075 967 0 967 32 64 96 (by decide)

private def row1077 := state 1007 0 [(~~~(primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h1077 : Good row1077 :=
  goodCut h1076 999 0 [(4,12)] (by decide)

private def row1078 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), (~~~((primaryWord 4 ||| primaryWord 6)))] 12
set_option maxRecDepth 8192 in
private theorem h1078 : Good row1078 :=
  goodCut h1077 1007 0 [(72,88)] (by decide)

private def row1079 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1079 : Good row1079 :=
  fastGoodSplit row1079 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h998, checked h1003, checked h956, checked h957,
  checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518,
  checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538,
  checked h1008, checked h1011, checked h958, checked h959, checked h539, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h586, checked h1016, checked h1021,
  checked h960, checked h961, checked h590, checked h594, checked h796, checked h651, checked h611, checked h616,
  checked h852, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h954, checked h628, checked h629, checked h1023, checked h1025, checked h962, checked h963, checked h633,
  checked h637, checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h658, checked h659, checked h964, checked h965, checked h663,
  checked h667, checked h803, checked h1027, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h1029, checked h1033, checked h966, checked h967,
  checked h688, checked h706, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h724, checked h728, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h733, checked h734, checked h1038, checked h739, checked h741, checked h817, checked h742,
  checked h743, checked h1043, checked h1048, checked h968, checked h969, checked h746, checked h818, checked h747,
  checked h748, checked h1050, checked h1052, checked h970, checked h971, checked h753, checked h755, checked h819,
  checked h1057, checked h1058, checked h973, checked h974, checked h1078, checked h1059, checked h1070, checked h1073,
  checked h991, checked h989, checked h990, checked h824
  ] [
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 41952778502, 36533736771, 36533736771, 36533597507, 36533597507,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 36533736771, 36533736771, 36533597507, 36533597507, 9738502, 151910486275395, 151910486275395, 151910486275395,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395,
  41952778502, 9738502, 36533736771, 36533736771, 36533597507, 36533597507, 9738502, 9738502, 151910486275395, 36533736771, 151910486275395, 151910486275395,
  36533736771, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 36533736771, 41952778502, 41952778502, 36533736771,
  36533736771, 36533597507, 36533597507, 9738502, 9738502, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395,
  151910486275395, 151910486275395, 151910486275395, 41952778502, 41952778502, 36533597507, 36533597507, 9738502, 9738502, 151910486275395, 36533736771, 151910486275395,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 41952778502, 41952778502, 36533736771, 36533736771, 36533597507, 36533597507,
  9738502, 9738502, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 41952778502, 41952778502, 9738502, 9738502,
  151910486275395, 151910486275395, 151910486275395, 151910486275395, 151910486275395, 41952778502, 41952778502, 36533736771, 9738502, 9738502, 151910486275395, 151910486275395,
  151910486275395, 36533736771, 36533736771, 36533597507, 36533597507, 9738502, 151910486275395, 41952778502, 41952778502, 36533736771, 36533736771, 36533597507,
  36533597507, 9738502, 9738502, 41952778502, 10107176, 10107176, 10107142, 10107142, 36533736771, 8783171, 2344, 2344,
  36533597507, 2310, 2310, 9738502
  ] (by decide)

private def row1080 := state 959 0 [(primaryWord 4 ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h1080 : Good row1080 :=
  goodBoth h88 h524 831 0 831 128 17 145 (by decide)

private def row1081 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h1081 : Good row1081 :=
  goodCut h1080 959 0 [(17,81)] (by decide)

private def row1082 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1082 : Good row1082 :=
  fastGoodSplit row1082 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h998, checked h1003, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h1008, checked h1011,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h1016, checked h1021, checked h590, checked h594, checked h796, checked h651,
  checked h611, checked h616, checked h852, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h954, checked h628, checked h629, checked h1023, checked h1025, checked h633,
  checked h637, checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h658, checked h659, checked h663, checked h667, checked h803,
  checked h1027, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h1029, checked h1033, checked h688, checked h706, checked h805, checked h707,
  checked h1079, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h724,
  checked h728, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h1038, checked h1081, checked h739, checked h741, checked h817, checked h742, checked h743, checked h1043,
  checked h1048, checked h746, checked h818, checked h747, checked h748, checked h1050, checked h1052, checked h753,
  checked h755, checked h819, checked h1057, checked h1058, checked h1078, checked h1070, checked h1073, checked h824
  ] [
  36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507,
  36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 8783171, 8783171, 36533597507, 36533597507,
  36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507,
  36533597507, 36533597507, 8783171, 8783171, 2310, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507,
  36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 2310, 8783171, 8783171,
  2310, 2310, 36533597507, 8783171, 36533597507, 36533597507, 8783171, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507,
  36533597507, 36533597507, 8783171, 10107142, 10107142, 8783171, 8783171, 2310, 2310, 36533597507, 36533597507, 36533597507,
  36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 10107142, 2310, 2310, 36533597507,
  8783171, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 10107142, 8783171, 8783171,
  2310, 2310, 36533597507, 36533597507, 0, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 10107142, 2310,
  2310, 36533597507, 36533597507, 36533597507, 36533597507, 36533597507, 10107142, 10107142, 8783171, 8783171, 2310, 2310,
  36533597507, 36533597507, 36533597507, 8783171, 8783171, 2310, 36533597507, 10107142, 10107142, 8783171, 8783171, 2310,
  2310, 10107142, 2434, 2434, 8783171, 0, 0, 2310
  ] (by decide)

private def row1083 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h1083 : Good row1083 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1084 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 0)] 12
set_option maxRecDepth 8192 in
private theorem h1084 : Good row1084 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1085 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h1085 : Good row1085 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1086 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 1)] 12
set_option maxRecDepth 8192 in
private theorem h1086 : Good row1086 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1087 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h1087 : Good row1087 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1088 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 12
set_option maxRecDepth 8192 in
private theorem h1088 : Good row1088 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1089 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h1089 : Good row1089 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1090 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 3)] 12
set_option maxRecDepth 8192 in
private theorem h1090 : Good row1090 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1091 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h1091 : Good row1091 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1092 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 4)] 12
set_option maxRecDepth 8192 in
private theorem h1092 : Good row1092 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1093 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h1093 : Good row1093 :=
  goodCut h1026 959 0 [(160,224)] (by decide)

private def row1094 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h1094 : Good row1094 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1095 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 7)] 12
set_option maxRecDepth 8192 in
private theorem h1095 : Good row1095 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1096 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h1096 : Good row1096 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1097 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 8)] 12
set_option maxRecDepth 8192 in
private theorem h1097 : Good row1097 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1098 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h1098 : Good row1098 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1099 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 9)] 12
set_option maxRecDepth 8192 in
private theorem h1099 : Good row1099 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1100 := state 124 0 [(primaryWord 5 &&& primaryWord 6)] 5
set_option maxRecDepth 8192 in
private theorem h1100 : Good row1100 :=
  goodCut h115 60 0 [(32,96)] (by decide)

private def row1101 := state 60 64 [(primaryWord 5 &&& primaryWord 6)] 5
set_option maxRecDepth 8192 in
private theorem h1101 : Good row1101 :=
  goodCut h115 60 0 [(0,64)] (by decide)

private def row1102 := state 125 0 [(primaryWord 5 &&& primaryWord 6)] 7
set_option maxRecDepth 8192 in
private theorem h1102 : Good row1102 :=
  goodBoth h1100 h1101 124 0 124 1 64 65 (by decide)

private def row1103 := state 637 0 [(primaryWord 5 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1103 : Good row1103 :=
  goodCut h1102 125 0 [(4,516)] (by decide)

private def row1104 := state 765 0 [(primaryWord 5 &&& primaryWord 6)] 9
set_option maxRecDepth 8192 in
private theorem h1104 : Good row1104 :=
  goodCut h1103 637 0 [(1,129)] (by decide)

private def row1105 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) &&& (primaryWord 5 &&& primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h1105 : Good row1105 :=
  goodCut h1104 765 0 [(1,3), (2,258)] (by decide)

private def row1106 := state 542 0 [] 5
set_option maxRecDepth 8192 in
private theorem h1106 : Good row1106 :=
  goodCut h189 540 0 [(4,6)] (by decide)

private def row1107 := state 540 2 [] 5
set_option maxRecDepth 8192 in
private theorem h1107 : Good row1107 :=
  goodCut h189 540 0 [(0,2)] (by decide)

private def row1108 := state 543 0 [] 7
set_option maxRecDepth 8192 in
private theorem h1108 : Good row1108 :=
  goodBoth h1106 h1107 542 0 542 1 2 3 (by decide)

private def row1109 := state 671 0 [] 8
set_option maxRecDepth 8192 in
private theorem h1109 : Good row1109 :=
  goodCut h1108 543 0 [(1,129)] (by decide)

private def row1110 := state 735 0 [] 9
set_option maxRecDepth 8192 in
private theorem h1110 : Good row1110 :=
  goodCut h1109 671 0 [(1,65)] (by decide)

private def row1111 := state 991 0 [(primaryWord 1 &&& primaryWord 8)] 10
set_option maxRecDepth 8192 in
private theorem h1111 : Good row1111 :=
  goodCut h1110 735 0 [(2,258)] (by decide)

private def row1112 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| (primaryWord 5 &&& primaryWord 6))] 11
set_option maxRecDepth 8192 in
private theorem h1112 : Good row1112 :=
  goodCut h1111 991 0 [(16,48)] (by decide)

private def row1113 := state 125 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 0)] 7
set_option maxRecDepth 8192 in
private theorem h1113 : Good row1113 :=
  goodBoth h1100 h1101 124 0 124 1 64 65 (by decide)

private def row1114 := state 637 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h1114 : Good row1114 :=
  goodCut h1113 125 0 [(4,516)] (by decide)

private def row1115 := state 765 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h1115 : Good row1115 :=
  goodCut h1114 637 0 [(1,129)] (by decide)

private def row1116 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), ((primaryWord 5 &&& primaryWord 6) &&& ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h1116 : Good row1116 :=
  goodCut h1115 765 0 [(1,3)] (by decide)

private def row1117 := state 927 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 8
set_option maxRecDepth 8192 in
private theorem h1117 : Good row1117 :=
  goodCut h986 799 0 [(1,129)] (by decide)

private def row1118 := state 991 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 9
set_option maxRecDepth 8192 in
private theorem h1118 : Good row1118 :=
  goodCut h1117 927 0 [(1,65)] (by decide)

private def row1119 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0), ((primaryWord 5 &&& primaryWord 6) ||| ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0))] 10
set_option maxRecDepth 8192 in
private theorem h1119 : Good row1119 :=
  goodCut h1118 991 0 [(16,48)] (by decide)

private def row1120 := state 1023 0 [(primaryWord 5 &&& primaryWord 6), (~~~((primaryWord 5 &&& primaryWord 6)))] 12
set_option maxRecDepth 8192 in
private theorem h1120 : Good row1120 :=
  goodCut h862 991 0 [(16,48)] (by decide)

private def row1121 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1121 : Good row1121 :=
  fastGoodSplit row1121 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1083, checked h1084, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h1085, checked h1086,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h1087, checked h1088, checked h590, checked h594, checked h796, checked h672,
  checked h611, checked h616, checked h863, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h955, checked h628, checked h629, checked h1089, checked h1090, checked h633,
  checked h637, checked h798, checked h642, checked h647, checked h649, checked h1027, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h1091, checked h1092,
  checked h663, checked h667, checked h803, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h688, checked h706, checked h805, checked h707,
  checked h1093, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h724,
  checked h728, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h1094, checked h1095, checked h739, checked h741, checked h817, checked h742, checked h743, checked h1096,
  checked h1097, checked h746, checked h818, checked h747, checked h748, checked h1098, checked h1099, checked h753,
  checked h755, checked h819, checked h1105, checked h1112, checked h1120, checked h1116, checked h1119, checked h824
  ] [
  36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299,
  36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 8783171, 8783171, 36529407299, 36529407299,
  36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299,
  36529407299, 36529407299, 8783171, 8783171, 1287, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299,
  36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 1287, 8783171, 8783171,
  1287, 1287, 36529407299, 8783171, 36529407299, 36529407299, 8783171, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299,
  36529407299, 36529407299, 8783171, 10106119, 10106119, 8783171, 8783171, 1287, 1287, 36529407299, 36529407299, 36529407299,
  36529407299, 8783171, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 10106119, 8783171, 8783171,
  1287, 1287, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 10106119,
  1287, 1287, 36529407299, 36529407299, 8783171, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 10106119, 1287,
  1287, 36529407299, 36529407299, 36529407299, 36529407299, 36529407299, 10106119, 10106119, 8783171, 8783171, 1287, 1287,
  36529407299, 36529407299, 36529407299, 8783171, 8783171, 1287, 36529407299, 10106119, 10106119, 8783171, 8783171, 1287,
  1287, 10106119, 2434, 2434, 8783171, 0, 0, 1287
  ] (by decide)

private def row1122 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1122 : Good row1122 :=
  fastGoodSplit row1122 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h956, checked h957, checked h786, checked h485,
  checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526,
  checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h958, checked h959,
  checked h539, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h586, checked h960, checked h961, checked h590, checked h594, checked h796, checked h712,
  checked h611, checked h616, checked h878, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h992, checked h628, checked h629, checked h962, checked h963, checked h633,
  checked h637, checked h798, checked h642, checked h647, checked h649, checked h1079, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h964, checked h965,
  checked h663, checked h667, checked h803, checked h1093, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h681, checked h682, checked h966, checked h967, checked h688,
  checked h706, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h717,
  checked h718, checked h724, checked h728, checked h806, checked h729, checked h730, checked h731, checked h732,
  checked h733, checked h734, checked h739, checked h741, checked h817, checked h742, checked h743, checked h968,
  checked h969, checked h746, checked h818, checked h747, checked h748, checked h970, checked h971, checked h753,
  checked h755, checked h819, checked h973, checked h974, checked h991, checked h989, checked h990, checked h824
  ] [
  36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771,
  36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176, 8783171, 8783171, 36533736771, 36533736771,
  36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771,
  36533736771, 36533736771, 8783171, 8783171, 2344, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771,
  36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176, 2344, 8783171, 8783171,
  2344, 2344, 36533736771, 8783171, 36533736771, 36533736771, 8783171, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771,
  36533736771, 36533736771, 0, 10107176, 10107176, 8783171, 8783171, 2344, 2344, 36533736771, 36533736771, 36533736771,
  36533736771, 0, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176, 10107176, 8783171, 8783171,
  2344, 2344, 36533736771, 8783171, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176,
  10107176, 8783171, 8783171, 2344, 2344, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176,
  10107176, 2344, 2344, 36533736771, 36533736771, 36533736771, 36533736771, 36533736771, 10107176, 10107176, 2344, 2344,
  36533736771, 36533736771, 36533736771, 8783171, 8783171, 2344, 36533736771, 10107176, 10107176, 8783171, 8783171, 2344,
  2344, 10107176, 2434, 2434, 8783171, 0, 0, 2344
  ] (by decide)

private def row1123 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 0)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1123 : Good row1123 :=
  fastGoodSplit row1123 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h786, checked h485, checked h487, checked h495,
  checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528, checked h529,
  checked h532, checked h534, checked h535, checked h538, checked h539, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h586, checked h590, checked h594,
  checked h796, checked h825, checked h611, checked h616, checked h942, checked h619, checked h621, checked h622,
  checked h623, checked h624, checked h625, checked h626, checked h993, checked h628, checked h629, checked h633,
  checked h637, checked h798, checked h642, checked h647, checked h649, checked h1082, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h663, checked h667,
  checked h803, checked h1121, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679,
  checked h680, checked h681, checked h682, checked h688, checked h706, checked h805, checked h707, checked h1122,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h724, checked h728,
  checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h739,
  checked h741, checked h817, checked h742, checked h743, checked h746, checked h818, checked h747, checked h748,
  checked h753, checked h755, checked h819, checked h824
  ] [
  8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171,
  8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 2434, 8783171, 8783171, 8783171, 8783171,
  8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171,
  0, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171,
  8783171, 8783171, 8783171, 8783171, 2434, 0, 0, 0, 8783171, 0, 8783171, 8783171,
  0, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171, 0, 2434, 2434, 0,
  0, 8783171, 8783171, 8783171, 8783171, 0, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171,
  2434, 2434, 0, 0, 8783171, 0, 8783171, 8783171, 8783171, 8783171, 8783171, 8783171,
  8783171, 2434, 2434, 0, 0, 8783171, 8783171, 0, 8783171, 8783171, 8783171, 8783171,
  2434, 2434, 0, 0, 8783171, 8783171, 8783171, 8783171, 8783171, 2434, 2434, 0,
  0, 8783171, 8783171, 8783171, 0, 8783171, 2434, 2434, 0, 0, 2434, 0
  ] (by decide)

private def row1124 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 0)] 11
set_option maxRecDepth 8192 in
private theorem h1124 : Good row1124 :=
  goodCut h589 765 0 [(1,3)] (by decide)

private def row1125 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 0)] 11
set_option maxRecDepth 8192 in
private theorem h1125 : Good row1125 :=
  goodCut h593 765 0 [(1,3)] (by decide)

private def row1126 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 1)] 11
set_option maxRecDepth 8192 in
private theorem h1126 : Good row1126 :=
  goodCut h298 765 0 [(1,3)] (by decide)

private def row1127 := state 524 0 [(primaryWord 2 &&& primaryWord 3)] 2
set_option maxRecDepth 8192 in
private theorem h1127 : Good row1127 :=
  goodCut h0 4 512 [(4,12), (4,516)] (by decide)

private def row1128 := state 516 8 [(primaryWord 2 &&& primaryWord 3)] 2
set_option maxRecDepth 8192 in
private theorem h1128 : Good row1128 :=
  goodCut h113 8 0 [(512,516), (4,516)] (by decide)

private def row1129 := state 540 0 [(primaryWord 2 &&& primaryWord 3)] 4
set_option maxRecDepth 8192 in
private theorem h1129 : Good row1129 :=
  goodBoth h1127 h1128 524 0 524 16 8 24 (by decide)

private def row1130 := state 572 0 [(primaryWord 2 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h1130 : Good row1130 :=
  goodCut h1129 540 0 [(16,48)] (by decide)

private def row1131 := state 540 32 [(primaryWord 2 &&& primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h1131 : Good row1131 :=
  goodCut h1129 540 0 [(0,32)] (by decide)

private def row1132 := state 636 0 [(primaryWord 2 &&& primaryWord 3)] 7
set_option maxRecDepth 8192 in
private theorem h1132 : Good row1132 :=
  goodBoth h1130 h1131 572 0 572 64 32 96 (by decide)

private def row1133 := state 637 0 [(primaryWord 2 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h1133 : Good row1133 :=
  goodCut h1132 636 0 [(64,65)] (by decide)

private def row1134 := state 636 1 [(primaryWord 2 &&& primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h1134 : Good row1134 :=
  goodCut h1132 636 0 [(0,1)] (by decide)

private def row1135 := state 765 0 [(primaryWord 2 &&& primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h1135 : Good row1135 :=
  goodBoth h1133 h1134 637 0 637 128 1 129 (by decide)

private def row1136 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h1136 : Good row1136 :=
  goodCut h1135 765 0 [(1,3)] (by decide)

private def row1137 := state 524 0 [(primaryWord 2 ||| primaryWord 3)] 2
set_option maxRecDepth 8192 in
private theorem h1137 : Good row1137 :=
  goodCut h0 4 8 [(4,12), (4,516)] (by decide)

private def row1138 := state 516 8 [(primaryWord 2 ||| primaryWord 3)] 2
set_option maxRecDepth 8192 in
private theorem h1138 : Good row1138 :=
  goodCut h113 8 4 [(512,516), (4,516)] (by decide)

private def row1139 := state 540 0 [(primaryWord 2 ||| primaryWord 3)] 4
set_option maxRecDepth 8192 in
private theorem h1139 : Good row1139 :=
  goodBoth h1137 h1138 524 0 524 16 8 24 (by decide)

private def row1140 := state 572 0 [(primaryWord 2 ||| primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h1140 : Good row1140 :=
  goodCut h1139 540 0 [(16,48)] (by decide)

private def row1141 := state 540 32 [(primaryWord 2 ||| primaryWord 3)] 5
set_option maxRecDepth 8192 in
private theorem h1141 : Good row1141 :=
  goodCut h1139 540 0 [(0,32)] (by decide)

private def row1142 := state 636 0 [(primaryWord 2 ||| primaryWord 3)] 7
set_option maxRecDepth 8192 in
private theorem h1142 : Good row1142 :=
  goodBoth h1140 h1141 572 0 572 64 32 96 (by decide)

private def row1143 := state 637 0 [(primaryWord 2 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h1143 : Good row1143 :=
  goodCut h1142 636 0 [(64,65)] (by decide)

private def row1144 := state 636 1 [(primaryWord 2 ||| primaryWord 3)] 8
set_option maxRecDepth 8192 in
private theorem h1144 : Good row1144 :=
  goodCut h1142 636 0 [(0,1)] (by decide)

private def row1145 := state 765 0 [(primaryWord 2 ||| primaryWord 3)] 10
set_option maxRecDepth 8192 in
private theorem h1145 : Good row1145 :=
  goodBoth h1143 h1144 637 0 637 128 1 129 (by decide)

private def row1146 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 3)] 11
set_option maxRecDepth 8192 in
private theorem h1146 : Good row1146 :=
  goodCut h1145 765 0 [(1,3)] (by decide)

private def row1147 := state 540 0 [(primaryWord 2 &&& primaryWord 4)] 4
set_option maxRecDepth 8192 in
private theorem h1147 : Good row1147 :=
  goodBoth h187 h188 524 0 524 16 8 24 (by decide)

private def row1148 := state 572 0 [(primaryWord 2 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1148 : Good row1148 :=
  goodCut h1147 540 0 [(16,48)] (by decide)

private def row1149 := state 524 32 [] 3
set_option maxRecDepth 8192 in
private theorem h1149 : Good row1149 :=
  goodCut h92 32 0 [(8,12), (4,12), (4,516)] (by decide)

private def row1150 := state 0 40 [] 1
set_option maxRecDepth 8192 in
private theorem h1150 : Good row1150 :=
  goodOne row1150 (by decide)

private def row1151 := state 516 40 [] 3
set_option maxRecDepth 8192 in
private theorem h1151 : Good row1151 :=
  goodCut h1150 40 0 [(512,516), (4,516)] (by decide)

private def row1152 := state 540 32 [(primaryWord 2 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1152 : Good row1152 :=
  goodBoth h1149 h1151 556 0 556 16 8 24 (by decide)

private def row1153 := state 636 0 [(primaryWord 2 &&& primaryWord 4)] 7
set_option maxRecDepth 8192 in
private theorem h1153 : Good row1153 :=
  goodBoth h1148 h1152 572 0 572 64 32 96 (by decide)

private def row1154 := state 637 0 [(primaryWord 2 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h1154 : Good row1154 :=
  goodCut h1153 636 0 [(64,65)] (by decide)

private def row1155 := state 636 1 [(primaryWord 2 &&& primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h1155 : Good row1155 :=
  goodCut h1153 636 0 [(0,1)] (by decide)

private def row1156 := state 765 0 [(primaryWord 2 &&& primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h1156 : Good row1156 :=
  goodBoth h1154 h1155 637 0 637 128 1 129 (by decide)

private def row1157 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h1157 : Good row1157 :=
  goodCut h1156 765 0 [(1,3)] (by decide)

private def row1158 := state 263 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h1158 : Good row1158 :=
  goodCut h2 2 1 [(2,3), (2,6)] (by decide)

private def row1159 := state 262 1 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h1159 : Good row1159 :=
  goodCut h152 1 0 [(260,262), (2,6)] (by decide)

private def row1160 := state 327 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 4
set_option maxRecDepth 8192 in
private theorem h1160 : Good row1160 :=
  goodBoth h1158 h1159 263 0 263 64 1 65 (by decide)

private def row1161 := state 359 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1161 : Good row1161 :=
  goodCut h1160 327 0 [(64,96)] (by decide)

private def row1162 := state 97 4 [] 3
set_option maxRecDepth 8192 in
private theorem h1162 : Good row1162 :=
  goodCut h0 4 0 [(64,65), (64,96), (1,65)] (by decide)

private def row1163 := state 0 261 [(primaryWord 2 ||| primaryWord 8)] 1
set_option maxRecDepth 8192 in
private theorem h1163 : Good row1163 :=
  goodOne row1163 (by decide)

private def row1164 := state 96 261 [(primaryWord 2 ||| primaryWord 8)] 3
set_option maxRecDepth 8192 in
private theorem h1164 : Good row1164 :=
  goodCut h1163 261 0 [(64,96), (32,96)] (by decide)

private def row1165 := state 355 4 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1165 : Good row1165 :=
  goodBoth h1162 h1164 101 0 357 2 1 3 (by decide)

private def row1166 := state 367 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1166 : Good row1166 :=
  goodBoth h1161 h1165 359 0 359 8 4 12 (by decide)

private def row1167 := state 383 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h1167 : Good row1167 :=
  goodCut h1166 367 0 [(36,52)] (by decide)

private def row1168 := state 121 4 [(primaryWord 2 ||| primaryWord 4)] 6
set_option maxRecDepth 8192 in
private theorem h1168 : Good row1168 :=
  goodCut h128 121 0 [(16,20)] (by decide)

private def row1169 := state 0 292 [(primaryWord 2 ||| primaryWord 8)] 1
set_option maxRecDepth 8192 in
private theorem h1169 : Good row1169 :=
  goodOne row1169 (by decide)

private def row1170 := state 0 300 [(primaryWord 2 ||| primaryWord 8)] 2
set_option maxRecDepth 8192 in
private theorem h1170 : Good row1170 :=
  goodCut h1169 292 0 [(0,8)] (by decide)

private def row1171 := state 56 260 [(primaryWord 2 ||| primaryWord 8), ((primaryWord 2 ||| primaryWord 8) ||| primaryWord 4)] 3
set_option maxRecDepth 8192 in
private theorem h1171 : Good row1171 :=
  goodCut h1170 300 16 [(8,24)] (by decide)

private def row1172 := state 24 292 [(primaryWord 2 ||| primaryWord 8), ((primaryWord 2 ||| primaryWord 8) ||| primaryWord 4)] 3
set_option maxRecDepth 8192 in
private theorem h1172 : Good row1172 :=
  goodCut h1169 292 16 [(16,24), (8,24)] (by decide)

private def row1173 := state 120 260 [(primaryWord 2 ||| primaryWord 8), ((primaryWord 2 ||| primaryWord 8) ||| primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1173 : Good row1173 :=
  goodBoth h1171 h1172 316 0 316 64 32 96 (by decide)

private def row1174 := state 120 261 [(primaryWord 2 ||| primaryWord 8), ((primaryWord 2 ||| primaryWord 8) ||| primaryWord 4)] 6
set_option maxRecDepth 8192 in
private theorem h1174 : Good row1174 :=
  goodCut h1173 380 0 [(0,1)] (by decide)

private def row1175 := state 379 4 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 4)] 8
set_option maxRecDepth 8192 in
private theorem h1175 : Good row1175 :=
  goodBoth h1168 h1174 125 0 381 2 1 3 (by decide)

private def row1176 := state 895 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 4)] 10
set_option maxRecDepth 8192 in
private theorem h1176 : Good row1176 :=
  goodBoth h1167 h1175 383 0 383 512 4 516 (by decide)

private def row1177 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 4)] 11
set_option maxRecDepth 8192 in
private theorem h1177 : Good row1177 :=
  goodCut h1176 895 0 [(1,129)] (by decide)

private def row1178 := state 572 0 [(primaryWord 2 &&& primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h1178 : Good row1178 :=
  goodCut h189 540 0 [(16,48)] (by decide)

private def row1179 := state 540 32 [(primaryWord 2 &&& primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h1179 : Good row1179 :=
  goodCut h189 540 0 [(0,32)] (by decide)

private def row1180 := state 636 0 [(primaryWord 2 &&& primaryWord 5)] 7
set_option maxRecDepth 8192 in
private theorem h1180 : Good row1180 :=
  goodBoth h1178 h1179 572 0 572 64 32 96 (by decide)

private def row1181 := state 637 0 [(primaryWord 2 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h1181 : Good row1181 :=
  goodCut h1180 636 0 [(64,65)] (by decide)

private def row1182 := state 636 1 [(primaryWord 2 &&& primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h1182 : Good row1182 :=
  goodCut h1180 636 0 [(0,1)] (by decide)

private def row1183 := state 765 0 [(primaryWord 2 &&& primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h1183 : Good row1183 :=
  goodBoth h1181 h1182 637 0 637 128 1 129 (by decide)

private def row1184 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h1184 : Good row1184 :=
  goodCut h1183 765 0 [(1,3)] (by decide)

private def row1185 := state 572 0 [(primaryWord 2 ||| primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h1185 : Good row1185 :=
  goodCut h189 540 0 [(20,52)] (by decide)

private def row1186 := state 540 32 [(primaryWord 2 ||| primaryWord 5)] 5
set_option maxRecDepth 8192 in
private theorem h1186 : Good row1186 :=
  goodCut h189 540 0 [(4,36)] (by decide)

private def row1187 := state 636 0 [(primaryWord 2 ||| primaryWord 5)] 7
set_option maxRecDepth 8192 in
private theorem h1187 : Good row1187 :=
  goodBoth h1185 h1186 572 0 572 64 32 96 (by decide)

private def row1188 := state 637 0 [(primaryWord 2 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h1188 : Good row1188 :=
  goodCut h1187 636 0 [(64,65)] (by decide)

private def row1189 := state 636 1 [(primaryWord 2 ||| primaryWord 5)] 8
set_option maxRecDepth 8192 in
private theorem h1189 : Good row1189 :=
  goodCut h1187 636 0 [(0,1)] (by decide)

private def row1190 := state 765 0 [(primaryWord 2 ||| primaryWord 5)] 10
set_option maxRecDepth 8192 in
private theorem h1190 : Good row1190 :=
  goodBoth h1188 h1189 637 0 637 128 1 129 (by decide)

private def row1191 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 5)] 11
set_option maxRecDepth 8192 in
private theorem h1191 : Good row1191 :=
  goodCut h1190 765 0 [(1,3)] (by decide)

private def row1192 := state 636 0 [(primaryWord 2 &&& primaryWord 6)] 7
set_option maxRecDepth 8192 in
private theorem h1192 : Good row1192 :=
  goodBoth h190 h191 572 0 572 64 32 96 (by decide)

private def row1193 := state 637 0 [(primaryWord 2 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1193 : Good row1193 :=
  goodCut h1192 636 0 [(64,65)] (by decide)

private def row1194 := state 572 1 [] 6
set_option maxRecDepth 8192 in
private theorem h1194 : Good row1194 :=
  goodCut h190 572 0 [(0,1)] (by decide)

private def row1195 := state 540 33 [] 6
set_option maxRecDepth 8192 in
private theorem h1195 : Good row1195 :=
  goodCut h191 572 0 [(0,1)] (by decide)

private def row1196 := state 636 1 [(primaryWord 2 &&& primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1196 : Good row1196 :=
  goodBoth h1194 h1195 573 0 573 64 32 96 (by decide)

private def row1197 := state 765 0 [(primaryWord 2 &&& primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1197 : Good row1197 :=
  goodBoth h1193 h1196 637 0 637 128 1 129 (by decide)

private def row1198 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1198 : Good row1198 :=
  goodCut h1197 765 0 [(1,3)] (by decide)

private def row1199 := state 636 0 [(primaryWord 2 ||| primaryWord 6)] 7
set_option maxRecDepth 8192 in
private theorem h1199 : Good row1199 :=
  goodBoth h190 h191 572 0 572 64 36 100 (by decide)

private def row1200 := state 637 0 [(primaryWord 2 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1200 : Good row1200 :=
  goodCut h1199 636 0 [(64,65)] (by decide)

private def row1201 := state 636 1 [(primaryWord 2 ||| primaryWord 6)] 8
set_option maxRecDepth 8192 in
private theorem h1201 : Good row1201 :=
  goodBoth h1194 h1195 573 0 573 64 36 100 (by decide)

private def row1202 := state 765 0 [(primaryWord 2 ||| primaryWord 6)] 10
set_option maxRecDepth 8192 in
private theorem h1202 : Good row1202 :=
  goodBoth h1200 h1201 637 0 637 128 1 129 (by decide)

private def row1203 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 6)] 11
set_option maxRecDepth 8192 in
private theorem h1203 : Good row1203 :=
  goodCut h1202 765 0 [(1,3)] (by decide)

private def row1204 := state 765 0 [(primaryWord 2 &&& primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h1204 : Good row1204 :=
  goodBoth h193 h297 637 0 637 128 1 129 (by decide)

private def row1205 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h1205 : Good row1205 :=
  goodCut h1204 765 0 [(1,3)] (by decide)

private def row1206 := state 765 0 [(primaryWord 2 ||| primaryWord 7)] 10
set_option maxRecDepth 8192 in
private theorem h1206 : Good row1206 :=
  goodBoth h193 h297 637 0 637 128 5 133 (by decide)

private def row1207 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 7)] 11
set_option maxRecDepth 8192 in
private theorem h1207 : Good row1207 :=
  goodCut h1206 765 0 [(1,3)] (by decide)

private def row1208 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 8)] 11
set_option maxRecDepth 8192 in
private theorem h1208 : Good row1208 :=
  goodCut h298 765 0 [(1,3)] (by decide)

private def row1209 := state 383 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1209 : Good row1209 :=
  goodCut h180 127 0 [] (by decide)

private def row1210 := state 511 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 10
set_option maxRecDepth 8192 in
private theorem h1210 : Good row1210 :=
  goodCut h1209 383 0 [(1,129)] (by decide)

private def row1211 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h1211 : Good row1211 :=
  goodCut h1210 511 0 [(4,516)] (by decide)

private def row1212 := state 765 0 [(primaryWord 2 ||| primaryWord 9)] 10
set_option maxRecDepth 8192 in
private theorem h1212 : Good row1212 :=
  goodBoth h388 h751 253 0 253 512 4 516 (by decide)

private def row1213 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| primaryWord 9)] 11
set_option maxRecDepth 8192 in
private theorem h1213 : Good row1213 :=
  goodCut h1212 765 0 [(1,3)] (by decide)

private def row1214 := state 121 0 [(primaryWord 3 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1214 : Good row1214 :=
  goodCut h141 113 0 [(16,24)] (by decide)

private def row1215 := state 113 8 [(primaryWord 3 &&& primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1215 : Good row1215 :=
  goodCut h141 113 0 [(0,8)] (by decide)

private def row1216 := state 125 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1216 : Good row1216 :=
  goodBoth h1214 h1215 121 0 121 4 8 12 (by decide)

private def row1217 := state 637 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1217 : Good row1217 :=
  goodCut h1216 125 0 [(4,516)] (by decide)

private def row1218 := state 765 0 [(primaryWord 3 &&& primaryWord 4), ((primaryWord 3 &&& primaryWord 4) &&& primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1218 : Good row1218 :=
  goodCut h1217 637 0 [(1,129)] (by decide)

private def row1219 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), ((primaryWord 3 &&& primaryWord 4) &&& ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h1219 : Good row1219 :=
  goodCut h1218 765 0 [(1,3)] (by decide)

private def row1220 := state 0 260 [(primaryWord 2 ||| primaryWord 8)] 0
set_option maxRecDepth 8192 in
private theorem h1220 : Good row1220 :=
  goodZero row1220 rfl

private def row1221 := state 774 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 2
set_option maxRecDepth 8192 in
private theorem h1221 : Good row1221 :=
  goodCut h1220 260 2 [(4,6), (4,516)] (by decide)

private def row1222 := state 775 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 4
set_option maxRecDepth 8192 in
private theorem h1222 : Good row1222 :=
  goodBoth h1221 h3 774 0 518 1 2 3 (by decide)

private def row1223 := state 839 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1223 : Good row1223 :=
  goodCut h1222 775 0 [(1,65)] (by decide)

private def row1224 := state 775 64 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1224 : Good row1224 :=
  goodCut h1222 775 0 [(0,64)] (by decide)

private def row1225 := state 871 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1225 : Good row1225 :=
  goodBoth h1223 h1224 839 0 839 32 64 96 (by decide)

private def row1226 := state 999 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1226 : Good row1226 :=
  goodCut h1225 871 0 [(1,129)] (by decide)

private def row1227 := state 1015 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1227 : Good row1227 :=
  goodCut h1226 999 0 [(32,48)] (by decide)

private def row1228 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), ((primaryWord 3 &&& primaryWord 4) ||| ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h1228 : Good row1228 :=
  goodCut h1227 1015 0 [(4,12)] (by decide)

private def row1229 := state 524 0 [(~~~(primaryWord 2))] 2
set_option maxRecDepth 8192 in
private theorem h1229 : Good row1229 :=
  goodCut h259 4 8 [(4,12), (4,516)] (by decide)

private def row1230 := state 516 8 [(~~~(primaryWord 2))] 2
set_option maxRecDepth 8192 in
private theorem h1230 : Good row1230 :=
  goodCut h113 8 0 [(512,516), (4,516)] (by decide)

private def row1231 := state 540 0 [(~~~(primaryWord 2))] 4
set_option maxRecDepth 8192 in
private theorem h1231 : Good row1231 :=
  goodBoth h1229 h1230 524 0 524 16 8 24 (by decide)

private def row1232 := state 572 0 [(~~~(primaryWord 2))] 5
set_option maxRecDepth 8192 in
private theorem h1232 : Good row1232 :=
  goodCut h1231 540 0 [(16,48)] (by decide)

private def row1233 := state 540 32 [(~~~(primaryWord 2))] 5
set_option maxRecDepth 8192 in
private theorem h1233 : Good row1233 :=
  goodCut h1231 540 0 [(0,32)] (by decide)

private def row1234 := state 636 0 [(~~~(primaryWord 2))] 7
set_option maxRecDepth 8192 in
private theorem h1234 : Good row1234 :=
  goodBoth h1232 h1233 572 0 572 64 32 96 (by decide)

private def row1235 := state 637 0 [(~~~(primaryWord 2))] 8
set_option maxRecDepth 8192 in
private theorem h1235 : Good row1235 :=
  goodCut h1234 636 0 [(64,65)] (by decide)

private def row1236 := state 636 1 [(~~~(primaryWord 2))] 8
set_option maxRecDepth 8192 in
private theorem h1236 : Good row1236 :=
  goodCut h1234 636 0 [(0,1)] (by decide)

private def row1237 := state 765 0 [(~~~(primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h1237 : Good row1237 :=
  goodBoth h1235 h1236 637 0 637 128 1 129 (by decide)

private def row1238 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (~~~(((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)))] 11
set_option maxRecDepth 8192 in
private theorem h1238 : Good row1238 :=
  goodCut h1237 765 0 [(1,3)] (by decide)

private def row1239 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1239 : Good row1239 :=
  fastGoodSplit row1239 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h600, checked h601, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h602, checked h603, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h604, checked h605, checked h796, checked h611,
  checked h616, checked h617, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625,
  checked h626, checked h627, checked h628, checked h629, checked h1136, checked h1146, checked h798, checked h642,
  checked h647, checked h649, checked h651, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h1157, checked h1177, checked h803, checked h672, checked h674,
  checked h675, checked h676, checked h677, checked h678, checked h679, checked h680, checked h681, checked h682,
  checked h683, checked h684, checked h1184, checked h1191, checked h805, checked h707, checked h712, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h719, checked h720, checked h1198,
  checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h735, checked h736, checked h1205, checked h1207, checked h817, checked h742, checked h743, checked h744,
  checked h745, checked h1208, checked h818, checked h747, checked h748, checked h749, checked h750, checked h1211,
  checked h1213, checked h819, checked h764, checked h772, checked h820, checked h1219, checked h1228, checked h1238
  ] [
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787,
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 10114245, 1221, 9045315, 9045315, 1221,
  1221, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787,
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 9045315, 9045315, 1221, 37602878787, 37602878787, 37602878787, 37602878787,
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 10114245,
  9045315, 9045315, 37602878787, 37602878787, 37602878787, 9045315, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787,
  37602878787, 9045315, 10114245, 10114245, 1221, 1221, 37602878787, 37602878787, 37602878787, 37602878787, 9045315, 37602878787,
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 10114245, 10114245, 1221, 1221, 37602878787, 9045315, 37602878787,
  37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 10114245, 10114245, 9045315, 9045315, 1221, 1221,
  37602878787, 37602878787, 9045315, 37602878787, 37602878787, 37602878787, 37602878787, 10114245, 10114245, 9045315, 9045315, 1221,
  1221, 37602878787, 37602878787, 37602878787, 37602878787, 37602878787, 10114245, 10114245, 9045315, 9045315, 1221, 1221,
  37602878787, 37602878787, 37602878787, 9045315, 9045315, 1221, 37602878787, 10114245, 10114245, 9045315, 9045315, 1221,
  1221, 10114245, 2436, 2436, 9045315, 0, 0, 1221
  ] (by decide)

private def row1240 := state 125 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1240 : Good row1240 :=
  goodCut h141 113 0 [(8,12), (36,44)] (by decide)

private def row1241 := state 48 0 [] 1
set_option maxRecDepth 8192 in
private theorem h1241 : Good row1241 :=
  goodOne row1241 (by decide)

private def row1242 := state 60 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 3
set_option maxRecDepth 8192 in
private theorem h1242 : Good row1242 :=
  goodCut h1241 48 0 [(8,12), (36,44)] (by decide)

private def row1243 := state 0 52 [] 2
set_option maxRecDepth 8192 in
private theorem h1243 : Good row1243 :=
  goodCut h1063 48 0 [(0,4)] (by decide)

private def row1244 := state 28 32 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 3
set_option maxRecDepth 8192 in
private theorem h1244 : Good row1244 :=
  goodCut h1243 52 8 [(16,24)] (by decide)

private def row1245 := state 124 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1245 : Good row1245 :=
  goodBoth h1242 h1244 60 0 60 64 32 96 (by decide)

private def row1246 := state 124 1 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1246 : Good row1246 :=
  goodCut h1245 124 0 [(0,1)] (by decide)

private def row1247 := state 253 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1247 : Good row1247 :=
  goodBoth h1240 h1246 125 0 125 128 1 129 (by decide)

private def row1248 := state 765 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) &&& primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1248 : Good row1248 :=
  goodCut h1247 253 0 [(4,516)] (by decide)

private def row1249 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& (primaryWord 3 ||| primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h1249 : Good row1249 :=
  goodCut h1248 765 0 [(1,3)] (by decide)

private def row1250 := state 253 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1250 : Good row1250 :=
  goodBoth h902 h903 249 0 249 4 8 12 (by decide)

private def row1251 := state 765 0 [(primaryWord 3 ||| primaryWord 5), ((primaryWord 3 ||| primaryWord 5) ||| primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1251 : Good row1251 :=
  goodCut h1250 253 0 [(4,516)] (by decide)

private def row1252 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| (primaryWord 3 ||| primaryWord 5))] 10
set_option maxRecDepth 8192 in
private theorem h1252 : Good row1252 :=
  goodCut h1251 765 0 [(1,3)] (by decide)

private def row1253 := state 391 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 4
set_option maxRecDepth 8192 in
private theorem h1253 : Good row1253 :=
  goodBoth h1158 h1159 263 0 263 128 1 129 (by decide)

private def row1254 := state 455 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1254 : Good row1254 :=
  goodCut h1253 391 0 [(1,65)] (by decide)

private def row1255 := state 391 64 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1255 : Good row1255 :=
  goodCut h1253 391 0 [(0,64)] (by decide)

private def row1256 := state 487 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1256 : Good row1256 :=
  goodBoth h1254 h1255 455 0 455 32 64 96 (by decide)

private def row1257 := state 503 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1257 : Good row1257 :=
  goodCut h1256 487 0 [(32,48)] (by decide)

private def row1258 := state 1015 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& primaryWord 9)] 9
set_option maxRecDepth 8192 in
private theorem h1258 : Good row1258 :=
  goodCut h1257 503 0 [(4,516)] (by decide)

private def row1259 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& (primaryWord 3 ||| primaryWord 9))] 10
set_option maxRecDepth 8192 in
private theorem h1259 : Good row1259 :=
  goodCut h1258 1015 0 [(528,536)] (by decide)

private def row1260 := state 507 0 [(primaryWord 1 &&& primaryWord 8)] 9
set_option maxRecDepth 8192 in
private theorem h1260 : Good row1260 :=
  goodCut h387 249 0 [(1,3), (2,258)] (by decide)

private def row1261 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| (primaryWord 3 ||| primaryWord 9))] 10
set_option maxRecDepth 8192 in
private theorem h1261 : Good row1261 :=
  goodCut h1260 507 512 [(4,516)] (by decide)

private def row1262 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1262 : Good row1262 :=
  fastGoodSplit row1262 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h828, checked h832, checked h845,
  checked h846, checked h1124, checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498,
  checked h507, checked h513, checked h518, checked h523, checked h526, checked h528, checked h529, checked h532,
  checked h534, checked h535, checked h538, checked h835, checked h838, checked h847, checked h848, checked h1126,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h585,
  checked h841, checked h844, checked h849, checked h850, checked h796, checked h617, checked h611, checked h616,
  checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h628,
  checked h629, checked h1136, checked h1146, checked h798, checked h642, checked h647, checked h649, checked h852,
  checked h652, checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659,
  checked h854, checked h856, checked h857, checked h858, checked h1157, checked h1177, checked h803, checked h863,
  checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680, checked h681,
  checked h682, checked h864, checked h865, checked h1184, checked h1191, checked h805, checked h707, checked h878,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882,
  checked h883, checked h884, checked h1198, checked h1203, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h733, checked h734, checked h886, checked h888, checked h889, checked h890, checked h1205,
  checked h1207, checked h817, checked h742, checked h743, checked h893, checked h896, checked h897, checked h898,
  checked h1208, checked h818, checked h747, checked h748, checked h901, checked h1211, checked h1213, checked h819,
  checked h906, checked h907, checked h909, checked h910, checked h937, checked h911, checked h1249, checked h1252,
  checked h938, checked h1259, checked h1261, checked h1238
  ] [
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 41986582757, 9988325, 37607728451, 37607728451, 37607204163,
  37607204163, 9988325, 9988325, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 37607728451, 37607728451, 37607204163, 37607204163, 9988325,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 41986582757, 37607728451, 37607728451, 37607204163, 37607204163, 156309556061507, 37607728451, 156309556061507, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 41986582757, 41986582757, 9988325, 9988325, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 37607728451, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 41986582757, 41986582757,
  37607728451, 37607728451, 37607204163, 37607204163, 9988325, 9988325, 156309556061507, 37607728451, 156309556061507, 156309556061507, 156309556061507, 156309556061507,
  156309556061507, 156309556061507, 156309556061507, 41986582757, 41986582757, 37607204163, 37607204163, 9988325, 9988325, 156309556061507, 156309556061507, 37607728451,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 41986582757, 41986582757, 37607728451, 37607728451, 37607204163, 37607204163, 9988325, 9988325,
  156309556061507, 156309556061507, 156309556061507, 156309556061507, 156309556061507, 41986582757, 41986582757, 37607728451, 37607728451, 37607204163, 37607204163, 9988325,
  9988325, 156309556061507, 156309556061507, 156309556061507, 37607728451, 37607728451, 37607204163, 37607204163, 9988325, 156309556061507, 41986582757, 41986582757,
  37607728451, 9988325, 9988325, 41986582757, 10115429, 10115429, 10115301, 10115301, 37607728451, 9045315, 2405, 2405,
  37607204163, 2277, 2277, 9988325
  ] (by decide)

private def row1263 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1263 : Good row1263 :=
  fastGoodSplit row1263 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h828, checked h832, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h835, checked h838, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h841, checked h844, checked h796, checked h617,
  checked h611, checked h616, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625,
  checked h626, checked h1262, checked h628, checked h629, checked h1136, checked h1146, checked h798, checked h642,
  checked h647, checked h649, checked h852, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h854, checked h856, checked h1157, checked h1177, checked h803,
  checked h863, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h1184, checked h1191, checked h805, checked h707, checked h878, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882, checked h1198,
  checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h886, checked h888, checked h1205, checked h1207, checked h817, checked h742, checked h743, checked h893,
  checked h896, checked h1208, checked h818, checked h747, checked h748, checked h901, checked h941, checked h1211,
  checked h1213, checked h819, checked h906, checked h907, checked h937, checked h1249, checked h1252, checked h1238
  ] [
  37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163,
  37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 10115301, 2277, 9045315, 9045315, 2277,
  2277, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163,
  37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 9045315, 9045315, 2277, 37607204163, 37607204163, 37607204163, 37607204163,
  37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 10115301,
  9045315, 9045315, 37607204163, 9045315, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163,
  37607204163, 0, 10115301, 10115301, 2277, 2277, 37607204163, 37607204163, 37607204163, 37607204163, 9045315, 37607204163,
  37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 10115301, 10115301, 9045315, 9045315, 2277, 2277, 37607204163,
  9045315, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 10115301, 10115301, 2277, 2277,
  37607204163, 37607204163, 9045315, 37607204163, 37607204163, 37607204163, 37607204163, 10115301, 10115301, 9045315, 9045315, 2277,
  2277, 37607204163, 37607204163, 37607204163, 37607204163, 37607204163, 10115301, 10115301, 9045315, 9045315, 2277, 2277,
  37607204163, 37607204163, 37607204163, 9045315, 9045315, 2277, 37607204163, 10115301, 10115301, 9045315, 9045315, 2277,
  2277, 10115301, 2436, 2436, 9045315, 0, 0, 2277
  ] (by decide)

private def row1264 := state 894 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1264 : Good row1264 :=
  goodCut h192 636 0 [(4,6)] (by decide)

private def row1265 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& (primaryWord 6 ||| primaryWord 7))] 10
set_option maxRecDepth 8192 in
private theorem h1265 : Good row1265 :=
  goodCut h1264 894 128 [(2,3), (1,129)] (by decide)

private def row1266 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| (primaryWord 6 ||| primaryWord 7))] 10
set_option maxRecDepth 8192 in
private theorem h1266 : Good row1266 :=
  goodCut h1264 894 128 [(2,3), (5,133)] (by decide)

private def row1267 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1267 : Good row1267 :=
  fastGoodSplit row1267 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h845, checked h846, checked h956,
  checked h957, checked h1124, checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498,
  checked h507, checked h513, checked h518, checked h523, checked h526, checked h528, checked h529, checked h532,
  checked h534, checked h535, checked h538, checked h847, checked h848, checked h958, checked h959, checked h1126,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h585,
  checked h849, checked h850, checked h960, checked h961, checked h796, checked h627, checked h611, checked h616,
  checked h878, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h628, checked h629, checked h962, checked h963, checked h1136, checked h1146, checked h798, checked h642,
  checked h647, checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h857, checked h858, checked h964, checked h965, checked h1157,
  checked h1177, checked h803, checked h955, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h864, checked h865, checked h966, checked h967,
  checked h1184, checked h1191, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h883, checked h884, checked h1198, checked h1203, checked h806, checked h729,
  checked h730, checked h731, checked h732, checked h733, checked h734, checked h889, checked h890, checked h1205,
  checked h1207, checked h817, checked h742, checked h743, checked h897, checked h898, checked h968, checked h969,
  checked h1208, checked h818, checked h747, checked h748, checked h970, checked h971, checked h1211, checked h1213,
  checked h819, checked h909, checked h910, checked h973, checked h974, checked h938, checked h979, checked h980,
  checked h1259, checked h1261, checked h991, checked h1265, checked h1266, checked h1238
  ] [
  156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619,
  156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 41986333029, 9738597, 37607478595, 37607478595, 37607728451,
  37607728451, 9738597, 9738597, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619,
  156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 37607478595, 37607478595, 37607728451, 37607728451, 9738597,
  156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619,
  156308533175619, 156308533175619, 156308533175619, 41986333029, 37607478595, 37607478595, 37607728451, 37607728451, 156308533175619, 37607478595, 156308533175619, 156308533175619,
  37607728451, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 41986333029, 41986333029, 37607728451, 37607728451,
  9738597, 9738597, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 37607478595, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619,
  156308533175619, 41986333029, 41986333029, 37607478595, 37607478595, 37607728451, 37607728451, 9738597, 9738597, 156308533175619, 37607478595, 156308533175619,
  156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 41986333029, 41986333029, 37607478595, 37607478595, 37607728451, 37607728451,
  9738597, 9738597, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 41986333029, 41986333029, 37607478595, 37607478595,
  9738597, 9738597, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 156308533175619, 41986333029, 41986333029, 37607478595, 37607478595, 9738597,
  9738597, 156308533175619, 156308533175619, 156308533175619, 37607478595, 37607478595, 37607728451, 37607728451, 9738597, 156308533175619, 41986333029, 41986333029,
  37607728451, 37607728451, 9738597, 9738597, 41986333029, 10115368, 10115368, 10115429, 10115429, 37607478595, 9045315, 9045315,
  2344, 2344, 37607728451, 2405, 2405, 9738597
  ] (by decide)

private def row1268 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1268 : Good row1268 :=
  fastGoodSplit row1268 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h845, checked h846, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h847, checked h848, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h849, checked h850, checked h796, checked h627,
  checked h611, checked h616, checked h1262, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h628, checked h629, checked h1136, checked h1146, checked h798, checked h642,
  checked h647, checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656,
  checked h657, checked h658, checked h659, checked h857, checked h858, checked h1157, checked h1177, checked h803,
  checked h955, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h864, checked h865, checked h1184, checked h1191, checked h805, checked h707,
  checked h1267, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h883,
  checked h884, checked h1198, checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732,
  checked h733, checked h734, checked h889, checked h890, checked h1205, checked h1207, checked h817, checked h742,
  checked h743, checked h897, checked h898, checked h1208, checked h818, checked h747, checked h748, checked h1211,
  checked h1213, checked h819, checked h909, checked h910, checked h938, checked h1259, checked h1261, checked h1238
  ] [
  37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451,
  37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 10115429, 2405, 9045315, 9045315, 2405,
  2405, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451,
  37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 9045315, 9045315, 2405, 37607728451, 37607728451, 37607728451, 37607728451,
  37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 10115429,
  9045315, 9045315, 37607728451, 9045315, 37607728451, 37607728451, 0, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451,
  37607728451, 37607728451, 10115429, 10115429, 2405, 2405, 37607728451, 37607728451, 37607728451, 37607728451, 9045315, 37607728451,
  37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 10115429, 10115429, 9045315, 9045315, 2405, 2405, 37607728451,
  9045315, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 10115429, 10115429, 9045315, 9045315,
  2405, 2405, 37607728451, 37607728451, 0, 37607728451, 37607728451, 37607728451, 37607728451, 10115429, 10115429, 9045315,
  9045315, 2405, 2405, 37607728451, 37607728451, 37607728451, 37607728451, 37607728451, 10115429, 10115429, 9045315, 9045315,
  2405, 2405, 37607728451, 37607728451, 37607728451, 9045315, 9045315, 2405, 37607728451, 10115429, 10115429, 2405,
  2405, 10115429, 2436, 2436, 9045315, 0, 0, 2405
  ] (by decide)

private def row1269 := state 636 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1269 : Good row1269 :=
  goodCut h189 540 64 [(16,48), (32,96)] (by decide)

private def row1270 := state 572 64 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1270 : Good row1270 :=
  goodCut h1148 572 0 [(16,80)] (by decide)

private def row1271 := state 637 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1271 : Good row1271 :=
  goodBoth h1269 h1270 636 0 636 1 64 65 (by decide)

private def row1272 := state 765 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) &&& primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1272 : Good row1272 :=
  goodCut h1271 637 0 [(1,129)] (by decide)

private def row1273 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) &&& (primaryWord 4 ||| primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h1273 : Good row1273 :=
  goodCut h1272 765 0 [(1,3)] (by decide)

private def row1274 := state 636 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1274 : Good row1274 :=
  goodCut h189 540 64 [(16,48), (36,100)] (by decide)

private def row1275 := state 24 0 [] 1
set_option maxRecDepth 8192 in
private theorem h1275 : Good row1275 :=
  goodOne row1275 (by decide)

private def row1276 := state 540 0 [(primaryWord 2 ||| primaryWord 4)] 3
set_option maxRecDepth 8192 in
private theorem h1276 : Good row1276 :=
  goodCut h1275 24 0 [(528,532), (4,516)] (by decide)

private def row1277 := state 0 528 [] 1
set_option maxRecDepth 8192 in
private theorem h1277 : Good row1277 :=
  goodOne row1277 (by decide)

private def row1278 := state 0 536 [] 2
set_option maxRecDepth 8192 in
private theorem h1278 : Good row1278 :=
  goodCut h1277 528 0 [(0,8)] (by decide)

private def row1279 := state 524 16 [(primaryWord 2 ||| primaryWord 4)] 3
set_option maxRecDepth 8192 in
private theorem h1279 : Good row1279 :=
  goodCut h1278 536 4 [(8,12)] (by decide)

private def row1280 := state 572 0 [(primaryWord 2 ||| primaryWord 4)] 5
set_option maxRecDepth 8192 in
private theorem h1280 : Good row1280 :=
  goodBoth h1276 h1279 540 0 540 32 16 48 (by decide)

private def row1281 := state 572 64 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 2)] 6
set_option maxRecDepth 8192 in
private theorem h1281 : Good row1281 :=
  goodCut h1280 572 0 [(16,80)] (by decide)

private def row1282 := state 637 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1282 : Good row1282 :=
  goodBoth h1274 h1281 636 0 636 1 64 65 (by decide)

private def row1283 := state 765 0 [(primaryWord 4 ||| primaryWord 6), ((primaryWord 4 ||| primaryWord 6) ||| primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1283 : Good row1283 :=
  goodCut h1282 637 0 [(1,129)] (by decide)

private def row1284 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), (((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2) ||| (primaryWord 4 ||| primaryWord 6))] 10
set_option maxRecDepth 8192 in
private theorem h1284 : Good row1284 :=
  goodCut h1283 765 0 [(1,3)] (by decide)

private def row1285 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 10
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1285 : Good row1285 :=
  fastGoodSplit row1285 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h998, checked h1003, checked h956,
  checked h957, checked h1124, checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498,
  checked h507, checked h513, checked h518, checked h523, checked h526, checked h528, checked h529, checked h532,
  checked h534, checked h535, checked h538, checked h1008, checked h1011, checked h958, checked h959, checked h1126,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h585,
  checked h1016, checked h1021, checked h960, checked h961, checked h796, checked h651, checked h611, checked h616,
  checked h852, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h954, checked h628, checked h629, checked h1023, checked h1025, checked h962, checked h963, checked h1136,
  checked h1146, checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h658, checked h659, checked h964, checked h965, checked h1157,
  checked h1177, checked h803, checked h1027, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h1029, checked h1033, checked h966, checked h967,
  checked h1184, checked h1191, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h1198, checked h1203, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h733, checked h734, checked h1038, checked h1205, checked h1207, checked h817, checked h742,
  checked h743, checked h1043, checked h1048, checked h968, checked h969, checked h1208, checked h818, checked h747,
  checked h748, checked h1050, checked h1052, checked h970, checked h971, checked h1211, checked h1213, checked h819,
  checked h1057, checked h1058, checked h973, checked h974, checked h1078, checked h1059, checked h1273, checked h1284,
  checked h991, checked h1265, checked h1266, checked h1238
  ] [
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499,
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 41986332934, 9738502, 37607478595, 37607478595, 37607339331,
  37607339331, 9738502, 9738502, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499,
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 37607478595, 37607478595, 37607339331, 37607339331, 9738502,
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499,
  156308532786499, 156308532786499, 156308532786499, 41986332934, 37607478595, 37607478595, 37607339331, 37607339331, 156308532786499, 37607478595, 156308532786499, 156308532786499,
  37607478595, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 37607478595, 41986332934, 41986332934, 37607478595,
  37607478595, 37607339331, 37607339331, 9738502, 9738502, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499,
  156308532786499, 156308532786499, 156308532786499, 41986332934, 41986332934, 37607339331, 37607339331, 9738502, 9738502, 156308532786499, 37607478595, 156308532786499,
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 41986332934, 41986332934, 37607478595, 37607478595, 37607339331, 37607339331,
  9738502, 9738502, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 41986332934, 41986332934, 9738502, 9738502,
  156308532786499, 156308532786499, 156308532786499, 156308532786499, 156308532786499, 41986332934, 41986332934, 37607478595, 9738502, 9738502, 156308532786499, 156308532786499,
  156308532786499, 37607478595, 37607478595, 37607339331, 37607339331, 9738502, 156308532786499, 41986332934, 41986332934, 37607478595, 37607478595, 37607339331,
  37607339331, 9738502, 9738502, 41986332934, 10115368, 10115368, 10115334, 10115334, 37607478595, 9045315, 2344, 2344,
  37607339331, 2310, 2310, 9738502
  ] (by decide)

private def row1286 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1286 : Good row1286 :=
  fastGoodSplit row1286 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h998, checked h1003, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h1008, checked h1011, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h1016, checked h1021, checked h796, checked h651,
  checked h611, checked h616, checked h852, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h954, checked h628, checked h629, checked h1023, checked h1025, checked h1136,
  checked h1146, checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h658, checked h659, checked h1157, checked h1177, checked h803,
  checked h1027, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h1029, checked h1033, checked h1184, checked h1191, checked h805, checked h707,
  checked h1285, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h1198,
  checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h1038, checked h1081, checked h1205, checked h1207, checked h817, checked h742, checked h743, checked h1043,
  checked h1048, checked h1208, checked h818, checked h747, checked h748, checked h1050, checked h1052, checked h1211,
  checked h1213, checked h819, checked h1057, checked h1058, checked h1078, checked h1273, checked h1284, checked h1238
  ] [
  37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331,
  37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 10115334, 2310, 9045315, 9045315, 2310,
  2310, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331,
  37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 9045315, 9045315, 2310, 37607339331, 37607339331, 37607339331, 37607339331,
  37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 10115334,
  9045315, 9045315, 37607339331, 9045315, 37607339331, 37607339331, 9045315, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331,
  37607339331, 37607339331, 9045315, 10115334, 10115334, 9045315, 9045315, 2310, 2310, 37607339331, 37607339331, 37607339331,
  37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 10115334, 10115334, 2310, 2310, 37607339331,
  9045315, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 10115334, 10115334, 9045315, 9045315,
  2310, 2310, 37607339331, 37607339331, 0, 37607339331, 37607339331, 37607339331, 37607339331, 10115334, 10115334, 2310,
  2310, 37607339331, 37607339331, 37607339331, 37607339331, 37607339331, 10115334, 10115334, 9045315, 9045315, 2310, 2310,
  37607339331, 37607339331, 37607339331, 9045315, 9045315, 2310, 37607339331, 10115334, 10115334, 9045315, 9045315, 2310,
  2310, 10115334, 2436, 2436, 9045315, 0, 0, 2310
  ] (by decide)

private def row1287 := state 112 0 [(primaryWord 5 &&& primaryWord 6)] 2
set_option maxRecDepth 8192 in
private theorem h1287 : Good row1287 :=
  goodCut h92 32 16 [(32,48), (32,96)] (by decide)

private def row1288 := state 48 64 [(primaryWord 5 &&& primaryWord 6)] 2
set_option maxRecDepth 8192 in
private theorem h1288 : Good row1288 :=
  goodCut h139 64 0 [(32,48), (16,48)] (by decide)

private def row1289 := state 113 0 [(primaryWord 5 &&& primaryWord 6)] 4
set_option maxRecDepth 8192 in
private theorem h1289 : Good row1289 :=
  goodBoth h1287 h1288 112 0 112 1 64 65 (by decide)

private def row1290 := state 121 0 [(primaryWord 5 &&& primaryWord 6)] 5
set_option maxRecDepth 8192 in
private theorem h1290 : Good row1290 :=
  goodCut h1289 113 0 [(16,24)] (by decide)

private def row1291 := state 113 8 [(primaryWord 5 &&& primaryWord 6)] 5
set_option maxRecDepth 8192 in
private theorem h1291 : Good row1291 :=
  goodCut h1289 113 0 [(0,8)] (by decide)

private def row1292 := state 125 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1292 : Good row1292 :=
  goodBoth h1290 h1291 121 0 121 4 8 12 (by decide)

private def row1293 := state 637 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1293 : Good row1293 :=
  goodCut h1292 125 0 [(4,516)] (by decide)

private def row1294 := state 765 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) &&& primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1294 : Good row1294 :=
  goodCut h1293 637 0 [(1,129)] (by decide)

private def row1295 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), ((primaryWord 5 &&& primaryWord 6) &&& ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h1295 : Good row1295 :=
  goodCut h1294 765 0 [(1,3)] (by decide)

private def row1296 := state 124 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1296 : Good row1296 :=
  goodCut h115 60 0 [(36,100)] (by decide)

private def row1297 := state 60 64 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 5
set_option maxRecDepth 8192 in
private theorem h1297 : Good row1297 :=
  goodCut h115 60 0 [(0,64)] (by decide)

private def row1298 := state 125 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 7
set_option maxRecDepth 8192 in
private theorem h1298 : Good row1298 :=
  goodBoth h1296 h1297 124 0 124 1 64 65 (by decide)

private def row1299 := state 637 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 8
set_option maxRecDepth 8192 in
private theorem h1299 : Good row1299 :=
  goodCut h1298 125 0 [(4,516)] (by decide)

private def row1300 := state 765 0 [(primaryWord 5 &&& primaryWord 6), ((primaryWord 5 &&& primaryWord 6) ||| primaryWord 2)] 9
set_option maxRecDepth 8192 in
private theorem h1300 : Good row1300 :=
  goodCut h1299 637 0 [(1,129)] (by decide)

private def row1301 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2), ((primaryWord 5 &&& primaryWord 6) ||| ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2))] 10
set_option maxRecDepth 8192 in
private theorem h1301 : Good row1301 :=
  goodCut h1300 765 0 [(1,3)] (by decide)

private def row1302 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1302 : Good row1302 :=
  fastGoodSplit row1302 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h1083, checked h1084, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h1085, checked h1086, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h1087, checked h1088, checked h796, checked h672,
  checked h611, checked h616, checked h863, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h955, checked h628, checked h629, checked h1089, checked h1090, checked h1136,
  checked h1146, checked h798, checked h642, checked h647, checked h649, checked h1027, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h1091, checked h1092,
  checked h1157, checked h1177, checked h803, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h1184, checked h1191, checked h805, checked h707,
  checked h1093, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h1198,
  checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h1094, checked h1095, checked h1205, checked h1207, checked h817, checked h742, checked h743, checked h1096,
  checked h1097, checked h1208, checked h818, checked h747, checked h748, checked h1098, checked h1099, checked h1211,
  checked h1213, checked h819, checked h1105, checked h1112, checked h1120, checked h1295, checked h1301, checked h1238
  ] [
  37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123,
  37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 10114311, 1287, 9045315, 9045315, 1287,
  1287, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123,
  37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 9045315, 9045315, 1287, 37603149123, 37603149123, 37603149123, 37603149123,
  37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 10114311,
  9045315, 9045315, 37603149123, 9045315, 37603149123, 37603149123, 9045315, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123,
  37603149123, 37603149123, 9045315, 10114311, 10114311, 9045315, 9045315, 1287, 1287, 37603149123, 37603149123, 37603149123,
  37603149123, 9045315, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 10114311, 10114311, 9045315, 9045315,
  1287, 1287, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 10114311, 10114311,
  1287, 1287, 37603149123, 37603149123, 9045315, 37603149123, 37603149123, 37603149123, 37603149123, 10114311, 10114311, 1287,
  1287, 37603149123, 37603149123, 37603149123, 37603149123, 37603149123, 10114311, 10114311, 9045315, 9045315, 1287, 1287,
  37603149123, 37603149123, 37603149123, 9045315, 9045315, 1287, 37603149123, 10114311, 10114311, 9045315, 9045315, 1287,
  1287, 10114311, 2436, 2436, 9045315, 0, 0, 1287
  ] (by decide)

private def row1303 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1303 : Good row1303 :=
  fastGoodSplit row1303 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h956, checked h957, checked h1124,
  checked h1125, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h958, checked h959, checked h1126, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h585, checked h960, checked h961, checked h796, checked h712,
  checked h611, checked h616, checked h878, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h1267, checked h628, checked h629, checked h962, checked h963, checked h1136,
  checked h1146, checked h798, checked h642, checked h647, checked h649, checked h1285, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h964, checked h965,
  checked h1157, checked h1177, checked h803, checked h1093, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h681, checked h682, checked h966, checked h967, checked h1184,
  checked h1191, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h717,
  checked h718, checked h1198, checked h1203, checked h806, checked h729, checked h730, checked h731, checked h732,
  checked h733, checked h734, checked h1205, checked h1207, checked h817, checked h742, checked h743, checked h968,
  checked h969, checked h1208, checked h818, checked h747, checked h748, checked h970, checked h971, checked h1211,
  checked h1213, checked h819, checked h973, checked h974, checked h991, checked h1265, checked h1266, checked h1238
  ] [
  37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595,
  37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368, 2344, 9045315, 9045315, 2344,
  2344, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595,
  37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 9045315, 9045315, 2344, 37607478595, 37607478595, 37607478595, 37607478595,
  37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368,
  9045315, 9045315, 37607478595, 9045315, 37607478595, 37607478595, 9045315, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595,
  37607478595, 37607478595, 0, 10115368, 10115368, 9045315, 9045315, 2344, 2344, 37607478595, 37607478595, 37607478595,
  37607478595, 0, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368, 10115368, 9045315, 9045315,
  2344, 2344, 37607478595, 9045315, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368,
  10115368, 9045315, 9045315, 2344, 2344, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368,
  10115368, 2344, 2344, 37607478595, 37607478595, 37607478595, 37607478595, 37607478595, 10115368, 10115368, 2344, 2344,
  37607478595, 37607478595, 37607478595, 9045315, 9045315, 2344, 37607478595, 10115368, 10115368, 9045315, 9045315, 2344,
  2344, 10115368, 2436, 2436, 9045315, 0, 0, 2344
  ] (by decide)

private def row1304 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), ((primaryWord 1 &&& primaryWord 8) ||| primaryWord 2)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1304 : Good row1304 :=
  fastGoodSplit row1304 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h586, checked h1124, checked h1125, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h1126,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h585,
  checked h796, checked h1239, checked h611, checked h616, checked h1263, checked h619, checked h621, checked h622,
  checked h623, checked h624, checked h625, checked h626, checked h1268, checked h628, checked h629, checked h1136,
  checked h1146, checked h798, checked h642, checked h647, checked h649, checked h1286, checked h652, checked h653,
  checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h1157, checked h1177,
  checked h803, checked h1302, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679,
  checked h680, checked h681, checked h682, checked h1184, checked h1191, checked h805, checked h707, checked h1303,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h1198, checked h1203,
  checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h1205,
  checked h1207, checked h817, checked h742, checked h743, checked h1208, checked h818, checked h747, checked h748,
  checked h1211, checked h1213, checked h819, checked h1238
  ] [
  9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315,
  9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 2436, 0, 0, 0, 9045315,
  9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315,
  9045315, 9045315, 9045315, 0, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315,
  9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 2436, 9045315, 0, 9045315, 9045315,
  0, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315, 0, 2436, 2436, 0,
  0, 9045315, 9045315, 9045315, 9045315, 0, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315,
  2436, 2436, 0, 0, 9045315, 0, 9045315, 9045315, 9045315, 9045315, 9045315, 9045315,
  9045315, 2436, 2436, 0, 0, 9045315, 9045315, 0, 9045315, 9045315, 9045315, 9045315,
  2436, 2436, 0, 0, 9045315, 9045315, 9045315, 9045315, 9045315, 2436, 2436, 0,
  0, 9045315, 9045315, 9045315, 0, 9045315, 2436, 2436, 0, 0, 2436, 0
  ] (by decide)

private def row1305 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 &&& primaryWord 4)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1305 : Good row1305 :=
  fastGoodSplit row1305 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h825, checked h600, checked h601, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h602,
  checked h603, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1239, checked h604, checked h605, checked h796, checked h611, checked h616, checked h617,
  checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h627,
  checked h628, checked h629, checked h798, checked h642, checked h647, checked h649, checked h651, checked h652,
  checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h803,
  checked h672, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679, checked h680,
  checked h681, checked h682, checked h683, checked h684, checked h805, checked h707, checked h712, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h719, checked h720, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h735, checked h736,
  checked h817, checked h742, checked h743, checked h744, checked h745, checked h818, checked h747, checked h748,
  checked h749, checked h750, checked h819, checked h764, checked h772, checked h820
  ] [
  5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731,
  5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 1221, 0, 1347, 1347, 5137731,
  5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731,
  5137731, 5137731, 5137731, 1347, 1347, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731,
  5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 1221, 0, 1347, 1347,
  5137731, 5137731, 5137731, 1347, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 1347,
  1221, 1221, 5137731, 5137731, 5137731, 5137731, 1347, 5137731, 5137731, 5137731, 5137731, 5137731,
  5137731, 1221, 1221, 5137731, 1347, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731, 5137731,
  1221, 1221, 1347, 1347, 5137731, 5137731, 1347, 5137731, 5137731, 5137731, 5137731, 1221,
  1221, 1347, 1347, 5137731, 5137731, 5137731, 5137731, 5137731, 1221, 1221, 1347, 1347,
  5137731, 5137731, 5137731, 1347, 1347, 5137731, 1221, 1221, 1347, 1347, 1221, 0,
  0, 1347
  ] (by decide)

private def row1306 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5), (primaryWord 3 ||| primaryWord 9)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1306 : Good row1306 :=
  fastGoodSplit row1306 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h939, checked h828, checked h832, checked h845,
  checked h846, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h835, checked h838, checked h847, checked h848, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h1262, checked h841, checked h844,
  checked h849, checked h850, checked h796, checked h617, checked h611, checked h616, checked h619, checked h621,
  checked h622, checked h623, checked h624, checked h625, checked h626, checked h628, checked h629, checked h798,
  checked h642, checked h647, checked h649, checked h852, checked h652, checked h653, checked h654, checked h655,
  checked h656, checked h657, checked h658, checked h659, checked h854, checked h856, checked h857, checked h858,
  checked h803, checked h863, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679,
  checked h680, checked h681, checked h682, checked h864, checked h865, checked h805, checked h707, checked h878,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882,
  checked h883, checked h884, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733,
  checked h734, checked h886, checked h888, checked h889, checked h890, checked h817, checked h742, checked h743,
  checked h893, checked h896, checked h897, checked h898, checked h818, checked h747, checked h748, checked h901,
  checked h819, checked h906, checked h907, checked h909, checked h910, checked h937, checked h911, checked h938
  ] [
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843,
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 0, 9987395, 9987395, 9463107,
  9463107, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843,
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9987395, 9987395, 9463107, 9463107, 41465963843, 41465963843, 41465963843,
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843,
  9988325, 0, 9987395, 9987395, 9463107, 9463107, 41465963843, 9987395, 41465963843, 41465963843, 41465963843, 41465963843,
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 9988325, 41465963843, 41465963843, 41465963843, 41465963843, 9987395,
  41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 9988325, 9987395, 9987395, 9463107, 9463107,
  41465963843, 9987395, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 9988325, 9463107,
  9463107, 41465963843, 41465963843, 9987395, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 9988325, 9987395, 9987395,
  9463107, 9463107, 41465963843, 41465963843, 41465963843, 41465963843, 41465963843, 9988325, 9988325, 9987395, 9987395, 9463107,
  9463107, 41465963843, 41465963843, 41465963843, 9987395, 9987395, 9463107, 9463107, 41465963843, 9988325, 9988325, 9987395,
  9988325, 2405, 2405, 2277, 2277, 9987395, 1347, 9463107
  ] (by decide)

private def row1307 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 5)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1307 : Good row1307 :=
  fastGoodSplit row1307 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h942, checked h828, checked h832, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h835,
  checked h838, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1263, checked h841, checked h844, checked h796, checked h617, checked h611, checked h616,
  checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h1306,
  checked h628, checked h629, checked h798, checked h642, checked h647, checked h649, checked h852, checked h652,
  checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h854,
  checked h856, checked h803, checked h863, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h805, checked h707, checked h878, checked h713,
  checked h714, checked h715, checked h716, checked h717, checked h718, checked h879, checked h882, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h886, checked h888,
  checked h817, checked h742, checked h743, checked h893, checked h896, checked h818, checked h747, checked h748,
  checked h901, checked h941, checked h819, checked h906, checked h907, checked h937
  ] [
  9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107,
  9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 2277, 0, 1347, 1347, 9463107,
  9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107,
  9463107, 9463107, 9463107, 1347, 1347, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107,
  9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 2277, 0, 1347, 1347,
  9463107, 1347, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 9463107, 0,
  2277, 2277, 9463107, 9463107, 9463107, 9463107, 1347, 9463107, 9463107, 9463107, 9463107, 9463107,
  9463107, 2277, 2277, 1347, 1347, 9463107, 1347, 9463107, 9463107, 9463107, 9463107, 9463107,
  9463107, 9463107, 2277, 2277, 9463107, 9463107, 1347, 9463107, 9463107, 9463107, 9463107, 2277,
  2277, 1347, 1347, 9463107, 9463107, 9463107, 9463107, 9463107, 2277, 2277, 1347, 1347,
  9463107, 9463107, 9463107, 1347, 1347, 9463107, 2277, 2277, 1347, 1347, 2277, 0,
  0, 1347
  ] (by decide)

private def row1308 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1308 : Good row1308 :=
  fastGoodSplit row1308 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h992, checked h845, checked h846, checked h956,
  checked h957, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h847, checked h848, checked h958, checked h959, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h1267, checked h849, checked h850,
  checked h960, checked h961, checked h796, checked h627, checked h611, checked h616, checked h878, checked h619,
  checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h628, checked h629,
  checked h962, checked h963, checked h798, checked h642, checked h647, checked h649, checked h954, checked h652,
  checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h857,
  checked h858, checked h964, checked h965, checked h803, checked h955, checked h674, checked h675, checked h676,
  checked h677, checked h678, checked h679, checked h680, checked h681, checked h682, checked h864, checked h865,
  checked h966, checked h967, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h883, checked h884, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h733, checked h734, checked h889, checked h890, checked h817, checked h742, checked h743,
  checked h897, checked h898, checked h968, checked h969, checked h818, checked h747, checked h748, checked h970,
  checked h971, checked h819, checked h909, checked h910, checked h973, checked h974, checked h938, checked h979,
  checked h980, checked h991
  ] [
  40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955,
  40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 9738597, 0, 9737539, 9737539, 9987395,
  9987395, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955,
  40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 9737539, 9737539, 9987395, 9987395, 40443077955, 40443077955, 40443077955,
  40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955,
  9738597, 0, 9737539, 9737539, 9987395, 9987395, 40443077955, 9737539, 40443077955, 40443077955, 9987395, 40443077955,
  40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 9738597, 9738597, 9987395, 9987395, 40443077955, 40443077955,
  40443077955, 40443077955, 9737539, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 9738597, 9738597, 9737539,
  9737539, 9987395, 9987395, 40443077955, 9737539, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955,
  9738597, 9738597, 9737539, 9737539, 9987395, 9987395, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955,
  9738597, 9738597, 9737539, 9737539, 40443077955, 40443077955, 40443077955, 40443077955, 40443077955, 9738597, 9738597, 9737539,
  9737539, 40443077955, 40443077955, 40443077955, 9737539, 9737539, 9987395, 9987395, 40443077955, 9738597, 9738597, 9987395,
  9987395, 9738597, 2344, 2344, 2405, 2405, 9737539, 1347, 1347, 9987395
  ] (by decide)

private def row1309 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 3 ||| primaryWord 9)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1309 : Good row1309 :=
  fastGoodSplit row1309 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h993, checked h845, checked h846, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h847,
  checked h848, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1268, checked h849, checked h850, checked h796, checked h627, checked h611, checked h616,
  checked h1306, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h628, checked h629, checked h798, checked h642, checked h647, checked h649, checked h954, checked h652,
  checked h653, checked h654, checked h655, checked h656, checked h657, checked h658, checked h659, checked h857,
  checked h858, checked h803, checked h955, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h864, checked h865, checked h805, checked h707,
  checked h1308, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h883,
  checked h884, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h889, checked h890, checked h817, checked h742, checked h743, checked h897, checked h898, checked h818,
  checked h747, checked h748, checked h819, checked h909, checked h910, checked h938
  ] [
  9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395,
  9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 2405, 0, 1347, 1347, 9987395,
  9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395,
  9987395, 9987395, 9987395, 1347, 1347, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395,
  9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 2405, 0, 1347, 1347,
  9987395, 1347, 9987395, 9987395, 0, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395, 9987395,
  2405, 2405, 9987395, 9987395, 9987395, 9987395, 1347, 9987395, 9987395, 9987395, 9987395, 9987395,
  9987395, 2405, 2405, 1347, 1347, 9987395, 1347, 9987395, 9987395, 9987395, 9987395, 9987395,
  9987395, 9987395, 2405, 2405, 1347, 1347, 9987395, 9987395, 0, 9987395, 9987395, 9987395,
  9987395, 2405, 2405, 1347, 1347, 9987395, 9987395, 9987395, 9987395, 9987395, 2405, 2405,
  1347, 1347, 9987395, 9987395, 9987395, 1347, 1347, 9987395, 2405, 2405, 2405, 0,
  0, 1347
  ] (by decide)

private def row1310 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6), (primaryWord 6 ||| primaryWord 7)] 11
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1310 : Good row1310 :=
  fastGoodSplit row1310 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1079, checked h998, checked h1003, checked h956,
  checked h957, checked h786, checked h485, checked h487, checked h495, checked h498, checked h507, checked h513,
  checked h518, checked h523, checked h526, checked h528, checked h529, checked h532, checked h534, checked h535,
  checked h538, checked h1008, checked h1011, checked h958, checked h959, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h1285, checked h1016, checked h1021,
  checked h960, checked h961, checked h796, checked h651, checked h611, checked h616, checked h852, checked h619,
  checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h954, checked h628,
  checked h629, checked h1023, checked h1025, checked h962, checked h963, checked h798, checked h642, checked h647,
  checked h649, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657, checked h658,
  checked h659, checked h964, checked h965, checked h803, checked h1027, checked h674, checked h675, checked h676,
  checked h677, checked h678, checked h679, checked h680, checked h681, checked h682, checked h1029, checked h1033,
  checked h966, checked h967, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716,
  checked h717, checked h718, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733,
  checked h734, checked h1038, checked h817, checked h742, checked h743, checked h1043, checked h1048, checked h968,
  checked h969, checked h818, checked h747, checked h748, checked h1050, checked h1052, checked h970, checked h971,
  checked h819, checked h1057, checked h1058, checked h973, checked h974, checked h1078, checked h1059, checked h991
  ] [
  40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835,
  40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 9738502, 0, 9737539, 9737539, 9598275,
  9598275, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835,
  40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 9737539, 9737539, 9598275, 9598275, 40442688835, 40442688835, 40442688835,
  40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835,
  9738502, 0, 9737539, 9737539, 9598275, 9598275, 40442688835, 9737539, 40442688835, 40442688835, 9737539, 40442688835,
  40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 9737539, 9738502, 9738502, 9737539, 9737539, 9598275,
  9598275, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 9738502,
  9738502, 9598275, 9598275, 40442688835, 9737539, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835,
  9738502, 9738502, 9737539, 9737539, 9598275, 9598275, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835,
  9738502, 9738502, 40442688835, 40442688835, 40442688835, 40442688835, 40442688835, 9738502, 9738502, 9737539, 40442688835, 40442688835,
  40442688835, 9737539, 9737539, 9598275, 9598275, 40442688835, 9738502, 9738502, 9737539, 9737539, 9598275, 9598275,
  9738502, 2344, 2344, 2310, 2310, 9737539, 1347, 9598275
  ] (by decide)

private def row1311 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 4 ||| primaryWord 6)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1311 : Good row1311 :=
  fastGoodSplit row1311 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1082, checked h998, checked h1003, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h1008,
  checked h1011, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1286, checked h1016, checked h1021, checked h796, checked h651, checked h611, checked h616,
  checked h852, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h954, checked h628, checked h629, checked h1023, checked h1025, checked h798, checked h642, checked h647,
  checked h649, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657, checked h658,
  checked h659, checked h803, checked h1027, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h681, checked h682, checked h1029, checked h1033, checked h805, checked h707,
  checked h1310, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h1038, checked h1081,
  checked h817, checked h742, checked h743, checked h1043, checked h1048, checked h818, checked h747, checked h748,
  checked h1050, checked h1052, checked h819, checked h1057, checked h1058, checked h1078
  ] [
  9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275,
  9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 2310, 0, 1347, 1347, 9598275,
  9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275,
  9598275, 9598275, 9598275, 1347, 1347, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275,
  9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 2310, 0, 1347, 1347,
  9598275, 1347, 9598275, 9598275, 1347, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275,
  1347, 2310, 2310, 1347, 1347, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275, 9598275,
  9598275, 9598275, 9598275, 2310, 2310, 9598275, 1347, 9598275, 9598275, 9598275, 9598275, 9598275,
  9598275, 9598275, 2310, 2310, 1347, 1347, 9598275, 9598275, 0, 9598275, 9598275, 9598275,
  9598275, 2310, 2310, 9598275, 9598275, 9598275, 9598275, 9598275, 2310, 2310, 1347, 1347,
  9598275, 9598275, 9598275, 1347, 1347, 9598275, 2310, 2310, 1347, 1347, 2310, 0,
  0, 1347
  ] (by decide)

private def row1312 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 5 &&& primaryWord 6)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1312 : Good row1312 :=
  fastGoodSplit row1312 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1121, checked h1083, checked h1084, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h1085,
  checked h1086, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1302, checked h1087, checked h1088, checked h796, checked h672, checked h611, checked h616,
  checked h863, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h955, checked h628, checked h629, checked h1089, checked h1090, checked h798, checked h642, checked h647,
  checked h649, checked h1027, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h658, checked h659, checked h1091, checked h1092, checked h803, checked h674, checked h675, checked h676,
  checked h677, checked h678, checked h679, checked h680, checked h681, checked h682, checked h805, checked h707,
  checked h1093, checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h733, checked h734, checked h1094, checked h1095,
  checked h817, checked h742, checked h743, checked h1096, checked h1097, checked h818, checked h747, checked h748,
  checked h1098, checked h1099, checked h819, checked h1105, checked h1112, checked h1120
  ] [
  5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067,
  5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 1287, 0, 1347, 1347, 5408067,
  5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067,
  5408067, 5408067, 5408067, 1347, 1347, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067,
  5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 1287, 0, 1347, 1347,
  5408067, 1347, 5408067, 5408067, 1347, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067, 5408067,
  1347, 1287, 1287, 1347, 1347, 5408067, 5408067, 5408067, 5408067, 1347, 5408067, 5408067,
  5408067, 5408067, 5408067, 5408067, 1287, 1287, 1347, 1347, 5408067, 5408067, 5408067, 5408067,
  5408067, 5408067, 5408067, 5408067, 1287, 1287, 5408067, 5408067, 1347, 5408067, 5408067, 5408067,
  5408067, 1287, 1287, 5408067, 5408067, 5408067, 5408067, 5408067, 1287, 1287, 1347, 1347,
  5408067, 5408067, 5408067, 1347, 1347, 5408067, 1287, 1287, 1347, 1347, 1287, 0,
  0, 1347
  ] (by decide)

private def row1313 := state 1023 0 [(primaryWord 1 &&& primaryWord 8), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1313 : Good row1313 :=
  fastGoodSplit row1313 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1122, checked h956, checked h957, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h534, checked h535, checked h538, checked h958,
  checked h959, checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573,
  checked h575, checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584,
  checked h585, checked h1303, checked h960, checked h961, checked h796, checked h712, checked h611, checked h616,
  checked h878, checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626,
  checked h1308, checked h628, checked h629, checked h962, checked h963, checked h798, checked h642, checked h647,
  checked h649, checked h1310, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h658, checked h659, checked h964, checked h965, checked h803, checked h1093, checked h674, checked h675,
  checked h676, checked h677, checked h678, checked h679, checked h680, checked h681, checked h682, checked h966,
  checked h967, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h717,
  checked h718, checked h806, checked h729, checked h730, checked h731, checked h732, checked h733, checked h734,
  checked h817, checked h742, checked h743, checked h968, checked h969, checked h818, checked h747, checked h748,
  checked h970, checked h971, checked h819, checked h973, checked h974, checked h991
  ] [
  9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539,
  9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 2344, 0, 1347, 1347, 9737539,
  9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539,
  9737539, 9737539, 9737539, 1347, 1347, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539,
  9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 2344, 0, 1347, 1347,
  9737539, 1347, 9737539, 9737539, 1347, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539, 9737539,
  0, 2344, 2344, 1347, 1347, 9737539, 9737539, 9737539, 9737539, 0, 9737539, 9737539,
  9737539, 9737539, 9737539, 9737539, 2344, 2344, 1347, 1347, 9737539, 1347, 9737539, 9737539,
  9737539, 9737539, 9737539, 9737539, 9737539, 2344, 2344, 1347, 1347, 9737539, 9737539, 9737539,
  9737539, 9737539, 9737539, 2344, 2344, 9737539, 9737539, 9737539, 9737539, 9737539, 2344, 2344,
  9737539, 9737539, 9737539, 1347, 1347, 9737539, 2344, 2344, 1347, 1347, 2344, 0,
  0, 1347
  ] (by decide)

private def row1314 := state 1023 0 [(primaryWord 1 &&& primaryWord 8)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1314 : Good row1314 :=
  fastGoodSplit row1314 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h533, checked h1123, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h534, checked h535, checked h538, checked h788, checked h547, checked h555,
  checked h561, checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579,
  checked h580, checked h582, checked h583, checked h584, checked h585, checked h1304, checked h796, checked h1305,
  checked h611, checked h616, checked h1307, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h1309, checked h628, checked h629, checked h798, checked h642, checked h647,
  checked h649, checked h1311, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h658, checked h659, checked h803, checked h1312, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h681, checked h682, checked h805, checked h707, checked h1313,
  checked h713, checked h714, checked h715, checked h716, checked h717, checked h718, checked h806, checked h729,
  checked h730, checked h731, checked h732, checked h733, checked h734, checked h817, checked h742, checked h743,
  checked h818, checked h747, checked h748, checked h819
  ] [
  1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347,
  1347, 1347, 1347, 1347, 1347, 1347, 1347, 0, 0, 1347, 1347, 1347,
  1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347,
  1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347, 1347,
  1347, 1347, 1347, 1347, 0, 0, 1347, 0, 1347, 1347, 0, 1347,
  1347, 1347, 1347, 1347, 1347, 1347, 0, 0, 0, 1347, 1347, 1347,
  1347, 0, 1347, 1347, 1347, 1347, 1347, 1347, 0, 0, 1347, 0,
  1347, 1347, 1347, 1347, 1347, 1347, 1347, 0, 0, 1347, 1347, 0,
  1347, 1347, 1347, 1347, 0, 0, 1347, 1347, 1347, 1347, 1347, 0,
  0, 1347, 1347, 1347, 1347, 0, 0, 0
  ] (by decide)

private def row1315 := state 1023 0 [(primaryWord 3 &&& primaryWord 4)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1315 : Good row1315 :=
  fastGoodSplit row1315 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h600, checked h601, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1305, checked h534, checked h535, checked h538, checked h602, checked h603,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h604,
  checked h605, checked h796, checked h611, checked h616, checked h617, checked h619, checked h621, checked h622,
  checked h623, checked h624, checked h625, checked h626, checked h627, checked h798, checked h642, checked h647,
  checked h649, checked h651, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h803, checked h672, checked h674, checked h675, checked h676, checked h677, checked h678, checked h679,
  checked h680, checked h683, checked h684, checked h805, checked h707, checked h712, checked h713, checked h714,
  checked h715, checked h716, checked h719, checked h720, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h735, checked h736, checked h817, checked h742, checked h743, checked h744, checked h745,
  checked h818, checked h749, checked h750, checked h820
  ] [
  1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221,
  1221, 1221, 1221, 1221, 1221, 1221, 1221, 0, 0, 1221, 1221, 1221,
  1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 0, 1221,
  1221, 1221, 0, 0, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 1221,
  1221, 1221, 1221, 1221, 1221, 1221, 1221, 0, 0, 1221, 1221, 1221,
  0, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 0, 1221, 1221, 1221,
  1221, 0, 1221, 1221, 1221, 1221, 1221, 1221, 1221, 0, 1221, 1221,
  1221, 1221, 1221, 1221, 1221, 0, 0, 1221, 1221, 0, 1221, 1221,
  1221, 1221, 0, 0, 1221, 1221, 1221, 1221, 1221, 0, 0, 1221,
  1221, 1221, 0, 0, 1221, 0, 0, 0
  ] (by decide)

private def row1316 := state 1023 0 [(primaryWord 3 ||| primaryWord 5), (primaryWord 3 ||| primaryWord 9)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1316 : Good row1316 :=
  fastGoodSplit row1316 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h828, checked h832, checked h845, checked h846, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h1306, checked h534, checked h535, checked h538,
  checked h835, checked h838, checked h847, checked h848, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h841, checked h844, checked h849, checked h850, checked h796,
  checked h617, checked h611, checked h616, checked h619, checked h621, checked h622, checked h623, checked h624,
  checked h625, checked h626, checked h798, checked h642, checked h647, checked h649, checked h852, checked h652,
  checked h653, checked h654, checked h655, checked h656, checked h657, checked h854, checked h856, checked h857,
  checked h858, checked h803, checked h863, checked h674, checked h675, checked h676, checked h677, checked h678,
  checked h679, checked h680, checked h864, checked h865, checked h805, checked h707, checked h878, checked h713,
  checked h714, checked h715, checked h716, checked h879, checked h882, checked h883, checked h884, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h886, checked h888, checked h889, checked h890,
  checked h817, checked h742, checked h743, checked h893, checked h896, checked h897, checked h898, checked h818,
  checked h901, checked h937, checked h911, checked h938
  ] [
  9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325,
  9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 2405, 2405, 2277, 2277, 9988325,
  9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325,
  0, 9988325, 9988325, 9988325, 2405, 2405, 2277, 2277, 9988325, 9988325, 9988325, 9988325,
  9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 2405,
  2405, 2277, 2277, 9988325, 2405, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 9988325,
  9988325, 9988325, 9988325, 9988325, 9988325, 9988325, 2405, 9988325, 9988325, 9988325, 9988325, 9988325,
  9988325, 2405, 2405, 2277, 2277, 9988325, 2405, 9988325, 9988325, 9988325, 9988325, 9988325,
  9988325, 9988325, 2277, 2277, 9988325, 9988325, 2405, 9988325, 9988325, 9988325, 9988325, 2405,
  2405, 2277, 2277, 9988325, 9988325, 9988325, 9988325, 9988325, 2405, 2405, 2277, 2277,
  9988325, 9988325, 9988325, 2405, 2405, 2277, 2277, 9988325, 2405, 2405, 0, 2277
  ] (by decide)

private def row1317 := state 1023 0 [(primaryWord 3 ||| primaryWord 5)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1317 : Good row1317 :=
  fastGoodSplit row1317 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h828, checked h832, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1307, checked h534, checked h535, checked h538, checked h835, checked h838,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h841,
  checked h844, checked h796, checked h617, checked h611, checked h616, checked h619, checked h621, checked h622,
  checked h623, checked h624, checked h625, checked h626, checked h1316, checked h798, checked h642, checked h647,
  checked h649, checked h852, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h854, checked h856, checked h803, checked h863, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h805, checked h707, checked h878, checked h713, checked h714,
  checked h715, checked h716, checked h879, checked h882, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h886, checked h888, checked h817, checked h742, checked h743, checked h893, checked h896,
  checked h818, checked h901, checked h941, checked h937
  ] [
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277,
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 0, 0, 2277, 2277, 2277,
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 0, 2277,
  2277, 2277, 0, 0, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277,
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 0, 0, 2277, 0, 2277,
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 0, 2277, 2277, 2277,
  2277, 0, 2277, 2277, 2277, 2277, 2277, 2277, 0, 0, 2277, 0,
  2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 2277, 0, 2277, 2277,
  2277, 2277, 0, 0, 2277, 2277, 2277, 2277, 2277, 0, 0, 2277,
  2277, 2277, 0, 0, 2277, 0, 0, 0
  ] (by decide)

private def row1318 := state 1023 0 [(primaryWord 3 ||| primaryWord 9), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1318 : Good row1318 :=
  fastGoodSplit row1318 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h845, checked h846, checked h956, checked h957, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h1308, checked h534, checked h535, checked h538,
  checked h847, checked h848, checked h958, checked h959, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h849, checked h850, checked h960, checked h961, checked h796,
  checked h627, checked h611, checked h616, checked h878, checked h619, checked h621, checked h622, checked h623,
  checked h624, checked h625, checked h626, checked h962, checked h963, checked h798, checked h642, checked h647,
  checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h857, checked h858, checked h964, checked h965, checked h803, checked h955, checked h674, checked h675,
  checked h676, checked h677, checked h678, checked h679, checked h680, checked h864, checked h865, checked h966,
  checked h967, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h883,
  checked h884, checked h806, checked h729, checked h730, checked h731, checked h732, checked h889, checked h890,
  checked h817, checked h742, checked h743, checked h897, checked h898, checked h968, checked h969, checked h818,
  checked h970, checked h971, checked h938, checked h979, checked h980, checked h991
  ] [
  9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597,
  9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 2344, 2344, 2405, 2405, 9738597,
  9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597,
  0, 9738597, 9738597, 9738597, 2344, 2344, 2405, 2405, 9738597, 9738597, 9738597, 9738597,
  9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 9738597, 2344,
  2344, 2405, 2405, 9738597, 2344, 9738597, 9738597, 2405, 9738597, 9738597, 9738597, 9738597,
  9738597, 9738597, 9738597, 2405, 2405, 9738597, 9738597, 9738597, 9738597, 2344, 9738597, 9738597,
  9738597, 9738597, 9738597, 9738597, 2344, 2344, 2405, 2405, 9738597, 2344, 9738597, 9738597,
  9738597, 9738597, 9738597, 9738597, 9738597, 2344, 2344, 2405, 2405, 9738597, 9738597, 9738597,
  9738597, 9738597, 9738597, 2344, 2344, 9738597, 9738597, 9738597, 9738597, 9738597, 2344, 2344,
  9738597, 9738597, 9738597, 2344, 2344, 2405, 2405, 9738597, 2405, 2405, 2344, 0,
  0, 2405
  ] (by decide)

private def row1319 := state 1023 0 [(primaryWord 3 ||| primaryWord 9)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1319 : Good row1319 :=
  fastGoodSplit row1319 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h845, checked h846, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1309, checked h534, checked h535, checked h538, checked h847, checked h848,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h849,
  checked h850, checked h796, checked h627, checked h611, checked h616, checked h1316, checked h619, checked h621,
  checked h622, checked h623, checked h624, checked h625, checked h626, checked h798, checked h642, checked h647,
  checked h649, checked h954, checked h652, checked h653, checked h654, checked h655, checked h656, checked h657,
  checked h857, checked h858, checked h803, checked h955, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h864, checked h865, checked h805, checked h707, checked h1318,
  checked h713, checked h714, checked h715, checked h716, checked h883, checked h884, checked h806, checked h729,
  checked h730, checked h731, checked h732, checked h889, checked h890, checked h817, checked h742, checked h743,
  checked h897, checked h898, checked h818, checked h938
  ] [
  2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405,
  2405, 2405, 2405, 2405, 2405, 2405, 2405, 0, 0, 2405, 2405, 2405,
  2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 0, 2405,
  2405, 2405, 0, 0, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405,
  2405, 2405, 2405, 2405, 2405, 2405, 2405, 0, 0, 2405, 0, 2405,
  2405, 0, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405, 2405,
  2405, 0, 2405, 2405, 2405, 2405, 2405, 2405, 0, 0, 2405, 0,
  2405, 2405, 2405, 2405, 2405, 2405, 2405, 0, 0, 2405, 2405, 0,
  2405, 2405, 2405, 2405, 0, 0, 2405, 2405, 2405, 2405, 2405, 0,
  0, 2405, 2405, 2405, 0, 0, 2405, 0
  ] (by decide)

private def row1320 := state 1023 0 [(primaryWord 4 ||| primaryWord 6), (primaryWord 6 ||| primaryWord 7)] 12
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1320 : Good row1320 :=
  fastGoodSplit row1320 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h998, checked h1003, checked h956, checked h957, checked h786,
  checked h485, checked h487, checked h495, checked h498, checked h507, checked h513, checked h518, checked h523,
  checked h526, checked h528, checked h529, checked h532, checked h1310, checked h534, checked h535, checked h538,
  checked h1008, checked h1011, checked h958, checked h959, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h1016, checked h1021, checked h960, checked h961, checked h796,
  checked h651, checked h611, checked h616, checked h852, checked h619, checked h621, checked h622, checked h623,
  checked h624, checked h625, checked h626, checked h954, checked h1023, checked h1025, checked h962, checked h963,
  checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654, checked h655,
  checked h656, checked h657, checked h964, checked h965, checked h803, checked h1027, checked h674, checked h675,
  checked h676, checked h677, checked h678, checked h679, checked h680, checked h1029, checked h1033, checked h966,
  checked h967, checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h806,
  checked h729, checked h730, checked h731, checked h732, checked h1038, checked h817, checked h742, checked h743,
  checked h1043, checked h1048, checked h968, checked h969, checked h818, checked h1050, checked h1052, checked h970,
  checked h971, checked h1078, checked h1059, checked h991
  ] [
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 2344, 2344, 2310, 2310, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502,
  0, 9738502, 9738502, 9738502, 2344, 2344, 2310, 2310, 9738502, 9738502, 9738502, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 2344,
  2344, 2310, 2310, 9738502, 2344, 9738502, 9738502, 2344, 9738502, 9738502, 9738502, 9738502,
  9738502, 9738502, 9738502, 2344, 2344, 2344, 2310, 2310, 9738502, 9738502, 9738502, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 2310, 2310, 9738502, 2344, 9738502, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 2344, 2344, 2310, 2310, 9738502, 9738502, 9738502,
  9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 9738502, 2344, 9738502, 9738502, 9738502,
  2344, 2344, 2310, 2310, 9738502, 2344, 2344, 2310, 2310, 2344, 0, 2310
  ] (by decide)

private def row1321 := state 1023 0 [(primaryWord 4 ||| primaryWord 6)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1321 : Good row1321 :=
  fastGoodSplit row1321 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h998, checked h1003, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1311, checked h534, checked h535, checked h538, checked h1008, checked h1011,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h1016,
  checked h1021, checked h796, checked h651, checked h611, checked h616, checked h852, checked h619, checked h621,
  checked h622, checked h623, checked h624, checked h625, checked h626, checked h954, checked h1023, checked h1025,
  checked h798, checked h642, checked h647, checked h649, checked h652, checked h653, checked h654, checked h655,
  checked h656, checked h657, checked h803, checked h1027, checked h674, checked h675, checked h676, checked h677,
  checked h678, checked h679, checked h680, checked h1029, checked h1033, checked h805, checked h707, checked h1320,
  checked h713, checked h714, checked h715, checked h716, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h1038, checked h1081, checked h817, checked h742, checked h743, checked h1043, checked h1048,
  checked h818, checked h1050, checked h1052, checked h1078
  ] [
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 0, 2310, 2310, 2310,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 2310,
  2310, 2310, 0, 0, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 0, 2310, 0, 2310,
  2310, 0, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 0, 0,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 0,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 0, 2310, 2310, 0,
  2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 2310, 0, 0, 2310,
  2310, 2310, 0, 0, 2310, 0, 0, 0
  ] (by decide)

private def row1322 := state 1023 0 [(primaryWord 5 &&& primaryWord 6)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1322 : Good row1322 :=
  fastGoodSplit row1322 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h1083, checked h1084, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1312, checked h534, checked h535, checked h538, checked h1085, checked h1086,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h1087,
  checked h1088, checked h796, checked h672, checked h611, checked h616, checked h863, checked h619, checked h621,
  checked h622, checked h623, checked h624, checked h625, checked h626, checked h955, checked h1089, checked h1090,
  checked h798, checked h642, checked h647, checked h649, checked h1027, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h1091, checked h1092, checked h803, checked h674, checked h675,
  checked h676, checked h677, checked h678, checked h679, checked h680, checked h805, checked h707, checked h1093,
  checked h713, checked h714, checked h715, checked h716, checked h806, checked h729, checked h730, checked h731,
  checked h732, checked h1094, checked h1095, checked h817, checked h742, checked h743, checked h1096, checked h1097,
  checked h818, checked h1098, checked h1099, checked h1120
  ] [
  1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287,
  1287, 1287, 1287, 1287, 1287, 1287, 1287, 0, 0, 1287, 1287, 1287,
  1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 0, 1287,
  1287, 1287, 0, 0, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287,
  1287, 1287, 1287, 1287, 1287, 1287, 1287, 0, 0, 1287, 0, 1287,
  1287, 0, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 0, 0, 0,
  1287, 1287, 1287, 1287, 0, 1287, 1287, 1287, 1287, 1287, 1287, 0,
  0, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 0,
  1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 1287, 0, 0, 1287,
  1287, 1287, 0, 0, 1287, 0, 0, 0
  ] (by decide)

private def row1323 := state 1023 0 [(primaryWord 6 ||| primaryWord 7)] 13
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1323 : Good row1323 :=
  fastGoodSplit row1323 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h956, checked h957, checked h786, checked h485, checked h487,
  checked h495, checked h498, checked h507, checked h513, checked h518, checked h523, checked h526, checked h528,
  checked h529, checked h532, checked h1313, checked h534, checked h535, checked h538, checked h958, checked h959,
  checked h788, checked h547, checked h555, checked h561, checked h563, checked h568, checked h573, checked h575,
  checked h577, checked h578, checked h579, checked h580, checked h582, checked h583, checked h584, checked h960,
  checked h961, checked h796, checked h712, checked h611, checked h616, checked h878, checked h619, checked h621,
  checked h622, checked h623, checked h624, checked h625, checked h626, checked h1318, checked h962, checked h963,
  checked h798, checked h642, checked h647, checked h649, checked h1320, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h964, checked h965, checked h803, checked h1093, checked h674,
  checked h675, checked h676, checked h677, checked h678, checked h679, checked h680, checked h966, checked h967,
  checked h805, checked h707, checked h713, checked h714, checked h715, checked h716, checked h806, checked h729,
  checked h730, checked h731, checked h732, checked h817, checked h742, checked h743, checked h968, checked h969,
  checked h818, checked h970, checked h971, checked h991
  ] [
  2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344,
  2344, 2344, 2344, 2344, 2344, 2344, 2344, 0, 0, 2344, 2344, 2344,
  2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 0, 2344,
  2344, 2344, 0, 0, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344,
  2344, 2344, 2344, 2344, 2344, 2344, 2344, 0, 0, 2344, 0, 2344,
  2344, 0, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 0, 0, 0,
  2344, 2344, 2344, 2344, 0, 2344, 2344, 2344, 2344, 2344, 2344, 0,
  0, 2344, 0, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 0, 0,
  2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344, 2344,
  2344, 2344, 0, 0, 2344, 0, 0, 0
  ] (by decide)

private def row1324 := state 1023 0 [] 14
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private theorem h1324 : Good row1324 :=
  fastGoodSplit row1324 [
  checked h784, checked h13, checked h16, checked h19, checked h22, checked h25, checked h28, checked h31,
  checked h34, checked h37, checked h40, checked h43, checked h46, checked h295, checked h296, checked h301,
  checked h303, checked h482, checked h483, checked h786, checked h485, checked h487, checked h495, checked h498,
  checked h507, checked h513, checked h518, checked h523, checked h526, checked h528, checked h529, checked h532,
  checked h1314, checked h534, checked h535, checked h538, checked h788, checked h547, checked h555, checked h561,
  checked h563, checked h568, checked h573, checked h575, checked h577, checked h578, checked h579, checked h580,
  checked h582, checked h583, checked h584, checked h796, checked h1315, checked h611, checked h616, checked h1317,
  checked h619, checked h621, checked h622, checked h623, checked h624, checked h625, checked h626, checked h1319,
  checked h798, checked h642, checked h647, checked h649, checked h1321, checked h652, checked h653, checked h654,
  checked h655, checked h656, checked h657, checked h803, checked h1322, checked h674, checked h675, checked h676,
  checked h677, checked h678, checked h679, checked h680, checked h805, checked h707, checked h1323, checked h713,
  checked h714, checked h715, checked h716, checked h806, checked h729, checked h730, checked h731, checked h732,
  checked h817, checked h742, checked h743, checked h818
  ] [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0
  ] (by decide)

end PEqualNP.Outside.L_meta_1543.Cert

theorem PEqualNP.Outside.L_meta_1543 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (2, 9)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) s → 14 ≤ s :=
  PEqualNP.Outside.L_meta_1543.Cert.rootFromWordLower PEqualNP.Outside.L_meta_1543.Cert.h1324
