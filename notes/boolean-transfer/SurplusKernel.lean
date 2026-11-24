import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Forced directed arc contraction for anchored cyclic listings.
The anchor is not repeated in the tail. A closing edge back to the anchor is required. -/

namespace BooleanTransfer.SurplusKernel

variable {α : Type*}

/-- Starting at x, visit all of l in order and return to the distinguished anchor. -/
def closes (E : Option α → Option α → Prop) : Option α → List α → Prop
  | x, [] => E x none
  | x, y :: ys => E x (some y) ∧ closes E (some y) ys

/-- A spanning directed cycle written uniquely from the specified anchor. -/
def isTour (E : Option α → Option α → Prop) (l : List α) : Prop :=
  l.Nodup ∧ (∀ i, i ∈ l) ∧ closes E none l

/-- Original vertices are u = none, v = some none, and the unaffected vertices.
The source end of the merged vertex is v and its destination end is u. -/
def src : Option α → Option (Option α)
  | none => some none
  | some i => some (some i)

def dst : Option α → Option (Option α)
  | none => none
  | some i => some (some i)

def contract (E : Option (Option α) → Option (Option α) → Prop)
    (x y : Option α) : Prop := E (src x) (dst y)

def expand (l : List α) : List (Option α) := none :: l.map some

def shrink (l : List (Option α)) : List α := l.tail.filterMap id

private theorem closes_map (E : Option (Option α) → Option (Option α) → Prop)
    (x : Option α) (l : List α) :
    closes E (src x) (l.map some) ↔ closes (contract E) x l := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change (E (src x) (some (some i)) ∧ closes E (src (some i)) (l.map some)) ↔
      (E (src x) (some (some i)) ∧ closes (contract E) (some i) l)
    rw [ih]

private theorem expand_covers (l : List α) :
    (∀ i, i ∈ expand l) ↔ ∀ i, i ∈ l := by
  constructor
  · intro all i
    simpa [expand] using all (some i)
  · intro all i
    cases i with
    | none => simp [expand]
    | some i => simpa [expand] using all i

/-- On correctly expanded listings the original and contracted edge tests agree. -/
theorem expand_iff (E : Option (Option α) → Option (Option α) → Prop)
    (arc : E none (some none)) (l : List α) :
    isTour E (expand l) ↔ isTour (contract E) l := by
  have nd : (expand l).Nodup ↔ l.Nodup := by
    simp [expand, List.nodup_map_iff (Option.some_injective α)]
  unfold isTour
  rw [nd, expand_covers]
  change (_ ∧ _ ∧ E none (some none) ∧ closes E (src none) (l.map some)) ↔ _
  rw [closes_map, and_iff_right arc]

private theorem map_filter_some (l : List (Option α)) (hn : none ∉ l) :
    (l.filterMap id).map some = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases x with
    | none => simp at hn
    | some x =>
      have tail : none ∉ l := fun h => hn (List.mem_cons_of_mem _ h)
      exact congrArg (List.cons (some x)) (ih tail)

private theorem shrink_expand (l : List α) : shrink (expand l) = l := by
  simp [shrink, expand, List.filterMap_map]

private theorem expand_shrink (E : Option (Option α) → Option (Option α) → Prop)
    (only : ∀ w, E none w → w = some none) (l : List (Option α)) (ht : isTour E l) :
    expand (shrink l) = l := by
  rcases l with _ | ⟨x,l⟩
  · have impossible := ht.2.1 none
    simp at impossible
  · have edge : E none (some x) := ht.2.2.1
    have hx : x = none := Option.some.inj (only _ edge)
    subst x
    have tail : none ∉ l := (List.nodup_cons.mp ht.1).1
    exact congrArg (List.cons none) (map_filter_some l tail)

/-- Inserting v after u and deleting it are mutually inverse on tours.
Additional incoming arcs to v and other outgoing arcs from v are unrestricted. -/
def tourEquiv (E : Option (Option α) → Option (Option α) → Prop)
    (arc : E none (some none)) (only : ∀ w, E none w → w = some none) :
    {l // isTour (contract E) l} ≃ {l // isTour E l} where
  toFun l := ⟨expand l.val, (expand_iff E arc l.val).2 l.property⟩
  invFun l := ⟨shrink l.val, (expand_iff E arc _).1 (by rw [expand_shrink E only _ l.property]; exact l.property)⟩
  left_inv l := Subtype.ext (shrink_expand l.val)
  right_inv l := Subtype.ext (expand_shrink E only l.val l.property)

theorem contract_iff (E : Option (Option α) → Option (Option α) → Prop)
    (arc : E none (some none)) (only : ∀ w, E none w → w = some none) :
    (∃ l, isTour E l) ↔ ∃ l, isTour (contract E) l := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨_, ((tourEquiv E arc only).symm ⟨l, hl⟩).property⟩
  · rintro ⟨l, hl⟩
    exact ⟨_, (tourEquiv E arc only ⟨l, hl⟩).property⟩

private def liftArc : (Option α × Option α) ↪ (Option (Option α) × Option (Option α)) where
  toFun e := (src e.1, dst e.2)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have h₁ : src a = src c := congrArg Prod.fst h
    have h₂ : dst b = dst d := congrArg Prod.snd h
    cases a <;> cases c <;> cases b <;> cases d <;> simp_all [src, dst]

/-- Store precisely the arcs allowed by the contraction relation. -/
def contractEdges [Fintype α] [DecidableEq α]
    (E : Finset (Option (Option α) × Option (Option α))) : Finset (Option α × Option α) :=
  Finset.univ.filter fun e => (src e.1, dst e.2) ∈ E

/-- One original arc is consumed and each retained arc has a distinct original preimage. -/
theorem arc_count [Fintype α] [DecidableEq α] (E : Finset (Option (Option α) × Option (Option α)))
    (arc : (none, some none) ∈ E) : (contractEdges E).card + 1 ≤ E.card := by
  classical
  let image := (contractEdges E).map liftArc
  have fresh : (none, some none) ∉ image := by
    intro mem
    obtain ⟨⟨x,y⟩, _, h⟩ := Finset.mem_map.mp mem
    have h₁ : src x = none := congrArg Prod.fst h
    cases x <;> contradiction
  have sub : insert (none, some none) image ⊆ E := by
    intro e he
    rcases Finset.mem_insert.mp he with h | h
    · exact h ▸ arc
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp h
      exact (Finset.mem_filter.mp ht).2
  have bound := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem fresh] at bound
  simpa [image] using bound

/-- The absolute surplus cap is inherited when two vertices become one. -/
theorem surplus_bound [Fintype α] [DecidableEq α] (E : Finset (Option (Option α) × Option (Option α)))
    (k : ℕ) (arc : (none, some none) ∈ E) (bound : E.card ≤ Fintype.card (Option (Option α)) + k) :
    (contractEdges E).card ≤ Fintype.card (Option α) + k := by
  have step := arc_count E arc
  rw [Fintype.card_option] at bound
  omega

/-- The reduced digraph has at most k vertices and 2k arcs if every source
has at least two outgoing arcs and the original surplus cap still holds. -/
theorem kernel_size {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (k : ℕ)
    (minimum : ∀ v, 2 ≤ (E.filter (fun e => e.1 = v)).card)
    (surplus : E.card ≤ Fintype.card V + k) :
    Fintype.card V ≤ k ∧ E.card ≤ 2*k := by
  classical
  have count : E.card = ∑ v : V, (E.filter (fun e => e.1 = v)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (by simp)
  have low := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => minimum v)
  rw [← count] at low
  simp at low
  omega

end BooleanTransfer.SurplusKernel

#print axioms BooleanTransfer.SurplusKernel.expand_iff
#print axioms BooleanTransfer.SurplusKernel.tourEquiv
#print axioms BooleanTransfer.SurplusKernel.kernel_size
