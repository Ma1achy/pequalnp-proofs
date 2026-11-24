import SurplusKernel

/-! Redirect the closing arcs of two disjoint rooted digraphs to the opposite roots. -/

namespace BooleanTransfer.SplicedTours

open BooleanTransfer.SurplusKernel

variable {α β : Type*}

/-- In the joined graph the distinguished left root is the outer none.
The right root is some (inr none). -/
abbrev Tail (α β : Type*) := α ⊕ Option β

private def fromLeft (E : Option α → Option α → Prop) (x : Option α) :
    Option (Tail α β) → Prop
  | none => False
  | some (.inl y) => E x (some y)
  | some (.inr none) => E x none
  | some (.inr (some _)) => False

private def fromRight (F : Option β → Option β → Prop) (x : Option β) :
    Option (Tail α β) → Prop
  | none => F x none
  | some (.inl _) => False
  | some (.inr none) => False
  | some (.inr (some y)) => F x (some y)

/-- Keep internal arcs with nonroot targets, and redirect every arc into
one of the two roots to the other root. All remaining cross arcs are absent. -/
def splice (E : Option α → Option α → Prop) (F : Option β → Option β → Prop) :
    Option (Tail α β) → Option (Tail α β) → Prop
  | none => fromLeft E none
  | some (.inl x) => fromLeft E (some x)
  | some (.inr x) => fromRight F x

/-- Tails of two anchored lists, joined by the right root. -/
def join (as : List α) (bs : List β) : List (Tail α β) :=
  as.map Sum.inl ++ Sum.inr none :: bs.map (fun b => Sum.inr (some b))

private theorem splice_left (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (x : Option α) (y : Option (Tail α β)) :
    splice E F (x.map Sum.inl) y ↔ fromLeft E x y := by cases x <;> rfl

private theorem closes_right (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (x : Option β) (bs : List β) :
    closes (splice E F) (some (.inr x)) (bs.map (fun b => .inr (some b))) ↔ closes F x bs := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
    change (_ ∧ closes (splice E F) (some (.inr (some b))) _) ↔ (_ ∧ closes F (some b) bs)
    rw [ih]
    rfl

private theorem closes_join_from (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (x : Option α) (as : List α) (bs : List β) :
    closes (splice E F) (x.map Sum.inl) (join as bs) ↔ closes E x as ∧ closes F none bs := by
  induction as generalizing x with
  | nil =>
    change (splice E F (x.map Sum.inl) (some (.inr none)) ∧ _) ↔ E x none ∧ _
    rw [splice_left, closes_right]
    rfl
  | cons a as ih =>
    change (splice E F (x.map Sum.inl) (some (.inl a)) ∧ closes (splice E F) _ (join as bs)) ↔
      (_ ∧ closes E (some a) as) ∧ _
    rw [splice_left]
    change (E x (some a) ∧ closes (splice E F) ((some a).map Sum.inl) (join as bs)) ↔ _
    rw [ih, and_assoc]

/-- The complete edge conjunction for the joined cyclic order factors. -/
theorem closes_join (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (as : List α) (bs : List β) :
    closes (splice E F) none (join as bs) ↔ closes E none as ∧ closes F none bs :=
  closes_join_from E F none as bs

private theorem right_shape (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (x : Option β) (l : List (Tail α β))
    (h : closes (splice E F) (some (.inr x)) l) :
    ∃ bs : List β, l = bs.map (fun b => .inr (some b)) := by
  induction l generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    cases v with
    | inl a => exact False.elim h.1
    | inr b =>
      cases b with
      | none => exact False.elim h.1
      | some b =>
        obtain ⟨bs, hb⟩ := ih (some b) h.2
        exact ⟨b :: bs, congrArg (List.cons _) hb⟩

private theorem left_shape (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (x : Option α) (l : List (Tail α β)) (h : closes (splice E F) (x.map Sum.inl) l) :
    ∃ as bs, l = join as bs := by
  induction l generalizing x with
  | nil =>
    exact False.elim ((splice_left E F x none).mp h)
  | cons v vs ih =>
    have arc := (splice_left E F x (some v)).mp h.1
    cases v with
    | inl a =>
      obtain ⟨as, bs, eq⟩ := ih (some a) h.2
      exact ⟨a :: as, bs, congrArg (List.cons _) eq⟩
    | inr b =>
      cases b with
      | none =>
        obtain ⟨bs, eq⟩ := right_shape E F none vs h.2
        exact ⟨[], bs, congrArg (List.cons _) eq⟩
      | some b => exact False.elim arc

/-- Every closed anchored listing traverses exactly one left block and one
right block, even before imposing coverage or absence of repeated vertices. -/
theorem blocks_of_closes (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (l : List (Tail α β)) (h : closes (splice E F) none l) :
    ∃ as bs, l = join as bs :=
  left_shape E F none l h

private theorem left_mem (a : α) (as : List α) (bs : List β) :
    Sum.inl a ∈ join as bs ↔ a ∈ as := by simp [join, List.mem_map]

private theorem right_mem (b : β) (as : List α) (bs : List β) :
    Sum.inr (some b) ∈ join as bs ↔ b ∈ bs := by simp [join, List.mem_map]

private theorem join_cover (as : List α) (bs : List β) :
    (∀ v, v ∈ join as bs) ↔ (∀ a, a ∈ as) ∧ (∀ b, b ∈ bs) := by
  constructor
  · intro h
    exact ⟨fun a => (left_mem a as bs).mp (h _), fun b => (right_mem b as bs).mp (h _)⟩
  · rintro ⟨ha, hb⟩ (a | (_ | b))
    · exact (left_mem a as bs).mpr (ha _)
    · simp [join]
    · exact (right_mem b as bs).mpr (hb _)

private theorem join_nodup (as : List α) (bs : List β) :
    (join as bs).Nodup ↔ as.Nodup ∧ bs.Nodup := by
  induction as with
  | nil =>
    have inj : Function.Injective (fun b : β => (Sum.inr (some b) : Tail α β)) := by
      intro a b h
      exact Option.some.inj (Sum.inr.inj h)
    simp [join, List.mem_map, List.nodup_map_iff inj]
  | cons a as ih =>
    change (.inl a :: join as bs).Nodup ↔ (a :: as).Nodup ∧ bs.Nodup
    simp only [List.nodup_cons, left_mem, ih, and_assoc]

/-- Both the spanning-list conditions and the edge checks factor. -/
theorem tour_join (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (as : List α) (bs : List β) :
    isTour (splice E F) (join as bs) ↔ isTour E as ∧ isTour F bs := by
  unfold isTour
  rw [join_nodup, join_cover, closes_join]
  tauto

/-- Recover the two ordinary tails by deleting the right root and discarding
entries belonging to the other side. -/
def split (l : List (Tail α β)) : List α × List β :=
  (l.filterMap (fun | .inl a => some a | .inr _ => none),
   l.filterMap (fun | .inl _ => none | .inr b => b))

@[simp] theorem split_join (as : List α) (bs : List β) :
    split (join as bs) = (as, bs) := by
  simp [split, join, List.filterMap_map]

/-- Every closed listing is reconstructed by its two projections. -/
theorem join_split (E : Option α → Option α → Prop) (F : Option β → Option β → Prop)
    (l : List (Tail α β)) (h : closes (splice E F) none l) :
    join (split l).1 (split l).2 = l := by
  obtain ⟨as, bs, rfl⟩ := blocks_of_closes E F l h
  simp

/-- Splicing and projection are mutual inverses on actual directed spanning tours. -/
def tourEquiv (E : Option α → Option α → Prop) (F : Option β → Option β → Prop) :
    ({as // isTour E as} × {bs // isTour F bs}) ≃ {l // isTour (splice E F) l} where
  toFun t := ⟨join t.1.val t.2.val, (tour_join E F _ _).mpr ⟨t.1.property, t.2.property⟩⟩
  invFun t :=
    let h := (tour_join E F _ _).mp (by
      rw [join_split E F t.val t.property.2.2]
      exact t.property)
    (⟨(split t.val).1, h.1⟩, ⟨(split t.val).2, h.2⟩)
  left_inv t := by
    rcases t with ⟨⟨as,ha⟩, ⟨bs,hb⟩⟩
    apply Prod.ext <;> apply Subtype.ext <;> simp
  right_inv t := Subtype.ext (join_split E F t.val t.property.2.2)

/-- The Boolean Hamiltonicity decision on the restricted graph is conjunction. -/
theorem exists_tour (E : Option α → Option α → Prop) (F : Option β → Option β → Prop) :
    (∃ l, isTour (splice E F) l) ↔ (∃ as, isTour E as) ∧ (∃ bs, isTour F bs) := by
  constructor
  · rintro ⟨l, h⟩
    obtain ⟨as, bs, rfl⟩ := blocks_of_closes E F l h.2.2
    have both := (tour_join E F as bs).mp h
    exact ⟨⟨as, both.1⟩, ⟨bs, both.2⟩⟩
  · rintro ⟨⟨as, ha⟩, ⟨bs, hb⟩⟩
    exact ⟨join as bs, (tour_join E F as bs).mpr ⟨ha, hb⟩⟩

end BooleanTransfer.SplicedTours

#print axioms BooleanTransfer.SplicedTours.closes_join
#print axioms BooleanTransfer.SplicedTours.blocks_of_closes
#print axioms BooleanTransfer.SplicedTours.tourEquiv
#print axioms BooleanTransfer.SplicedTours.exists_tour
