import Init

/-! Affine systems over visible bits with existential helpers.
An equation lists the coordinates summed over F₂. An empty system describes
all assignments, and an inconsistent system describes the empty set. -/

namespace AffineElimination.HelperCover

structure Row (n : Nat) where
  support : List (Fin n)
  rhs : Bool

structure ExtendedRow (n : Nat) where
  row : Row n
  helperCoeff : Bool

abbrev Flat (n : Nat) := List (Row n)
abbrev ExtendedFlat (n : Nat) := List (ExtendedRow n)

def dot (s : List (Fin n)) (y : Fin n → Bool) : Bool :=
  s.foldl (fun p i => p ^^ y i) false

def contains (f : Flat n) (y : Fin n → Bool) : Prop :=
  ∀ r ∈ f, dot r.support y = r.rhs

def containsExt (f : ExtendedFlat n) (y : Fin n → Bool) (b : Bool) : Prop :=
  ∀ e ∈ f, (dot e.row.support y ^^ (e.helperCoeff && b)) = e.row.rhs

def covers (fs : List (Flat n)) (y : Fin n → Bool) : Prop := ∃ f ∈ fs, contains f y

def coversExt (fs : List (ExtendedFlat n)) (y : Fin n → Bool) (b : Bool) : Prop :=
  ∃ f ∈ fs, containsExt f y b

def sliceRow (b : Bool) (e : ExtendedRow n) : Row n :=
  ⟨e.row.support, e.row.rhs ^^ (e.helperCoeff && b)⟩

def slice (b : Bool) (f : ExtendedFlat n) : Flat n := f.map (sliceRow b)

theorem slice_contains (b : Bool) (f : ExtendedFlat n) (y : Fin n → Bool) :
    contains (slice b f) y ↔ containsExt f y b := by
  have cancel (a h d : Bool) : (a = (d ^^ h)) ↔ ((a ^^ h) = d) := by
    cases a <;> cases h <;> cases d <;> decide
  simp [contains, slice, containsExt, sliceRow, cancel]

theorem append_contains (f g : Flat n) (y : Fin n → Bool) :
    contains (f ++ g) y ↔ contains f y ∧ contains g y := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left g hr),
           fun r hr => h r (List.mem_append_right f hr)⟩
  · rintro ⟨hf, hg⟩ r hr
    exact (List.mem_append.mp hr).elim (hf r) (hg r)

/-- Intersection of two unions, distributing over their listed systems. -/
def meet (fs gs : List (Flat n)) : List (Flat n) :=
  fs.flatMap (fun f => gs.map (fun g => f ++ g))

theorem meet_length (fs gs : List (Flat n)) :
    (meet fs gs).length = fs.length * gs.length := by
  induction fs with
  | nil => simp [meet]
  | cons f fs ih => simp [meet] at ih ⊢; rw [ih, Nat.succ_mul, Nat.add_comm]

theorem meet_covers (fs gs : List (Flat n)) (y : Fin n → Bool) :
    covers (meet fs gs) y ↔ covers fs y ∧ covers gs y := by
  constructor
  · rintro ⟨flat, hflat, hcontains⟩
    obtain ⟨f, hf, hrow⟩ := List.mem_flatMap.mp hflat
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hrow
    subst flat
    obtain ⟨h₀, h₁⟩ := (append_contains _ _ y).mp hcontains
    exact ⟨⟨f, hf, h₀⟩, ⟨g, hg, h₁⟩⟩
  · rintro ⟨⟨f, hf, h₀⟩, ⟨g, hg, h₁⟩⟩
    exact ⟨_, List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨g, hg, rfl⟩⟩,
      (append_contains _ _ y).mpr ⟨h₀, h₁⟩⟩

/-- Intersect each slice at false with each slice at true. -/
def paired (fs gs : List (ExtendedFlat n)) : List (Flat n) :=
  meet (fs.map (slice false)) (gs.map (slice true))

theorem paired_length (fs gs : List (ExtendedFlat n)) :
    (paired fs gs).length = fs.length * gs.length := by
  simp [paired, meet_length]

theorem paired_covers (fs gs : List (ExtendedFlat n)) (y : Fin n → Bool) :
    covers (paired fs gs) y ↔ coversExt fs y false ∧ coversExt gs y true := by
  have hs (b : Bool) (ls : List (ExtendedFlat n)) :
      covers (ls.map (slice b)) y ↔ coversExt ls y b := by
    constructor
    · rintro ⟨g, hg, hh⟩
      obtain ⟨f, hf, he⟩ := List.mem_map.mp hg
      subst g
      exact ⟨f, hf, (slice_contains b f y).mp hh⟩
    · rintro ⟨f, hf, hh⟩
      exact ⟨_, List.mem_map.mpr ⟨f, hf, rfl⟩, (slice_contains b f y).mpr hh⟩
  rw [paired, meet_covers, hs, hs]

/-- A helper value satisfying the conjunction exists exactly when the visible
assignment avoids all of the paired forbidden systems. -/
theorem exact_projection (fs : List (ExtendedFlat n)) (y : Fin n → Bool) :
    (∃ b : Bool, ¬ coversExt fs y b) ↔ ¬ covers (paired fs fs) y := by
  rw [paired_covers]
  constructor
  · rintro ⟨b, hb⟩ both
    cases b with
    | false => exact hb both.1
    | true => exact hb both.2
  · intro h
    by_cases h₀ : coversExt fs y false
    · exact ⟨true, fun h₁ => h ⟨h₀, h₁⟩⟩
    · exact ⟨false, h₀⟩

/-- Any lower bound for explicit forbidden-flat descriptions of `accept` transfers
to the square of the number of extended flats used with one helper. -/
theorem lower_bound_transfer (accept : (Fin n → Bool) → Prop) (lower : Nat)
    (minCover : ∀ gs : List (Flat n),
      (∀ y, accept y ↔ ¬ covers gs y) → lower ≤ gs.length)
    (fs : List (ExtendedFlat n))
    (rep : ∀ y, accept y ↔ ∃ b : Bool, ¬ coversExt fs y b) :
    lower ≤ fs.length * fs.length := by
  rw [← paired_length fs fs]
  exact minCover _ (fun y => (rep y).trans (exact_projection fs y))

/-! Explicit elimination of every valuation of an h-bit helper word. -/

structure MultiRow (n h : Nat) where
  row : Row n
  hidden : List (Fin h)

abbrev MultiFlat (n h : Nat) := List (MultiRow n h)

def hiddenDot (s : List (Fin h)) (z : BitVec h) : Bool :=
  dot s (fun i => z.getLsbD i.val)

def coversMulti (fs : List (MultiFlat n h)) (y : Fin n → Bool) (z : BitVec h) : Prop :=
  ∃ f ∈ fs, ∀ e ∈ f, (dot e.row.support y ^^ hiddenDot e.hidden z) = e.row.rhs

def sliceAt (z : BitVec h) (f : MultiFlat n h) : Flat n :=
  f.map (fun e => ⟨e.row.support, e.row.rhs ^^ hiddenDot e.hidden z⟩)

theorem covers_at (fs : List (MultiFlat n h)) (z : BitVec h) (y : Fin n → Bool) :
    covers (fs.map (sliceAt z)) y ↔ coversMulti fs y z := by
  have cancel (a h d : Bool) : (a = (d ^^ h)) ↔ ((a ^^ h) = d) := by
    cases a <;> cases h <;> cases d <;> decide
  have hs (f : MultiFlat n h) : contains (sliceAt z f) y ↔
      ∀ e ∈ f, (dot e.row.support y ^^ hiddenDot e.hidden z) = e.row.rhs := by
    simp [contains, sliceAt, cancel]
  constructor
  · rintro ⟨g, hg, hh⟩
    obtain ⟨f, hf, he⟩ := List.mem_map.mp hg
    subst g
    exact ⟨f, hf, (hs f).mp hh⟩
  · rintro ⟨f, hf, hh⟩
    exact ⟨_, List.mem_map.mpr ⟨f, hf, rfl⟩, (hs f).mpr hh⟩

def overWords (fs : List (MultiFlat n h)) : List (BitVec h) → List (Flat n)
  | [] => [[]]
  | z :: zs => meet (fs.map (sliceAt z)) (overWords fs zs)

theorem overWords_length (fs : List (MultiFlat n h)) (zs : List (BitVec h)) :
    (overWords fs zs).length = fs.length ^ zs.length := by
  induction zs with
  | nil => simp [overWords]
  | cons z zs ih => simp [overWords, meet_length, ih, Nat.pow_succ, Nat.mul_comm]

theorem overWords_covers (fs : List (MultiFlat n h)) (zs : List (BitVec h))
    (y : Fin n → Bool) : covers (overWords fs zs) y ↔ ∀ z ∈ zs, coversMulti fs y z := by
  induction zs with
  | nil => simp [overWords, covers, contains]
  | cons z zs ih => simp [overWords, meet_covers, covers_at, ih]

/-- The unsimplified cover uses one choice of parent flat for each helper valuation. -/
def allWords (h : Nat) : List (BitVec h) := List.ofFn BitVec.ofFin

theorem allWords_mem (z : BitVec h) : z ∈ allWords h :=
  List.mem_ofFn.mpr ⟨z.toFin, rfl⟩

theorem allWords_length (h : Nat) : (allWords h).length = 2 ^ h := List.length_ofFn

theorem exact_multi_projection (fs : List (MultiFlat n h)) (y : Fin n → Bool) :
    (∃ z, ¬ coversMulti fs y z) ↔ ¬ covers (overWords fs (allWords h)) y := by
  rw [overWords_covers]
  constructor
  · rintro ⟨z, hz⟩ hall
    exact hz (hall z (allWords_mem z))
  · intro hn
    apply Classical.byContradiction
    intro hn'
    apply hn
    intro z _
    exact Classical.byContradiction (fun hz => hn' ⟨z, hz⟩)

theorem multi_lower_bound_transfer (accept : (Fin n → Bool) → Prop) (lower : Nat)
    (minCover : ∀ gs : List (Flat n),
      (∀ y, accept y ↔ ¬ covers gs y) → lower ≤ gs.length)
    (fs : List (MultiFlat n h))
    (rep : ∀ y, accept y ↔ ∃ z, ¬ coversMulti fs y z) :
    lower ≤ fs.length ^ (2 ^ h) := by
  rw [← allWords_length, ← overWords_length]
  exact minCover _ (fun y => (rep y).trans (exact_multi_projection fs y))

end AffineElimination.HelperCover
