import Init

/-! An interface state separates the two sides of a cut. All hidden variables
on each side are quantified by that side. A finite fooling family gives a bound
on the number of possible interface states. -/

namespace AffineElimination.InterfaceCover

structure Rectangle (X Y : Type _) where
  left : X → Prop
  right : Y → Prop

def Rectangle.accepts (q : Rectangle X Y) (x : X) (y : Y) : Prop := q.left x ∧ q.right y

def hiddenAccepts (left : X → H → S → Prop) (right : Y → K → Prop)
    (state : Y → K → S) (x : X) (y : Y) : Prop :=
  ∃ h k, left x h (state y k) ∧ right y k

def stateRectangle (left : X → H → S → Prop) (right : Y → K → Prop)
    (state : Y → K → S) (s : S) : Rectangle X Y :=
  ⟨fun x => ∃ h, left x h s, fun y => ∃ k, right y k ∧ state y k = s⟩

theorem state_union (left : X → H → S → Prop) (right : Y → K → Prop)
    (state : Y → K → S) (x : X) (y : Y) :
    hiddenAccepts left right state x y ↔ ∃ s, (stateRectangle left right state s).accepts x y := by
  constructor
  · rintro ⟨h, k, hl, hr⟩
    exact ⟨_, ⟨h, hl⟩, ⟨k, hr, rfl⟩⟩
  · rintro ⟨s, ⟨h, hl⟩, ⟨k, hr, hk⟩⟩
    exact ⟨h, k, hk ▸ hl, hr⟩

/-- Reordering interleaved existential coordinates is legitimate when every pair
of assignments to the two groups comes from an original complete assignment. -/
theorem regroup_hidden (split : W → H × K) (full : Function.Surjective split)
    (left : X → H → S → Prop) (right : Y → K → Prop) (state : Y → K → S)
    (x : X) (y : Y) :
    (∃ w, left x (split w).1 (state y (split w).2) ∧ right y (split w).2) ↔
      hiddenAccepts left right state x y := by
  constructor
  · rintro ⟨w, hl, hr⟩
    exact ⟨(split w).1, (split w).2, hl, hr⟩
  · rintro ⟨h, k, hl, hr⟩
    obtain ⟨w, hw⟩ := full (h, k)
    exact ⟨w, by simpa [hw] using hl, by simpa [hw] using hr⟩

def rectangles (left : X → H → BitVec r → Prop) (right : Y → K → Prop)
    (state : Y → K → BitVec r) : List (Rectangle X Y) :=
  List.ofFn (fun i => stateRectangle left right state (BitVec.ofFin i))

theorem rectangles_length (left : X → H → BitVec r → Prop) (right : Y → K → Prop)
    (state : Y → K → BitVec r) : (rectangles left right state).length = 2 ^ r :=
  List.length_ofFn

theorem rectangles_exact (left : X → H → BitVec r → Prop) (right : Y → K → Prop)
    (state : Y → K → BitVec r) (x : X) (y : Y) :
    hiddenAccepts left right state x y ↔ ∃ q ∈ rectangles left right state, q.accepts x y := by
  rw [state_union]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨_, List.mem_ofFn.mpr ⟨s.toFin, rfl⟩, hs⟩
  · rintro ⟨q, hq, hxy⟩
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
    exact ⟨BitVec.ofFin i, hi ▸ hxy⟩

/-- An accepting rectangle containing two diagonal points contains both crosses. -/
theorem fooling_injection {R : X → Y → Prop} (q : S → Rectangle X Y)
    (cover : ∀ x y, R x y ↔ ∃ s, (q s).accepts x y) (a : I → X) (b : I → Y)
    (diagonal : ∀ i, R (a i) (b i))
    (cross : ∀ i j, i ≠ j → ¬ (R (a i) (b j) ∧ R (a j) (b i))) :
    ∃ f : I → S, Function.Injective f := by
  let hit (i : I) := (cover (a i) (b i)).mp (diagonal i)
  let f (i : I) := Classical.choose (hit i)
  have hw (i : I) : (q (f i)).accepts (a i) (b i) := Classical.choose_spec (hit i)
  refine ⟨f, ?_⟩
  intro i j heq
  apply Classical.byContradiction
  intro hne
  have hj : (q (f i)).accepts (a j) (b j) := heq ▸ hw j
  exact cross i j hne ⟨(cover _ _).mpr ⟨_, (hw i).1, hj.2⟩,
    (cover _ _).mpr ⟨_, hj.1, (hw i).2⟩⟩

theorem state_count {R : X → Y → Prop} (q : BitVec r → Rectangle X Y)
    (cover : ∀ x y, R x y ↔ ∃ s, (q s).accepts x y) (a : Fin d → X) (b : Fin d → Y)
    (diagonal : ∀ i, R (a i) (b i))
    (cross : ∀ i j, i ≠ j → ¬ (R (a i) (b j) ∧ R (a j) (b i))) : d ≤ 2 ^ r := by
  obtain ⟨f, hf⟩ := fooling_injection q cover a b diagonal cross
  let g (i : Fin d) := (f i).toFin
  have hg : Function.Injective g := by
    intro i j eq
    apply hf
    exact congrArg BitVec.ofFin eq
  have nodup : ((List.finRange d).map g).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange d).imp (fun h eq => h (hg eq))
  have sub : (List.finRange d).map g ⊆ List.finRange (2 ^ r) := by
    intro v _
    exact List.mem_finRange v
  simpa using nodup.length_le_of_subset sub

/-- A cut with arbitrary, possibly interleaved hidden coordinates and an r-bit
state can accommodate at most `2 ^ r` members of any fooling family. -/
theorem bounded_interface {X Y : Type _} {R : X → Y → Prop} (split : W → H × K)
    (full : Function.Surjective split) (left : X → H → BitVec r → Prop)
    (right : Y → K → Prop) (state : Y → K → BitVec r)
    (rep : ∀ x y, R x y ↔ ∃ w,
      left x (split w).1 (state y (split w).2) ∧ right y (split w).2)
    (a : Fin d → X) (b : Fin d → Y) (diagonal : ∀ i, R (a i) (b i))
    (cross : ∀ i j, i ≠ j → ¬ (R (a i) (b j) ∧ R (a j) (b i))) : d ≤ 2 ^ r := by
  refine state_count (R := R) (stateRectangle left right state) ?_ a b diagonal cross
  intro x y
  exact (rep x y).trans ((regroup_hidden split full left right state x y).trans
    (state_union left right state x y))

end AffineElimination.InterfaceCover
