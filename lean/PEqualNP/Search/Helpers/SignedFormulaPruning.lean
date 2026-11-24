import PEqualNP.Search.Helpers.PetersenCofactors
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-! Pruning a Boolean formula when some variable occurrences are fixed. A
nonconstant restriction is determined by the surviving leaf positions. -/

namespace PEqualNP.Search.Petersen2541

inductive FormulaTree where
  | constant (value : Bool)
  | leaf
  | neg (child : FormulaTree)
  | gate (isAnd : Bool) (left right : FormulaTree)
  deriving DecidableEq

namespace FormulaTree

/-- Leaf positions distinguish different occurrences of the same variable. -/
@[reducible] def Pos : FormulaTree → Type
  | .constant _ => Empty
  | .leaf => Unit
  | .neg t => t.Pos
  | .gate _ l r => l.Pos ⊕ r.Pos

noncomputable instance posFintype (t : FormulaTree) : Fintype t.Pos := by
  induction t with
  | constant => exact inferInstanceAs (Fintype Empty)
  | leaf => exact inferInstanceAs (Fintype Unit)
  | neg _ ih => exact ih
  | gate _ l r il ir => exact inferInstanceAs (Fintype (l.Pos ⊕ r.Pos))

private def combine (isAnd a b : Bool) : Bool := if isAnd then a && b else a || b

/-- Evaluate the formula with a separate Boolean supplied at each occurrence. -/
def eval : (t : FormulaTree) → (t.Pos → Bool) → Bool
  | .constant b, _ => b
  | .leaf, x => x ()
  | .neg t, x => !(t.eval x)
  | .gate n l r, x => combine n (l.eval (fun p => x (.inl p))) (r.eval (fun p => x (.inr p)))

private def join (n : Bool) : Option Bool → Option Bool → Option Bool
  | none, b => b
  | some a, none => some a
  | some a, some b => some (combine n a b)

/-- Delete the unmarked leaves and all constant subtrees, contracting a binary
gate when only one child survives. Unary negations on surviving paths remain. -/
private def pruned : (t : FormulaTree) → (t.Pos → Bool) → (t.Pos → Bool) → Option Bool
  | .constant _, _, _ => none
  | .leaf, mark, x => if mark () then some (x ()) else none
  | .neg t, mark, x => (t.pruned mark x).map Bool.not
  | .gate n l r, mark, x => join n
    (l.pruned (fun p => mark (.inl p)) (fun p => x (.inl p)))
    (r.pruned (fun p => mark (.inr p)) (fun p => x (.inr p)))

private theorem pruned_empty (t : FormulaTree) (x : t.Pos → Bool) :
    t.pruned (fun _ => false) x = none := by
  induction t with
  | constant | leaf => rfl
  | neg t ih => exact congrArg (Option.map Bool.not) (ih x)
  | gate _ _ _ il ir => simp [pruned,il,ir,join]

private theorem pruned_congr (t : FormulaTree) (mark x y : t.Pos → Bool)
    (agree : ∀ p, mark p = true → x p = y p) : t.pruned mark x = t.pruned mark y := by
  induction t with
  | constant => rfl
  | leaf =>
    by_cases h : mark () = true
    · simp [pruned,h,agree _ h]
    · simp [pruned,h]
  | neg _ ih => exact congrArg (Option.map Bool.not) (ih mark x y agree)
  | gate _ _ _ il ir =>
    apply congrArg₂ (join _)
    · exact il _ _ _ (fun p => agree (.inl p))
    · exact ir _ _ _ (fun p => agree (.inr p))

private abbrev mix {A : Type} (active fixed x : A → Bool) := fun p => if active p then x p else fixed p

private theorem prune_restriction (t : FormulaTree) (active fixed : t.Pos → Bool) :
    (∃ b, ∀ x, t.eval (mix active fixed x) = b) ∨
    (∃ mark : t.Pos → Bool, (∀ p, mark p = true → active p = true) ∧
      ∀ x, t.pruned mark x = some (t.eval (mix active fixed x))) := by
  induction t with
  | constant b => exact .inl ⟨b,fun _ => rfl⟩
  | leaf =>
    by_cases h : active () = true
    · exact .inr ⟨fun _ => true,fun p _ => by cases p; exact h,fun _ => by simp [pruned,eval,mix,h]⟩
    · exact .inl ⟨fixed (),fun _ => by simp [eval,mix,h]⟩
  | neg t ih =>
    rcases ih active fixed with ⟨b,h⟩ | ⟨M,sub,h⟩
    · exact .inl ⟨!b,fun x => congrArg Bool.not (h x)⟩
    · exact .inr ⟨M,sub,fun x => congrArg (Option.map Bool.not) (h x)⟩
  | gate n l r il ir =>
    rcases il (fun p => active (.inl p)) (fun p => fixed (.inl p)) with ⟨b,hL⟩ | ⟨L,sL,hL⟩
    · rcases ir (fun p => active (.inr p)) (fun p => fixed (.inr p)) with ⟨c,hR⟩ | ⟨R,sR,hR⟩
      · exact .inl ⟨combine n b c, fun x => congrArg₂ (combine n)
          (hL (fun p => x (.inl p))) (hR (fun p => x (.inr p)))⟩
      · by_cases neutral : b = n
        · refine .inr ⟨Sum.elim (fun _ => false) R, ?_, ?_⟩
          · rintro (p|p) hp
            · contradiction
            · exact sR p hp
          · intro x
            change join n (l.pruned (fun _ => false) _) (r.pruned R _) = _
            rw [pruned_empty,hR,show (FormulaTree.gate n l r).eval (mix active fixed x) =
              combine n b (r.eval _) from congrArg₂ (combine n) (hL (fun p => x (.inl p))) rfl]
            subst b; cases n <;> simp [join,combine,mix]
        · refine .inl ⟨b,fun x => ?_⟩
          change combine n (l.eval _) (r.eval _) = _
          rw [hL (fun p => x (.inl p))]
          cases n <;> cases b <;> simp_all [combine]
    · rcases ir (fun p => active (.inr p)) (fun p => fixed (.inr p)) with ⟨c,hR⟩ | ⟨R,sR,hR⟩
      · by_cases neutral : c = n
        · refine .inr ⟨Sum.elim L (fun _ => false), ?_, ?_⟩
          · rintro (p|p) hp
            · exact sL p hp
            · contradiction
          · intro x
            change join n (l.pruned L _) (r.pruned (fun _ => false) _) = _
            rw [pruned_empty,hL,show (FormulaTree.gate n l r).eval (mix active fixed x) =
              combine n (l.eval _) c from congrArg₂ (combine n) rfl (hR (fun p => x (.inr p)))]
            subst c; cases n <;> simp [join,combine,mix]
        · refine .inl ⟨c,fun x => ?_⟩
          change combine n (l.eval _) (r.eval _) = _
          rw [hR (fun p => x (.inr p))]
          cases n <;> cases c <;> simp_all [combine]
      · refine .inr ⟨Sum.elim L R, ?_, ?_⟩
        · rintro (p|p) hp
          · exact sL p hp
          · exact sR p hp
        · intro x
          change join n (l.pruned L _) (r.pruned R _) = _
          rw [hL,hR]
          rfl

/-- Binary gates in the formula, with each occurrence counted separately. -/
def binaryGates : FormulaTree → ℕ
  | .constant _ | .leaf => 0
  | .neg t => t.binaryGates
  | .gate _ l r => l.binaryGates + r.binaryGates + 1

theorem card_pos_le_binaryGates_add_one (t : FormulaTree) :
    Fintype.card t.Pos ≤ t.binaryGates + 1 := by
  induction t with
  | constant => change Fintype.card Empty ≤ 1; simp
  | leaf => change Fintype.card Unit ≤ 1; simp
  | neg t ih => exact ih
  | gate n l r il ir =>
    change Fintype.card (l.Pos ⊕ r.Pos) ≤ l.binaryGates + r.binaryGates + 1 + 1
    rw [Fintype.card_sum]
    omega

/-- Number of variable leaves carrying a particular label, including either sign. -/
noncomputable def occurrences {V : Type} [DecidableEq V] (t : FormulaTree)
    (lab : t.Pos → V) (i : V) : ℕ := Fintype.card {p : t.Pos // lab p = i}

theorem sum_occurrences {V : Type} [Fintype V] [DecidableEq V] (t : FormulaTree)
    (lab : t.Pos → V) : ∑ i, t.occurrences lab i = Fintype.card t.Pos := by
  simpa only [Fintype.card_sigma, occurrences] using Fintype.card_congr (Equiv.sigmaFiberEquiv lab)

/-- Every full-support cofactor is encoded by a nonempty subset of the
occurrences of each free variable. Signs may be chosen separately at each leaf. -/
theorem occurrence_product_bound {V : Type} [DecidableEq V] (t : FormulaTree)
    (lab : t.Pos → V) (sign : t.Pos → Bool) (f : (V → Bool) → Bool)
    (computes : ∀ x, t.eval (fun p => x (lab p) != sign p) = f x)
    {S : Finset V} (hne : S.Nonempty) {k : ℕ} (family : CofactorFamily f S k) :
    k ≤ ∏ i ∈ S, (2 ^ (t.occurrences lab i) - 1) := by
  classical
  obtain ⟨fixed, inj, sens⟩ := family
  let co (j : Fin k) (x : V → Bool) := f (fun i => if i ∈ S then x i else fixed j i)
  let active (p : t.Pos) := decide (lab p ∈ S)
  let val (x : V → Bool) (p : t.Pos) := x (lab p) != sign p
  have bridge (j : Fin k) (x : V → Bool) :
      t.eval (mix active (val (fixed j)) (val x)) = co j x := by
    unfold co
    rw [← computes]
    congr 1
    funext p
    by_cases h : lab p ∈ S <;> simp [mix,active,val,h]
  have masks (j : Fin k) : ∃ M : t.Pos → Bool,
      (∀ p, M p = true → lab p ∈ S) ∧ ∀ x, t.pruned M (val x) = some (co j x) := by
    rcases t.prune_restriction active (val (fixed j)) with ⟨b,h⟩ | ⟨M,sub,ev⟩
    · obtain ⟨i,hi⟩ := hne
      obtain ⟨x,hx⟩ := sens j i hi
      exact False.elim (hx (((bridge j x).symm.trans (h (val x))).trans
        ((h _).symm.trans (bridge j _))))
    · exact ⟨M,fun p hp => of_decide_eq_true (sub p hp),
        fun x => (ev (val x)).trans (congrArg some (bridge j x))⟩
  choose mark sub ev using masks
  have used (j : Fin k) (i : ↥S) :
      (fun p : {p : t.Pos // lab p = i.val} => mark j p.val) ≠ fun _ => false := by
    intro empty
    obtain ⟨x,hx⟩ := sens j i i.property
    apply hx
    apply Option.some.inj
    change some (co j x) = some (co j _)
    rw [← ev, ← ev]
    apply pruned_congr
    intro p hp
    have hn : lab p ≠ i.val := by
      intro eq
      have habs : mark j p = false := congrFun empty ⟨p,eq⟩
      simp [hp] at habs
    simp [val, Function.update_of_ne hn]
  let Code (i : ↥S) := {M : {p : t.Pos // lab p = i.val} → Bool // M ≠ fun _ => false}
  let encode (j : Fin k) : ∀ i : ↥S, Code i := fun i => ⟨_, used j i⟩
  have injCode : Function.Injective encode := by
    intro j j' eq
    apply inj
    funext x
    change co j x = co j' x
    have same : mark j = mark j' := by
      funext p
      by_cases h : lab p ∈ S
      · let i : ↥S := ⟨lab p,h⟩
        have sameI := congrArg Subtype.val (congrFun eq i)
        exact congrFun sameI ⟨p,rfl⟩
      · have left : mark j p = false := by
          cases e : mark j p <;> simp_all [sub j p]
        have right : mark j' p = false := by
          cases e : mark j' p <;> simp_all [sub j' p]
        exact left.trans right.symm
    apply Option.some.inj
    rw [← ev, ← ev, same]
  have cardCode (i : ↥S) : Fintype.card (Code i) = 2 ^ (t.occurrences lab i) - 1 := by
    unfold Code occurrences
    rw [Fintype.card_subtype_compl]
    simp
  have hk := Fintype.card_le_of_injective encode injCode
  rw [← Finset.prod_coe_sort S (fun i => 2 ^ (t.occurrences lab i) - 1)]
  simpa only [Fintype.card_fin, Fintype.card_pi, cardCode] using hk

end FormulaTree

end PEqualNP.Search.Petersen2541
