import Mathlib
import PEqualNP.Defs

namespace Separate1612

private theorem three_points :
    ∀ a b c d : Fin 3, a ≠ b → c ≠ d →
      ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) →
      ∀ f : Fin 3 → Bool, f a = f b → f c = f d → ∀ x y, f x = f y := by
  have core : ∀ a b c d x y : Fin 3, a ≠ b → c ≠ d →
      ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) →
      (a = c ∨ a = d ∨ b = c ∨ b = d) ∧
      (x = a ∨ x = b ∨ x = c ∨ x = d) ∧ (y = a ∨ y = b ∨ y = c ∨ y = d) := by decide
  intro a b c d hab hcd hd hr f ha hc x y
  obtain ⟨h₁,h₂,h₃⟩ := core a b c d x y hab hcd hd hr
  grind

theorem card_le_two {ι α : Type*} [LinearOrder ι] [DecidableEq α]
    (I : Finset ι) (P : Finset α) (hp : P.card ≤ 3)
    (a b : ↥I → α) (mem : ∀ g, a g ∈ P ∧ b g ∈ P)
    (cuts : ∀ g : ↥I, ∃ X : Finset α, a g ∈ X ∧ b g ∉ X ∧
      ∀ h : ↥I, h < g → (a h ∈ X ↔ b h ∈ X)) : I.card ≤ 2 := by
  classical
  by_contra! hc
  let q : Fin 3 ↪o ↥I := (Fin.castLEOrderEmb (show 3 ≤ I.card by omega)).trans
    (I.orderIsoOfFin rfl).toOrderEmbedding
  obtain ⟨e : ↥P ↪ Fin 3⟩ := Function.Embedding.nonempty_of_card_le (α := ↥P) (β := Fin 3) (by simpa using hp)
  let A (j : Fin 3) : ↥P := ⟨a (q j), (mem _).1⟩
  let B (j : Fin 3) : ↥P := ⟨b (q j), (mem _).2⟩
  let tag (X : Finset α) : Fin 3 → Bool :=
    Function.extend e (fun z : ↥P => decide (z.val ∈ X)) (fun _ => false)
  have tag_at (X : Finset α) (z : ↥P) :
      tag X (e z) = decide (z.val ∈ X) := e.injective.extend_apply _ _ z
  have h (j : Fin 3) : ∃ f : Fin 3 → Bool,
      f (e (A j)) ≠ f (e (B j)) ∧ ∀ i : Fin 3, i < j → f (e (A i)) = f (e (B i)) := by
    obtain ⟨X, ha, hb, earlier⟩ := cuts (q j)
    refine ⟨tag X, by simp [tag_at, A, B, ha, hb], ?_⟩
    intro i hi
    simpa only [tag_at, A, B] using
      (decide_eq_decide.mpr (earlier (q i) (q.strictMono hi)))
  obtain ⟨f0, sep0, _⟩ := h 0
  obtain ⟨f1, sep1, eq1⟩ := h 1
  obtain ⟨f2, sep2, eq2⟩ := h 2
  have h1 := eq1 0 (by decide)
  apply sep2
  apply three_points (e (A 0)) (e (B 0)) (e (A 1)) (e (B 1))
  · exact fun he => sep0 (congrArg f0 he)
  · exact fun he => sep1 (congrArg f1 he)
  · rintro ⟨ha,hb⟩
    exact sep1 (ha ▸ hb ▸ h1)
  · rintro ⟨ha,hb⟩
    exact sep1 (hb ▸ ha ▸ h1.symm)
  · exact eq2 0 (by decide)
  · exact eq2 1 (by decide)

end Separate1612

namespace Wire1612

open PEqualNP.CircuitLowerBounds

private def step (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]

private def Pointwise (xs ys : List Bool) := ∀ k, xs.getD k false = true → ys.getD k false = true

private theorem append_at (xs : List Bool) (x : Bool) (i : Nat) :
    (xs ++ [x]).getD i false = if i = xs.length then x else xs.getD i false := by
  by_cases h : i < xs.length
  · simp [List.getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · have hh : xs.length ≤ i := by omega
    rw [List.getD, List.getElem?_append_right hh]
    by_cases he : i = xs.length
    · simp [he]
    · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; omega)]
      simp [he, List.getD, List.getElem?_eq_none hh]

private theorem run_mono (gs : List Gate)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (hxy : Pointwise xs ys) :
    Pointwise (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih (fun q hq => basis q (by simp [hq])) _ _ (by simp [step, hlen])
    intro k hk
    simp only [step, append_at, hlen] at hk ⊢
    split at hk
    · next he =>
      simp only [he, ite_true]
      rcases basis g (by simp) with ha|ho
      · simp [ha, GateOp.eval] at hk ⊢
        exact fun q hq => hxy q (hk q hq)
      · simp [ho, GateOp.eval] at hk ⊢
        obtain ⟨q,hq,hit⟩ := hk
        exact ⟨q,hq,hxy q hit⟩
    · next he => simpa only [ite_eq_right he] using hxy k hk

theorem eval_mono {n : Nat} (gs : List Gate)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (wire : Nat) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    (Circuit.mk gs wire).eval (List.ofFn x) = true →
    (Circuit.mk gs wire).eval (List.ofFn y) = true := by
  apply run_mono gs basis _ _ (by simp) _ wire
  intro k hk
  by_cases h : k < n
  · simp [List.getD,h] at hk ⊢
    exact hxy _ hk
  · simp [List.getD,h] at hk

private theorem run_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

private theorem earlier_wire (gs : List Gate) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, List.getD, List.getElem?_append_left hi]

theorem or_operands_false {n : Nat} (gs : List Gate) (i : Fin gs.length) (x : Fin n → Bool)
    (back : ∀ w ∈ (gs.get i).inputs, w < n+i.val) (hor : (gs.get i).op = .or)
    {a b : Nat} (hab : (gs.get i).inputs = [a,b])
    (hout : (Circuit.mk gs (n+i.val)).eval (List.ofFn x) = false) :
    (Circuit.mk gs a).eval (List.ofFn x) = false ∧
    (Circuit.mk gs b).eval (List.ofFn x) = false := by
  let before := (gs.take i.val).foldl step (List.ofFn x)
  have hlen : before.length = n+i.val := by simp [before, run_length]
  have lookup (w : Nat) (hw : w < n+i.val) :
      (gs.foldl step (List.ofFn x)).getD w false = before.getD w false := by
    conv => lhs; rw [← List.take_append_drop i.val gs, List.foldl_append]
    exact earlier_wire _ before w (by rwa [hlen])
  have split : gs = gs.take i.val ++ gs.get i :: gs.drop (i.val+1) := by
    conv => lhs; rw [← List.take_append_drop i.val gs, List.drop_eq_getElem_cons i.isLt]
    rfl
  change (gs.foldl step (List.ofFn x)).getD (n+i.val) false = false at hout
  have runEq := congrArg (fun q : List Gate => q.foldl step (List.ofFn x)) split
  simp only [List.foldl_append, List.foldl_cons] at runEq
  rw [runEq] at hout
  change ((gs.drop (i.val+1)).foldl step (step before (gs.get i))).getD _ false = false at hout
  rw [earlier_wire _ _ _ (by simp [step, hlen]), step, append_at, hlen, ite_eq_left (Eq.refl _), hor, hab] at hout
  change (gs.foldl step (List.ofFn x)).getD a false = false ∧
    (gs.foldl step (List.ofFn x)).getD b false = false
  rw [lookup a (back a (by rw [hab]; simp)), lookup b (back b (by rw [hab]; simp))]
  simpa [GateOp.eval] using hout

theorem singleton_or_false {n : Nat} (gs : List Gate) (i : Fin gs.length)
    (M : Finset (Fin n)) (p : Fin n) (hp : p ∉ M)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (back : ∀ w ∈ (gs.get i).inputs, w < n+i.val) (hor : (gs.get i).op = .or)
    {a b : Nat} (hab : (gs.get i).inputs = [a,b])
    (hout : (Circuit.mk gs (n+i.val)).eval (List.ofFn (fun v => decide (v ∉ M))) = false) :
    (Circuit.mk gs a).eval (List.ofFn (fun v => decide (v=p))) = false ∧
    (Circuit.mk gs b).eval (List.ofFn (fun v => decide (v=p))) = false := by
  have quiet := or_operands_false gs i _ back hor hab hout
  have le (v : Fin n) : decide (v=p) = true → decide (v ∉ M) = true := by
    simp; rintro rfl; exact hp
  have down (w : Nat) (hw : (Circuit.mk gs w).eval (List.ofFn (fun v => decide (v ∉ M))) = false) :
      (Circuit.mk gs w).eval (List.ofFn (fun v => decide (v=p))) = false := by
    cases he : (Circuit.mk gs w).eval (List.ofFn (fun v => decide (v=p))) with
    | false => rfl
    | true => exact (Bool.false_ne_true (hw.symm.trans (eval_mono gs basis w le he))).elim
  exact ⟨down a quiet.1, down b quiet.2⟩

end Wire1612

namespace Merge1612

open PEqualNP.CircuitLowerBounds

private def active (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) : Bool :=
  (Circuit.mk gs w).eval (List.ofFn x)

private def outside (L : Finset (Fin 13)) (v : Fin 13) := decide (v ∉ L)

private def joins (gs : List Gate) (i : Fin gs.length) (S : Finset (Fin 13))
    (test : Fin 13 → Fin 13 → Bool) : Prop :=
  (gs.get i).op = .or ∧ active gs (13+i.val) (outside S) = false ∧
    ∃ a b, (gs.get i).inputs = [a,b] ∧ ∃ r ∈ S, ∃ s ∈ S,
      active gs a (test r) = true ∧ active gs b (test s) = true ∧
      ∃ X : Finset (Fin 13), r ∈ X ∧ s ∉ X ∧
        ∀ j : Fin gs.length, j < i → (gs.get j).op = .or →
          active gs (13+j.val) (outside S) = false →
          ∀ c d, (gs.get j).inputs = [c,d] → ∀ y ∈ S, ∀ z ∈ S,
            (active gs c (test y) = true ∨ active gs d (test y) = true) →
            (active gs c (test z) = true ∨ active gs d (test z) = true) → (y ∈ X ↔ z ∈ X)

private theorem merges (gs : List Gate) (S : Finset (Fin 13)) (p : Fin 13)
    (test : Fin 13 → Fin 13 → Bool) (M : Fin 13 → Finset (Fin 13)) (other : Finset (Fin 13))
    (size : (S.erase p).card ≤ 3) (outsideOther : ∀ m ∈ other, p ∉ M m)
    (point : test p = fun v => decide (v = p))
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (back : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < 13+i.val)
    (I : Finset (Fin gs.length)) (all : ∀ g ∈ I, joins gs g S test ∧
      ∃ m ∈ other, active gs (13+g.val) (outside (M m)) = false) : I.card ≤ 2 := by
  classical
  have pick (g : ↥I) := (all g.val g.property).1.2.2
  choose a b ab r hr s hs ar bs X rX sX closed using pick
  have avoid (g : ↥I) : r g ≠ p ∧ s g ≠ p := by
    obtain ⟨m, hm, off⟩ := (all g.val g.property).2
    have z := Wire1612.singleton_or_false gs g.val (M m) p (outsideOther m hm)
      basis (back g.val) (all g.val g.property).1.1 (ab g) off
    constructor
    · intro eq
      have h := ar g
      rw [eq, point] at h
      exact Bool.false_ne_true (z.1.symm.trans h)
    · intro eq
      have h := bs g
      rw [eq, point] at h
      exact Bool.false_ne_true (z.2.symm.trans h)
  apply Separate1612.card_le_two I (S.erase p) size r s
  · intro g
    exact ⟨Finset.mem_erase.mpr ⟨(avoid g).1,hr g⟩, Finset.mem_erase.mpr ⟨(avoid g).2,hs g⟩⟩
  · intro g
    refine ⟨X g, rX g, sX g, ?_⟩
    intro h earlier
    have old := (all h.val h.property).1
    exact closed g h.val earlier old.1 old.2.1 _ _ (ab h) _ (hr h) _ (hs h)
      (Or.inl (ar h)) (Or.inr (bs h))

private def line (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

private theorem leftSize : ∀ l ∈ ({4,10,12} : Finset (Fin 13)), ((line l).erase 0).card ≤ 3 := by decide
private theorem rightSize : ∀ m ∈ ({1,5,11} : Finset (Fin 13)), ((line m).erase 1).card ≤ 3 := by decide
private theorem zeroOutside : ∀ m ∈ ({1,5,11} : Finset (Fin 13)), (0 : Fin 13) ∉ line m := by decide
private theorem oneOutside : ∀ l ∈ ({4,10,12} : Finset (Fin 13)), (1 : Fin 13) ∉ line l := by decide

end Merge1612

theorem PEqualNP.Outside.L_meta_1612 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), T l 0 = (fun v : Fin 13 => decide (v = 0))) → (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), T m 1 = (fun v : Fin 13 => decide (v = 1))) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ)) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L l, ∀ y' ∈ L l, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) → I.card ≤ 2) ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L m, ∀ y' ∈ L m, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false) → I.card ≤ 2) := by
  intro L lines T gates _ zero one basis back
  have eqn : L = Merge1612.line := funext lines
  subst L
  constructor
  · intro l hl _ I hI
    exact Merge1612.merges gates _ 0 (T l) _ {1,5,11} (Merge1612.leftSize l hl)
      Merge1612.zeroOutside (zero l hl) (fun g hg => (basis g hg).1) back I hI
  · intro m hm _ I hI
    exact Merge1612.merges gates _ 1 (T m) _ {4,10,12} (Merge1612.rightSize m hm)
      Merge1612.oneOutside (one m hm) (fun g hg => (basis g hg).1) back I hI
