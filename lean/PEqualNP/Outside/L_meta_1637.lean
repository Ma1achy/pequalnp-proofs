import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


theorem raw {N : Nat} (gs : List Gate) (x : Fin N → Bool) (p : Fin N) :
    Circuit.eval ⟨gs,p.val⟩ (List.ofFn x) = x p := by
  change (wiresFrom gs (List.ofFn x)).getD p.val false = _
  rw [getD_wiresFrom_lt _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp)]
  simp

theorem past {N : Nat} (gs : List Gate) (x : Fin N → Bool) (w : Nat)
    (h : N + gs.length ≤ w) :
    Circuit.eval ⟨gs,w⟩ (List.ofFn x) = false := by
  change (wiresFrom gs (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [length_wiresFrom] using h)

theorem or_iff {N : Nat} (gs : List Gate) (x : Fin N → Bool) (k : Fin gs.length)
    (hop : (gs.get k).op = .or) (hw : ∀ w ∈ (gs.get k).inputs, w < N + k.val) :
    Circuit.eval ⟨gs,N+k.val⟩ (List.ofFn x) = true ↔
    ∃ w ∈ (gs.get k).inputs, Circuit.eval ⟨gs,w⟩ (List.ofFn x) = true := by
  change (wiresFrom gs (List.ofFn x)).getD (N + k.val) false = true ↔
    ∃ w ∈ gs[k.val].inputs, (wiresFrom gs (List.ofFn x)).getD w false = true
  have ev := getD_wiresFrom_gate gs (List.ofFn x) k.val k.isLt
  simp only [List.length_ofFn] at ev
  rw [ev, show gs[k.val].op = .or from hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
  constructor
  · rintro ⟨w,mem,hit⟩
    refine ⟨w,mem,?_⟩
    simpa only [ite_eq_left (hw w mem)] using hit
  · rintro ⟨w,mem,hit⟩
    exact ⟨w,mem,by simpa only [ite_eq_left (hw w mem)] using hit⟩

lemma raw_tests {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 : Fin N)
    (T : Fin N → Fin N → Fin N → Bool)
    (hT : ∀ (t p v : Fin N), T t p v = true ↔
      (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨
        (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
        (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t)))
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hraw : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p)
    (TS : Fin N → Fin N → ℕ → Prop)
    (hTS : ∀ l m w, TS l m w ↔
      ev w (fun v => decide (v ∉ L l)) = false ∧
      ev w (fun v => decide (v ∉ L m)) = false ∧
      (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)
    (l m : Fin N) (hl : p0 ∈ L l ∧ p1 ∉ L l) (hm : p1 ∈ L m ∧ p0 ∉ L m) :
    (∀ p : Fin N, TS l m (p : ℕ) ↔ p ∈ L l ∧ p ∈ L m) ∧
    (∀ p : Fin N, p ∈ L l → p ∈ L m →
      (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧
      (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) := by
  constructor
  · intro p
    rw [hTS]
    constructor
    · rintro ⟨hl0, hm0, _, _⟩
      exact ⟨by simpa [hraw] using hl0, by simpa [hraw] using hm0⟩
    · rintro ⟨hpl, hpm⟩
      refine ⟨by simp [hraw, hpl], by simp [hraw, hpm], ⟨p, hpl, ?_⟩, ⟨p, hpm, ?_⟩⟩
      · exact (hraw p (T l p)).trans ((hT l p p).mpr (Or.inl rfl))
      · exact (hraw p (T m p)).trans ((hT m p p).mpr (Or.inl rfl))
  · intro p hpl hpm
    have hp0 : p ≠ p0 := fun e => hm.2 (e ▸ hpm)
    have hp1 : p ≠ p1 := fun e => hl.2 (e ▸ hpl)
    have point (t : Fin N) (h : ¬ (p0 ∈ L t ∧ p1 ∈ L t)) (s : Fin N) :
        ev (p : ℕ) (T t s) = true ↔ s = p := by
      rw [hraw, hT]
      constructor
      · rintro (e | h0 | h1 | hboth)
        · exact e.symm
        · exact (hp0 h0.2.2).elim
        · exact (hp1 h1.2.2.2).elim
        · exact (h ⟨hboth.1, hboth.2.1⟩).elim
      · exact fun e => Or.inl e.symm
    exact ⟨fun s _ => point l (fun h => hl.2 h.2) s,
      fun s _ => point m (fun h => hm.2 h.1) s⟩

end PEqualNP.Outside.L_meta_1637

theorem PEqualNP.Outside.L_meta_1637 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ TS : Fin N → Fin N → ℕ → Prop,
    (∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)) →
    ∀ Hg : Fin N → Fin N → Fin gates.length → Prop,
    (∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)))) →
    ∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  intro q N L i0 p0 p1 hq hN hsize hint hline hne h0 h1 T hT gates hops hlen hw ev hev TS hTS Hg hHg l m hl hm
  classical
  have hraw : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hev]
    exact PEqualNP.Outside.L_meta_1637.raw gates x p
  have hpts : (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m →
        (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧
        (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) := by
    exact PEqualNP.Outside.L_meta_1637.raw_tests L p0 p1 T hT ev hraw TS hTS l m hl hm
  refine ⟨hpts.1, hpts.2, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ht
    obtain ⟨_, _, hp, hq'⟩ := (hTS l m w).mp ht
    by_cases hir : w < N
    · let p : Fin N := ⟨w, hir⟩
      obtain ⟨hpl, hpm⟩ := (hpts.1 p).mp ht
      exact ⟨w, fun _ h _ => h, Or.inl ⟨p, hpl, hpm, rfl⟩,
        fun _ _ h => h, fun _ _ h => h, hp, hq'⟩
    by_cases hout : N + gates.length ≤ w
    · obtain ⟨p, _, h⟩ := hp
      rw [hev, PEqualNP.Outside.L_meta_1637.past gates (T l p) w hout] at h
      contradiction
    let k : Fin gates.length := ⟨w - N, by omega⟩
    have hk : N + (k : ℕ) = w := by dsimp [k]; omega
    by_cases hex : (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ e ∈ (gates.get k).inputs, TS l m e
    · obtain ⟨hop, e, hem, het⟩ := hex
      obtain ⟨v, hv, hkind, hvl, hvm, hpl, hpm⟩ :=
        ih e (hk ▸ hw k e hem) het
      have lift (x : Fin N → Bool) (htest : ev e x = true) : ev w x = true := by
        rw [← hk, hev]
        apply (PEqualNP.Outside.L_meta_1637.or_iff gates x k hop (hw k)).2
        exact ⟨e, hem, (hev e x) ▸ htest⟩
      refine ⟨v, ?_, hkind, fun s hs h => lift _ (hvl s hs h),
        fun s hs h => lift _ (hvm s hs h), hpl, hpm⟩
      intro Z hwZ hc
      exact hv Z (hc k (hk.symm ▸ hwZ) e hem) hc
    · have hh : Hg l m k := by
        apply (hHg l m k).2
        refine ⟨hk.symm ▸ ht, ?_⟩
        rcases (hops (gates.get k) (List.get_mem gates k)).1 with ha | ho
        · exact Or.inl ha
        · exact Or.inr ⟨ho, fun e he h => hex ⟨ho, e, he, h⟩⟩
      exact ⟨w, fun _ h _ => h, Or.inr ⟨k, hk.symm, hh⟩,
        fun _ _ h => h, fun _ _ h => h, hp, hq'⟩
