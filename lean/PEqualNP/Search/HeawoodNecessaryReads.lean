import PEqualNP.Outside.L_meta_1483

/-! For the exact edge list of L-meta-582, every circuit of size at most 26
has a raw input with a unique reader in the output cone. This reader combines
that input with an earlier derived wire. The AND and OR cases force different
truth-table entries on the derived wire. -/

namespace PEqualNP.Search.HeawoodNecessaryReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1483

/-- The desk's oriented list, with points first and lines second. -/
def edges : List (Fin 14 × Fin 14) :=
  [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
   (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
   (6,8),(6,9),(6,11)]

def target (a : Fin 14 → Bool) : Bool :=
  edges.any fun p => a p.1 && a p.2

def deskEdges : List (ℕ × ℕ) := edges.map fun p => (p.1.val, p.2.val)

theorem target_iff (a : Fin 14 → Bool) : target a = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ deskEdges ∧ a u = true ∧ a v = true := by
  simp only [target, List.any_eq_true, Bool.and_eq_true, deskEdges, List.mem_map]
  constructor
  · rintro ⟨⟨u,v⟩, hm, hu, hv⟩
    exact ⟨u,v,⟨(u,v),hm,rfl⟩,hu,hv⟩
  · rintro ⟨u,v,⟨⟨i,j⟩,hm,he⟩,hu,hv⟩
    obtain ⟨rfl,rfl⟩ : i = u ∧ j = v :=
      ⟨Fin.ext (congrArg Prod.fst he), Fin.ext (congrArg Prod.snd he)⟩
    exact ⟨_,hm,hu,hv⟩

theorem graphEval_of_desk {C : Circuit}
    (h : ∀ a : Fin 14 → Bool, C.eval (List.ofFn a) = true ↔
      ∃ u v : Fin 14, (u.val,v.val) ∈ deskEdges ∧ a u = true ∧ a v = true) :
    GraphEval C Ha := by
  have adj : ∀ u v : Fin 14, Ha.Adj u v ↔
      (u.val,v.val) ∈ deskEdges ∨ (v.val,u.val) ∈ deskEdges := by decide
  intro a
  change C.eval (List.ofFn a) = true ↔ _
  rw [h a]
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    exact ⟨u,v,(adj u v).2 (Or.inl huv),hu,hv⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    rcases (adj u v).1 huv with h | h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩

private def mask (u v w : Fin 14) (fixed value : Bool) (i : Fin 14) :=
  if i = u then value else if i = v then fixed else decide (i = w)

/-- For either fixed value of a second raw input, the target is sensitive to the first. -/
theorem sensitive (u v : Fin 14) (ne : u ≠ v) (f : Bool) :
    ∃ a b : Fin 14 → Bool, a v = f ∧ b v = f ∧
      (∀ i, i ≠ u → a i = b i) ∧ target a ≠ target b := by
  have cert : ∀ u v : Fin 14, u ≠ v → ∀ f : Bool, ∃ w : Fin 14,
      target (mask u v w f false) ≠ target (mask u v w f true) := by decide
  obtain ⟨w,hw⟩ := cert u v ne f
  exact ⟨_,_,by simp [mask,Ne.symm ne],by simp [mask,Ne.symm ne],
    fun i hi => by simp [mask,hi],hw⟩

private theorem pair_list {l : List ℕ} {u v : ℕ} (hu : u ∈ l) (hv : v ∈ l)
    (ne : u ≠ v) (len : l.length ≤ 2) : l = [u,v] ∨ l = [v,u] := by
  cases l with
  | nil => simp at hu
  | cons i l =>
    cases l with
    | nil => simp_all
    | cons j l =>
      cases l with
      | cons k l => simp at len
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-- A live gate combining distinct raw inputs forces two different live readers of either input. -/
theorem branch_of_raw_pair {C : Circuit} (hC : Monotone2 C)
    (he : ∀ a, val C a C.output = target a) {u v : Fin 14} (ne : u ≠ v) {q : ℕ}
    (hu : LNext 14 C u.val q) (hv : LNext 14 C v.val q) :
    Branch 14 C u.val := by
  by_contra hn
  obtain ⟨⟨huq,p,g,hg,eq,hug⟩,live⟩ := hu
  obtain ⟨⟨hvq,p',g',hg',eq',hvg⟩,_⟩ := hv
  have ep : p' = p := by omega
  subst p'
  have eg : g' = g := Option.some.inj (hg'.symm.trans hg)
  subst g'
  subst q
  obtain ⟨op,len⟩ := hC g (List.mem_of_getElem? hg)
  have pair := pair_list hug hvg (fun e => ne (Fin.ext e)) len
  let f := match g.op with | .or => true | _ => false
  obtain ⟨a,b,hav,hbv,agr,diff⟩ := sensitive u v ne f
  have read (x : Fin 14 → Bool) (hx : x v = f) : val C x (14+p) = f := by
    rw [val_gate C x hg]
    rcases op with hand | hor <;> rcases pair with pair | pair
    all_goals
      simp only [Set.mem_singleton_iff] at *
      first | simp [pair, operand, huq, hvq, val_input, hx, f, hand, GateOp.eval] | simp [pair, operand, huq, hvq, val_input, hx, f, hor, GateOp.eval]
  have path : Trace 14 C (fun a => a = u.val) u.val (14+p) :=
    Relation.ReflTransGen.single ⟨rfl,⟨huq,p,g,hg,rfl,hug⟩,live⟩
  have uniq : ∀ i j j', i < 14+p → i = u.val → LNext 14 C i j → LNext 14 C i j' → j = j' := by
    rintro _ _ _ _ rfl
    exact nonbranch_unique hn
  have hd : val C a C.output ≠ val C b C.output := by rwa [he,he]
  rcases influence path uniq agr (j := C.output) .refl hd with h | h
  · exact (Nat.not_lt_of_ge (next_le live)) h.1
  · exact h.2 ((read a hav).trans (read b hbv).symm)

/-- A 26-gate witness has a raw input with a unique live reader. No other raw
input is an operand of that reader. In particular, the live gates that combine
two distinct raw inputs cannot collectively cover all fourteen variables. -/
theorem unique_reader_of_size_le_26 (C : Circuit) (hC : Monotone2 C) (size : C.size ≤ 26)
    (h : ∀ a : Fin 14 → Bool, C.eval (List.ofFn a) = true ↔
      ∃ u v : Fin 14, (u.val,v.val) ∈ deskEdges ∧ a u = true ∧ a v = true) :
    ∃ (u : Fin 14) (q : ℕ), LNext 14 C u.val q ∧
      (∀ j, LNext 14 C u.val j → j = q) ∧
      (∀ v : Fin 14, v ≠ u → ¬LNext 14 C v.val q) := by
  classical
  have he := graphEval_of_desk h
  obtain ⟨w,hw⟩ := hdegree 0
  obtain ⟨ho1,ho2⟩ := edge_at_output he hw
  have hb := branch_budget hC he hdegree (mem_living.2 ⟨ho2,.refl⟩)
  have choice : ∃ u : Fin 14, ¬Branch 14 C u.val := by
    by_contra! allb
    have sub : Finset.range 14 ⊆ (living 14 C).filter (Branch 14 C) := by
      intro a ha
      let u : Fin 14 := ⟨a,Finset.mem_range.1 ha⟩
      obtain ⟨w,hw⟩ := hdegree u
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨by have := u.isLt; change a < 14 at this; omega,
        input_live he hw⟩,allb u⟩
    have h14 := Finset.card_le_card sub
    rw [Finset.card_range] at h14
    omega
  obtain ⟨u,hn⟩ := choice
  obtain ⟨w,hw⟩ := hdegree u
  obtain ⟨q,hq⟩ := live_readers_nonempty (input_live he hw) (by have := u.isLt; omega)
  have uq := mem_readers.1 hq
  refine ⟨u,q,uq,fun _ hj => nonbranch_unique hn hj uq,?_⟩
  intro v hne hv
  apply hn (branch_of_raw_pair hC _ (Ne.symm hne) uq hv)
  intro a
  have H := (h a).trans (target_iff a).symm
  change C.eval (List.ofFn a) = target a
  exact Bool.eq_iff_iff.mpr H

/-- Live gate wires with fewer than two distinct live operands. -/
noncomputable def lostSlots (n : ℕ) (C : Circuit) : Finset ℕ := open Classical in
  (living n C).filter fun j => n ≤ j ∧ ((living n C).filter (fun i => LNext n C i j)).card ≤ 1

/-- Count one extra use per branching wire and one missing input per gate in
`lostSlots`. This refines the double count in `L_meta_1483.branch_budget`. -/
private theorem budget_with_lost_slot {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card + (lostSlots n C).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have slots : (lostSlots n C).card = ∑ j ∈ W, (if j ∈ lostSlots n C then 1 else 0 : ℕ) := by
    rw [← Finset.sum_filter]
    have e : W.filter (fun j => j ∈ lostSlots n C) = lostSlots n C := by
      ext j
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => (Finset.mem_filter.mp h).1
    simp [e]
  have upp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) + (lostSlots n C).card ≤ 2*S.card := by
    rw [slots,←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases h : j ∈ lostSlots n C
        · obtain ⟨_,nj,one⟩ := Finset.mem_filter.1 h
          have nj' : ¬j < n := Nat.not_lt_of_ge nj
          simp [h,nj']
          change (W.filter _).card ≤ 1 at one
          omega
        · simpa [h] using incoming_bound hC hj
      _ = 2*S.card := by simp [S,Finset.sum_ite,Nat.mul_comm]
  rw [hcomm] at hlow
  change n+B.card+(lostSlots n C).card ≤ C.gates.length+1
  omega

/-- A private raw input whose unique consumer has two distinct, in-range predecessors. -/
theorem private_binary_reader (C : Circuit) (hC : Monotone2 C) (size : C.size ≤ 26)
    (he : GraphEval C Ha) :
    ∃ (u : Fin 14) (q t : ℕ), LNext 14 C u.val q ∧
      (∀ j, LNext 14 C u.val j → j = q) ∧ LNext 14 C t q ∧ t ≠ u.val := by
  classical
  obtain ⟨w,hw⟩ := hdegree 0
  obtain ⟨ho1,ho2⟩ := edge_at_output he hw
  have bu := budget_with_lost_slot hC he hdegree (mem_living.2 ⟨ho2,.refl⟩)
  let B := (living 14 C).filter (Branch 14 C)
  let T := Finset.univ.filter (fun u : Fin 14 => ¬Branch 14 C u.val)
  let R := Finset.univ \ T
  have rawLive (u : Fin 14) : u.val ∈ living 14 C := by
    obtain ⟨w,hw⟩ := hdegree u
    exact mem_living.2 ⟨by have := u.isLt; omega, input_live he hw⟩
  have incl : R.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro u hu
      apply Finset.mem_filter.2
      refine ⟨rawLive u,?_⟩
      simpa [T] using (Finset.mem_sdiff.1 hu).2
    · exact fun _ _ _ _ h => Fin.ext h
  have someReader (u : Fin 14) : ∃ q, LNext 14 C u.val q := by
    obtain ⟨q,m⟩ := live_readers_nonempty (mem_living.1 (rawLive u)).2 (by have := u.isLt; omega)
    exact ⟨q,mem_readers.1 m⟩
  choose Q hQ using someReader
  by_contra! nope
  have unary (u : Fin 14) (hu : u ∈ T) : Q u ∈ lostSlots 14 C := by
    obtain ⟨nxt,live⟩ := hQ u
    obtain ⟨_,p,g,_,eq,_⟩ := nxt
    have nonb : ¬Branch 14 C u.val := (Finset.mem_filter.1 hu).2
    apply Finset.mem_filter.2
    refine ⟨mem_living.2 ⟨next_in_range (hQ u).1,live⟩,by omega,?_⟩
    have pred (t : ℕ) (ht : LNext 14 C t (Q u)) : t = u.val := by
      exact nope u (Q u) t (hQ u) (fun j hj => nonbranch_unique nonb hj (hQ u)) ht
    apply Finset.card_le_one_iff.2
    intro a b ha hb
    exact (pred a (Finset.mem_filter.1 ha).2).trans (pred b (Finset.mem_filter.1 hb).2).symm
  have cap : T.card ≤ (lostSlots 14 C).card := by
    apply Finset.card_le_card_of_injOn Q unary
    intro i hi j hj eq
    have one := (Finset.mem_filter.1 (unary i hi)).2.2
    apply Fin.ext
    exact (Finset.card_le_one_iff.1 one)
      (Finset.mem_filter.2 ⟨rawLive i,hQ i⟩)
      (Finset.mem_filter.2 ⟨rawLive j,eq ▸ hQ j⟩)
  have add := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  change R.card + T.card = _ at add
  simp only [Finset.card_univ, Fintype.card_fin] at add
  change 14+B.card+(lostSlots 14 C).card ≤ C.size+1 at bu
  omega

private theorem influence_of_unique {C : Circuit} {u : Fin 14} {q : ℕ}
    (hq : LNext 14 C u.val q) (only : ∀ j, LNext 14 C u.val j → j = q)
    {a b : Fin 14 → Bool} (agree : ∀ i, i ≠ u → a i = b i) :
    (val C a C.output ≠ val C b C.output → val C a q ≠ val C b q) ∧
    (∀ t, t < q → t ≠ u.val → Live 14 C t → val C a t = val C b t) := by
  have path : Trace 14 C (fun i => i = u.val) u.val q :=
    Relation.ReflTransGen.single ⟨rfl,hq⟩
  have uniq : ∀ i j j', i < q → i = u.val → LNext 14 C i j → LNext 14 C i j' → j = j' := by
    rintro _ j j' _ rfl h1 h2
    exact (only j h1).trans (only j' h2).symm
  constructor
  · intro hd
    rcases influence path uniq agree (j := C.output) .refl hd with h | h
    · exact (Nat.not_lt_of_ge (next_le hq.2) h.1).elim
    · exact h.2
  · intro t lt ne live
    by_contra hd
    rcases influence path uniq agree live hd with h | h
    · exact ne h.2
    · omega

/-- The earlier partner of an input's unique AND reader accepts every neighbor
singleton. By monotonicity it accepts every assignment containing a neighbor. -/
theorem and_partner {C : Circuit} (he : GraphEval C Ha) {u : Fin 14} {q t : ℕ}
    (hq : LNext 14 C u.val q) (only : ∀ j, LNext 14 C u.val j → j = q)
    (ht : LNext 14 C t q) (ne : t ≠ u.val)
    (gate : ∀ a : Fin 14 → Bool, val C a q = (a u && val C a t)) :
    ∀ w : Fin 14, Ha.Adj u w → val C (point {w}) t = true := by
  intro w hw
  have agr : ∀ i, i ≠ u → point {w} i = point {u,w} i := by
    intro i hi
    exact (point_insert hi).symm
  obtain ⟨change,stable⟩ := influence_of_unique hq only agr
  have diff : val C (point {w}) C.output ≠ val C (point {u,w}) C.output := by
    rw [point_single_quiet he, (point_pair he u w).2 hw]
    decide
  have d := change diff
  have e := stable t ht.1.1 ne (live_before ht.1 hq.2)
  rw [gate, gate] at d
  have huw := Ha.ne_of_adj hw
  simpa [point,huw,←e] using d

/-- In the Heawood graph any independent pair of other vertices can be
extended to an independent set containing a neighbor of `u`. -/
theorem pair_extendible : ∀ u i j : Fin 14, i ≠ u → j ≠ u → ¬Ha.Adj i j →
    ∃ w : Fin 14, Ha.Adj u w ∧ ¬Ha.Adj i w ∧ ¬Ha.Adj j w := by
  let : DecidableRel Ha.Adj := fun _ _ => decidable_of_iff _ Ha_adj.symm
  decide

/-- The partner of an input's unique OR reader rejects every independent pair
of other vertices, allowing a repeated vertex for the singleton case. -/
theorem or_partner (C : Circuit) (hC : Monotone2 C) (he : GraphEval C Ha)
    {u : Fin 14} {q t : ℕ} (hq : LNext 14 C u.val q)
    (only : ∀ j, LNext 14 C u.val j → j = q)
    (gate : ∀ a : Fin 14 → Bool, val C a q = (a u || val C a t)) :
    ∀ i j : Fin 14, i ≠ u → j ≠ u → ¬Ha.Adj i j → val C (point {i,j}) t = false := by
  intro i j hi hj hij
  obtain ⟨w,huw,hiw,hjw⟩ := pair_extendible u i j hi hj hij
  let s : Finset (Fin 14) := {w,i,j}
  have low : val C (point s) C.output = false := by
    rw [← Bool.not_eq_true, edge_of_point he]
    rintro ⟨a,ha,b,hb,hab⟩
    have H : ∀ a ∈ s, a = w ∨ a = i ∨ a = j := by simp [s]
    rcases H a ha with rfl | rfl | rfl <;> rcases H b hb with rfl | rfl | rfl
    all_goals first | exact Ha.irrefl hab | exact hiw hab | exact hiw (Ha.adj_symm hab)
                    | exact hjw hab | exact hjw (Ha.adj_symm hab) | exact hij hab | exact hij (Ha.adj_symm hab)
  have high : val C (point (insert u s)) C.output = true := by
    apply (edge_of_point he).2
    exact ⟨u,by simp,w,by simp [s],huw⟩
  have hd : val C (point s) C.output ≠ val C (point (insert u s)) C.output := by simp [low,high]
  have agr : ∀ k, k ≠ u → point s k = point (insert u s) k := fun k hk => (point_insert hk).symm
  have d := (influence_of_unique hq only agr).1 hd
  rw [gate,gate] at d
  have hu : point s u = false := by simp [s,point,Ha.ne_of_adj huw,Ne.symm hi,Ne.symm hj]
  rw [hu, show point (insert u s) u = true by simp [point]] at d
  have h : val C (point s) t = false := by simpa using d
  rw [← Bool.not_eq_true]
  intro accepts
  have sub : ({i,j} : Finset (Fin 14)) ⊆ s := Finset.subset_insert _ _
  exact Bool.noConfusion ((acts_mono hC (point_mono sub) t accepts).symm.trans h)



private theorem reader_op {C : Circuit} (hC : Monotone2 C) {u : Fin 14} {q t : ℕ}
    (hu : LNext 14 C u.val q) (ht : LNext 14 C t q) (ne : u.val ≠ t) :
    (∀ a : Fin 14 → Bool, val C a q = (a u && val C a t)) ∨
    (∀ a : Fin 14 → Bool, val C a q = (a u || val C a t)) := by
  obtain ⟨⟨huq,p,g,hg,eq,hug⟩,_⟩ := hu
  obtain ⟨⟨htq,p',g',hg',eq',htg⟩,_⟩ := ht
  have ep : p' = p := by omega
  subst p'
  have eg : g' = g := Option.some.inj (hg'.symm.trans hg)
  subst g'
  subst q
  obtain ⟨op,len⟩ := hC g (List.mem_of_getElem? hg)
  have pair := pair_list hug htg ne len
  rcases op with hand | hor
  · left
    intro a
    rcases pair with pair | pair
    all_goals simp [val_gate C a hg,pair,operand,huq,htq,val_input,hand,GateOp.eval,Bool.and_comm]
  · right
    intro a
    rcases pair with pair | pair
    all_goals simp only [Set.mem_singleton_iff] at hor
    all_goals simp [val_gate C a hg,pair,operand,huq,htq,val_input,hor,GateOp.eval,Bool.or_comm]

/-- Every witness of size at most 26 has a raw input read by just one live
gate. That gate also reads an earlier derived wire. For AND, the derived
wire accepts each neighboring singleton. For OR, it rejects every
independent pair of other vertices, including singletons. -/
theorem private_partner_fingerprint (C : Circuit) (hC : Monotone2 C) (size : C.size ≤ 26)
    (h : ∀ a : Fin 14 → Bool, C.eval (List.ofFn a) = true ↔
      ∃ u v : Fin 14, (u.val,v.val) ∈ deskEdges ∧ a u = true ∧ a v = true) :
    ∃ (u : Fin 14) (q t : ℕ), LNext 14 C u.val q ∧
      (∀ j, LNext 14 C u.val j → j = q) ∧ 14 ≤ t ∧ LNext 14 C t q ∧
      (((∀ a : Fin 14 → Bool, val C a q = (a u && val C a t)) ∧
        ∀ w : Fin 14, Ha.Adj u w → val C (point {w}) t = true) ∨
       ((∀ a : Fin 14 → Bool, val C a q = (a u || val C a t)) ∧
        ∀ i j : Fin 14, i ≠ u → j ≠ u → ¬Ha.Adj i j →
          val C (point {i,j}) t = false)) := by
  classical
  have he := graphEval_of_desk h
  obtain ⟨u,q,t, hu, only,ht,ne⟩ := private_binary_reader C hC size he
  have derived : 14 ≤ t := by
    by_contra! small
    let v : Fin 14 := ⟨t,small⟩
    have diff : u ≠ v := fun eq => ne (congrArg Fin.val eq).symm
    have hev (a : Fin 14 → Bool) : val C a C.output = target a :=
      Bool.eq_iff_iff.mpr ((h a).trans (target_iff a).symm)
    have branch := branch_of_raw_pair hC hev diff hu ht
    have one : (readers 14 C u.val).card ≤ 1 := by
      apply Finset.card_le_one_iff.2
      intro i j hi hj
      exact (only i (mem_readers.1 hi)).trans (only j (mem_readers.1 hj)).symm
    unfold Branch at branch
    omega
  refine ⟨u,q,t,hu,only,derived,ht,?_⟩
  rcases reader_op hC hu ht (Ne.symm ne) with hand | hor
  · exact Or.inl ⟨hand,and_partner he hu only ht ne hand⟩
  · exact Or.inr ⟨hor,or_partner C hC he hu only hor⟩

end PEqualNP.Search.HeawoodNecessaryReads
