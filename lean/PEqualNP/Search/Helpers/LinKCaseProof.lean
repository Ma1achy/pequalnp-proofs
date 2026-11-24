import PEqualNP.Search.Helpers.LinKGuardTaut
import PEqualNP.Search.Helpers.ParityTree

/-!
# Case analysis for a binary inference on bounded parity terms

Split on a decision tree for the conclusion head. A true leaf contributes
its path term by conjunction introduction. At a false leaf, split on the
first premise head. On every resulting cell one premise head is impossible,
so its individual terms imply the disjunction of the blocking singletons.
Keeping all non-head terms in the target makes this a termwise weakening.
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V] {k : ℕ} {F Γ : Set (LinKLine V)}

private def KAdd (k : ℕ) (F Γ : Set (LinKLine V)) (G : LinKLine V) (m : ℕ) : Prop :=
  ∀ ρ, IsLinKDerivation k IsLinKWeakening F ρ → (∀ L ∈ Γ, L ∈ ρ) →
    ∃ σ, IsLinKDerivation k IsLinKWeakening F (σ ++ ρ) ∧ G ∈ σ ∧ σ.length ≤ m

private abbrev Bounded (k : ℕ) (G : LinKLine V) := ∀ T ∈ G, T.card ≤ k

private theorem bound_guard (hk : 1 ≤ k) {G : LinKLine V} (w : Bounded k G)
    (P : ProofComplexity.LinClause V) : Bounded k (G ∪ guardSingles P) := by
  intro T hT
  rcases Finset.mem_union.mp hT with h | h
  · exact w T h
  · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
    simpa using hk

private theorem cut_siblings (G : LinKLine V) (q : Finset V) :
    IsLinKCut (insert ({(q, false)} : LinTerm V) G) (insert ({(q, true)} : LinTerm V) G) G := by
  classical
  refine ⟨{(q,false)}, by simp, ?_, ?_⟩
  · intro e he
    obtain rfl := Finset.mem_singleton.mp he
    simp [negLinEq]
  · ext T
    simp only [Finset.image_singleton, negLinEq, Bool.not_false, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    by_cases h0 : T = {(q, false)} <;> by_cases h1 : T = {(q, true)} <;> simp_all

/-- Accumulate path blockers as one-equation terms. They never increase term width. -/
private theorem split_K_at (hk : 1 ≤ k) (t : ParityTree V) (G : LinKLine V)
    (wg : Bounded k G) (P : ProofComplexity.LinClause V) (m : ℕ)
    (leaf : ∀ b B, (b,B) ∈ t.cellsAt P → KAdd k F Γ (G ∪ guardSingles B) m) :
    KAdd k F Γ (G ∪ guardSingles P) (t.leaves * (m+1) - 1) := by
  induction t generalizing P with
  | leaf b => simpa [ParityTree.leaves] using leaf b P List.mem_cons_self
  | node q lo hi ihl ihr =>
    have left := ihl (insert (q,true) P) (fun b B hm => leaf b B (List.mem_append_left _ hm))
    have right := ihr (insert (q,false) P) (fun b B hm => leaf b B (List.mem_append_right _ hm))
    intro ρ hd hΓ
    obtain ⟨s, ds, hs, ls⟩ := left ρ hd hΓ
    obtain ⟨t, dt, ht, lt⟩ := right (s ++ ρ) ds (fun L hL => List.mem_append_right _ (hΓ L hL))
    let T := G ∪ guardSingles P
    have hm0 : insert ({(q,false)} : LinTerm V) T ∈ t ++ (s ++ ρ) := by
      apply List.mem_append_left
      simpa [T, guardSingles, Finset.union_insert] using ht
    have hm1 : insert ({(q,true)} : LinTerm V) T ∈ t ++ (s ++ ρ) := by
      apply List.mem_append_right
      apply List.mem_append_left
      simpa [T, guardSingles, Finset.union_insert] using hs
    have res := dt.cut hm0 hm1 (cut_siblings T q) (bound_guard hk wg P)
    refine ⟨T :: (t ++ s), by simpa [List.append_assoc] using res, List.mem_cons_self, ?_⟩
    have hlpos : 0 < lo.leaves * (m+1) := Nat.mul_pos lo.leaves_pos (by omega)
    have hrpos : 0 < hi.leaves * (m+1) := Nat.mul_pos hi.leaves_pos (by omega)
    simp only [List.length_cons, List.length_append, ParityTree.leaves, Nat.add_mul]
    omega

private theorem false_head {parent rest G : LinKLine V} {P : ProofComplexity.LinClause V}
    (hk : 1 ≤ k) (w : Bounded k G) (hparent : parent ∪ rest ∈ Γ) (retain : rest ⊆ G)
    (off : ∀ a, ¬ LinClauseSat a P → ¬ LinKLineSat a parent) :
    KAdd k F Γ (G ∪ guardSingles P) 1 := by
  classical
  intro ρ hd hΓ
  refine ⟨[G ∪ guardSingles P], hd.weak (hΓ _ hparent) ?_ (bound_guard hk w P), by simp, by simp⟩
  intro T hT
  rcases Finset.mem_union.mp hT with head | tail
  · apply Or.inr
    intro a ha
    have blocked : LinClauseSat a P := by
      by_contra hf
      exact off a hf ⟨T, head, ha⟩
    obtain ⟨q, hq, sat⟩ := blocked
    exact ⟨q, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩), sat⟩
  · exact Or.inl ⟨T, Finset.mem_union_left _ (retain tail), fun _ h => h⟩

private theorem true_head {G : LinKLine V} {P : ProofComplexity.LinClause V}
    (hk : 1 ≤ k) (w : Bounded k G) (hΓ : Γ.Nonempty) (path : guardTerm P ∈ G)
    (depth : P.card ≤ k) : KAdd k F Γ (G ∪ guardSingles P) (4*(k+1)+1) := by
  intro ρ hd hav
  obtain ⟨C, hc⟩ := hΓ
  have hn : ρ ≠ [] := fun h => List.not_mem_nil (h ▸ hav C hc)
  obtain ⟨s, ds, hm, hlen⟩ := linK_guard_taut P hk depth hd hn
  refine ⟨(G ∪ guardSingles P) :: s,
    ds.weak (List.mem_append_left _ hm) ?_ (bound_guard hk w P), List.mem_cons_self, ?_⟩
  · intro T ht
    apply Or.inl
    refine ⟨T, ?_, fun _ hx => hx⟩
    rcases Finset.mem_union.mp ht with h | h
    · exact Finset.mem_union_left _ ((Finset.mem_singleton.mp h).symm ▸ path)
    · exact Finset.mem_union_right _ h
  · simp only [List.length_cons]
    omega

/-- Simulate an integer-head inference in termwise Res(k,⊕). The head codes
are A, B, G and the two unchanged tails are C, D. Only the trees for A and G
enter the size bound. -/
theorem linK_two_head_step (hk : 1 ≤ k) (A B G C D : LinKLine V) (ta tg : ParityTree V)
    (eA : ∀ a, LinKLineSat a A ↔ ta.eval a = true)
    (eG : ∀ a, LinKLineSat a G ↔ tg.eval a = true)
    (posG : ∀ P, (true,P) ∈ tg.cells → guardTerm P ∈ G)
    (widthG : ∀ P, (true,P) ∈ tg.cells → P.card ≤ k)
    (rule : ∀ a, LinKLineSat a A → LinKLineSat a B → LinKLineSat a G)
    (width : ∀ T ∈ G ∪ (C ∪ D), T.card ≤ k)
    {ρ : List (LinKLine V)} (hd : IsLinKDerivation k IsLinKWeakening F ρ)
    (hA : A ∪ C ∈ ρ) (hB : B ∪ D ∈ ρ) :
    ∃ σ, IsLinKDerivation k IsLinKWeakening F (σ ++ ρ) ∧ G ∪ (C ∪ D) ∈ σ ∧
      σ.length ≤ (4*(k+1) + 2*ta.leaves + 2) * tg.leaves := by
  classical
  let Γ : Set (LinKLine V) := {A ∪ C, B ∪ D}
  let T := G ∪ (C ∪ D)
  have ha : A ∪ C ∈ Γ := by simp [Γ]
  have hb : B ∪ D ∈ Γ := by simp [Γ]
  let m := 4*(k+1) + 2*ta.leaves + 1
  have inner (P : ProofComplexity.LinClause V) (blocked : (false,P) ∈ tg.cells) :
      KAdd k F Γ (T ∪ guardSingles P) (ta.leaves*(1+1)-1) := by
    apply split_K_at hk ta T width P 1
    intro a Z hm
    rw [ParityTree.cellsAt_eq_map] at hm
    obtain ⟨⟨b, Q⟩, hq, eq⟩ := List.mem_map.mp hm
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have parts (x) (off : ¬ LinClauseSat x (P ∪ Q)) : ¬ LinClauseSat x P ∧ ¬ LinClauseSat x Q :=
      ⟨fun ⟨e, he, hx⟩ => off ⟨e, Finset.mem_union_left _ he, hx⟩,
       fun ⟨e, he, hx⟩ => off ⟨e, Finset.mem_union_right _ he, hx⟩⟩
    cases b with
    | false =>
      apply false_head hk width ha (fun _ h => Finset.mem_union_right _ (Finset.mem_union_left _ h))
      intro x off holds
      have hf := ta.eval_of_mem_cells x hq (parts x off).2
      have yes := (eA x).mp holds
      simp [hf] at yes
    | true =>
      apply false_head hk width hb (fun _ h => Finset.mem_union_right _ (Finset.mem_union_right _ h))
      intro x off holds
      have hta := ta.eval_of_mem_cells x hq (parts x off).2
      have htg := tg.eval_of_mem_cells x blocked (parts x off).1
      have yes := (eG x).mp (rule x ((eA x).mpr hta) holds)
      simp [htg] at yes
  have outer := split_K_at (F := F) (Γ := Γ) hk tg T width ∅ m (by
    intro b P hp ρ' d' hav
    change (b,P) ∈ tg.cells at hp
    cases b with
    | false =>
      obtain ⟨s, ds, hm, budget⟩ := inner P hp ρ' d' hav
      exact ⟨s, ds, hm, by dsimp [m]; omega⟩
    | true =>
      obtain ⟨s, ds, hm, budget⟩ := true_head hk width ⟨_, ha⟩
        (Finset.mem_union_left _ (posG _ hp)) (widthG _ hp) ρ' d' hav
      exact ⟨s, ds, hm, by dsimp [m]; omega⟩)
  obtain ⟨σ, ds, hm, budget⟩ := outer ρ hd (fun x hx => by
    rcases Set.mem_insert_iff.mp hx with rfl | single
    · exact hA
    · exact Set.mem_singleton_iff.mp single ▸ hB)
  refine ⟨σ, ds, by simpa [guardSingles, T] using hm, ?_⟩
  exact budget.trans ((Nat.sub_le _ _).trans_eq (by unfold m; rw [Nat.mul_comm]))

end PEqualNP.Search.Helpers
