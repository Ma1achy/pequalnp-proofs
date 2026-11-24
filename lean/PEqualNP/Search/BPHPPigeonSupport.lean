import PEqualNP.Search.Helpers.BPHPExtension
import PEqualNP.Defs.SearchQSyn

/-!
# Semantic pigeon support in dag-like syntactic integer R(lin)

A support determines a line's truth from the rows of the named pigeons.
At a binary inference, the pigeons in at least two of the three supports
are the only ones requiring simultaneous coordination. If all three
supports have size at most w, this shared set has size at most 3w/2.
Fill it injectively first, then complete each premise separately.
-/

namespace PEqualNP.Search.PigeonSupport

open Helpers Helpers.Width

variable {N l w : ℕ}

private abbrev Line (N l : ℕ) := QLine (Fin N × Fin l)
private abbrev Point (N l : ℕ) := Fin N × Fin l → Bool

/-- The rows of the pigeons in S determine whether the entire line holds. -/
def Supports (S : Finset (Fin N)) (L : QLine (Fin N × Fin l)) : Prop :=
  ∀ a b : Fin N × Fin l → Bool, (∀ i ∈ S, ∀ j, a (i, j) = b (i, j)) →
    (QLine.Holds a L ↔ QLine.Holds b L)

private theorem restrict_inj {a : Point N l} {S T : Finset (Fin N)}
    (h : S ⊆ T) (ha : InjP a T) : InjP a S :=
  fun i hi j hj => ha i (h hi) j (h hj)

private theorem transfer_inj {a b : Point N l} {S : Finset (Fin N)}
    (h : ∀ i ∈ S, ∀ j, b (i, j) = a (i, j)) (ha : InjP a S) : InjP b S := by
  intro i hi k hk eqv
  exact ha i hi k hk fun j => (h i hi j).symm.trans ((eqv j).trans (h k hk j))

/-- Preserve every row in F while filling T injectively. Frozen rows outside T
do not use up any of T's holes. -/
private theorem fill (a : Point N l) (F T : Finset (Fin N))
    (bound : T.card ≤ 2 ^ l) (h : InjP a (T ∩ F)) :
    ∃ b ∈ Ext a F, InjP b T := by
  classical
  obtain ⟨b, hb, hinj⟩ := extend_injP a Finset.inter_subset_left bound h
  let c : Point N l := fun v => if v.1 ∈ T then b v else a v
  refine ⟨c, mem_Ext.mpr ?_, transfer_inj (a := b) ?_ hinj⟩
  · intro i hi j
    by_cases ht : i ∈ T
    · simpa [c, ht] using mem_Ext.mp hb i (Finset.mem_inter.mpr ⟨ht, hi⟩) j
    · simp [c, ht]
  · intro i hi j
    simp [c, hi]

/-- Extend a point fixed on S to a point injective on A and injective on B.
Distinct pigeons exclusive to different premises may share a hole. -/
private theorem complete_two (a : Point N l) (S A B : Finset (Fin N))
    (hs : S.card ≤ w) (ha : A.card ≤ w) (hb : B.card ≤ w)
    (bound : 3 * w ≤ 2 * 2 ^ l) (inj : InjP a S) :
    ∃ b ∈ Ext a S, InjP b A ∧ InjP b B := by
  classical
  let U := A ∩ B ∪ (S ∩ (A ∪ B))
  have hUs : U.card ≤ (A ∩ B).card + S.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left
      (Finset.card_le_card Finset.inter_subset_left) _)
  have hUab : U ⊆ A ∪ B := by
    intro i hi
    rcases Finset.mem_union.mp hi with hab | hsu
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hab).1
    · exact (Finset.mem_inter.mp hsu).2
  have hU := Finset.card_le_card hUab
  have heq := Finset.card_union_add_card_inter A B
  have hu : U.card ≤ 2 ^ l := by omega
  obtain ⟨b, hbS, hbu⟩ := fill a S U hu (restrict_inj Finset.inter_subset_right inj)
  have hAS : A ∩ (S ∪ U) ⊆ U := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hia, hrest⟩
    rcases Finset.mem_union.mp hrest with his | hiu
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨his, Finset.mem_union_left _ hia⟩)
    · exact hiu
  obtain ⟨c, hcSU, hca⟩ := fill b (S ∪ U) A (by omega) (restrict_inj hAS hbu)
  have hcu : InjP c U := transfer_inj (fun i hi => mem_Ext.mp hcSU i (Finset.mem_union_right _ hi)) hbu
  have hBS : B ∩ (S ∪ U ∪ A) ⊆ U := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hib, hrest⟩
    rcases Finset.mem_union.mp hrest with hsu | hia
    · rcases Finset.mem_union.mp hsu with his | hiu
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨his, Finset.mem_union_right _ hib⟩)
      · exact hiu
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hia, hib⟩)
  obtain ⟨d, hdSUA, hdb⟩ := fill c (S ∪ U ∪ A) B (by omega) (restrict_inj hBS hcu)
  refine ⟨d, mem_Ext.mpr ?_, transfer_inj (a := c) ?_ hca, hdb⟩
  · intro i hi j
    have hsu : i ∈ S ∪ U := Finset.mem_union_left _ hi
    exact (mem_Ext.mp hdSUA i (Finset.mem_union_left _ hsu) j).trans
      ((mem_Ext.mp hcSU i hsu j).trans (mem_Ext.mp hbS i hi j))
  · intro i hi
    exact mem_Ext.mp hdSUA i (Finset.mem_union_right _ hi)

private def Local (w : ℕ) (L : Line N l) : Prop :=
  ∀ S : Finset (Fin N), S.card ≤ w → Supports S L → ∀ a, InjP a S → QLine.Holds a L

private def Small (w : ℕ) (L : Line N l) : Prop :=
  ∃ S : Finset (Fin N), S.card ≤ w ∧ Supports S L

private theorem infer_local (bound : 3 * w ≤ 2 * 2 ^ l) {C D L : Line N l}
    (hc : Small w C) (hd : Small w D) (locC : Local w C) (locD : Local w D)
    (rule : ∀ a, QLine.Holds a C → QLine.Holds a D → QLine.Holds a L) : Local w L := by
  obtain ⟨A, ha, sa⟩ := hc
  obtain ⟨B, hb, sb⟩ := hd
  intro S hs ss a inj
  obtain ⟨b, hbs, hba, hbb⟩ := complete_two a S A B hs ha hb bound inj
  exact (ss b a (mem_Ext.mp hbs)).mp (rule b (locC A ha sa b hba) (locD B hb sb b hbb))

private theorem input_local {C : ProofComplexity.Clause (Fin N × Fin l)}
    (hc : C ∈ ProofComplexity.BPHP N l) {L : Line N l}
    (rep : ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) (bits : 0 < l) : Local w L := by
  classical
  obtain ⟨i, k, α, hik, rfl⟩ := hc
  intro S _ ss a hinj
  let T : Finset (Fin N) := {i, k}
  have ht : T.card ≤ 2 ^ l := by
    have hcard : T.card = 2 := by simp [T, hik]
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ l by omega)
    omega
  obtain ⟨b, hbs, hbinj⟩ := fill a S T ht (restrict_inj Finset.inter_subset_right hinj)
  apply (ss b a (mem_Ext.mp hbs)).mp
  by_contra hf
  have same (p : Fin N) (hp : p = i ∨ p = k) (j : Fin l) : b (p, j) = α j := by
    by_contra hdiff
    have hval : b (p, j) = !α j := by cases h : b (p, j) <;> cases h' : α j <;> simp_all
    apply hf
    apply Exists.intro (litQEq ((p, j), !α j))
    refine ⟨(rep _).mpr ⟨((p, j), !α j), ?_, rfl⟩, litQEq_holds b _ hval⟩
    rcases hp with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  exact hik (hbinj i (by simp [T]) k (by simp [T]) fun j =>
    (same i (Or.inl rfl) j).trans (same k (Or.inr rfl) j).symm)

private theorem local_derivation {π : List (Line N l)} (bits : 0 < l)
    (bound : 3 * w ≤ 2 * 2 ^ l)
    (der : IsResLinQSynDerivation (ProofComplexity.BPHP N l) π)
    (small : ∀ L ∈ π, Small w L) : ∀ L ∈ π, Local w L := by
  induction der with
  | nil => simp
  | ax C _ hc rep ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | h
    · exact input_local hc rep bits
    · exact ih (fun L hL => small L (List.mem_cons_of_mem _ hL)) L h
  | bool v _ ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | h
    · intro _ _ _ a _
      cases hv : a v with
      | false => exact ⟨litQEq (v, false), by simp, litQEq_holds a _ hv⟩
      | true => exact ⟨litQEq (v, true), by simp, litQEq_holds a _ hv⟩
    · exact ih (fun L hL => small L (List.mem_cons_of_mem _ hL)) L h
  | @res π e e' C D α β _ hc hd ih =>
    have st : ∀ L ∈ π, Small w L := fun L hL => small L (List.mem_cons_of_mem _ hL)
    have loc := ih st
    intro L hL
    rcases List.mem_cons.mp hL with rfl | h
    · apply infer_local bound (st _ hc) (st _ hd) (loc _ hc) (loc _ hd)
      rintro a ⟨f, hf, haf⟩ ⟨g, hg, hag⟩
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨_, List.mem_cons_self, combo_holds a f g α β haf hag⟩
        · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hag⟩
      · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), haf⟩
    · exact loc _ h
  | @weaken π C D _ hc sub ih =>
    have st : ∀ L ∈ π, Small w L := fun L hL => small L (List.mem_cons_of_mem _ hL)
    have loc := ih st
    intro L hL
    rcases List.mem_cons.mp hL with rfl | h
    · exact infer_local bound (st _ hc) (st _ hc) (loc _ hc) (loc _ hc)
        fun _ ⟨e, he, ha⟩ _ => ⟨e, sub _ he, ha⟩
    · exact loc _ h
  | @simp π C _ hc ih =>
    have st : ∀ L ∈ π, Small w L := fun L hL => small L (List.mem_cons_of_mem _ hL)
    have loc := ih st
    intro L hL
    rcases List.mem_cons.mp hL with rfl | h
    · apply infer_local bound (st _ hc) (st _ hc) (loc _ hc) (loc _ hc)
      rintro a ⟨e, he, h⟩ _
      refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, h⟩
      simp only [decide_eq_true_eq]
      rintro ⟨hz, hn⟩
      exact hn (by simpa [QEq.Holds, hz] using h.symm)
    · exact loc _ h

/-- In every syntactic refutation some line's truth requires more than two
thirds of the holes' count in pigeon rows, even for arbitrary coefficients. -/
theorem bphp_pigeon_support (l : ℕ) (bits : 0 < l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (ProofComplexity.BPHP (2 ^ l + 1) l) π) :
    ∃ L ∈ π, ∀ S : Finset (Fin (2 ^ l + 1)), Supports S L → 2 * 2 ^ l < 3 * S.card := by
  classical
  by_contra h
  push Not at h
  let w := 2 * 2 ^ l / 3
  have sm : ∀ L ∈ π, Small w L := by
    intro L hL
    obtain ⟨S, hs, hcard⟩ := h L hL
    exact ⟨S, by dsimp [w]; omega, hs⟩
  have localEmpty := local_derivation bits (w := w) (by dsimp [w]; omega) hπ.1 sm [] hπ.2
  have bad := localEmpty ∅ (by simp) (fun _ _ _ => by simp [QLine.Holds]) (fun _ => false) (by
    intro i hi
    simp at hi)
  obtain ⟨_, he, _⟩ := bad
  exact List.not_mem_nil he

end PEqualNP.Search.PigeonSupport
