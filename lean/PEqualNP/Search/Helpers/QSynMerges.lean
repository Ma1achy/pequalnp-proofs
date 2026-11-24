import PEqualNP.Search.Helpers.QSynEssential

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)} {k : ℕ}

/-- A record of the inputs and premises used to justify a proof. Premises can refer to
any earlier line, and may be reused. With at most two premises, the cost counts exactly
the binary steps. Semantic justification also covers the individual syntactic rules. -/
inductive QSynMergeTrace {V : Type} [Fintype V] (F : Set (PEqualNP.ProofComplexity.Clause V)) :
    List (QLine V) → ℕ → Prop
  | nil : QSynMergeTrace F [] 0
  | input {π k L} {C : PEqualNP.ProofComplexity.Clause V} :
      QSynMergeTrace F π k → C ∈ F → (∀ a, ClauseSat a C → QLine.Holds a L) →
      QSynMergeTrace F (L :: π) k
  | step {π k L} (parents : List (QLine V)) :
      QSynMergeTrace F π k → parents.length ≤ 2 → (∀ p ∈ parents, p ∈ π) →
      (∀ a, (∀ p ∈ parents, QLine.Holds a p) → QLine.Holds a L) →
      QSynMergeTrace F (L :: π) (k + (parents.length - 1))

/-- Trace the actual syntactic rules: resolution takes two premises, weakening and
simplification one, and a Boolean axiom none. -/
theorem exists_merge_trace (h : IsResLinQSynDerivation F π) : ∃ k, QSynMergeTrace F π k := by
  induction h with
  | nil => exact ⟨0, .nil⟩
  | ax C _ hC hL ih =>
    obtain ⟨k, t⟩ := ih
    refine ⟨k, .input t hC ?_⟩
    rintro a ⟨lit, hl, ha⟩
    exact ⟨litQEq lit, (hL _).mpr ⟨lit, hl, rfl⟩, litQEq_holds a lit ha⟩
  | bool v _ ih =>
    obtain ⟨k, t⟩ := ih
    refine ⟨k, .step [] t (by simp) (by simp) ?_⟩
    intro a _
    cases hv : a v with
    | false => exact ⟨litQEq (v, false), by simp, litQEq_holds a _ hv⟩
    | true => exact ⟨litQEq (v, true), by simp, litQEq_holds a _ hv⟩
  | @res π e e' C D α β _ hC hD ih =>
    obtain ⟨k, t⟩ := ih
    refine ⟨k + 1, .step [e :: C, e' :: D] t (by simp) (by simpa using And.intro hC hD) ?_⟩
    intro a h
    obtain ⟨f, hf, hfa⟩ := h (e :: C) (by simp)
    obtain ⟨g, hg, hga⟩ := h (e' :: D) (by simp)
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨_, List.mem_cons_self, combo_holds a f g α β hfa hga⟩
      · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hga⟩
    · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), hfa⟩
  | @weaken π C D _ hC hsub ih =>
    obtain ⟨k, t⟩ := ih
    refine ⟨k, .step [C] t (by simp) (by simpa using hC) ?_⟩
    intro a h
    obtain ⟨e, he, ha⟩ := h C (by simp)
    exact ⟨e, hsub _ he, ha⟩
  | @simp π C _ hC ih =>
    obtain ⟨k, t⟩ := ih
    refine ⟨k, .step [C] t (by simp) (by simpa using hC) ?_⟩
    intro a h
    obtain ⟨e, he, ha⟩ := h C (by simp)
    refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, ha⟩
    simp only [decide_eq_true_eq]
    rintro ⟨hz, hn⟩
    exact hn (by simpa [QEq.Holds, hz] using ha.symm)

/-- Starting with a finite set of target lines, extract enough input clauses to
entail them. Walk backwards, replacing each needed conclusion by its premises. -/
private theorem extract_inputs (trace : QSynMergeTrace F π k) (T : Finset (QLine V))
    (hT : ∀ L ∈ T, L ∈ π) :
    ∃ S : Finset (PEqualNP.ProofComplexity.Clause V), (∀ C ∈ S, C ∈ F) ∧ S.card ≤ T.card + k ∧
      ∀ a, (∀ C ∈ S, ClauseSat a C) → ∀ L ∈ T, QLine.Holds a L := by
  classical
  induction trace generalizing T with
  | nil =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro a _ L hL
    simpa using hT L hL
  | @input π k L C _ hC hs ih =>
    by_cases hL : L ∈ T
    · obtain ⟨S, hF, hk, h⟩ := ih (T.erase L) (by
        intro K hK
        exact (List.mem_cons.mp (hT K (Finset.mem_of_mem_erase hK))).resolve_left
          (Finset.ne_of_mem_erase hK))
      refine ⟨insert C S, ?_, ?_, ?_⟩
      · simpa [hC] using hF
      · have := Finset.card_insert_le C S
        have := Finset.card_pos.mpr ⟨L, hL⟩
        rw [Finset.card_erase_of_mem hL] at hk
        omega
      · intro a ha K hK
        by_cases he : K = L
        · exact he ▸ hs a (ha C (Finset.mem_insert_self _ _))
        · exact h a (fun D hD => ha D (Finset.mem_insert_of_mem hD)) K
            (Finset.mem_erase.mpr ⟨he, hK⟩)
    · exact ih T (fun K hK => (List.mem_cons.mp (hT K hK)).resolve_left
        (fun he => hL (he ▸ hK)))
  | @step π k L parents _ _ hp hs ih =>
    by_cases hL : L ∈ T
    · let U := T.erase L ∪ parents.toFinset
      have hU : ∀ K ∈ U, K ∈ π := by
        intro K hK
        rcases Finset.mem_union.mp hK with hK | hK
        · exact (List.mem_cons.mp (hT K (Finset.mem_of_mem_erase hK))).resolve_left
            (Finset.ne_of_mem_erase hK)
        · exact hp K (List.mem_toFinset.mp hK)
      obtain ⟨S, hF, hk, h⟩ := ih U hU
      refine ⟨S, hF, ?_, ?_⟩
      · have hu : U.card ≤ (T.erase L).card + parents.toFinset.card := Finset.card_union_le _ _
        have := Finset.card_pos.mpr ⟨L, hL⟩
        have := parents.toFinset_card_le
        rw [Finset.card_erase_of_mem hL] at hu
        omega
      · intro a ha K hK
        by_cases he : K = L
        · apply he ▸ hs a
          exact fun p hp => h a ha p (Finset.mem_union_right _ (List.mem_toFinset.mpr hp))
        · exact h a ha K (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hK⟩))
    · obtain ⟨S, hF, hk, h⟩ := ih T (fun K hK => (List.mem_cons.mp (hT K hK)).resolve_left
        (fun he => hL (he ▸ hK)))
      exact ⟨S, hF, by omega, h⟩

/-- At least one fewer binary inference than critical inputs is required, even when
derived lines can be reused arbitrarily many times. -/
theorem critical_card_le_binary_add_one (trace : QSynMergeTrace F π k)
    (hempty : ([] : QLine V) ∈ π) (T : Finset (PEqualNP.ProofComplexity.Clause V))
    (crit : ∀ C ∈ T, ∃ a, ∀ D ∈ F, D ≠ C → ClauseSat a D) : T.card ≤ k + 1 := by
  classical
  obtain ⟨S, hF, hk, hs⟩ := extract_inputs trace {[]} (by simpa using hempty)
  have hsub : T ⊆ S := by
    intro C hC
    by_contra h
    obtain ⟨a, ha⟩ := crit C hC
    obtain ⟨_, he, _⟩ := hs a (fun D hD => ha D (hF D hD) (fun hd => h (hd ▸ hD))) [] (by simp)
    simp at he
  exact (Finset.card_le_card hsub).trans (by simpa [Nat.add_comm] using hk)

end PEqualNP.Search.Helpers
