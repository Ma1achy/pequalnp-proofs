import PEqualNP.Search.Helpers.Width.Walk

namespace PEqualNP.Search.Helpers.Width

/-- Extend an injection from a subset of the pigeons by assigning each additional
pigeon to an unused hole. Bits of pigeons already in the subset are preserved. -/
theorem extend_injP {N l : ℕ} (a : Fin N × Fin l → Bool) {S T : Finset (Fin N)}
    (hST : S ⊆ T) (hT : T.card ≤ 2 ^ l) (hS : InjP a S) :
    ∃ a' ∈ Ext a S, InjP a' T := by
  classical
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    by_cases hall : T ⊆ S
    · exact ⟨a, self_mem_Ext a S, fun i hi j hj => hS i (hall hi) j (hall hj)⟩
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp hall
    have hsub : S ⊆ T.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hj), hST hj⟩
    have hcard : (T.erase i).card < 2 ^ l :=
      (Finset.card_lt_card (Finset.erase_ssubset hi)).trans_le hT
    obtain ⟨q, hq, hinj⟩ := ih _ (Finset.erase_ssubset hi) hsub hcard.le
    let hole (j : Fin N) (b : Fin l) := q (j, b)
    have hused : ((T.erase i).image hole).card < (Finset.univ : Finset (Fin l → Bool)).card := by
      simpa using (Finset.card_image_le (s := T.erase i) (f := hole)).trans_lt hcard
    obtain ⟨fresh, _, hfresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
    have different (j : Fin N) (hj : j ∈ T.erase i) : hole j ≠ fresh := by
      intro heq
      exact hfresh (Finset.mem_image.mpr ⟨j, hj, heq⟩)
    let q' (v : Fin N × Fin l) := if v.1 = i then fresh v.2 else q v
    refine ⟨q', mem_Ext.mpr ?_, ?_⟩
    · intro j hj b
      have hji := (Finset.mem_erase.mp (hsub hj)).1
      simpa [q', hji] using (mem_Ext.mp hq j hj b)
    · intro j hj k hk hbits
      by_cases hji : j = i <;> by_cases hki : k = i
      · exact hji.trans hki.symm
      · subst j
        apply False.elim (different k (Finset.mem_erase.mpr ⟨hki, hk⟩) _)
        funext b
        simpa [q', hole, hki] using (hbits b).symm
      · subst k
        apply False.elim (different j (Finset.mem_erase.mpr ⟨hji, hj⟩) _)
        funext b
        simpa [q', hole, hji] using hbits b
      · apply hinj j (Finset.mem_erase.mpr ⟨hji, hj⟩) k (Finset.mem_erase.mpr ⟨hki, hk⟩)
        intro b
        simpa [q', hji, hki] using hbits b

end PEqualNP.Search.Helpers.Width
