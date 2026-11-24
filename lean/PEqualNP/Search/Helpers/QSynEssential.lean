import PEqualNP.Defs.SearchQSyn
import PEqualNP.Search.Helpers.ResLinQ

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}

omit [Fintype V] in
private theorem restrict_axiom_hypothesis {a : V → Bool} {L : QLine V}
    (ha : ∀ C ∈ F, (∃ K ∈ L :: π, ∀ e, e ∈ K ↔ ∃ lit ∈ C, e = litQEq lit) → ClauseSat a C) :
    ∀ C ∈ F, (∃ K ∈ π, ∀ e, e ∈ K ↔ ∃ lit ∈ C, e = litQEq lit) → ClauseSat a C := by
  rintro C hC ⟨K, hK, h⟩
  exact ha C hC ⟨K, List.mem_cons_of_mem _ hK, h⟩

/-- Under an assignment satisfying the input clauses represented in the derivation,
every line holds. The axiom rule permits repetitions and reordering of literals. -/
theorem syn_lines_hold_of_used_axioms (hπ : IsResLinQSynDerivation F π) (a : V → Bool)
    (ha : ∀ C ∈ F, (∃ L ∈ π, ∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit) → ClauseSat a C) :
    ∀ L ∈ π, QLine.Holds a L := by
  induction hπ with
  | nil => simp
  | @ax π L C _ hCF hL ih =>
    have hold := ih (restrict_axiom_hypothesis ha)
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · obtain ⟨lit, hl, ha'⟩ := ha C hCF ⟨_, List.mem_cons_self, hL⟩
      exact ⟨litQEq lit, (hL _).mpr ⟨lit, hl, rfl⟩, litQEq_holds a lit ha'⟩
    · exact hold K hK
  | bool v _ ih =>
    have hold := ih (restrict_axiom_hypothesis ha)
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · cases hv : a v with
      | false => exact ⟨litQEq (v, false), by simp, litQEq_holds a _ hv⟩
      | true => exact ⟨litQEq (v, true), by simp, litQEq_holds a _ hv⟩
    · exact hold K hK
  | @res π e e' C D α β _ hC hD ih =>
    have hold := ih (restrict_axiom_hypothesis ha)
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · obtain ⟨f, hf, hfa⟩ := hold _ hC
      obtain ⟨g, hg, hga⟩ := hold _ hD
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨_, List.mem_cons_self, combo_holds a f g α β hfa hga⟩
        · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hga⟩
      · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), hfa⟩
    · exact hold K hK
  | weaken _ hC hsub ih =>
    have hold := ih (restrict_axiom_hypothesis ha)
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · obtain ⟨e, he, h⟩ := hold _ hC
      exact ⟨e, hsub _ he, h⟩
    · exact hold K hK
  | simp _ hC ih =>
    have hold := ih (restrict_axiom_hypothesis ha)
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · obtain ⟨e, he, h⟩ := hold _ hC
      refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, h⟩
      simp only [decide_eq_true_eq]
      rintro ⟨hz, hn⟩
      exact hn (by simpa [QEq.Holds, hz] using h.symm)
    · exact hold K hK

/-- If deleting an input clause leaves a satisfiable formula, every syntactic
refutation contains a line representing that clause exactly. -/
theorem exists_axiom_line_of_critical {C : PEqualNP.ProofComplexity.Clause V} (hπ : IsResLinQSynRefutation F π)
    (crit : ∃ a, ∀ D ∈ F, D ≠ C → ClauseSat a D) :
    ∃ L ∈ π, ∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit := by
  classical
  by_contra hC
  obtain ⟨a, ha⟩ := crit
  have hold := syn_lines_hold_of_used_axioms hπ.1 a (fun D hD hrep =>
    ha D hD (fun h => hC (h ▸ hrep)))
  obtain ⟨_, he, _⟩ := hold [] hπ.2
  simp at he

end PEqualNP.Search.Helpers
