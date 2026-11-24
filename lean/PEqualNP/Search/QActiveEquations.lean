import PEqualNP.Search.QEquationSimulation
import PEqualNP.Search.BPHPHardCancellation

/-! Equations on the boundary of the integer resolution inferences can be projected
to constants. Exact small trees suffice where a produced equation is also selected. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

variable {V : Type}

/-- An integer equation is the combined head at a resolution site in the trace. -/
def QProduced (π : List (QLine V)) (e : QEq V) : Prop :=
  ∃ s : ResolutionSite π, (s.α • s.firstHead.1 + s.β • s.secondHead.1,
    s.α*s.firstHead.2 + s.β*s.secondHead.2) = e

/-- An integer equation is selected as one of the two heads at a resolution site. -/
def QSelected (π : List (QLine V)) (e : QEq V) : Prop :=
  ∃ s : ResolutionSite π, s.firstHead = e ∨ s.secondHead = e

variable [Fintype V] [DecidableEq V]

/-- Compile exact codes where a produced equation is also selected. Elsewhere
a selected-only equation may be sent to false, and a produced-only equation to true. -/
theorem active_code_equation_simulation (k : ℕ) (hk : 1 ≤ k)
    {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π) (easy : QEq V → Prop)
    (repr : ∀ e, easy e → ParityTree V) (easyLit : ∀ t : V × Bool, easy (litQEq t))
    (literal : ∀ t : V × Bool, treeDNF (repr _ (easyLit t)) = {({({t.1},t.2)} : LinTerm V)})
    (exactCode : ∀ e (h : easy e) a, (repr e h).eval a = true ↔ QEq.Holds a e)
    (limits : ∀ e (h : easy e), (repr e h).leaves ≤ 2^k ∧
      ∀ B, (true,B) ∈ (repr e h).cells → B.card ≤ k)
    (short : ∀ e, QProduced π e → QSelected π e → easy e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let trees (e : QEq V) : ParityTree V := if h : easy e then repr e h
    else .leaf (decide (QProduced π e ∧ ¬ (e.1 = 0 ∧ e.2 ≠ 0)))
  have evaluate (e : QEq V) (h : easy e) (a : V → Bool) :
      (trees e).eval a = true ↔ QEq.Holds a e := by
    simpa only [trees, dite_eq_left h] using exactCode e h a
  have input (e : QEq V) (hs : QSelected π e) (a : V → Bool) (he : (trees e).eval a = true) :
      QEq.Holds a e := by
    by_cases h : easy e
    · exact (evaluate e h a).mp he
    · have hp : ¬ QProduced π e := fun hp => h (short e hp hs)
      simp [trees,h,hp,ParityTree.eval] at he
  have output (e : QEq V) (hp : QProduced π e) (a : V → Bool) (he : QEq.Holds a e) :
      (trees e).eval a = true := by
    by_cases h : easy e
    · exact (evaluate e h a).mpr he
    · have alive : ¬ (e.1 = 0 ∧ e.2 ≠ 0) := by
        rintro ⟨hz,hn⟩
        exact hn (by simpa [QEq.Holds,hz] using he.symm)
      simp only [trees, dite_eq_right h, ParityTree.eval, decide_eq_true_eq]
      exact ⟨hp,alive⟩
  apply equation_tree_step_compilation k hk seed ref trees
  · intro t
    simp only [trees, dite_eq_left (easyLit t)]
    exact literal t
  · intro e hz hn a he
    by_cases h : easy e
    · have ha := (evaluate e h a).mp he
      exact hn (by simpa [QEq.Holds,hz] using ha.symm)
    · simp [trees,h,hz,hn,ParityTree.eval] at he
  · intro L hL e he
    by_cases h : easy e
    · simp only [trees, dite_eq_left h]
      exact limits e h
    · simp only [trees, dite_eq_right h, ParityTree.leaves, ParityTree.cells, ParityTree.cellsAt,
        List.mem_singleton, Prod.mk.injEq]
      exact ⟨Nat.one_le_two_pow, fun _ eq => by simp [eq.2]⟩
  · intro front tail e f C D α β g pos left right a he hf
    let s : ResolutionSite π := ⟨front,tail,e,f,C,D,α,β,pos,left,right⟩
    exact output g ⟨s,rfl⟩ a (combo_holds a e f α β
      (input e ⟨s,Or.inl rfl⟩ a he) (input f ⟨s,Or.inr rfl⟩ a hf))

/-- A bounded list of fixed parity queries gives an exact code at every
equation that is both a resolution output and a selected premise. -/
theorem active_parity_query_equation_simulation (k : ℕ) (hk : 1 ≤ k)
    {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π)
    (short : ∀ e, QProduced π e → QSelected π e →
      ∃ Q : List (Finset V), Q.length ≤ k ∧ QDetermined Q e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let easy (e : QEq V) := ∃ Q : List (Finset V), Q.length ≤ k ∧ QDetermined Q e
  have easyLit (t : V × Bool) : easy (litQEq t) := by
    refine ⟨supportQueries _, ?_, supportQueries_determine _⟩
    rw [supportQueries_length]
    have subset : Finset.univ.filter (fun v => (litQEq t).1 v ≠ 0) ⊆ {t.1} := by
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      by_contra h
      exact hv' (by simp [litQEq, Finset.notMem_singleton.mp h])
    exact (Finset.card_le_card subset).trans (by simpa using hk)
  apply active_code_equation_simulation k hk seed ref easy
    (fun e h => qCodeTree h.choose e) easyLit (fun t => qCode_lit _ t)
    (fun e h a => qCodeTree_eval h.choose e a h.choose_spec.2) _ short
  intro e h
  exact ⟨qCodeTree_leaves _ _ hk h.choose_spec.1,
    fun B hB => qCodeTree_cell_width _ _ hk h.choose_spec.1 _ _ hB⟩

/-- A coefficient-support bound on produced and selected equations gives the
same length simulation, regardless of every remaining equation's support. -/
theorem active_sparse_equation_simulation (k : ℕ) (hk : 1 ≤ k)
    {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π)
    (short : ∀ e, QProduced π e → QSelected π e →
      (Finset.univ.filter (fun v => e.1 v ≠ 0)).card ≤ k) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  apply active_parity_query_equation_simulation k hk seed ref
  intro e p s
  exact ⟨supportQueries e, by simpa using short e p s, supportQueries_determine e⟩

end PEqualNP.Search
