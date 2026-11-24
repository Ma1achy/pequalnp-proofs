import PEqualNP.Search.Helpers.ParityRepairTree

/-! A parity clause whose counterexamples lie in a small list has a short
resolution proof from any unsatisfiable input CNF. A coordinate query only
branches when it separates two possible counterexamples. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Recover the queried bit and the child path from a falsified singleton-query path. -/
theorem singleton_node_cell {V : Type} [DecidableEq V] (v : V) (lo hi : ParityTree V)
    {b : Bool} {B : PEqualNP.ProofComplexity.LinClause V} (hm : (b, B) ∈ (ParityTree.node {v} lo hi).cells) :
    (∃ B', (b, B') ∈ lo.cells ∧
      ∀ a, ¬ LinClauseSat a B → a v = false ∧ ¬ LinClauseSat a B') ∨
    (∃ B', (b, B') ∈ hi.cells ∧
      ∀ a, ¬ LinClauseSat a B → a v = true ∧ ¬ LinClauseSat a B') := by
  have branch (t : ParityTree V) (c : Bool)
      (h : (b, B) ∈ t.cellsAt {({v}, !c)}) :
      ∃ B', (b, B') ∈ t.cells ∧ ∀ a, ¬ LinClauseSat a B → a v = c ∧ ¬ LinClauseSat a B' := by
    rw [ParityTree.cellsAt_eq_map] at h
    obtain ⟨⟨b', B'⟩, hm', eq⟩ := List.mem_map.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    refine ⟨B', hm', fun a hf => ⟨?_, ?_⟩⟩
    · have noHead : ¬ LinEqSat a (({v} : Finset V), !c) := fun hs =>
        hf ⟨_, Finset.mem_union_left _ (Finset.mem_singleton_self _), hs⟩
      cases c <;> cases hval : a v <;> simp_all [LinEqSat, Finset.filter_singleton]
    · exact fun ⟨e, he, hs⟩ => hf ⟨e, Finset.mem_union_right _ he, hs⟩
  change (b,B) ∈ lo.cellsAt (insert ({v}, true) ∅) ++ hi.cellsAt (insert ({v}, false) ∅) at hm
  rcases List.mem_append.mp hm with hlo | hhi
  · exact Or.inl (branch lo false hlo)
  · exact Or.inr (branch hi true hhi)

variable {V : Type} [DecidableEq V]

/-- A coordinate-query tree distinguishes the members of X using at most
one leaf per member. An empty X needs just one leaf. -/
theorem distinguish_points (X : Finset (V → Bool)) :
    ∃ t : ParityTree V, t.leaves ≤ max 1 X.card ∧
      ∀ b C, (b, C) ∈ t.cells → ∀ a ∈ X, ∀ z ∈ X,
        ¬ LinClauseSat a C → ¬ LinClauseSat z C → a = z := by
  classical
  by_cases hsmall : X.card ≤ 1
  · refine ⟨.leaf false, by simp [ParityTree.leaves], ?_⟩
    intro b C hm a ha z hz _ _
    exact Finset.card_le_one.mp hsmall a ha z hz
  obtain ⟨v, -, smaller⟩ := Finset.exists_of_one_lt_card_pi (Nat.lt_of_not_ge hsmall)
  let A := X.filter (fun a => a v = false)
  let B := X.filter (fun a => a v = true)
  have ltA : A.card < X.card := Finset.card_lt_card (smaller false)
  have ltB : B.card < X.card := Finset.card_lt_card (smaller true)
  have tot : B.card + A.card = X.card := by
    simpa [A, B] using X.card_filter_add_card_filter_not (fun a => a v = true)
  obtain ⟨lo, nlo, slo⟩ := distinguish_points A
  obtain ⟨hi, nhi, shi⟩ := distinguish_points B
  refine ⟨.node {v} lo hi, ?_, ?_⟩
  · simp only [ParityTree.leaves]
    omega
  · intro b C hm a ha z hz hna hnz
    rcases singleton_node_cell v lo hi hm with ⟨T, ht, part⟩ | ⟨T, ht, part⟩
    · obtain ⟨hva, hnA⟩ := part a hna
      obtain ⟨hvz, hnZ⟩ := part z hnz
      exact slo b T ht a (Finset.mem_filter.mpr ⟨ha, hva⟩) z (Finset.mem_filter.mpr ⟨hz, hvz⟩) hnA hnZ
    · obtain ⟨hva, hnA⟩ := part a hna
      obtain ⟨hvz, hnZ⟩ := part z hnz
      exact shi b T ht a (Finset.mem_filter.mpr ⟨ha, hva⟩) z (Finset.mem_filter.mpr ⟨hz, hvz⟩) hnA hnZ
termination_by X.card

/-- A parity clause with b possible falsifying assignments can be derived from
any unsatisfiable input CNF using at most 3b+2 lines. The false assignment
at a nonempty leaf determines an input axiom that implies its guard. -/
theorem parity_point_cover (F : Set (PEqualNP.ProofComplexity.Clause V)) (R : PEqualNP.ProofComplexity.LinClause V)
    (X : Finset (V → Bool)) (cover : ∀ a, ¬ LinClauseSat a R → a ∈ X)
    (unsat : ∀ a, ∃ C ∈ F, ¬ ClauseSat a C) :
    CanAdd (linOfClause '' F) ∅ R (3 * X.card + 2) := by
  classical
  obtain ⟨t, hlen, hsep⟩ := distinguish_points X
  have search (b : Bool) (B : PEqualNP.ProofComplexity.LinClause V) (hm : (b, B) ∈ t.cells) :
      ∃ C ∈ F, ∀ a, ¬ LinClauseSat a R → ¬ LinClauseSat a B → ¬ ClauseSat a C := by
    by_cases h : ∃ a, ¬ LinClauseSat a R ∧ ¬ LinClauseSat a B
    · obtain ⟨x, xr, xb⟩ := h
      obtain ⟨C, hc, hf⟩ := unsat x
      refine ⟨C, hc, ?_⟩
      intro a ar ab
      have eq := hsep b B hm a (cover a ar) x (cover x xr) ab xb
      simpa [eq] using hf
    · obtain ⟨C, hc, -⟩ := unsat (fun _ => false)
      exact ⟨C, hc, fun a ar ab => False.elim (h ⟨a, ar, ab⟩)⟩
  obtain ⟨σ, ds, hm, cost⟩ := repair_from_parity_tree R t search
  intro ρ dρ _
  refine ⟨σ, PEqualNP.ProofComplexity.Recomb.deriv_append dρ ds (fun _ h => Or.inl h),
    List.mem_append_left _ hm, ?_⟩
  omega

theorem parity_point_cover_list (F : Set (PEqualNP.ProofComplexity.Clause V)) (R : PEqualNP.ProofComplexity.LinClause V)
    (X : List (V → Bool)) (cover : ∀ a, ¬ LinClauseSat a R → a ∈ X)
    (unsat : ∀ a, ∃ C ∈ F, ¬ ClauseSat a C) :
    CanAdd (linOfClause '' F) ∅ R (3 * X.length + 2) := by
  classical
  have h := parity_point_cover F R X.toFinset (fun a ha => List.mem_toFinset.mpr (cover a ha)) unsat
  intro ρ dρ γ
  obtain ⟨σ, ds, hR, sz⟩ := h ρ dρ γ
  have := List.toFinset_card_le X
  exact ⟨σ, ds, hR, by omega⟩

end PEqualNP.Search.Helpers
