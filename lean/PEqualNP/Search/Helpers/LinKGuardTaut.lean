import PEqualNP.ProofComplexity.Helpers.LinKSplit

/-! A parity path's blocking clause and its complementary conjunction give a short
Res(k, ⊕) tautology. Extend the conjunction by one equation per and-introduction. -/
namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity
open PEqualNP.ProofComplexity.Helpers.LinKSplit

variable {V : Type} [DecidableEq V]

/-- The term that holds when the blocking clause is false. -/
def guardTerm (B : LinClause V) : LinTerm V := B.image negLinEq

/-- A linear clause represented as a disjunction of one-equation terms. -/
def guardSingles (B : LinClause V) : LinKLine V := B.image (fun q => ({q} : LinTerm V))

theorem guardTerm_sat_iff (a : V → Bool) (B : LinClause V) :
    LinTermSat a (guardTerm B) ↔ ¬ LinClauseSat a B := by
  have neg (q : LinEq V) : LinEqSat a (negLinEq q) ↔ ¬ LinEqSat a q := by
    rcases q with ⟨f, b⟩
    cases b <;> simp [LinEqSat, negLinEq]
  constructor
  · rintro hs ⟨q, hq, hsat⟩
    exact (neg q).mp (hs _ (Finset.mem_image_of_mem _ hq)) hsat
  · rintro hs e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    exact (neg q).mpr (fun hsat => hs ⟨q, hq, hsat⟩)

private abbrev guardLine (B : LinClause V) : LinKLine V := {guardTerm B} ∪ guardSingles B

private theorem guardLine_width {B : LinClause V} {k : ℕ} (hk : 1 ≤ k) (hB : B.card ≤ k) :
    ∀ T ∈ guardLine B, T.card ≤ k := by
  intro T hT
  rcases Finset.mem_union.mp hT with h | h
  · rw [Finset.mem_singleton.mp h]
    exact (Finset.card_image_le).trans hB
  · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
    simpa using hk

/-- From a nonempty derivation, add a proof of the complementary path term
disjoined with its blocking clause. The construction adds at most three lines per
equation after the initial tautology. -/
theorem linK_guard_taut {k : ℕ} {F : Set (LinKLine V)} {ρ : List (LinKLine V)}
    (B : LinClause V) (hk : 1 ≤ k) (hB : B.card ≤ k)
    (hρ : IsLinKDerivation k IsLinKWeakening F ρ) (hne : ρ ≠ []) :
    ∃ σ, IsLinKDerivation k IsLinKWeakening F (σ ++ ρ) ∧
      ({guardTerm B} ∪ guardSingles B : LinKLine V) ∈ σ ∧ σ.length ≤ 4 * (B.card + 1) := by
  obtain ⟨L, hL⟩ := List.exists_mem_of_ne_nil ρ hne
  induction B using Finset.induction_on with
  | empty =>
    have hw : IsLinKWeakening L (guardLine (∅ : LinClause V)) := by
      intro T _
      left
      refine ⟨∅, by simp [guardTerm,guardLine,guardSingles], ?_⟩
      simp [LinTermSat]
    exact ⟨[guardLine ∅], .weak hρ hL hw (guardLine_width hk hB), by simp, by simp⟩
  | @insert q B hq ih =>
    have hsub : B.card ≤ k := (Finset.card_le_card (Finset.subset_insert q B)).trans hB
    obtain ⟨σ, hσ, hprev, hlen⟩ := ih hsub
    let C := guardLine B
    let D := tautLine q.1
    let R := (C.erase (guardTerm B) ∪ D.erase {negLinEq q}) ∪
      {guardTerm B ∪ {negLinEq q}}
    have hC : C ∈ σ ++ ρ := List.mem_append_left _ hprev
    have hD := taut_line hk hσ hC q.1
    have negInD : ({negLinEq q} : LinTerm V) ∈ D := by
      rcases q with ⟨f, b⟩
      cases b <;> simp [D, tautLine, negLinEq]
    have hnc : guardTerm B ∈ C := Finset.mem_union_left _ (Finset.mem_singleton_self _)
    have hand : IsLinKAndIntro C D R := ⟨guardTerm B, {negLinEq q}, hnc, negInD, rfl⟩
    have smaller : R ⊆ guardLine (insert q B) := by
      intro T hT
      rcases Finset.mem_union.mp hT with h | h
      · rcases Finset.mem_union.mp h with h | h
        · have hc := Finset.mem_union.mp (Finset.mem_of_mem_erase h)
          rcases hc with heq | hB'
          · exact False.elim ((Finset.ne_of_mem_erase h) (Finset.mem_singleton.mp heq))
          · exact Finset.mem_union_right _ (Finset.image_subset_image (Finset.subset_insert q B) hB')
        · have heq : T = {q} := by
            have hm := (mem_tautLine _ T).mp (Finset.mem_of_mem_erase h)
            have hn := Finset.ne_of_mem_erase h
            rcases q with ⟨f,b⟩
            cases b <;> simp_all [negLinEq]
          rw [heq]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
      · apply Finset.mem_union_left
        rw [Finset.mem_singleton.mp h]
        simp [guardTerm]
    have width := guardLine_width hk hB
    have dR := IsLinKDerivation.andIntro hD (List.mem_cons_of_mem _ hC)
      List.mem_cons_self hand (fun T hT => width T (smaller hT))
    have weak : IsLinKWeakening R (guardLine (insert q B)) := fun T hT =>
      Or.inl ⟨T, smaller hT, fun _ hs => hs⟩
    refine ⟨guardLine (insert q B) :: R :: D :: σ,
      .weak dR List.mem_cons_self weak width, List.mem_cons_self, ?_⟩
    simp only [List.length_cons, Finset.card_insert_of_notMem hq]
    omega

end PEqualNP.Search.Helpers
