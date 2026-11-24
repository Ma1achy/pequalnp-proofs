import PEqualNP.Search.Helpers.QCoordinateCases

/-! Compile a certified clause-search leaf into a syntactic integer-resolution derivation. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

private theorem literalWeight (lits : List (PEqualNP.ProofComplexity.Literal V)) :
    qWeight (lits.map litQEq) ≤ 3*lits.length := by
  induction lits with
  | nil => simp
  | cons l ls ih =>
    change (litQEq l).size + qWeight (ls.map litQEq) ≤ 3*(ls.length+1)
    have := litQEq_size l
    omega

/-- A path whose assignments all falsify one input clause can be added in two lines,
including when its signed coordinates conflict and it has no assignments. -/
theorem qCoordinateLeaf (path : List (V × Bool)) (C : PEqualNP.ProofComplexity.Clause V)
    (cert : ∀ a : V → Bool, (∀ l ∈ path, a l.1 ≠ l.2) → C ∈ F ∧ ¬ ClauseSat a C) :
    QCanAdd F ∅ (path.map litQEq) (2*(1+4*path.length)) := by
  classical
  intro ρ d _
  suffices input : ∃ lits : List (PEqualNP.ProofComplexity.Literal V), lits.length ≤ path.length ∧
      (∀ l ∈ lits, l ∈ path) ∧ IsResLinQSynDerivation F (lits.map litQEq :: ρ) by
    obtain ⟨lits,len,sub,valid⟩ := input
    have weakened : IsResLinQSynDerivation F (path.map litQEq :: lits.map litQEq :: ρ) := by
      apply IsResLinQSynDerivation.weaken valid List.mem_cons_self
      intro e he
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      exact List.mem_map.mpr ⟨l, sub l hl, rfl⟩
    refine ⟨[path.map litQEq, lits.map litQEq], weakened, List.mem_cons_self, ?_⟩
    change (1 + qWeight (path.map litQEq)) + ((1 + qWeight (lits.map litQEq)) + 0) ≤ _
    have := literalWeight path
    have := literalWeight lits
    omega
  by_cases clash : ∃ v : V, (v,false) ∈ path ∧ (v,true) ∈ path
  · obtain ⟨v,hf,ht⟩ := clash
    let lits : List (PEqualNP.ProofComplexity.Literal V) := [(v,false), (v,true)]
    have sub : ∀ l ∈ lits, l ∈ path := by simpa [lits] using And.intro hf ht
    have inclusion : lits.toFinset ⊆ path.toFinset :=
      fun l h => List.mem_toFinset.mpr (sub l (List.mem_toFinset.mp h))
    have size := (Finset.card_le_card inclusion).trans (List.toFinset_card_le path)
    exact ⟨lits, by simpa [lits] using size, sub, .bool v d⟩
  · let a (v : V) : Bool := decide ((v,false) ∈ path)
    have avoid : ∀ l ∈ path, a l.1 ≠ l.2 := by
      rintro ⟨v,b⟩ hp
      cases b with
      | false => simp [a,hp]
      | true =>
        have hf : (v,false) ∉ path := fun h => clash ⟨v,h,hp⟩
        simp [a,hf]
    have sub : ∀ l ∈ C, l ∈ path := by
      rintro ⟨v,b⟩ hc
      by_contra absent
      let a' (w : V) := if w = v then b else a w
      have avoid' : ∀ l ∈ path, a' l.1 ≠ l.2 := by
        rintro ⟨w,c⟩ hp
        by_cases hw : w = v
        · subst w
          have hbc : b ≠ c := by rintro rfl; exact absent hp
          simpa [a'] using hbc
        · simpa [a',hw] using avoid (w,c) hp
      exact (cert a' avoid').2 ⟨(v,b),hc,by simp [a']⟩
    have inclusion : C ⊆ path.toFinset := fun l h => List.mem_toFinset.mpr (sub l h)
    refine ⟨C.toList, ?_, by simpa using sub, ?_⟩
    · simpa using (Finset.card_le_card inclusion).trans (List.toFinset_card_le path)
    · exact .ax C d (cert a avoid).1 (by simp [eq_comm])

end PEqualNP.Search.Helpers
