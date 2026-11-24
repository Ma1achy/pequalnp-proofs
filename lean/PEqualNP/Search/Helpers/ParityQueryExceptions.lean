import PEqualNP.Search.Helpers.ParityQuerySupport

/-!
# Querying a support with a finite exceptional set

On each pattern of W, either one input clause suffices or every relevant point
belongs to the exceptional set X. Distinguish exceptional points only in the
second kind of leaf. The children of a coordinate query partition X, so each
exception contributes at most one extra leaf in the whole construction.
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

private abbrev Point (V : Type) := V → Bool

private def Agreement (W : Finset V) (y a : Point V) : Prop := ∀ v ∈ W, y v = a v

private def CommonOrExceptional (F : Set (PEqualNP.ProofComplexity.Clause V))
    (active : Point V → Prop) (W : Finset V) (X : Finset (Point V)) : Prop :=
  ∀ a, (∃ C ∈ F, ∀ y, Agreement W y a → active y → ¬ ClauseSat y C) ∨
    (∀ y, Agreement W y a → active y → y ∈ X)

private def FindsInput (F : Set (PEqualNP.ProofComplexity.Clause V)) (active : Point V → Prop)
    (t : ParityTree V) : Prop :=
  ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F,
    ∀ a, active a → ¬ LinClauseSat a B → ¬ ClauseSat a C

private theorem exceptions_only (F : Set (PEqualNP.ProofComplexity.Clause V)) (hne : F.Nonempty)
    (active : Point V → Prop) (X : Finset (Point V)) (covered : ∀ a, active a → a ∈ X)
    (bad : ∀ a ∈ X, ∃ C ∈ F, ¬ ClauseSat a C) :
    ∃ t : ParityTree V, t.leaves ≤ max 1 X.card ∧ FindsInput F active t := by
  classical
  obtain ⟨t, cost, separate⟩ := distinguish_points X
  refine ⟨t, cost, ?_⟩
  intro b B hm
  by_cases h : ∃ a, active a ∧ ¬ LinClauseSat a B
  · obtain ⟨x, hx, hb⟩ := h
    obtain ⟨C, hc, hbad⟩ := bad x (covered x hx)
    refine ⟨C, hc, ?_⟩
    intro a ha hB
    have eq := separate b B hm a (covered a ha) x (covered x hx) hB hb
    exact eq ▸ hbad
  · obtain ⟨C, hc⟩ := hne
    exact ⟨C, hc, fun a ha hB => False.elim (h ⟨a, ha, hB⟩)⟩

private theorem query_patterns (F : Set (PEqualNP.ProofComplexity.Clause V)) (hne : F.Nonempty)
    (W : Finset V) (X : Finset (Point V)) (active : Point V → Prop)
    (patterns : CommonOrExceptional F active W X)
    (bad : ∀ a ∈ X, ∃ C ∈ F, ¬ ClauseSat a C) :
    ∃ t : ParityTree V, t.leaves ≤ 2 ^ W.card + X.card ∧ FindsInput F active t := by
  classical
  induction W using Finset.induction_on generalizing X active with
  | empty =>
    rcases patterns (fun _ => false) with ⟨C, hc, hit⟩ | all
    · refine ⟨.leaf false, by simp [ParityTree.leaves], ?_⟩
      exact fun _ _ _ => ⟨C, hc, fun a ha _ => hit a (by simp [Agreement]) ha⟩
    · obtain ⟨t, cost, good⟩ := exceptions_only F hne active X
          (fun a ha => all a (by simp [Agreement]) ha) bad
      refine ⟨t, cost.trans ?_, good⟩
      simp
  | @insert v W hv ih =>
    let part (b : Bool) := X.filter (fun a => a v = b)
    let live (b : Bool) (a : Point V) := active a ∧ a v = b
    have child (b : Bool) : CommonOrExceptional F (live b) W (part b) := by
      intro a
      let x : Point V := Function.update a v b
      have agreement (y : Point V) (hy : Agreement W y a) (hl : live b y) :
          Agreement (insert v W) y x := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hW
        · simpa [x] using hl.2
        · have ne : i ≠ v := fun e => hv (e ▸ hW)
          simpa [x, Function.update_of_ne ne] using hy i hW
      rcases patterns x with ⟨C, hc, hit⟩ | all
      · exact Or.inl ⟨C, hc, fun y hy hl => hit y (agreement y hy hl) hl.1⟩
      · exact Or.inr (fun y hy hl => Finset.mem_filter.mpr ⟨all y (agreement y hy hl) hl.1, hl.2⟩)
    have input (b : Bool) : ∀ a ∈ part b, ∃ C ∈ F, ¬ ClauseSat a C :=
      fun a ha => bad a (Finset.mem_filter.mp ha).1
    obtain ⟨lo, hlo, slo⟩ := ih (part false) (live false) (child false) (input false)
    obtain ⟨hi, hhi, shi⟩ := ih (part true) (live true) (child true) (input true)
    refine ⟨.node {v} lo hi, ?_, ?_⟩
    · have total : (part true).card + (part false).card = X.card := by
        simpa [part] using X.card_filter_add_card_filter_not (fun a => a v = true)
      simp only [ParityTree.leaves, Finset.card_insert_of_notMem hv, pow_succ]
      omega
    · intro b B hm
      rcases singleton_node_cell v lo hi hm with ⟨Q, hQ, side⟩ | ⟨Q, hQ, side⟩
      · obtain ⟨C, hc, hit⟩ := slo b Q hQ
        exact ⟨C, hc, fun y hy hf => hit y ⟨hy, (side y hf).1⟩ (side y hf).2⟩
      · obtain ⟨C, hc, hit⟩ := shi b Q hQ
        exact ⟨C, hc, fun y hy hf => hit y ⟨hy, (side y hf).1⟩ (side y hf).2⟩

/-- A pattern either names one violated input throughout its counterexamples
or has every counterexample in X. The exceptional allowance is paid only once. -/
theorem pattern_violation_except_tree (F : Set (PEqualNP.ProofComplexity.Clause V))
    (R : PEqualNP.ProofComplexity.LinClause V) (W : Finset V) (X : Finset (V → Bool))
    (hne : F.Nonempty)
    (patterns : ∀ a : V → Bool,
      (∃ C ∈ F, ∀ y, (∀ v ∈ W, y v = a v) → ¬ LinClauseSat y R → ¬ ClauseSat y C) ∨
      (∀ y, (∀ v ∈ W, y v = a v) → ¬ LinClauseSat y R → y ∈ X))
    (hex : ∀ a ∈ X, ∃ C ∈ F, ¬ ClauseSat a C) :
    ∃ t : ParityTree V, t.leaves ≤ 2 ^ W.card + X.card ∧
      ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F, ∀ a,
        ¬ LinClauseSat a R → ¬ LinClauseSat a B → ¬ ClauseSat a C :=
  query_patterns F hne W X (fun a => ¬ LinClauseSat a R) patterns hex

/-- If every nonexceptional counterexample violates a clause supported on W,
then a W-pattern containing such a counterexample names a common violated input. -/
theorem supported_violation_except_tree (F : Set (PEqualNP.ProofComplexity.Clause V))
    (R : PEqualNP.ProofComplexity.LinClause V) (W : Finset V) (X : Finset (V → Bool))
    (hne : F.Nonempty)
    (hlocal : ∀ a, ¬ LinClauseSat a R → a ∉ X →
      ∃ C ∈ F, (∀ lit ∈ C, lit.1 ∈ W) ∧ ¬ ClauseSat a C)
    (hex : ∀ a ∈ X, ∃ C ∈ F, ¬ ClauseSat a C) :
    ∃ t : ParityTree V, t.leaves ≤ 2 ^ W.card + X.card ∧
      ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F, ∀ a,
        ¬ LinClauseSat a R → ¬ LinClauseSat a B → ¬ ClauseSat a C := by
  classical
  apply pattern_violation_except_tree F R W X hne _ hex
  intro a
  by_cases h : ∃ x : V → Bool, (∀ v ∈ W, x v = a v) ∧ ¬ LinClauseSat x R ∧ x ∉ X
  · obtain ⟨x, eq, hx, hX⟩ := h
    obtain ⟨C, hc, supp, bad⟩ := hlocal x hx hX
    refine Or.inl ⟨C, hc, ?_⟩
    rintro y hey _ ⟨lit, hlit, val⟩
    have hm := supp lit hlit
    exact bad ⟨lit, hlit, (eq lit.1 hm).trans ((hey lit.1 hm).symm.trans val)⟩
  · exact Or.inr fun y hy hr => by
      by_contra no
      exact h ⟨y, hy, hr, no⟩

end PEqualNP.Search.Helpers
