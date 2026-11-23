import PEqualNP.Search.Helpers.ParityTreeRules
import PEqualNP.Search.Helpers.ParityBatch
import PEqualNP.Search.Helpers.QSynMerges
import PEqualNP.ProofComplexity.Helpers.Lin

/-! Compile a proof line by line. Each integer line has its own parity decision tree;
no common partition of the Boolean cube is assumed. The false leaves of a tree
supply all parity clauses needed when a later inference uses that line. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]

private def falseCells (t : ParityTree V) :=
  (t.cells.filter (fun z => !z.1)).map Prod.snd

omit [Fintype V] in
private theorem mem_falseCells (t : ParityTree V) (C : PEqualNP.ProofComplexity.LinClause V) :
    C ∈ falseCells t ↔ (false, C) ∈ t.cells := by
  simp only [falseCells, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨b, K⟩, ⟨hK, hb⟩, rfl⟩
    cases b <;> simp_all
  · intro h
    exact ⟨(false, C), ⟨h, rfl⟩, rfl⟩

omit [Fintype V] in
private theorem falseCells_length (t : ParityTree V) : (falseCells t).length ≤ t.leaves := by
  calc
    (falseCells t).length ≤ t.cells.length := by
      simpa only [falseCells, List.length_map] using List.length_filter_le _ t.cells
    _ = t.leaves := t.length_cellsAt ∅

omit [Fintype V] in
private theorem larger_budget {F Γ : Set (PEqualNP.ProofComplexity.LinClause V)} {G : PEqualNP.ProofComplexity.LinClause V} {m n : ℕ}
    (h : CanAdd F Γ G m) (hm : m ≤ n) : CanAdd F Γ G n := by
  intro ρ d hΓ
  obtain ⟨σ, dσ, hG, hk⟩ := h ρ d hΓ
  exact ⟨σ, dσ, hG, hk.trans hm⟩

private def stepCost (r : ℕ) := 4 * (r + 1) * (r + 1)

omit [Fintype V] [DecidableEq V] in
private theorem pairCost {t u : ParityTree V} {r : ℕ} (ht : t.leaves ≤ r) (hu : u.leaves ≤ r) :
    4 * (t.leaves + 1) * (u.leaves + 1) ≤ stepCost r :=
  Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.succ_le_succ ht)) (Nat.succ_le_succ hu)

omit [Fintype V] in
private theorem input_leaf {F : Set (PEqualNP.ProofComplexity.Clause V)} {Γ : Set (PEqualNP.ProofComplexity.LinClause V)}
    {C : PEqualNP.ProofComplexity.Clause V} (hC : C ∈ F) {G : PEqualNP.ProofComplexity.LinClause V}
    (imp : ∀ a, ClauseSat a C → LinClauseSat a G) :
    CanAdd (linOfClause '' F) Γ G 2 := by
  intro ρ d _
  have dC := d.ax (Set.mem_image_of_mem linOfClause hC)
  refine ⟨[G, linOfClause C], dC.weak List.mem_cons_self ?_, List.mem_cons_self, by simp⟩
  exact fun a h => imp a ((PEqualNP.ProofComplexity.Helpers.linOfClause_sat a C).mp h)

private def Compiled (F : Set (PEqualNP.ProofComplexity.Clause V)) (r : ℕ) (trees : QLine V → ParityTree V)
    (π : List (QLine V)) : Prop :=
  ∃ ρ : List (PEqualNP.ProofComplexity.LinClause V), IsLinDerivation (linOfClause '' F) ρ ∧ ρ ≠ [] ∧
    (∀ L ∈ π, ∀ C, (false,C) ∈ (trees L).cells → C ∈ ρ) ∧
    ρ.length ≤ π.length * (r * stepCost r) + 1

private theorem extend_compiled {F : Set (PEqualNP.ProofComplexity.Clause V)} {r : ℕ} {trees : QLine V → ParityTree V}
    {π : List (QLine V)} {L : QLine V}
    (old : Compiled F r trees π) (hr : (trees L).leaves ≤ r)
    (recipe : ∀ Γ : Set (PEqualNP.ProofComplexity.LinClause V), Γ.Nonempty →
      (∀ K ∈ π, ∀ C, (false,C) ∈ (trees K).cells → C ∈ Γ) →
      ∀ G, (false,G) ∈ (trees L).cells → CanAdd (linOfClause '' F) Γ G (stepCost r)) :
    Compiled F r trees (L :: π) := by
  obtain ⟨ρ, d, hn, previous, len⟩ := old
  let Γ : Set (PEqualNP.ProofComplexity.LinClause V) := {C | C ∈ ρ}
  have rcp := recipe Γ (List.exists_mem_of_ne_nil ρ hn) previous
  obtain ⟨σ, dσ, new, cost⟩ := canAdd_many (falseCells (trees L)) (stepCost r)
    (fun G h => rcp G ((mem_falseCells _ _).mp h)) ρ d (fun _ h => h)
  refine ⟨σ ++ ρ, dσ, by simp [hn], ?_, ?_⟩
  · intro K hK C hc
    rcases List.mem_cons.mp hK with rfl | hK
    · exact new C ((mem_falseCells _ _).mpr hc)
    · exact List.mem_append_right _ (previous _ hK _ hc)
  · have bound := cost.trans (Nat.mul_le_mul_right _ ((falseCells_length _).trans hr))
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem compile_trace_trees {F : Set (PEqualNP.ProofComplexity.Clause V)} (seed : F.Nonempty)
    (r : ℕ) (trees : QLine V → ParityTree V) {π : List (QLine V)} {k : ℕ}
    (trace : QSynMergeTrace F π k)
    (rep : ∀ K ∈ π, (trees K).leaves ≤ r ∧ ∀ a, (trees K).eval a = true ↔ QLine.Holds a K) :
    Compiled F r trees π := by
  classical
  induction trace with
  | nil =>
    obtain ⟨C,hC⟩ := seed
    exact ⟨[linOfClause C], .ax .nil ⟨C,hC,rfl⟩, by simp, by simp, by simp⟩
  | @input π k L C _ hC imp ih =>
    obtain ⟨hr, hrep⟩ := rep L List.mem_cons_self
    apply extend_compiled (ih (fun K hK => rep K (List.mem_cons_of_mem _ hK))) hr
    intro Γ _ _ G hG
    apply larger_budget (input_leaf hC ?_) (by unfold stepCost; nlinarith)
    intro a ha
    by_contra hn
    have hf := (trees L).eval_of_mem_cells a hG hn
    have ht := (hrep a).mpr (imp a ha)
    simp_all
  | @step π k L parents _ hlen hmem imp ih =>
    have prev := fun K (hK : K ∈ π) => rep K (List.mem_cons_of_mem _ hK)
    apply extend_compiled (ih prev) (rep L List.mem_cons_self).1
    intro Γ hn stored G hG
    have finish (a) (h : ∀ K ∈ parents, QLine.Holds a K) : LinClauseSat a G := by
      by_contra ng
      have hf := (trees L).eval_of_mem_cells a hG ng
      have ht := ((rep L List.mem_cons_self).2 a).mpr (imp a h)
      simp_all
    cases parents with
    | nil =>
      apply larger_budget (CanAdd.of_tautology hn (fun a => finish a (by simp)))
      unfold stepCost
      nlinarith
    | cons A tail =>
      have ha := hmem A List.mem_cons_self
      cases tail with
      | nil =>
        apply larger_budget (tree_implies_clause (trees A) G hn (stored A ha) ?_)
          (pairCost (prev A ha).1 (prev A ha).1)
        exact fun a h => finish a (by simpa using ((prev A ha).2 a).mp h)
      | cons B rest =>
        have hempty : rest = [] := by cases rest <;> simp_all
        subst rest
        have hb := hmem B (by simp)
        apply larger_budget (trees_imply_clause (trees A) (trees B) G hn (stored A ha) (stored B hb) ?_)
          (pairCost (prev A ha).1 (prev B hb).1)
        exact fun a h₁ h₂ => finish a (by simpa using And.intro (((prev A ha).2 a).mp h₁) (((prev B hb).2 a).mp h₂))

/-- If each line of an integer proof can be decided by some parity decision tree
with at most r leaves, the whole DAG has a parity refutation of polynomially
related length. Different proof lines may query completely different parities. -/
theorem parity_refutation_of_small_trees {F : Set (PEqualNP.ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) (r : ℕ)
    (repr : ∀ L ∈ π, ∃ t : ParityTree V, t.leaves ≤ r ∧
      ∀ a, t.eval a = true ↔ QLine.Holds a L) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ π.length * (r * (4 * (r+1) * (r+1))) + 1 := by
  classical
  have hr := (repr [] hπ.2).choose_spec.1
  have hrpos := (repr [] hπ.2).choose.leaves_pos
  let trees (L : QLine V) := if L = [] then ParityTree.leaf false else
    if h : L ∈ π then (repr L h).choose else ParityTree.leaf false
  have rep (L) (hL : L ∈ π) : (trees L).leaves ≤ r ∧
      ∀ a, (trees L).eval a = true ↔ QLine.Holds a L := by
    by_cases he : L = []
    · subst L
      simpa [trees, ParityTree.leaves, ParityTree.eval, QLine.Holds] using
        (show 1 ≤ r by omega)
    · simpa [trees, he, hL] using (repr L hL).choose_spec
  obtain ⟨k,trace⟩ := exists_merge_trace hπ.1
  obtain ⟨ρ, d, _, lines, cost⟩ := compile_trace_trees seed r trees trace rep
  exact ⟨ρ, ⟨d, lines [] hπ.2 ∅ (by simp [trees, ParityTree.cells, ParityTree.cellsAt])⟩, cost⟩

end PEqualNP.Search.Helpers
