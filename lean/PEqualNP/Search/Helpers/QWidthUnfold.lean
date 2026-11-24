import PEqualNP.Search.Helpers.BPHPTreeRate
import PEqualNP.Search.Helpers.QSynEssential
import PEqualNP.Search.Helpers.QDeferSimp

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}

/-- The two unary rules of the syntactic integer proof system. -/
def UnaryWidthRule (C D : QLine V) : Prop :=
  (∀ e ∈ C, e ∈ D) ∨ D = C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))

/-- Account for local drops in list width at unary syntactic rule applications.
The total loss unfolds their uses with multiplicity. A Boolean axiom is an input
of the syntactic proof, including when its semantic-tree realization uses weakening. -/
structure QWidthUnfolding (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (QLine V))
    (unary : QLine V → QLine V → Prop := UnaryWidthRule) where
  parents : Fin π.length → List (Fin π.length)
  later : ∀ i j, j ∈ parents i → i < j
  tree : (i : Fin π.length) → ResLinQTree F (π.get i)
  loss : Fin π.length → ℕ
  totalLoss : Fin π.length → ℕ
  loss_spec : ∀ i, 0 < loss i → ∃ j, parents i = [j] ∧
    loss i = (π.get j).length - (π.get i).length
  loss_rule : ∀ i, 0 < loss i → ∃ j, parents i = [j] ∧ unary (π.get j) (π.get i)
  total_rec : ∀ i, totalLoss i = loss i + ((parents i).map totalLoss).sum
  potential : ∀ i, (Tree.axiomUses (tree i)).length + 1 ≤ totalLoss i + (π.get i).length

variable {U : QLine V → QLine V → Prop}

private def extendWidth (g : QWidthUnfolding F π U) {L : QLine V} (t : ResLinQTree F L)
    (deps : List (Fin π.length)) (d : ℕ)
    (hd : 0 < d → ∃ j, deps = [j] ∧ d = (π.get j).length - L.length)
    (hr : 0 < d → ∃ j, deps = [j] ∧ U (π.get j) L)
    (bound : (Tree.axiomUses t).length + 1 ≤ d + (deps.map g.totalLoss).sum + L.length) :
    QWidthUnfolding F (L :: π) U := by
  let parents : Fin (π.length + 1) → List (Fin (π.length + 1)) :=
    Fin.cases (deps.map Fin.succ) (fun i => (g.parents i).map Fin.succ)
  let tree : (i : Fin (L :: π).length) → ResLinQTree F ((L :: π).get i) :=
    Fin.cases t (fun j => g.tree j)
  let total : Fin (π.length+1) → ℕ := Fin.cases (d + (deps.map g.totalLoss).sum) g.totalLoss
  refine ⟨parents, ?_, tree, Fin.cases d g.loss, total, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parents]
    · simp only [parents, Fin.cases_succ, List.mem_map]
      rintro _ ⟨u, hu, rfl⟩
      exact Fin.succ_lt_succ_iff.mpr (g.later j u hu)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h
      obtain ⟨u, hu, hu'⟩ := hd h
      exact ⟨u.succ, by simp [parents, hu], hu'⟩
    · intro h
      obtain ⟨u, hu, hu'⟩ := g.loss_spec j h
      exact ⟨u.succ, by simp [parents, hu], hu'⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h
      obtain ⟨u, hu, hu'⟩ := hr h
      exact ⟨u.succ, by simp [parents, hu], hu'⟩
    · intro h
      obtain ⟨u, hu, hu'⟩ := g.loss_rule j h
      exact ⟨u.succ, by simp [parents, hu], hu'⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parents, total, List.map_map, Function.comp_def]
    · simpa [parents, total, List.map_map, Function.comp_def] using g.total_rec j
  · intro i
    exact Fin.cases bound (fun j => g.potential j) i

private def widthTreeAt (g : QWidthUnfolding F π U) (i : Fin π.length) {L : QLine V}
    (h : π.get i = L) : ResLinQTree F L := h ▸ g.tree i

private theorem leaves_widthTreeAt (g : QWidthUnfolding F π U) (i : Fin π.length) {L : QLine V}
    (h : π.get i = L) :
    Tree.axiomUses (widthTreeAt g i h) = Tree.axiomUses (g.tree i) := by
  subst L
  rfl

private def extendUnary (g : QWidthUnfolding F π U) {L : QLine V} (i : Fin π.length)
    (rule : U (π.get i) L) (sound : ∀ a, QLine.Holds a (π.get i) → QLine.Holds a L) : QWidthUnfolding F (L :: π) U := by
  refine extendWidth g ((g.tree i).weaken sound) [i] ((π.get i).length - L.length)
    (fun _ => ⟨i, rfl, rfl⟩) (fun _ => ⟨i, rfl, rule⟩) ?_
  simp only [Tree.axiomUses, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have := g.potential i
  omega

private theorem nil_width : Nonempty (QWidthUnfolding F [] U) := by
  refine ⟨⟨(fun i => i.elim0), ?_, (fun i => i.elim0), (fun _ => 0), (fun _ => 0),
    ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;> exact i.elim0

private theorem input_width (g : QWidthUnfolding F π U) {C : PEqualNP.ProofComplexity.Clause V}
    {L : QLine V} (hC : C ∈ F) (rep : ∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit)
    (width : 2 ≤ L.length) : Nonempty (QWidthUnfolding F (L :: π) U) := by
  exact ⟨extendWidth g (.ax C hC rep) [] 0 (by simp) (by simp) (by simpa [Tree.axiomUses] using width)⟩

private theorem bool_width (seed : F.Nonempty) (g : QWidthUnfolding F π U) (v : V) :
    Nonempty (QWidthUnfolding F ([litQEq (v, false), litQEq (v, true)] :: π) U) := by
  classical
  obtain ⟨C, hC⟩ := seed
  let t : ResLinQTree F (C.toList.map litQEq) := .ax C hC (by
    intro e
    simp only [List.mem_map, Finset.mem_toList]
    grind)
  let u : ResLinQTree F [litQEq (v, false), litQEq (v, true)] := t.weaken (by
    intro a _
    cases hv : a v with
    | false => exact ⟨_, List.mem_cons_self, litQEq_holds a (v, false) hv⟩
    | true => exact ⟨_, by simp, litQEq_holds a (v, true) hv⟩)
  exact ⟨extendWidth g u [] 0 (by simp) (by simp) (by simp [u, t, Tree.axiomUses])⟩

private theorem res_width (g : QWidthUnfolding F π U) {e f : QEq V} {C D : QLine V}
    (α β : ℤ) (hC : (e :: C) ∈ π) (hD : (f :: D) ∈ π) :
    Nonempty (QWidthUnfolding F
      (((α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)) :: π) U) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hD
  refine ⟨extendWidth g (.res α β (widthTreeAt g i hi) (widthTreeAt g j hj)) [i,j] 0 (by simp) (by simp) ?_⟩
  have hp := g.potential i
  have hq := g.potential j
  have hwi := congrArg List.length hi
  have hwj := congrArg List.length hj
  simp only [List.length_cons] at hwi hwj
  simp [Tree.axiomUses, leaves_widthTreeAt]
  omega

private theorem weaken_width (g : QWidthUnfolding F π U) {C D : QLine V}
    (hC : C ∈ π) (hsub : ∀ e ∈ C, e ∈ D) (rule : U C D) :
    Nonempty (QWidthUnfolding F (D :: π) U) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
  refine ⟨extendUnary g i (by rw [hi]; exact rule) ?_⟩
  rw [hi]
  rintro a ⟨e, he, ha⟩
  exact ⟨e, hsub e he, ha⟩

/-- Width minus one is additive at resolution. At a unary rule, the positive
part of its width drop bounds the increase in the deficit relative to leaf count. -/
theorem exists_width_unfolding (seed : F.Nonempty)
    (wide : ∀ C ∈ F, ∀ L : QLine V, (∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit) → 2 ≤ L.length)
    (h : IsResLinQSynDerivation F π) : Nonempty (QWidthUnfolding F π) := by
  induction h with
  | nil => exact nil_width
  | ax _ _ hC rep ih =>
    exact ih.elim (fun g => input_width g hC rep (wide _ hC _ rep))
  | bool v _ ih => exact ih.elim (fun g => bool_width seed g v)
  | res α β _ hC hD ih => exact ih.elim (fun g => res_width g α β hC hD)
  | weaken _ hC hsub ih => exact ih.elim (fun g => weaken_width g hC hsub (Or.inl hsub))
  | @simp π C _ hC ih =>
    obtain ⟨g⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    refine ⟨extendUnary g i (by rw [hi]; exact Or.inr rfl) ?_⟩
    rw [hi]
    rintro a ⟨e, he, ha⟩
    refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, ha⟩
    simp only [decide_eq_true_eq]
    rintro ⟨hz, hn⟩
    exact hn (by simpa [QEq.Holds, hz] using ha.symm)


/-- A simplification-free derivation has an unfolding in which every positive
width loss is a weakening preserving every equation from its unique parent. -/
theorem exists_nosimp_width_unfolding (seed : F.Nonempty)
    (wide : ∀ C ∈ F, ∀ L : QLine V, (∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit) → 2 ≤ L.length)
    (h : NoSimpDerivation F π) :
    ∃ g : QWidthUnfolding F π, ∀ i j, 0 < g.loss i → g.parents i = [j] →
      ∀ e ∈ π.get j, e ∈ π.get i := by
  let U : QLine V → QLine V → Prop := fun C D => ∀ e ∈ C, e ∈ D
  have strict : Nonempty (QWidthUnfolding F π U) := by
    induction h with
    | nil => exact nil_width
    | ax _ _ hC rep ih =>
      exact ih.elim (fun g => input_width g hC rep (wide _ hC _ rep))
    | bool v _ ih => exact ih.elim (fun g => bool_width seed g v)
    | res α β _ hC hD ih => exact ih.elim (fun g => res_width g α β hC hD)
    | weaken _ hC hsub ih => exact ih.elim (fun g => weaken_width g hC hsub hsub)
  obtain ⟨g⟩ := strict
  let base : QWidthUnfolding F π := {
    parents := g.parents
    later := g.later
    tree := g.tree
    loss := g.loss
    totalLoss := g.totalLoss
    loss_spec := g.loss_spec
    loss_rule := fun i h => by
      obtain ⟨j, hj, hs⟩ := g.loss_rule i h
      exact ⟨j, hj, Or.inl hs⟩
    total_rec := g.total_rec
    potential := g.potential }
  refine ⟨base, ?_⟩
  intro i j hi hj
  obtain ⟨k, hk, hs⟩ := g.loss_rule i hi
  have he : k = j := by simpa using hk.symm.trans hj
  subst k
  exact hs

end PEqualNP.Search.Helpers
