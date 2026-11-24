import PEqualNP.Defs.SearchQTree
import PEqualNP.Search.Helpers.DagUnfoldBound
import PEqualNP.Search.Helpers.QSynEssential

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
variable {F : Set (PEqualNP.ProofComplexity.Clause V)} {π : List (QLine V)}

/-- Index dependencies by their positions in the newest-first proof, retaining
multiplicity when one resolution uses the same earlier line twice. Each position
also carries its unfolded tree and the exact additive accounting identity. -/
structure QSynUnfolding (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (QLine V)) where
  parents : Fin π.length → List (Fin π.length)
  later : ∀ i, ∀ j ∈ parents i, i < j
  arity : ∀ i, (parents i).length ≤ 2
  tree : (i : Fin π.length) → ResLinQTree F (π.get i)
  localCost : Fin π.length → ℕ
  localCost_le : ∀ i, localCost i ≤ 2
  count : ∀ i, (tree i).size = localCost i + ((parents i).map (fun j => (tree j).size)).sum

private def extendUnfolding (g : QSynUnfolding F π) {L : QLine V} (t : ResLinQTree F L)
    (deps : List (Fin π.length)) (hd : deps.length ≤ 2) (c : ℕ) (hc : c ≤ 2)
    (ht : t.size = c + (deps.map (fun i => (g.tree i).size)).sum) :
    QSynUnfolding F (L :: π) := by
  let parents : Fin (π.length + 1) → List (Fin (π.length + 1)) :=
    Fin.cases (deps.map Fin.succ) (fun i => (g.parents i).map Fin.succ)
  let tree : (i : Fin (L :: π).length) → ResLinQTree F ((L :: π).get i) :=
    Fin.cases t (fun j => g.tree j)
  have hs (j : Fin π.length) : (tree j.succ).size = (g.tree j).size := by
    cases j
    rfl
  refine ⟨parents, ?_, ?_, tree, Fin.cases c g.localCost, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parents]
    · simp only [parents, Fin.cases_succ, List.mem_map]
      rintro _ ⟨u, hu, rfl⟩
      exact Fin.succ_lt_succ_iff.mpr (g.later j u hu)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [parents] using hd
    · simpa [parents] using g.arity j
  · exact Fin.cases hc g.localCost_le
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change t.size = c + ((deps.map Fin.succ).map (fun j => (tree j).size)).sum
      simpa only [List.map_map, Function.comp_def, hs] using ht
    · change (g.tree j).size = g.localCost j + (((g.parents j).map Fin.succ).map
          (fun u => (tree u).size)).sum
      simpa only [List.map_map, Function.comp_def, hs] using g.count j

private def treeAt (g : QSynUnfolding F π) (i : Fin π.length) {L : QLine V}
    (h : π.get i = L) : ResLinQTree F L := h ▸ g.tree i

private theorem treeAt_size (g : QSynUnfolding F π) (i : Fin π.length) {L : QLine V}
    (h : π.get i = L) : (treeAt g i h).size = (g.tree i).size := by
  subst L
  rfl

/-- Unfold the individual syntactic derivation rules. A Boolean axiom of the
syntactic system costs two tree nodes: an arbitrary input axiom and weakening.
Every other rule contributes one node in addition to its selected parents. -/
theorem exists_syn_unfolding (seed : F.Nonempty) (h : IsResLinQSynDerivation F π) :
    Nonempty (QSynUnfolding F π) := by
  classical
  induction h with
  | nil =>
    refine ⟨⟨(fun i => i.elim0), ?_, ?_, (fun i => i.elim0), (fun _ => 0), ?_, ?_⟩⟩ <;>
      intro i <;> exact i.elim0
  | ax C _ hC rep ih =>
    obtain ⟨g⟩ := ih
    exact ⟨extendUnfolding g (.ax C hC rep) [] (by simp) 1 (by decide) rfl⟩
  | bool v _ ih =>
    obtain ⟨g⟩ := ih
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
    exact ⟨extendUnfolding g u [] (by simp) 2 (by decide) rfl⟩
  | @res π e f C D α β _ hC hD ih =>
    obtain ⟨g⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hD
    refine ⟨extendUnfolding g (.res α β (treeAt g i hi) (treeAt g j hj))
      [i,j] (by simp) 1 (by decide) ?_⟩
    simp [ResLinQTree.size, treeAt_size]
    omega
  | @weaken π C D _ hC hsub ih =>
    obtain ⟨g⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    have sound (a) : QLine.Holds a C → QLine.Holds a D := by
      rintro ⟨e, he, ha⟩
      exact ⟨e, hsub e he, ha⟩
    refine ⟨extendUnfolding g ((treeAt g i hi).weaken sound) [i] (by simp) 1 (by decide) ?_⟩
    simp [ResLinQTree.size, treeAt_size, Nat.add_comm]
  | @simp π C _ hC ih =>
    obtain ⟨g⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    refine ⟨extendUnfolding g ((treeAt g i hi).weaken ?_) [i] (by simp) 1 (by decide) ?_⟩
    · rintro a ⟨e, he, ha⟩
      refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, ha⟩
      simp only [decide_eq_true_eq]
      rintro ⟨hz, hn⟩
      exact hn (by simpa [QEq.Holds, hz] using ha.symm)
    · simp [ResLinQTree.size, treeAt_size, Nat.add_comm]

/-- Unfold any designated line to a semantic tree, paying for the proof length
and the excess uses of shared input or derived lines. -/
theorem QSynUnfolding.exists_tree_le (g : QSynUnfolding F π) {L : QLine V} (hL : L ∈ π) :
    ∃ t : ResLinQTree F L, t.size ≤ 2 * π.length * 2 ^ dagExcess g.parents := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hL
  refine ⟨treeAt g i hi, ?_⟩
  rw [treeAt_size]
  apply dag_unfold_cost_le g.parents g.later (fun j => (g.tree j).size) 2 _ i
  intro j
  rw [g.count j]
  exact Nat.add_le_add_right (g.localCost_le j) _

end PEqualNP.Search.Helpers
