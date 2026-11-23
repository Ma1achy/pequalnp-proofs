import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside

open SimpleGraph

private abbrev edge01 := edge (0 : Fin 6) 1
private abbrev edge02 := edge (0 : Fin 6) 2
private abbrev edge03 := edge (0 : Fin 6) 3
private abbrev edge45 := edge (4 : Fin 6) 5
private abbrev forest := ((edge01 ⊔ edge02) ⊔ edge03) ⊔ edge45

private lemma not_reachable_from_isolated {G : SimpleGraph (Fin 6)} {v w : Fin 6}
    (h : ∀ u, ¬ G.Adj v u) (hne : v ≠ w) : ¬ G.Reachable w v := by
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  cases p with
  | nil => exact hne rfl
  | cons hadj _ => exact h _ hadj

private lemma forest_acyclic : forest.IsAcyclic := by
  refine IsAcyclic.sup_edge_of_not_reachable ?_ ?_
  · exact not_reachable_from_isolated (by simp [edge01, edge02, edge03, sup_adj, edge_adj]) (by decide)
  refine IsAcyclic.sup_edge_of_not_reachable ?_ ?_
  · exact not_reachable_from_isolated (by simp [edge01, edge02, sup_adj, edge_adj]) (by decide)
  refine IsAcyclic.sup_edge_of_not_reachable ?_ ?_
  · exact not_reachable_from_isolated (by simp [edge01, edge_adj]) (by decide)
  have h : ((⊥ : SimpleGraph (Fin 6)) ⊔ edge01).IsAcyclic := by
    refine IsAcyclic.sup_edge_of_not_reachable ?_ isAcyclic_bot
    exact not_reachable_from_isolated (by decide) (by decide)
  simpa using h

private lemma forest_adj_01 : forest.Adj 0 1 := by
  simp [forest, edge01, sup_adj, edge_adj]

private lemma forest_adj_45 : forest.Adj 4 5 := by
  simp [forest, edge45, sup_adj, edge_adj]

private lemma forest_nonempty : ∃ i j, forest.Adj i j :=
  ⟨0, 1, forest_adj_01⟩

private lemma forest_card [Fintype forest.edgeSet] : forest.edgeFinset.card = 4 := by
  let edges : Finset (Sym2 (Fin 6)) := {s(0, 1), s(0, 2), s(0, 3), s(4, 5)}
  have h01 : edge01.edgeSet = {s(0, 1)} := edgeSet_edge_of_ne (by decide)
  have h02 : edge02.edgeSet = {s(0, 2)} := edgeSet_edge_of_ne (by decide)
  have h03 : edge03.edgeSet = {s(0, 3)} := edgeSet_edge_of_ne (by decide)
  have h45 : edge45.edgeSet = {s(4, 5)} := edgeSet_edge_of_ne (by decide)
  have h : forest.edgeFinset = edges := by
    ext e
    simp only [mem_edgeFinset, forest, edgeSet_sup, h01, h02, h03, h45, Set.mem_union,
      Set.mem_singleton_iff, edges, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h]
  decide

private lemma cover_card_lower (T : Finset (Fin 6))
    (h : ∀ i j, forest.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  have pair_bound {u v : Fin 6} (hu : u ∈ T) (hv : v ∈ T) (hne : u ≠ v) : 2 ≤ T.card := by
    exact Finset.one_lt_card_iff.mpr ⟨u, v, hu, hv, hne⟩
  rcases h 0 1 forest_adj_01 with h0 | h1
  · rcases h 4 5 forest_adj_45 with h4 | h5
    · exact pair_bound h0 h4 (by decide)
    · exact pair_bound h0 h5 (by decide)
  · rcases h 4 5 forest_adj_45 with h4 | h5
    · exact pair_bound h1 h4 (by decide)
    · exact pair_bound h1 h5 (by decide)

private lemma target_eq :
    (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) =
      (fun x : Fin 6 → Bool =>
        decide (∃ i j : Fin 6, forest.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨0, 1, forest_adj_01, h.1, h.2⟩
    · exact ⟨0, 2, by simp [forest, edge02, sup_adj, edge_adj], h.1, h.2⟩
    · exact ⟨0, 3, by simp [forest, edge03, sup_adj, edge_adj], h.1, h.2⟩
    · exact ⟨4, 5, forest_adj_45, h.1, h.2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    simp only [forest, edge01, edge02, edge03, edge45, sup_adj, edge_adj] at hij
    grind

theorem L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [target_eq]
  constructor
  · intro h
    have hbound := MetaComplexity.L104 6 2 s forest forest_acyclic forest_nonempty cover_card_lower h
    rw [@forest_card] at hbound
    omega
  · intro hs
    have hcover : ∀ i j, forest.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
      intro i j hij
      simp only [forest, edge01, edge02, edge03, edge45, sup_adj, edge_adj] at hij
      grind
    have hsize := MetaComplexity.L105 6 forest {0, 4} forest_nonempty hcover
    rw [@forest_card, show ({0, 4} : Finset (Fin 6)).card = 2 by decide] at hsize
    obtain ⟨c, hfan, hcard, heval⟩ := hsize
    exact ⟨c, hfan, hcard.trans hs, heval⟩

end PEqualNP.Outside
