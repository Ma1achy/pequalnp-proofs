import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2270_427
    (pure : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ¬ G.Colorable 2 →
  (∀ i, (G.neighborSet i).ncard = 0 ∨ (G.neighborSet i).ncard = 3) →
  (∀ i (w : G.Walk i i), w.IsCycle → 7 ≤ w.length) →
  (∃ i j, G.Adj i j) →
  ∀ g : (Fin n → Bool) → Bool,
    (∀ x, g x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
    ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n g s →
    ∃ u v, G.Adj u v ∧ ∃ t, t + 7 ≤ s ∧
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => g (Function.update (Function.update x u false) v false)) t)
    (peel : ∀ (n : ℕ) (A : Finset (Fin n)) (g f : (Fin n → Bool) → Bool),
  (∃ x y, g x ≠ g y) →
  (∀ x, g x = g (fun i => if i ∈ A then false else x i)) →
  (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨ g x = true) →
  ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s →
  ∃ t, t + A.card ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n g t)
    (lift : ∀ (n : ℕ) (A : Finset (Fin n)) (g f : (Fin n → Bool) → Bool),
  (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨ g x = true) →
  ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n g s →
  PEqualNP.MetaComplexity.HasCircuitSize n f (s + A.card))
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hchrom hdeg hgirth hiso hedge hf s hs
  let g : (Fin n → Bool) → Bool := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  have hg (x) : g x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by simp [g]
  have degrees (i) : (G.neighborSet i).ncard = 0 ∨ (G.neighborSet i).ncard = 3 := by
    by_cases hi : i ∈ A
    · left
      have he : G.neighborSet i = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun j hij => hiso i j hij hi)
      simp [he]
    · exact Or.inr (hdeg i hi)
  have hnc : ∃ x y, g x ≠ g y := by
    obtain ⟨i,j,hij⟩ := hedge
    refine ⟨fun _ => false,fun _ => true,?_⟩
    have h0 : g (fun _ => false) = false := by simp [g]
    have h1 := (hg (fun _ => true)).mpr ⟨i,j,hij,rfl,rfl⟩
    simp [h0,h1]
  have erased (x) : g x = g (fun i => if i ∈ A then false else x i) := by
    apply Bool.eq_iff_iff.mpr
    rw [hg,hg]
    constructor
    · rintro ⟨i,j,hij,hi,hj⟩
      exact ⟨i,j,hij,by simpa [hiso i j hij] using hi,by simpa [hiso j i hij.symm] using hj⟩
    · rintro ⟨i,j,hij,hi,hj⟩
      exact ⟨i,j,hij,by simpa [hiso i j hij] using hi,by simpa [hiso j i hij.symm] using hj⟩
  have hfg (x) : f x = true ↔ (∃ i ∈ A, x i = true) ∨ g x = true := by rw [hf,hg]
  obtain ⟨t,hbudget,ht⟩ := peel n A g f hnc erased hfg s hs
  obtain ⟨u,v,huv,r,hr,hcore⟩ := pure n G hchrom degrees hgirth hedge g hg t ht
  have hU := hiso u v huv
  have hV := hiso v u huv.symm
  refine ⟨u,v,hU,hV,huv,r+A.card,by omega,?_⟩
  refine lift n A _ _ ?_ r hcore
  intro x
  rw [hfg]
  apply or_congr _ Iff.rfl
  constructor
  · rintro ⟨i,hi,yi⟩
    have hiu : i ≠ u := fun h => hU (h ▸ hi)
    have hiv : i ≠ v := fun h => hV (h ▸ hi)
    exact ⟨i,hi,by simpa [hiu,hiv] using yi⟩
  · rintro ⟨i,hi,xi⟩
    have hiu : i ≠ u := fun h => hU (h ▸ hi)
    have hiv : i ≠ v := fun h => hV (h ▸ hi)
    exact ⟨i,hi,by simpa [hiu,hiv] using xi⟩
