import EasyTourLayer

/-! # Weighted model counting of deterministic circuit transcripts

Each accepted Boolean input contributes a product with exactly one literal
per input coordinate. Hidden gate bits have unit weight. The proof identifies
this formal polynomial with every multilinear representative of the circuit
on the Boolean cube and specializes its minimum tour layer to the pinned HC.
-/
namespace BooleanTransfer.TreewidthTransfer

open Finset MvPolynomial Classical

variable {σ τ R : Type} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- One product for one complete input assignment. -/
noncomputable def point (s : Finset σ) : MvPolynomial σ R :=
  ∏ i : σ, if i ∈ s then X i else 1 - X i

private theorem pointEval (s t : Finset σ) :
    eval (fun i => if i ∈ t then (1 : R) else 0) (point s) =
      if s = t then 1 else 0 := by
  classical
  rw [point, map_prod]
  by_cases eq : s = t
  · subst s
    rw [if_pos rfl]
    apply prod_eq_one
    intro i _
    by_cases hi : i ∈ t <;> simp [hi]
  · rw [if_neg eq]
    have diff : ∃ i, ¬ (i ∈ s ↔ i ∈ t) := by
      by_contra! h
      exact eq (Finset.ext h)
    obtain ⟨i, hi⟩ := diff
    apply Finset.prod_eq_zero (mem_univ i)
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

private theorem pointDegree [Nontrivial R] (s : Finset σ) (j : σ) : (point (R := R) s).degreeOf j ≤ 1 := by
  classical
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc
    _ ≤ ∑ i : σ, if j = i then 1 else 0 := by
      apply sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · simp [hi, degreeOf_X]
      · simp only [if_neg hi]
        apply (degreeOf_sub_le _ _ _).trans
        simp [degreeOf_X]
    _ = 1 := by simp

/-- The unnormalized symbolic weighted model count of a finite acceptance relation. -/
noncomputable def weighted [Fintype τ] (valid : Finset σ → τ → Prop) : MvPolynomial σ R :=
  ∑ s : Finset σ, ∑ t : τ, if valid s t then point s else 0

/-- When acceptance has a unique hidden assignment, its symbolic weight is
exactly the canonical sum of the accepted input indicators. -/
theorem collapse [Fintype τ] (valid : Finset σ → τ → Prop) (accept : Finset σ → Prop)
    (run : Finset σ → τ) (det : ∀ s t, valid s t ↔ accept s ∧ t = run s) :
    weighted (R := R) valid = ∑ s : Finset σ, if accept s then point s else 0 := by
  classical
  apply sum_congr rfl
  intro s _
  by_cases h : accept s <;> simp [det, h]

/-- Equality to a formally multilinear polynomial follows from its values on
the cube. This step works over every integral domain, including finite fields. -/
theorem canonical [Fintype τ] [IsDomain R] (valid : Finset σ → τ → Prop)
    (accept : Finset σ → Prop) (run : Finset σ → τ)
    (det : ∀ s t, valid s t ↔ accept s ∧ t = run s)
    (q : MvPolynomial σ R) (multi : ∀ j, q.degreeOf j ≤ 1)
    (correct : ∀ s : Finset σ,
      eval (fun i => if i ∈ s then (1 : R) else 0) q = if accept s then 1 else 0) :
    weighted valid = q := by
  classical
  rw [collapse valid accept run det]
  apply BooleanTransfer.multilinear_ext _ multi
  · intro v hv
    let s := univ.filter (fun i => v i = 1)
    have ev : v = fun i => if i ∈ s then 1 else 0 := by
      funext i
      rcases hv i with h | h <;> simp [s, h]
    rw [ev, correct s, map_sum]
    have one (a : Finset σ) : eval (fun i => if i ∈ s then (1 : R) else 0)
        (if accept a then point a else 0) = if a = s then (if accept a then 1 else 0) else 0 := by
      by_cases h : accept a <;> simp [h, pointEval]
    simp_rw [one]
    simp
  · intro j
    apply (degreeOf_sum_le _ _ _).trans (Finset.sup_le _)
    intro s _
    split <;> simp [pointDegree]

open TourLayer

/-- A deterministic transcript test for tour existence has the pinned formal
Hamiltonian polynomial as its degree-m weighted-count component over F₂. -/
theorem hamiltonianLayer [Fintype τ] {m : ℕ} (valid : Finset (Arc m) → τ → Prop)
    (run : Finset (Arc m) → τ)
    (det : ∀ s t, valid s t ↔ (tours s).Nonempty ∧ t = run s) :
    homogeneousComponent m (weighted valid) = Statement.hc (ZMod 2) m := by
  classical
  rw [canonical valid (fun s => (tours s).Nonempty) run det (decisionANF m) _ (fun s => by
    have ev : (fun i : Arc m => if i ∈ s then (1 : ZMod 2) else 0) =
        TourLayer.indicator _ s := by
      funext i
      by_cases h : i ∈ s <;> simp [TourLayer.indicator, h]
    rw [ev]
    by_cases h : (tours s).Nonempty <;> simpa [h] using eval_decisionANF s)]
  · exact decisionANF_component m
  · intro j
    have bounded := decisionANF_multilinear m
    rw [mem_restrictDegree_iff_sup] at bounded
    simpa only [degreeOf_def] using bounded j

/-- The deterministic exact-tour comparison language has the same component. -/
theorem exactHamiltonianLayer [Fintype τ] {m : ℕ} (valid : Finset (Arc m) → τ → Prop)
    (run : Finset (Arc m) → τ)
    (det : ∀ s t, valid s t ↔ EasyTourLayer.IsExactTour s ∧ t = run s) :
    homogeneousComponent m (weighted valid) = Statement.hc (ZMod 2) m := by
  classical
  rw [canonical valid EasyTourLayer.IsExactTour run det (EasyTourLayer.exactANF m) _
    (fun s => EasyTourLayer.eval_exactANF s)]
  · exact EasyTourLayer.exactANF_component m
  · intro j
    have bounded := EasyTourLayer.exactANF_multilinear m
    rw [mem_restrictDegree_iff_sup] at bounded
    simpa only [degreeOf_def] using bounded j

end BooleanTransfer.TreewidthTransfer

#print axioms BooleanTransfer.TreewidthTransfer.collapse
#print axioms BooleanTransfer.TreewidthTransfer.canonical

#print axioms BooleanTransfer.TreewidthTransfer.hamiltonianLayer
#print axioms BooleanTransfer.TreewidthTransfer.exactHamiltonianLayer
