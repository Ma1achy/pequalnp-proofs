import SparseRepeat

/-! A graph that is *exactly* one spanning directed tour has a different
characteristic function from a graph merely containing one. Their canonical
multilinear polynomials nevertheless have the same degree-m component. -/
namespace BooleanTransfer.EasyTourLayer
open Finset MvPolynomial BooleanTransfer.TourLayer

private noncomputable abbrev mon (S : Finset (Arc m)) : MvPolynomial (Arc m) (ZMod 2) :=
  ∏ e ∈ S, X e

/-- Expanded form of x_T times the product of (1+x_e) for all e outside T. -/
private noncomputable def point (T : Finset (Arc m)) : MvPolynomial (Arc m) (ZMod 2) :=
  ∑ S : Finset (Arc m) with T ⊆ S, mon S

private theorem eval_point (T E : Finset (Arc m)) :
    eval (indicator (ZMod 2) E) (point T) = if T = E then 1 else 0 := by
  classical
  let supers := univ.filter (fun S : Finset (Arc m) => T ⊆ S)
  have interval : supers.filter (fun S => S ⊆ E) = Icc T E := by ext; simp [supers]
  calc
    _ = ∑ S ∈ supers, if S ⊆ E then (1 : ZMod 2) else 0 := by
      simp only [point, map_sum, mon, map_prod, eval_X, BooleanTransfer.TourLayer.indicator, Finset.prod_boole]
      apply Finset.sum_congr rfl
      intro S _
      by_cases sub : S ⊆ E
      · rw [if_pos (show ∀ e ∈ S, e ∈ E from sub), if_pos sub]
      · rw [if_neg (show ¬∀ e ∈ S, e ∈ E from sub), if_neg sub]
    _ = ((Icc T E).card : ZMod 2) := by
      rw [Finset.sum_boole, interval]
    _ = _ := by
      by_cases same : T = E
      · simp [same]
      by_cases sub : T ⊆ E
      · have pos : 0 < E.card - T.card :=
          Nat.sub_pos_of_lt (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, same⟩))
        rw [Finset.card_Icc_finset sub, Nat.cast_pow, Nat.cast_ofNat, if_neg same]
        rw [show (2 : ZMod 2) = 0 by decide, zero_pow pos.ne']
      · have empty : Icc T E = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro U h
          obtain ⟨hTU, hUE⟩ := Finset.mem_Icc.mp h
          exact sub (hTU.trans hUE)
        simp [empty, same]

private theorem component_point (T : Finset (Arc m)) :
    homogeneousComponent T.card (point T) = mon T := by
  classical
  simp only [point, map_sum]
  rw [Finset.sum_eq_single T]
  · apply homogeneousComponent_eq_self
    simpa using IsHomogeneous.prod T (fun e => X (R := ZMod 2) e) (fun _ => 1)
      (fun e _ => isHomogeneous_X _ e)
  · intro S hS ne
    have sub := (Finset.mem_filter.mp hS).2
    have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, Ne.symm ne⟩)
    have hom : IsHomogeneous (mon S) S.card := by
      simpa using IsHomogeneous.prod S (fun e => X (R := ZMod 2) e) (fun _ => 1)
        (fun e _ => isHomogeneous_X _ e)
    simp [homogeneousComponent_of_mem hom, lt.ne]
  · simp

open Classical in
noncomputable def exactANF (m : Nat) : MvPolynomial (Arc m) (ZMod 2) :=
  ∑ σ : Equiv.Perm (Fin m) with σ.IsCycleOn Set.univ, point (arcs σ)

def IsExactTour (E : Finset (Arc m)) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), σ.IsCycleOn Set.univ ∧ arcs σ = E

private theorem arcs_inj {σ τ : Equiv.Perm (Fin m)} (eq : arcs σ = arcs τ) : σ = τ := by
  apply Equiv.ext
  intro i
  have h : (i, σ i) ∈ arcs τ := by rw [← eq]; simp
  exact ((mem_arcs τ i (σ i)).mp h).symm

open Classical in
theorem eval_exactANF (E : Finset (Arc m)) :
    eval (indicator (ZMod 2) E) (exactANF m) = if IsExactTour E then 1 else 0 := by
  classical
  simp only [exactANF, map_sum, eval_point]
  split
  · next h =>
    obtain ⟨σ, hc, eq⟩ := h
    rw [Finset.sum_eq_single σ]
    · simp [eq]
    · intro τ _ ne
      exact if_neg (fun e => ne (arcs_inj (e.trans eq.symm)))
    · simp [hc]
  · next h =>
    apply Finset.sum_eq_zero
    intro σ hc
    exact if_neg (fun eq => h ⟨σ, (Finset.mem_filter.mp hc).2, eq⟩)

theorem exactANF_multilinear (m : Nat) :
    exactANF m ∈ restrictDegree (Arc m) (ZMod 2) 1 := by
  classical
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.sum_mem
  intro S _
  rw [mem_restrictDegree_iff_sup]
  intro i
  rw [← degreeOf_def]
  apply (degreeOf_prod_le i _ _).trans
  simp only [degreeOf_X]
  rw [Finset.sum_ite_eq]
  split <;> decide

theorem exactANF_component (m : Nat) :
    homogeneousComponent m (exactANF m) = Statement.hc (ZMod 2) m := by
  classical
  simp only [exactANF, Statement.hc, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have eq := component_point (arcs σ)
  rw [card_arcs] at eq
  rw [eq]
  simp only [mon, arcs, Finset.prod_map]
  rfl

open Classical PartialLayer SparseRepeat in
/-- The same sparse-repeat projection computes formal hc even if the original
circuit solves the deterministic logspace exact-tour test. -/
theorem exact_sparse_layer {m r : ℕ} (p : MvPolynomial (Arc m) (ZMod 2))
    (hr : ∀ a ∈ p.support, a.support.card ≤ m → (repeated a).card ≤ r)
    (correct : ∀ E, eval (indicator (ZMod 2) E) p = if IsExactTour E then 1 else 0) :
    homogeneousComponent m (sparseReduction r p) = Statement.hc (ZMod 2) m := by
  classical
  rw [sparseReduction_layer p m r hr, ← exactANF_component]
  congr 1
  apply multilinear_ext (degreeOf_reduceOn_univ p)
  · intro i
    have bounded := exactANF_multilinear m
    rw [mem_restrictDegree_iff_sup] at bounded
    simpa only [degreeOf_def] using bounded i
  · intro v hv
    rw [eval_reduceOn_cube _ _ _ hv]
    let E := univ.filter (fun e => v e = 1)
    have eq : v = indicator (ZMod 2) E := by
      funext e
      rcases hv e with h | h <;> simp [TourLayer.indicator, E, h]
    rw [eq, correct, eval_exactANF]

end BooleanTransfer.EasyTourLayer
#print axioms BooleanTransfer.EasyTourLayer.eval_exactANF
#print axioms BooleanTransfer.EasyTourLayer.exactANF_multilinear
#print axioms BooleanTransfer.EasyTourLayer.exactANF_component
