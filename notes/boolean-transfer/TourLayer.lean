import Statement
import PartialLayer

/-! The degree-m component of the canonical decision polynomial is the upstream
Hamiltonian-cycle polynomial. Partial reduction suffices when it covers all
repetitions in output monomials with at most m distinct edge variables. -/
namespace BooleanTransfer.TourLayer
open Finset MvPolynomial

abbrev Arc (m : Nat) := Fin m × Fin m

def arcs (σ : Equiv.Perm (Fin m)) : Finset (Arc m) :=
  univ.map ⟨fun i => (i, σ i), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_arcs (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    (i,j) ∈ arcs σ ↔ σ i = j := by
  simp only [arcs, Finset.mem_map, mem_univ, true_and]
  change (∃ a, (a, σ a) = (i,j)) ↔ _
  simp

@[simp] theorem card_arcs (σ : Equiv.Perm (Fin m)) : (arcs σ).card = m := by
  simp [arcs]

private theorem arcs_subset (σ : Equiv.Perm (Fin m)) (E : Finset (Arc m)) :
    arcs σ ⊆ E ↔ ∀ i, (i, σ i) ∈ E := by
  constructor
  · intro h i; exact h (by simp)
  · rintro h ⟨i,j⟩ hij
    rw [← (mem_arcs σ i j).mp hij]
    exact h i

noncomputable def tours (E : Finset (Arc m)) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact (univ.filter (fun σ : Equiv.Perm (Fin m) => σ.IsCycleOn Set.univ)).filter
    (fun σ => ∀ i, (i,σ i) ∈ E)

def indicator (R : Type*) [Zero R] [One R] (E : Finset (Arc m)) (e : Arc m) : R :=
  if e ∈ E then 1 else 0

/-- This cardinality is cast into R; in characteristic two this records parity. -/
theorem eval_hc_counts (R : Type*) [CommSemiring R] (E : Finset (Arc m)) :
    eval (indicator R E) (Statement.hc R m) = ((tours E).card : R) := by
  classical
  simp only [Statement.hc, map_sum, map_prod, eval_X, indicator, Fintype.prod_boole]
  rw [tours, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : ∀ i, (i, σ i) ∈ E <;> simp [h]

private theorem unique_on_layer (E : Finset (Arc m)) (h : E.card ≤ m) :
    (tours E).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro σ τ hσ hτ
  have full {π : Equiv.Perm (Fin m)} (hp : π ∈ tours E) : arcs π = E :=
    Finset.eq_of_subset_of_card_le ((arcs_subset π E).2 (Finset.mem_filter.mp hp).2) (by simpa using h)
  apply Equiv.ext
  intro i
  have hi : (i, σ i) ∈ arcs τ := by rw [full hτ, ← full hσ]; simp
  exact ((mem_arcs τ i (σ i)).mp hi).symm

/-- Exact agreement with existence, with no counting-to-decision assumption. -/
theorem hc_on_small_graph (R : Type*) [CommSemiring R] (E : Finset (Arc m)) (h : E.card ≤ m) :
    eval (indicator R E) (Statement.hc R m) = if (tours E).Nonempty then 1 else 0 := by
  classical
  rw [eval_hc_counts]
  split
  · next hn =>
    have hp := Finset.card_pos.mpr hn
    have hu := unique_on_layer E h
    have eq : (tours E).card = 1 := by omega
    simp [eq]
  · next hn => simp [Finset.not_nonempty_iff_eq_empty.mp hn]

private def zeta {α : Type*} (f : Finset α → ZMod 2) (S : Finset α) : ZMod 2 :=
  ∑ T ∈ S.powerset, f T

private theorem zeta_ins {α : Type*} [DecidableEq α] (f : Finset α → ZMod 2)
    {a : α} {S : Finset α} (ha : a ∉ S) :
    zeta f (insert a S) = zeta f S + zeta (fun T => f (insert a T)) S :=
  Finset.sum_powerset_insert ha f

private theorem zeta_twice {α : Type*} [DecidableEq α] (f : Finset α → ZMod 2) (S : Finset α) :
    zeta (zeta f) S = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [zeta]
  | @insert a S ha ih =>
    rw [zeta_ins _ ha, ih]
    have separate : zeta (fun T => zeta f (insert a T)) S =
        zeta (zeta f) S + zeta (zeta (fun T => f (insert a T))) S := by
      change (∑ T ∈ S.powerset, zeta f (insert a T)) = _ + _
      rw [show zeta (zeta f) S + zeta (zeta (fun T => f (insert a T))) S =
        ∑ T ∈ S.powerset, (zeta f T + zeta (fun U => f (insert a U)) T) from
        (Finset.sum_add_distrib).symm]
      apply Finset.sum_congr rfl
      intro T ht
      exact zeta_ins _ (fun mem => ha ((Finset.mem_powerset.mp ht) mem))
    rw [separate, ih, ih, ← add_assoc]
    have char : ∀ v : ZMod 2, v + v = 0 := by decide
    rw [char, zero_add]

private noncomputable def existsBit (E : Finset (Arc m)) : ZMod 2 :=
  if (tours E).Nonempty then 1 else 0

/-- Explicit squarefree algebraic normal form of directed tour existence. -/
noncomputable def decisionANF (m : Nat) : MvPolynomial (Arc m) (ZMod 2) :=
  ∑ S : Finset (Arc m), C (zeta existsBit S) * ∏ e ∈ S, X e

theorem eval_decisionANF (E : Finset (Arc m)) :
    eval (indicator (ZMod 2) E) (decisionANF m) = if (tours E).Nonempty then 1 else 0 := by
  classical
  have sets : univ.filter (fun S : Finset (Arc m) => S ⊆ E) = E.powerset := by ext; simp
  calc
    _ = ∑ S : Finset (Arc m), if S ⊆ E then zeta existsBit S else 0 := by
      simp only [decisionANF, map_sum, map_mul, eval_C, map_prod, eval_X, indicator, Finset.prod_boole]
      apply Finset.sum_congr rfl
      intro S _
      by_cases sub : S ⊆ E
      · rw [if_pos (show ∀ e ∈ S, e ∈ E from sub), if_pos sub, mul_one]
      · rw [if_neg (show ¬∀ e ∈ S, e ∈ E from sub), if_neg sub, mul_zero]
    _ = zeta (zeta existsBit) E := by
      rw [← Finset.sum_filter, sets]; rfl
    _ = _ := zeta_twice _ _

private theorem zeta_on_layer (E : Finset (Arc m)) (size : E.card = m) :
    zeta existsBit E = existsBit E := by
  classical
  unfold zeta
  apply Finset.sum_eq_single E
  · intro S hS hne
    have sub := Finset.mem_powerset.mp hS
    have lt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, hne⟩)
    have none : ¬(tours S).Nonempty := by
      rintro ⟨σ,hσ⟩
      have lo := Finset.card_le_card ((arcs_subset σ S).2 (Finset.mem_filter.mp hσ).2)
      rw [card_arcs] at lo
      omega
    simp [existsBit, none]
  · simp

/-- The formal homogeneous component of the canonical decision polynomial is
the upstream Hamiltonian cycle polynomial, without evaluating either side. -/
theorem decisionANF_component (m : Nat) :
    homogeneousComponent m (decisionANF m) = Statement.hc (ZMod 2) m := by
  classical
  let good (S : Finset (Arc m)) := S.card = m ∧ (tours S).Nonempty
  calc
    _ = ∑ S : Finset (Arc m), if good S then (∏ e ∈ S, X e) else 0 := by
      simp only [decisionANF, map_sum]
      apply Finset.sum_congr rfl
      intro S _
      have mono : IsHomogeneous (∏ e ∈ S, (X e : MvPolynomial (Arc m) (ZMod 2))) S.card := by
        simpa using IsHomogeneous.prod S (fun e => X (R := ZMod 2) e) (fun _ => 1)
          (fun i _ => isHomogeneous_X _ i)
      rw [homogeneousComponent_of_mem (mono.C_mul _)]
      by_cases size : S.card = m
      · rw [zeta_on_layer S size]
        by_cases hg : (tours S).Nonempty <;> simp [good, existsBit, size, hg]
      · simp [good, size, Ne.symm size]
    _ = _ := by
      rw [← Finset.sum_filter, Statement.hc]
      symm
      apply Finset.sum_bij (fun σ _ => arcs σ)
      · intro σ hc
        apply Finset.mem_filter.mpr
        refine ⟨mem_univ _, card_arcs _, σ, ?_⟩
        exact Finset.mem_filter.mpr ⟨hc, fun i => by simp⟩
      · intro σ hσ τ hτ eq
        apply Equiv.ext
        intro i
        have mem : (i, σ i) ∈ arcs τ := by rw [← eq]; simp
        exact ((mem_arcs τ i (σ i)).mp mem).symm
      · intro E hE
        obtain ⟨_, size, σ, hσ⟩ := Finset.mem_filter.mp hE
        obtain ⟨hc, edges⟩ := Finset.mem_filter.mp hσ
        exact ⟨σ, hc, Finset.eq_of_subset_of_card_le ((arcs_subset σ E).2 edges) (by simpa using size.le)⟩
      · intro σ _
        simp only [arcs, Finset.prod_map]; rfl


theorem decisionANF_multilinear (m : Nat) :
    decisionANF m ∈ restrictDegree (Arc m) (ZMod 2) 1 := by
  classical
  rw [mem_restrictDegree_iff_sup]
  intro i
  rw [← degreeOf_def]
  unfold decisionANF
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro S _
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le i _ _).trans
  simp only [degreeOf_X]
  rw [Finset.sum_ite_eq]
  split <;> decide

/-- The degree-m component is forced for every *formally multilinear*
representative agreeing with tour existence on the Boolean cube. -/
theorem multilinear_component_of_correct (p : MvPolynomial (Arc m) (ZMod 2))
    (multi : p ∈ restrictDegree (Arc m) (ZMod 2) 1)
    (correct : ∀ E, eval (indicator (ZMod 2) E) p = if (tours E).Nonempty then 1 else 0) :
    homogeneousComponent m p = Statement.hc (ZMod 2) m := by
  classical
  have zero : p - decisionANF m = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero (Arc m) (ZMod 2)
    · intro v
      let E := univ.filter (fun e => v e = 1)
      have ind : v = indicator (ZMod 2) E := by
        funext e
        have binary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases binary (v e) with h|h <;> simp [indicator, E, h]
      rw [ind, map_sub, correct, eval_decisionANF, sub_self]
    · simpa [ZMod.card] using
        (restrictDegree (Arc m) (ZMod 2) 1).sub_mem multi (decisionANF_multilinear m)
  rw [sub_eq_zero.mp zero, decisionANF_component]

/-- A supplied set of repeated coordinates suffices to recover formal hc
from any cube-correct decision polynomial, with no total-degree promise. -/
theorem partial_component_of_correct (B : Set (Arc m)) (p : MvPolynomial (Arc m) (ZMod 2))
    (covers : ∀ a ∈ p.support, a.support.card ≤ m → ∀ i ∉ B, a i ≤ 1)
    (correct : ∀ E, eval (indicator (ZMod 2) E) p = if (tours E).Nonempty then 1 else 0) :
    homogeneousComponent m (PartialLayer.reduceOn B p) = Statement.hc (ZMod 2) m := by
  classical
  rw [PartialLayer.homogeneous_reduceOn_eq B m p covers]
  apply multilinear_component_of_correct
  · rw [mem_restrictDegree_iff_sup]
    intro i
    rw [← degreeOf_def]
    exact PartialLayer.degreeOf_reduceOn_univ p i
  · intro E
    rw [PartialLayer.eval_reduceOn_cube]
    · exact correct E
    · intro i
      by_cases h : i ∈ E <;> simp [indicator, h]

end BooleanTransfer.TourLayer

#print axioms BooleanTransfer.TourLayer.hc_on_small_graph
#print axioms BooleanTransfer.TourLayer.eval_decisionANF
#print axioms BooleanTransfer.TourLayer.decisionANF_component
#print axioms BooleanTransfer.TourLayer.multilinear_component_of_correct
