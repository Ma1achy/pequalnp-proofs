import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Finite

/-! Boundary tests for monotone Boolean circuits on a finite input cube. -/

namespace PEqualNP.Search.HeawoodBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem eval_mono {n : ℕ} (C : Circuit) (hc : Monotone2 C) {x y : Fin n → Bool}
    (sub : x ≤ y) (accept : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  have basis : IsMonotoneCircuit C := fun g hg => (hc g hg).1
  apply LowMergeProof.wires_mono C basis (List.ofFn x) (List.ofFn y) (by simp) _ C.output accept
  intro i hi
  by_cases bound : i < n
  · have atX : x ⟨i,bound⟩ = true := by
      simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,bound] using hi
    have atY := sub (⟨i,bound⟩ : Fin n)
    rw [atX] at atY
    have bit : y ⟨i,bound⟩ = true := by
      cases h : y ⟨i,bound⟩ with
      | true => rfl
      | false => rw [h] at atY; exact (by decide : ¬ (true ≤ false)) atY |>.elim
    simpa [List.getD_eq_getElem?_getD,bound] using bit
  · simp [List.getD_eq_getElem?_getD,bound] at hi

/-- A Boolean property is recognized everywhere if a monotone circuit accepts
its inclusion-minimal true inputs and rejects its inclusion-maximal false ones. -/
theorem boundary_complete {n : ℕ} (C : Circuit) (hc : Monotone2 C) (P : (Fin n → Bool) → Prop)
    (pos : ∀ x, Minimal P x → C.eval (List.ofFn x) = true)
    (neg : ∀ x, Maximal (fun y => ¬ P y) x → C.eval (List.ofFn x) = false) :
    ∀ x, C.eval (List.ofFn x) = true ↔ P x := by
  classical
  intro x
  constructor
  · intro accepted
    by_contra hx
    obtain ⟨y,xy,hy⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬ P y) x hx
    have yes := eval_mono C hc xy accepted
    rw [neg y hy] at yes
    contradiction
  · intro hx
    obtain ⟨y,yx,hy⟩ := exists_minimal_le_of_wellFoundedLT P x hx
    exact eval_mono C hc yx (pos y hy)

/-- For an edge function the positive tests may be indexed by edges: turn on
only their endpoints. The negative tests are the maximal edge-free inputs. -/
theorem edge_boundary_complete {n : ℕ} (E : List (ℕ × ℕ)) (C : Circuit) (hc : Monotone2 C)
    (edge : ∀ u v : Fin n, (u.val,v.val) ∈ E →
      C.eval (List.ofFn (fun i : Fin n => decide (i=u ∨ i=v))) = true)
    (independent : ∀ x : Fin n → Bool,
      Maximal (fun y : Fin n → Bool =>
        ¬ ∃ u v : Fin n, (u.val,v.val) ∈ E ∧ y u = true ∧ y v = true) x →
      C.eval (List.ofFn x) = false) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true := by
  apply boundary_complete C hc _ _ independent
  intro x hx
  obtain ⟨u,v,mem,hu,hv⟩ := hx.1
  apply eval_mono C hc _ (edge u v mem)
  intro i
  by_cases same : i=u ∨ i=v
  · rcases same with rfl | rfl <;> simp_all
  · simp [same]

end PEqualNP.Search.HeawoodBoundary
