import SurplusKernel
import Mathlib.Data.Fintype.List
import Mathlib.Algebra.MvPolynomial.Rename

/-! The weighted polynomial identity for a forced arc in a fixed directed graph template. -/

namespace BooleanTransfer.ForcedTourWeight

open BooleanTransfer.SurplusKernel Finset MvPolynomial

variable {α R S : Type*}

/-- Product of arc weights along the tail of an anchored tour and its closing arc. -/
def walkWeight [Mul R] (W : Option α → Option α → R) : Option α → List α → R
  | x, [] => W x none
  | x, y :: l => W x (some y) * walkWeight W (some y) l

private theorem map_tail [Mul R] (W : Option (Option α) → Option (Option α) → R)
    (x : Option α) (l : List α) :
    walkWeight W (src x) (l.map some) =
      walkWeight (fun i j => W (src i) (dst j)) x l := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    change W (src x) (some (some i)) * walkWeight W (src (some i)) (l.map some) = _
    rw [ih]
    rfl

/-- Per-tour factor, before summing and even without commutativity. -/
theorem expand_weight [Mul R] (W : Option (Option α) → Option (Option α) → R) (l : List α) :
    walkWeight W none (expand l) =
      W none (some none) * walkWeight (fun i j => W (src i) (dst j)) none l := by
  change W none (some none) * walkWeight W (src none) (l.map some) = _
  rw [map_tail]

private noncomputable instance tourFintype [Fintype α] (E : Option α → Option α → Prop) :
    Fintype {l // isTour E l} := by
  classical
  let forget (t : {l // isTour E l}) : {l : List α // l.Nodup} := ⟨t.val, t.property.1⟩
  exact Fintype.ofInjective forget (fun _ _ eq =>
    Subtype.ext (congrArg (fun q : {l : List α // l.Nodup} => q.val) eq))

/-- Sum over distinct tours, each written starting from the specified anchor. -/
noncomputable def weightedSum [Fintype α] [CommSemiring R]
    (E : Option α → Option α → Prop) (W : Option α → Option α → R) : R :=
  ∑ l : {l // isTour E l}, walkWeight W none l.val

/-- The forced arc factors out of the entire finite sum in every commutative semiring. -/
theorem weighted_factor [Fintype α] [CommSemiring R]
    (E : Option (Option α) → Option (Option α) → Prop)
    (W : Option (Option α) → Option (Option α) → R)
    (arc : E none (some none)) (only : ∀ w, E none w → w = some none) :
    weightedSum E W =
      W none (some none) * weightedSum (contract E) (fun i j => W (src i) (dst j)) := by
  classical
  unfold weightedSum
  rw [← (tourEquiv E arc only).sum_comp (fun t => walkWeight W none t.val), mul_sum]
  exact sum_congr rfl fun t _ => expand_weight W t.val

private theorem map_walk [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (W : Option α → Option α → R) (x : Option α) (l : List α) :
    f (walkWeight W x l) = walkWeight (fun i j => f (W i j)) x l := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => simp [walkWeight, map_mul, ih]

private theorem map_sumWeight [Fintype α] [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (E : Option α → Option α → Prop) (W : Option α → Option α → R) :
    f (weightedSum E W) = weightedSum E (fun i j => f (W i j)) := by
  simp [weightedSum, map_walk]

/-- Formal tour-generating polynomial of a fixed directed graph. -/
noncomputable def tourPolynomial (R : Type*) [CommSemiring R] [Fintype α]
    (E : Option α → Option α → Prop) : MvPolynomial (Option α × Option α) R :=
  weightedSum E (fun i j => X (i, j))

/-- Literal formal polynomial identity, with the surviving arc variables renamed. -/
theorem polynomial_factor [Fintype α] (R : Type*) [CommSemiring R]
    (E : Option (Option α) → Option (Option α) → Prop)
    (arc : E none (some none)) (only : ∀ w, E none w → w = some none) :
    tourPolynomial R E =
      X (none, some none) * rename (fun ij => (src ij.1, dst ij.2)) (tourPolynomial R (contract E)) := by
  unfold tourPolynomial
  rw [weighted_factor E _ arc only]
  congr 1
  let f := (rename (R := R) (fun ij : Option α × Option α => (src ij.1, dst ij.2))).toRingHom
  symm
  change f (weightedSum _ _) = _
  rw [map_sumWeight]
  simp [f]

end BooleanTransfer.ForcedTourWeight

#print axioms BooleanTransfer.ForcedTourWeight.expand_weight
#print axioms BooleanTransfer.ForcedTourWeight.weighted_factor
#print axioms BooleanTransfer.ForcedTourWeight.polynomial_factor
