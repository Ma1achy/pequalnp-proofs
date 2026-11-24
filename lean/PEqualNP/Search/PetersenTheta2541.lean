import PEqualNP.Search.PetersenGateWitness
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The same seven-vertex theta graph occurs after fixing any chosen vertex
and one further vertex to false. The two hubs are coordinates 0 and 1, with
three internally disjoint paths of lengths 2, 3 and 3. -/

namespace PEqualNP.Search.PetersenTheta2541

open PEqualNP.Search.PetersenGateWitness

def theta (x : Fin 7 → Bool) : Bool :=
  x 0 && x 3 || x 0 && x 2 || x 3 && x 4 || x 0 && x 5 ||
  x 2 && x 1 || x 6 && x 5 || x 4 && x 1 || x 1 && x 6

def mate : Fin 9 → Fin 9 := ![4, 6, 7, 4, 0, 7, 1, 2, 6]

-- Value 7 denotes an input to fix to false. All other entries are theta coordinates.
private def index : Fin 9 → Fin 9 → Fin 8 :=
  ![![7,3,0,2,7,6,4,5,1], ![3,7,6,1,4,0,7,5,2],
    ![0,3,7,6,5,2,4,7,1], ![2,0,3,7,7,1,5,4,6],
    ![7,3,0,2,7,6,4,5,1], ![3,0,2,1,4,7,5,7,6],
    ![3,7,6,1,4,0,7,5,2], ![0,3,7,6,5,2,4,7,1],
    ![1,2,0,3,4,6,7,5,7]]

def liftTheta (v : Fin 9) (x : Fin 7 → Bool) (i : Fin 9) : Bool :=
  if hi : (index v i).val < 7 then x ⟨(index v i).val, hi⟩ else false

def zeroAt (v : Fin 9) (x : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i = v then false else x i

theorem mate_ne (v : Fin 9) : mate v ≠ v := (by decide : ∀ j : Fin 9, mate j ≠ j) v

theorem lift_coord (v i : Fin 9) :
    (∀ x, liftTheta v x i = false) ∨ ∃ j : Fin 7, ∀ x, liftTheta v x i = x j := by
  by_cases h : (index v i).val < 7
  · exact Or.inr ⟨⟨(index v i).val, h⟩, fun _ => dif_pos h⟩
  · exact Or.inl (fun _ => dif_neg h)

theorem lift_zero (v : Fin 9) (x : Fin 7 → Bool) :
    liftTheta v x v = false ∧ liftTheta v x (mate v) = false := by
  have hz : ∀ k : Fin 9, (index k k).val = 7 ∧ (index k (mate k)).val = 7 := by decide
  simp [liftTheta, (hz v).1, (hz v).2]

theorem zeroAt_lift (v : Fin 9) (x : Fin 7 → Bool) : zeroAt v (liftTheta v x) = liftTheta v x := by
  funext i
  by_cases h : i = v
  · subst i; simp [zeroAt, (lift_zero v x).1]
  · simp [zeroAt,h]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem lift_correct : ∀ (v : Fin 9) (x : Fin 7 → Bool), edgeFunction (liftTheta v x) = theta x := by
  decide

-- The surviving mate is essential even after the first deletion.
theorem mate_pivotal (v : Fin 9) :
    ∃ a b : Fin 9 → Bool, (∀ i, i ≠ mate v → a i = b i) ∧
      edgeFunction (zeroAt v a) ≠ edgeFunction (zeroAt v b) := by
  let a (w : Fin 9) : Fin 9 → Bool := fun i => decide (i = w)
  let b (u w : Fin 9) : Fin 9 → Bool := fun i => decide (i = w ∨ i = u)
  have cert : ∀ k : Fin 9, ∃ w : Fin 9,
      edgeFunction (zeroAt k (a w)) ≠ edgeFunction (zeroAt k (b (mate k) w)) := by decide
  obtain ⟨w,hw⟩ := cert v
  exact ⟨a w,b (mate v) w,fun i hi => by simp [a,b,hi],hw⟩

end PEqualNP.Search.PetersenTheta2541
