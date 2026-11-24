import PEqualNP.Search.PetersenGateWitness
import Mathlib.Data.Fintype.Basic

namespace PEqualNP.Search.Petersen2541

open PetersenGateWitness

/-- Distinct restrictions of `f` in which every coordinate of `S` remains essential. -/
def CofactorFamily {V : Type} [DecidableEq V] (f : (V → Bool) → Bool)
    (S : Finset V) (k : ℕ) : Prop :=
  ∃ fixed : Fin k → V → Bool,
    let co := fun j (x : V → Bool) => f (fun i => if i ∈ S then x i else fixed j i)
    Function.Injective co ∧
      ∀ j i, i ∈ S → ∃ x : V → Bool, co j x ≠ co j (Function.update x i (!x i))

private def probe (t : Fin 10) (i : Fin 9) : Bool := decide (t.val = i.val)

private def cofactor (S : Finset (Fin 9)) (m : ℕ) (x : Fin 9 → Bool) : Bool :=
  edgeFunction fun i => if i ∈ S then x i else m.testBit i.val

/-- Singletons and the all-false assignment distinguish the restrictions. Those same
assignments also witness that each of the free coordinates remains essential. -/
private theorem ofMasks {k : ℕ} (S : Finset (Fin 9)) (mask : Fin k → ℕ)
    (hd : ∀ j j', j ≠ j' → ∃ t : Fin 10,
      cofactor S (mask j) (probe t) ≠ cofactor S (mask j') (probe t))
    (hs : ∀ j i, i ∈ S → ∃ t : Fin 10,
      cofactor S (mask j) (probe t) ≠
      cofactor S (mask j) (Function.update (probe t) i (!(probe t i)))) :
    CofactorFamily edgeFunction S k := by
  refine ⟨fun j i => (mask j).testBit i.val, ?_, ?_⟩
  · intro j j' he
    by_contra h
    obtain ⟨t, ht⟩ := hd j j' h
    exact ht (congrFun he (probe t))
  · intro j i hi
    obtain ⟨t, ht⟩ := hs j i hi
    exact ⟨probe t, ht⟩

theorem family058 : CofactorFamily edgeFunction {0, 5, 8} 4 := by
  apply ofMasks _ (fun j => [0, 2, 8, 138].getD j.val 0) <;> decide +kernel

theorem family016 : CofactorFamily edgeFunction {0, 1, 6} 4 := by
  apply ofMasks _ (fun j => [0, 16, 256, 276].getD j.val 0) <;> decide +kernel

theorem family237 : CofactorFamily edgeFunction {2, 3, 7} 4 := by
  apply ofMasks _ (fun j => [0, 16, 32, 50].getD j.val 0) <;> decide +kernel

theorem family04 : CofactorFamily edgeFunction {0, 4} 2 := by
  apply ofMasks _ (fun j => [0, 10].getD j.val 0) <;> decide +kernel

end PEqualNP.Search.Petersen2541
