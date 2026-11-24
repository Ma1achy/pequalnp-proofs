import CircuitDAG
import Statement

namespace BooleanTransfer.MvPolynomialModel
open MvPolynomial

/-! The upstream gate predicate operates on formal polynomials. The correctness
claim below only compares evaluation on Boolean inputs and has no degree bound. -/

def encodeBit (b : Bool) : ZMod 2 := if b then 1 else 0
def decodeBit (a : ZMod 2) : Bool := decide (a = 1)

private theorem decode_encode (b : Bool) : decodeBit (encodeBit b) = b := by
  cases b <;> decide

private theorem encode_decode : ∀ a : ZMod 2, encodeBit (decodeBit a) = a := by decide
private theorem decode_add : ∀ a b : ZMod 2, decodeBit (a+b) = Bool.xor (decodeBit a) (decodeBit b) := by decide
private theorem decode_mul : ∀ a b : ZMod 2, decodeBit (a*b) = (decodeBit a && decodeBit b) := by decide

noncomputable def ops (V : Type) : Arithmetic V (MvPolynomial V (ZMod 2)) :=
  ⟨X, fun b => C (encodeBit b), (· + ·), (· * ·)⟩

noncomputable def reads (V : Type) : Reads (ops V) where
  ev x p := decodeBit (eval (fun i => encodeBit (x i)) p)
  var x i := by
    change decodeBit (eval _ (X i)) = x i
    rw [eval_X, decode_encode]
  lit x b := by
    change decodeBit (eval _ (C (encodeBit b))) = b
    rw [eval_C, decode_encode]
  add x p q := by
    change decodeBit (eval _ (p+q)) = _
    rw [map_add, decode_add]
  mul x p q := by
    change decodeBit (eval _ (p*q)) = _
    rw [map_mul, decode_mul]

theorem gate_translation (p : Net V n) (out : Fin n) :
    ∃ f : MvPolynomial V (ZMod 2), Statement.Computes f (3*n) ∧
      ∀ x, eval (fun i => encodeBit (x i)) f = encodeBit (p.values x out) := by
  obtain ⟨f, hf, eq⟩ := translate (ops V) (reads V) p out
  refine ⟨f, toSLP hf C (fun b => ⟨encodeBit b, rfl⟩), ?_⟩
  intro x
  have h := congrArg encodeBit (eq x)
  change encodeBit (decodeBit (eval _ f)) = _ at h
  simpa only [encode_decode] using h

def PolySize (L : DecisionFamily) : Prop :=
  ∃ c d : Nat, ∀ m, ∃ s : Nat, ∃ f : MvPolynomial (Fin m) (ZMod 2),
    s ≤ c*(m+1)^d ∧ Statement.Computes f s ∧
    ∀ x, eval (fun i => encodeBit (x i)) f = encodeBit (L m x)

theorem lower_bound_transfer (L : DecisionFamily) (hard : ¬ PolySize L) : ¬ PolyBool L := by
  rintro ⟨c, d, h⟩
  apply hard
  refine ⟨3*c, d, ?_⟩
  intro m
  obtain ⟨s, p, out, bound, correct⟩ := h m
  obtain ⟨f, computed, eq⟩ := gate_translation p out
  refine ⟨3*s, f, ?_, computed, ?_⟩
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 bound
  · intro x
    rw [eq, correct]

end BooleanTransfer.MvPolynomialModel
#print axioms BooleanTransfer.MvPolynomialModel.gate_translation
#print axioms BooleanTransfer.MvPolynomialModel.lower_bound_transfer
