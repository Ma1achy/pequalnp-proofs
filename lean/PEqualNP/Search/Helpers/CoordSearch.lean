import PEqualNP.Defs.ProofComplexity

/-! Adaptive Boolean coordinate queries with arbitrary leaf values. -/

namespace PEqualNP.Search.Helpers

inductive CoordDecision (V A : Type) where
  | leaf (label : A)
  | node (v : V) (lo hi : CoordDecision V A)

abbrev CoordSearch (V : Type) := CoordDecision V (PEqualNP.ProofComplexity.Clause V)

namespace CoordDecision

variable {V A B : Type}

def eval (t : CoordDecision V A) (a : V → Bool) : A :=
  match t with
  | .leaf label => label
  | .node v lo hi => if a v then hi.eval a else lo.eval a

def depth : CoordDecision V A → ℕ
  | .leaf _ => 0
  | .node _ lo hi => max lo.depth hi.depth + 1

def map (f : A → B) : CoordDecision V A → CoordDecision V B
  | .leaf label => .leaf (f label)
  | .node v lo hi => .node v (lo.map f) (hi.map f)

@[simp] theorem eval_map (f : A → B) (t : CoordDecision V A) (a : V → Bool) :
    (t.map f).eval a = f (t.eval a) := by
  induction t with
  | leaf => rfl
  | node v lo hi hlo hhi => cases h : a v <;> simp [map,eval,h,hlo,hhi]

@[simp] theorem depth_map (f : A → B) (t : CoordDecision V A) : (t.map f).depth = t.depth := by
  induction t with
  | leaf => rfl
  | node _ _ _ hlo hhi => simp [map,depth,hlo,hhi]

end CoordDecision

end PEqualNP.Search.Helpers
