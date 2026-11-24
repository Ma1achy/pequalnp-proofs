import Statement

namespace BooleanTransfer

/-- Append one gate, with both operands referencing the old output slot. -/
theorem computes_square {R : Type u} {V : Type} [CommSemiring R]
    {p : MvPolynomial V R} {s : Nat} (h : Statement.Computes p s) :
    Statement.Computes (p ^ 2) (s + 1) := by
  obtain ⟨l, valid, o, ho, out⟩ := h
  let next := fun k => if k < s then l k else p ^ 2
  have old {k : Nat} (hk : k < s) : next k = l k := if_pos hk
  refine ⟨next, ?_, s, Nat.lt_succ_self _, if_neg (Nat.lt_irrefl _)⟩
  intro k hk
  by_cases before : k < s
  · rcases valid k before with ⟨v, ev⟩ | ⟨a, ea⟩ | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · exact Or.inl ⟨v, (old before).trans ev⟩
    · exact Or.inr (Or.inl ⟨a, (old before).trans ea⟩)
    · refine Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, ?_⟩))
      rw [old before, old (hi.trans before), old (hj.trans before), e]
    · refine Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, ?_⟩))
      rw [old before, old (hi.trans before), old (hj.trans before), e]
  · have eq : k = s := by omega
    subst k
    refine Or.inr (Or.inr (Or.inr ⟨o, ho, o, ho, ?_⟩))
    rw [old ho, out]
    simp [next, pow_two]

/-- j repeated squarings cost j extra SLP slots at any commutative semiring. -/
theorem computes_pow_two_pow {R : Type u} {V : Type} [CommSemiring R]
    {p : MvPolynomial V R} {s : Nat} (h : Statement.Computes p s) (j : Nat) :
    Statement.Computes (p ^ (2 ^ j)) (s + j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    simpa only [Nat.pow_succ, pow_mul, Nat.add_assoc] using computes_square ih

end BooleanTransfer

#print axioms BooleanTransfer.computes_pow_two_pow
