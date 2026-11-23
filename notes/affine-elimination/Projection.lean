import Init

/-! Exact elimination of a Boolean variable from a family of guarded forbidden values.
The guards, the forbidden values and the unaffected constraint may all depend on an
arbitrary remaining assignment `y`. -/

namespace AffineElimination

/-- A common admissible Boolean value exists exactly when all active guards forbid
one and the same value. Pairwise compatibility also covers an empty active family. -/
theorem exists_avoiding_iff_pairwise {Y I : Type _} (keep : Y → Prop)
    (guard : I → Y → Prop) (forbid : I → Y → Bool) (y : Y) :
    (∃ z : Bool, keep y ∧ ∀ i, guard i y → z ≠ forbid i y) ↔
      keep y ∧ ∀ i j, guard i y → guard j y → forbid i y = forbid j y := by
  constructor
  · rintro ⟨z, hk, hav⟩
    refine ⟨hk, ?_⟩
    intro i j hi hj
    have uniqueness (p q r : Bool) : p ≠ q → p ≠ r → q = r := by
      cases p <;> cases q <;> cases r <;> decide
    exact uniqueness z _ _ (hav i hi) (hav j hj)
  · rintro ⟨hk, hpair⟩
    by_cases hactive : ∃ i, guard i y
    · obtain ⟨i, hi⟩ := hactive
      refine ⟨!(forbid i y), hk, ?_⟩
      intro j hj
      rw [hpair i j hi hj]
      cases forbid j y <;> decide
    · exact ⟨false, hk, fun i hi => False.elim (hactive ⟨i, hi⟩)⟩

/-- The two guarded clauses in the initial exercise. The four bits can be values
of arbitrary expressions in the remaining variables. -/
theorem two_clauses (a b c d : Bool) :
    (∃ z : Bool, (a || (z ^^ b)) = true ∧ (c || (z ^^ d)) = true) ↔
      (a || c || !(b ^^ d)) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Positive exactly-one as one odd-parity constraint and three negative
binary clauses. Addition on the right counts true bits as natural numbers. -/
theorem one_in_three (a b c : Bool) :
    ((a ^^ b ^^ c) = true ∧ ((!a) || (!b)) = true ∧
      ((!a) || (!c)) = true ∧ ((!b) || (!c)) = true) ↔
      a.toNat + b.toNat + c.toNat = 1 := by
  cases a <;> cases b <;> cases c <;> decide

end AffineElimination
