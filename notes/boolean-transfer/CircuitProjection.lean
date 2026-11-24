import Statement

/-! Literal projections preserve the slot budget of the reference circuit model. -/
namespace BooleanTransfer.CircuitProjection

open MvPolynomial

variable {R V W : Type} [CommSemiring R]

/-- Substituting a variable or a scalar for each input preserves every gate index. -/
theorem project (f : V → MvPolynomial W R)
    (hf : ∀ v, (∃ w, f v = X w) ∨ (∃ a, f v = C a))
    {p : MvPolynomial V R} {s : ℕ} (h : Statement.Computes p s) :
    Statement.Computes (aeval f p) s := by
  obtain ⟨l, hl, k, hk, hout⟩ := h
  refine ⟨fun j => aeval f (l j), ?_, k, hk, congrArg (aeval f) hout⟩
  intro j hj
  dsimp only
  rcases hl j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨u, hu, v, hv, hadd⟩ | ⟨u, hu, v, hv, hmul⟩
  · rw [hv, aeval_X]
    rcases hf v with hX | hC
    · exact Or.inl hX
    · exact Or.inr (Or.inl hC)
  · exact Or.inr (Or.inl ⟨a, by simp [ha]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨u, hu, v, hv, by simp [hadd]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨u, hu, v, hv, by simp [hmul]⟩))

end BooleanTransfer.CircuitProjection
