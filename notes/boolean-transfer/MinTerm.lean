import Init

/-! A finite cube is indexed by an ordered list of distinct coordinates.
Its subsets are ordered sublists. Over F₂, both the subset zeta transform
and its inverse use XOR; a coefficient is the XOR over all sublists. -/
namespace BooleanTransfer.MinTerm

/-- Recursively choose to drop or keep the next coordinate. -/
def subsetXor (f : List α → Bool) : List α → Bool
  | [] => f []
  | x :: xs => subsetXor f xs ^^ subsetXor (fun ys => f (x :: ys)) xs

private theorem xor_swap (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem subsetXor_add (s : List α) (f g : List α → Bool) :
    subsetXor (fun t => f t ^^ g t) s = (subsetXor f s ^^ subsetXor g s) := by
  induction s generalizing f g with
  | nil => rfl
  | cons x s ih =>
    simp only [subsetXor]
    rw [ih f g, ih (fun t => f (x :: t)) (fun t => g (x :: t))]
    exact xor_swap _ _ _ _

/-- Evaluating the resulting ANF coefficients on the indicator of s recovers f(s). -/
theorem subsetXor_involutive (s : List α) (f : List α → Bool) :
    subsetXor (subsetXor f) s = f s := by
  induction s generalizing f with
  | nil => rfl
  | cons x s ih =>
    simp only [subsetXor]
    rw [subsetXor_add, ih f, ih (fun t => f (x :: t))]
    cases f s <;> cases f (x :: s) <;> rfl

/-- A function which vanishes below layer |s| has coefficient f(s) on s. -/
theorem coefficient_at_first_layer (s : List α) (f : List α → Bool)
    (low : ∀ t, t.length < s.length → f t = false) :
    subsetXor f s = f s := by
  induction s generalizing f with
  | nil => rfl
  | cons x s ih =>
    have h₀ : subsetXor f s = false := by
      rw [ih f (fun t h => low t (by simp; omega))]
      exact low s (by simp)
    have h₁ : subsetXor (fun t => f (x :: t)) s = f (x :: s) :=
      ih _ (fun t h => low (x :: t) (by simpa using h))
    simp [subsetXor, h₀, h₁]

/-- Detect whether the input contains a member of the supplied minterm list.
All sets, including each member of M, are listed in the common coordinate order. -/
def containsMinterm [DecidableEq α] (M : List (List α)) (s : List α) : Bool :=
  M.any fun E => E.isSublist s

theorem homogeneous_minterm_coefficient [DecidableEq α] (M : List (List α))
    (d : Nat) (uniform : ∀ E ∈ M, E.length = d) (s : List α) (hs : s.length = d) :
    subsetXor (containsMinterm M) s = decide (s ∈ M) := by
  rw [coefficient_at_first_layer]
  · apply Bool.eq_iff_iff.mpr
    simp only [containsMinterm, List.any_eq_true, List.isSublist_iff_sublist, decide_eq_true_eq]
    constructor
    · rintro ⟨E, hE, sub⟩
      rw [← sub.eq_of_length ((uniform E hE).trans hs.symm)]
      exact hE
    · intro mem
      exact ⟨s, mem, List.Sublist.refl _⟩
  · intro t ht
    apply List.any_eq_false.mpr
    intro E hE hactive
    have le := (List.isSublist_iff_sublist.mp hactive).length_le
    rw [uniform E hE] at le
    omega

/-- Every coefficient of lower degree vanishes for the same decision predicate. -/
theorem below_minterm_coefficient [DecidableEq α] (M : List (List α))
    (d : Nat) (uniform : ∀ E ∈ M, E.length = d) (s : List α) (hs : s.length < d) :
    subsetXor (containsMinterm M) s = false := by
  have h : ∀ t : List α, t.length < d → containsMinterm M t = false := by
    intro t ht
    apply List.any_eq_false.mpr
    intro E hE hactive
    have le := (List.isSublist_iff_sublist.mp hactive).length_le
    rw [uniform E hE] at le
    omega
  rw [coefficient_at_first_layer s _ (fun t ht => h t (by omega))]
  exact h s hs

end BooleanTransfer.MinTerm

#print axioms BooleanTransfer.MinTerm.subsetXor_involutive
#print axioms BooleanTransfer.MinTerm.homogeneous_minterm_coefficient
#print axioms BooleanTransfer.MinTerm.below_minterm_coefficient
