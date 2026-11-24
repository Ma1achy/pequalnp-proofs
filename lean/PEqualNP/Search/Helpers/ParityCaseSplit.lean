import PEqualNP.ProofComplexity.Helpers.Recomb

/-! Reassemble a parity refutation from a family of proofs that exclude all assignments
to selected parity forms. The variables themselves are the special case of singleton forms. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The disjunction saying that at least one of the chosen forms differs from its
assigned value. This construction also allows repeated or dependent forms. -/
def parityBlock {k : ℕ} (forms : Fin k → Finset V) (a : Fin k → Bool) : LinClause V :=
  Finset.univ.image (fun i => (forms i, !a i))

private theorem block_cons {k : ℕ} (forms : Fin (k + 1) → Finset V)
    (b : Bool) (a : Fin k → Bool) :
    parityBlock forms (Fin.cons b a) =
      insert (forms 0, !b) (parityBlock (fun i => forms i.succ) a) := by
  ext e
  simp only [parityBlock, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hi.symm
    | succ j => exact Or.inr ⟨j, hi⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, rfl⟩

theorem resolve_siblings (T : LinClause V) (q : Finset V) :
    IsLinResolvent (insert (q, false) T) (insert (q, true) T) T := by
  refine ⟨q, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, ?_⟩
  ext e
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
  have : ((q, false) : LinEq V) ≠ (q, true) := by simp
  by_cases h₀ : e = (q, false) <;> by_cases h₁ : e = (q, true) <;> simp_all

private theorem parity_leaf_sum {k : ℕ} (g : (Fin (k + 1) → Bool) → ℕ) :
    (∑ a, g a) = (∑ a, g (Fin.cons true a)) + ∑ a, g (Fin.cons false a) := by
  let e := Fin.consEquiv (fun _ : Fin (k+1) => Bool)
  rw [← e.sum_comp g, Fintype.sum_prod_type]
  simp [e, Fin.consEquiv_apply, add_comm]

private theorem parity_cases_derive {F : Set (LinClause V)} {k : ℕ}
    (forms : Fin k → Finset V) (T : LinClause V)
    (leaf : (Fin k → Bool) → List (LinClause V))
    (hd : ∀ a, IsLinDerivation F (leaf a))
    (hm : ∀ a, T ∪ parityBlock forms a ∈ leaf a) :
    ∃ ρ, IsLinDerivation F ρ ∧ T ∈ ρ ∧
      ρ.length ≤ (∑ a, (leaf a).length) + (2 ^ k - 1) := by
  classical
  induction k generalizing T with
  | zero =>
    let u : Fin 0 → Bool := Fin.elim0
    refine ⟨leaf u, hd u, ?_, ?_⟩
    · simpa [parityBlock] using hm u
    · simpa using (Finset.single_le_sum
        (f := fun a => (leaf a).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
  | succ k ih =>
    have branch (b : Bool) : ∃ ρ, IsLinDerivation F ρ ∧ insert (forms 0, !b) T ∈ ρ ∧
        ρ.length ≤ (∑ a : Fin k → Bool, (leaf (Fin.cons b a)).length) + (2 ^ k - 1) := by
      apply ih (fun i => forms i.succ) (insert (forms 0, !b) T) (fun a => leaf (Fin.cons b a))
        (fun a => hd _)
      intro a
      specialize hm (Fin.cons b a)
      simpa only [block_cons, Finset.union_insert, Finset.insert_union] using hm
    obtain ⟨ρ₀, d₀, m₀, s₀⟩ := branch true
    obtain ⟨ρ₁, d₁, m₁, s₁⟩ := branch false
    have d := Recomb.deriv_append d₁ d₀ (fun C hC => Or.inl hC)
    have step := IsLinDerivation.res d (List.mem_append_left _ m₀)
      (List.mem_append_right _ m₁) (resolve_siblings T (forms 0))
    refine ⟨T :: (ρ₀ ++ ρ₁), step, List.mem_cons_self, ?_⟩
    rw [List.length_cons, List.length_append, parity_leaf_sum, pow_succ]
    have hp : 0 < 2 ^ k := by positivity
    omega

/-- If every branch has a derivation from the original formula of its blocking
clause, concatenate the leaf proofs and add one resolution per internal node. -/
theorem parity_cases_refutation {F : Set (Clause V)} {k : ℕ}
    (forms : Fin k → Finset V) (leaf : (Fin k → Bool) → List (LinClause V))
    (hd : ∀ a, IsLinDerivation (linOfClause '' F) (leaf a))
    (hm : ∀ a, parityBlock forms a ∈ leaf a) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ (∑ a, (leaf a).length) + (2 ^ k - 1) := by
  obtain ⟨ρ, d, h, s⟩ := parity_cases_derive forms ∅ leaf hd (by simpa using hm)
  exact ⟨ρ, ⟨d, h⟩, s⟩

end PEqualNP.Search.Helpers
