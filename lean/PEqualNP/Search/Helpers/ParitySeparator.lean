import PEqualNP.ProofComplexity.Helpers.ChainC2

/-! A binary semantic consequence of parity clauses is a weakening of one premise
or admits a separating parity pivot. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

private def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bitZ_xor (s t : Bool) : bitZ (xor s t) = bitZ s + bitZ t := by
  cases s <;> cases t <;> decide

private theorem eqSat_iff {V : Type} (a : V → Bool) (q : LinEq V) :
    LinEqSat a q ↔ ∑ v ∈ q.1, bitZ (a v) = bitZ q.2 := by
  have h := PEqualNP.ProofComplexity.Helpers.linEqSat_iff_sum (fun v => bitZ (a v)) q
  have back : (fun v => decide (bitZ (a v) = 1)) = a := by
    funext v
    cases a v <;> decide
  rw [back] at h
  rw [h]
  clear h
  generalize (∑ v ∈ q.1, bitZ (a v)) = t
  rcases q with ⟨s, b⟩
  change (t + (if b = true then 0 else 1) = 1) ↔ t = bitZ b
  revert t b
  decide

private def triple {V : Type} (a b c : V → Bool) (v : V) : Bool := xor (xor (a v) (b v)) (c v)

/-- Two arguments giving the same truth value to an affine equation cancel in the
pointwise ternary sum. -/
private theorem triple_sat {V : Type} (a b c : V → Bool) (q : LinEq V)
    (h : LinEqSat b q ↔ LinEqSat c q) : LinEqSat (triple a b c) q ↔ LinEqSat a q := by
  simp only [eqSat_iff, triple, bitZ_xor, Finset.sum_add_distrib] at *
  exact (by decide : ∀ s t u v : ZMod 2, (t = v ↔ u = v) → (s + t + u = v ↔ s = v)) _ _ _ _ h

private theorem triple_comm {V : Type} (a b c : V → Bool) : triple a b c = triple b a c := by
  funext v
  simp [triple, Bool.xor_comm (a v) (b v)]

private theorem flip_sat {V : Type} (a : V → Bool) (q : LinEq V) :
    LinEqSat a (q.1, !q.2) ↔ ¬ LinEqSat a q := by
  rcases q with ⟨f, b⟩
  cases b <;> simp [LinEqSat]

/-- If two clauses jointly entail a third one, either one premise suffices or a
single parity equation separates the two premises outside the target. -/
theorem paritySeparator {V : Type} [DecidableEq V] {A B T : LinClause V}
    (h : ∀ a, LinClauseSat a A → LinClauseSat a B → LinClauseSat a T) :
    (∀ a, LinClauseSat a A → LinClauseSat a T) ∨
    (∀ a, LinClauseSat a B → LinClauseSat a T) ∨
    ∃ q : LinEq V,
      (∀ a, LinClauseSat a A → LinClauseSat a T ∨ LinEqSat a (q.1, !q.2)) ∧
      (∀ a, LinClauseSat a B → LinClauseSat a T ∨ LinEqSat a q) := by
  classical
  by_cases hA : ∀ a, LinClauseSat a A → LinClauseSat a T
  · exact Or.inl hA
  by_cases hB : ∀ a, LinClauseSat a B → LinClauseSat a T
  · exact Or.inr (Or.inl hB)
  push Not at hA hB
  obtain ⟨a, ha, hat⟩ := hA
  obtain ⟨b, hb, hbt⟩ := hB
  obtain ⟨p, hp, hap⟩ := ha
  obtain ⟨q, hq, hbq⟩ := hb
  refine Or.inr (Or.inr ⟨q, ?_, ?_⟩)
  · intro z hz
    by_cases ht : LinClauseSat z T
    · exact Or.inl ht
    · exact Or.inr ((flip_sat z q).mpr fun hqz => ht (h z hz ⟨q, hq, hqz⟩))
  · intro z hz
    by_cases ht : LinClauseSat z T
    · exact Or.inl ht
    right
    by_contra hzq
    have haq : ¬ LinEqSat a q := fun hs => hat (h a ⟨p, hp, hap⟩ ⟨q, hq, hs⟩)
    have hbp : ¬ LinEqSat b p := fun hs => hbt (h b ⟨p, hp, hs⟩ ⟨q, hq, hbq⟩)
    have hzp : ¬ LinEqSat z p := fun hs => ht (h z ⟨p, hp, hs⟩ hz)
    have hp' : LinEqSat (triple a b z) p :=
      (triple_sat a b z p (iff_of_false hbp hzp)).mpr hap
    have hq' : LinEqSat (triple a b z) q := by
      rw [triple_comm a b z]
      exact (triple_sat b a z q (iff_of_false haq hzq)).mpr hbq
    obtain ⟨t, htm, hts⟩ := h _ ⟨p, hp, hp'⟩ ⟨q, hq, hq'⟩
    have hbt' : ¬ LinEqSat b t := fun hs => hbt ⟨t, htm, hs⟩
    have hzt' : ¬ LinEqSat z t := fun hs => ht ⟨t, htm, hs⟩
    exact hat ⟨t, htm, (triple_sat a b z t (iff_of_false hbt' hzt')).mp hts⟩

end PEqualNP.Search.Helpers
