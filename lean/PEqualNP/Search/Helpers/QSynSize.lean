import PEqualNP.Defs.SearchQ

/-! Counting distinct input clauses in an integer resolution proof, including the space
occupied by the equations of each clause. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

private theorem litQEq_injective : Function.Injective (litQEq (V := V)) := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ he
  have hv : v = v' := by
    by_contra hne
    have h := congrArg (fun e : QEq V => e.1 v) he
    simp [litQEq, hne] at h
  subst v'
  have h := congrArg Prod.snd he
  cases b <;> cases b' <;> simp_all [litQEq]

private theorem eq_of_same_axiom_line {C D : Clause V} {L : QLine V}
    (hC : ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t)
    (hD : ∀ e, e ∈ L ↔ ∃ t ∈ D, e = litQEq t) : C = D := by
  ext t
  have encode (A : Clause V) : (∃ s ∈ A, litQEq t = litQEq s) ↔ t ∈ A := by
    simp [litQEq_injective.eq_iff]
  rw [← encode C, ← hC, hD, encode D]

/-- Each distinct literal of an input clause occupies at least one position in its axiom line. -/
theorem card_le_axiom_length {C : Clause V} {L : QLine V}
    (h : ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) : C.card ≤ L.length := by
  classical
  have him : C.image litQEq ⊆ L.toFinset := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    exact List.mem_toFinset.mpr ((h _).mpr ⟨t, ht, rfl⟩)
  calc
    C.card = (C.image litQEq).card := (Finset.card_image_of_injective _ litQEq_injective).symm
    _ ≤ L.toFinset.card := Finset.card_le_card him
    _ ≤ L.length := List.toFinset_card_le L

variable [Fintype V]

private theorem card_le_axiom_cost {C : Clause V} {L : QLine V}
    (h : ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) :
    C.card ≤ (L.map QEq.size).sum := by
  have length_le_cost (K : QLine V) : K.length ≤ (K.map QEq.size).sum := by
    induction K with
    | nil => simp
    | cons e K ih =>
      have he : 1 ≤ QEq.size e := by unfold QEq.size; omega
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  exact (card_le_axiom_length h).trans (length_le_cost L)

/-- Each distinct represented input clause contributes a line and at least one unit per
literal, even when the proof repeats equations, changes their order, or reuses lines. -/
theorem clauseCount_le_resLinQSize (S : Finset (Clause V)) (π : List (QLine V)) (w : ℕ)
    (hwidth : ∀ C ∈ S, w ≤ C.card)
    (hocc : ∀ C ∈ S, ∃ L ∈ π, ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t) :
    (w + 1) * S.card ≤ resLinQSize π := by
  classical
  induction π generalizing S with
  | nil =>
    have h : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro C hC
      obtain ⟨L, hL, -⟩ := hocc C hC
      exact List.not_mem_nil hL)
    simp [h, resLinQSize]
  | cons L π ih =>
    have hsum : resLinQSize (L :: π) = 1 + (L.map QEq.size).sum + resLinQSize π := rfl
    rw [hsum]
    by_cases h : ∃ C ∈ S, ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t
    · obtain ⟨C, hC, hL⟩ := h
      have hrest := ih (S.erase C)
        (fun D hD => hwidth D (Finset.mem_of_mem_erase hD)) (by
          intro D hD
          obtain ⟨K, hK, hDK⟩ := hocc D (Finset.mem_of_mem_erase hD)
          rcases List.mem_cons.mp hK with rfl | hK
          · exact False.elim ((Finset.ne_of_mem_erase hD) (eq_of_same_axiom_line hDK hL))
          · exact ⟨K, hK, hDK⟩)
      have hcost := (hwidth C hC).trans (card_le_axiom_cost hL)
      rw [← Finset.card_erase_add_one hC, Nat.mul_add, Nat.mul_one]
      omega
    · have hrest := ih S hwidth (by
        intro C hC
        obtain ⟨K, hK, hCK⟩ := hocc C hC
        rcases List.mem_cons.mp hK with rfl | hK
        · exact False.elim (h ⟨C, hC, hCK⟩)
        · exact ⟨K, hK, hCK⟩)
      omega

end PEqualNP.Search.Helpers
