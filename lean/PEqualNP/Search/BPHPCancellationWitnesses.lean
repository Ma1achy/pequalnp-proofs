import PEqualNP.Search.BPHPCancellationPigeons

namespace PEqualNP.Search

/-- One resolution site admits cancellation witnesses that are injective on
any prescribed set of pigeons within the given query budget. The witnesses
may depend on the set, while the site and the normalization are fixed. -/
theorem BPHPCancellationWitnesses :
  ∀ (l : ℕ), 32 ≤ l →
  let V := Fin (2 ^ l + 1) × Fin l
  let sat : (V → Bool) → PEqualNP.Search.QEq V → Prop :=
    fun a x => (∑ v, x.1 v * (if a v then 1 else 0)) ≡ x.2 [ZMOD 2]
  ∀ (π : List (PEqualNP.Search.QLine V)),
    PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
    ∀ r : ℕ, (3 * (r : ℝ) + 10) * π.length + 1 ≤ Real.exp ((2 : ℝ)^l / (32768 * (l : ℝ)^2)) →
    ∃ (P : PEqualNP.Search.QEq V → PEqualNP.Search.QEq V) (scale : PEqualNP.Search.QEq V → ℕ),
      P 0 = 0 ∧ scale 0 = 0 ∧
      (∀ x v, x.1 v = (2 : ℤ)^(scale x) * (P x).1 v) ∧
      (∀ x, x.2 = (2 : ℤ)^(scale x) * (P x).2) ∧
      (∀ x, x ≠ 0 → (∃ v, Odd ((P x).1 v)) ∨ Odd ((P x).2)) ∧
      ∃ (front tail : List (PEqualNP.Search.QLine V)) (e f : PEqualNP.Search.QEq V)
        (C D : PEqualNP.Search.QLine V) (α β : ℤ),
        let R : PEqualNP.Search.QLine V := (α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)
        π = front ++ (R :: tail) ∧ (e :: C) ∈ tail ∧ (f :: D) ∈ tail ∧
        ∀ U : Finset (Fin (2 ^ l + 1)), 2 ^ (l * U.card) ≤ r →
          ∃ a : V → Bool, sat a (P e) ∧ sat a (P f) ∧ (∀ x ∈ R, ¬ sat a (P x)) ∧
            Set.InjOn (fun (i : Fin (2 ^ l + 1)) (b : Fin l) => a (i, b)) (↑U : Set _) := by
  intro l hl V sat π hπ r hshort
  obtain ⟨step, _, _, _, distinct⟩ := BPHPCancellationPigeons hl hπ r hshort
  refine ⟨Helpers.qPrimitive, Helpers.qOrder, Helpers.qPrimitive_zero, Helpers.qOrder_zero,
    Helpers.qPrimitive_coeff, Helpers.qPrimitive_rhs, fun _ h => Helpers.qPrimitive_odd h,
    step.front, step.tail, step.firstHead, step.secondHead, step.firstContext, step.secondContext,
    step.α, step.β, step.position, step.firstEarlier, step.secondEarlier, ?_⟩
  intro U hU
  obtain ⟨a, ha, hinj⟩ := distinct U hU
  obtain ⟨he, hf, hr⟩ := (step.mem_falsifiers_iff a).mp ha
  refine ⟨a, (Helpers.qParity_sat a _).mp he, (Helpers.qParity_sat a _).mp hf, ?_, hinj⟩
  intro x hx hs
  apply hr
  exact (Helpers.projectLine_sat _ a step.result).mpr ⟨x, hx, (Helpers.qParity_sat a _).mpr hs⟩

end PEqualNP.Search
