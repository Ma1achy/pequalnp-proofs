import PEqualNP.Search.BPHPPrimitiveCancellation

namespace PEqualNP.Search

/-- A short bit-pigeonhole refutation has a resolution step whose two
dyadically normalized heads have equal parity rows and a nonzero even minor. -/
theorem BPHPPrimitiveMinor :
  ∀ (l : ℕ), 32 ≤ l →
  let V := Fin (2 ^ l + 1) × Fin l
  let row : PEqualNP.Search.QEq V → Option V → ℤ :=
    fun x i => Option.elim i x.2 x.1
  ∀ π : List (PEqualNP.Search.QLine V),
    PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
    4 * (π.length : ℝ) + 1 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) →
    ∃ (front tail : List (PEqualNP.Search.QLine V)) (e f : PEqualNP.Search.QEq V)
      (C D : PEqualNP.Search.QLine V) (α β : ℤ) (r s : ℕ) (A B : PEqualNP.Search.QEq V),
      π = front ++ (((α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)) :: tail) ∧
      (e :: C) ∈ tail ∧ (f :: D) ∈ tail ∧
      (∀ i, row e i = (2 : ℤ)^r * row A i ∧ row f i = (2 : ℤ)^s * row B i) ∧
      (∀ i, row A i ≡ row B i [ZMOD 2]) ∧
      (∃ v, Odd (A.1 v) ∧ Odd (B.1 v)) ∧
      (∃ i j, row A i * row B j ≠ row A j * row B i ∧
        Even (row A i * row B j - row A j * row B i)) := by
  intro l hl V row π hπ hshort
  obtain ⟨front, tail, e, f, C, D, α, β, loc, he, hf, pair, _⟩ :=
    BPHPPrimitiveCancellation hl hπ hshort
  obtain ⟨parity, var, even_minor, i, j, hminor⟩ := pair
  have coord (x : QEq V) (c : Option V) : row x c = Helpers.qCoord x c := by cases c <;> rfl
  refine ⟨front, tail, e, f, C, D, α, β, Helpers.qOrder e, Helpers.qOrder f,
    Helpers.qPrimitive e, Helpers.qPrimitive f, loc, he, hf, ?_, ?_, ?_, ?_⟩
  · intro c
    cases c with
    | none => exact ⟨Helpers.qPrimitive_rhs e, Helpers.qPrimitive_rhs f⟩
    | some v => exact ⟨Helpers.qPrimitive_coeff e v, Helpers.qPrimitive_coeff f v⟩
  · intro c
    simpa only [coord] using Helpers.coord_modEq_of_qParity_eq parity c
  · obtain ⟨v, hv⟩ := var
    have ha : (Helpers.qPrimitive e).1 v % 2 = 1 := (Finset.mem_filter.mp hv).2
    have h := Helpers.coord_modEq_of_qParity_eq parity (some v)
    refine ⟨v, Int.odd_iff.mpr ha, Int.odd_iff.mpr ?_⟩
    change (Helpers.qPrimitive e).1 v % 2 = (Helpers.qPrimitive f).1 v % 2 at h
    exact h.symm.trans ha
  · exact ⟨i, j, by simpa only [coord] using hminor, by simpa only [coord] using even_minor i j⟩

end PEqualNP.Search
