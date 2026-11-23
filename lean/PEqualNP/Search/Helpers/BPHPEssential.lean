import PEqualNP.Search.Helpers.QSynEssential
import PEqualNP.Search.Helpers.QSynSize
import PEqualNP.ProofComplexity.Helpers.SizeBound

/-!
# A clause-counting baseline for syntactic integer R(lin) on bit PHP

Every collision clause is essential and contains two literals per bit.
Counting the corresponding axiom lines gives a size bound for arbitrary
dag-like proofs, including proofs that reorder or duplicate literals.
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

/-- Every collision clause occurs, up to the ordering and repetition permitted by the axiom rule. -/
theorem bphp_syn_axiom_occurs {l : ℕ} {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (i i' : Fin (2 ^ l + 1)) (hne : i ≠ i') (α : Fin l → Bool) :
    ∃ L ∈ π, ∀ e, e ∈ L ↔ ∃ lit ∈ bax i i' α, e = litQEq lit :=
  exists_axiom_line_of_critical hπ (bphp_critical i i' hne α)

/-- A family of literals indexed by a set of pigeons and the bits of a single hole. -/
private def collisionLiterals {m l : ℕ} (p : Finset (Fin m) × (Fin l → Bool)) :
    PEqualNP.ProofComplexity.Clause (Fin m × Fin l) :=
  (p.1 ×ˢ (Finset.univ : Finset (Fin l))).image (fun v => (v, !p.2 v.2))

private theorem collisionLiterals_pair {m l : ℕ} (i i' : Fin m) (α : Fin l → Bool) :
    collisionLiterals (({i, i'} : Finset (Fin m)), α) = bax i i' α := by
  ext lit
  simp only [collisionLiterals, bax, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, true_and, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨j, b⟩, (rfl | rfl), rfl⟩
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(i, b), Or.inl rfl, rfl⟩
    · exact ⟨(i', b), Or.inr rfl, rfl⟩

private theorem collisionLiterals_card {m l : ℕ} (p : Finset (Fin m) × (Fin l → Bool)) :
    (collisionLiterals p).card = p.1.card * l := by
  unfold collisionLiterals
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp [Finset.card_product]

/-- Every axiom line representing a bit-PHP collision contains at least two literals per bit. -/
theorem bphp_axiom_length {N l : ℕ} {C : PEqualNP.ProofComplexity.Clause (Fin N × Fin l)}
    {L : QLine (Fin N × Fin l)} (hc : C ∈ BPHP N l)
    (rep : ∀ e, e ∈ L ↔ ∃ lit ∈ C, e = litQEq lit) : 2 * l ≤ L.length := by
  obtain ⟨i, j, α, hij, rfl⟩ := hc
  have hh := card_le_axiom_length rep
  change (bax i j α).card ≤ L.length at hh
  rw [← collisionLiterals_pair, collisionLiterals_card] at hh
  simpa [hij] using hh

private theorem collisionLiterals_inj {m l : ℕ} (hl : 0 < l)
    {p q : Finset (Fin m) × (Fin l → Bool)} (hp : p.1.Nonempty)
    (h : collisionLiterals p = collisionLiterals q) : p = q := by
  apply setClause_inj hl hp
  simpa only [linOfClause, collisionLiterals, Finset.image_image, Function.comp_def, setClause]
    using congrArg linOfClause h

/-- A pair of pigeons and a hole index an essential collision clause. All these
clauses have exactly two literals per bit. -/
theorem exists_bphp_critical_family {l : ℕ} (hl : 0 < l) :
    ∃ S : Finset (PEqualNP.ProofComplexity.Clause (Fin (2 ^ l + 1) × Fin l)),
      S.card = (2 ^ l + 1).choose 2 * 2 ^ l ∧
      (∀ C ∈ S, C.card = 2 * l) ∧
      (∀ C ∈ S, ∃ a, ∀ D ∈ BPHP (2 ^ l + 1) l, D ≠ C → ClauseSat a D) := by
  classical
  let I := (Finset.univ : Finset (Fin (2 ^ l + 1))).powersetCard 2 ×ˢ
    (Finset.univ : Finset (Fin l → Bool))
  have pairCard (p) (hp : p ∈ I) : p.1.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
  have inj : Set.InjOn collisionLiterals (I : Set (Finset (Fin (2 ^ l + 1)) × (Fin l → Bool))) := by
    intro p hp q _ h
    exact collisionLiterals_inj hl (Finset.card_pos.mp (by rw [pairCard p hp]; decide)) h
  have card : (I.image collisionLiterals).card = (2 ^ l + 1).choose 2 * 2 ^ l := by
    rw [Finset.card_image_of_injOn inj]
    simp [I, Finset.card_product]
  refine ⟨I.image collisionLiterals, card, ?_, ?_⟩
  · intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    rw [collisionLiterals_card, pairCard p hp]
  · intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨i, j, hne, hs⟩ := Finset.card_eq_two.mp (pairCard p hp)
    have heq : p = (({i, j} : Finset (Fin (2 ^ l + 1))), p.2) := Prod.ext hs rfl
    rw [heq, collisionLiterals_pair]
    exact bphp_critical i j hne p.2

/-- With n = 2^l holes, all n * choose(n+1, 2) collision clauses must occur,
and each costs at least 2*l + 1 units of the project's size measure. -/
theorem bphp_syn_size_lower_bound {l : ℕ} (hl : 0 < l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) :
    (2 * l + 1) * ((2 ^ l + 1).choose 2 * 2 ^ l) ≤ resLinQSize π := by
  obtain ⟨S, hcard, hwidth, hcrit⟩ := exists_bphp_critical_family hl
  rw [← hcard]
  exact clauseCount_le_resLinQSize S π (2 * l)
    (fun C hC => (hwidth C hC).ge)
    (fun C hC => exists_axiom_line_of_critical hπ (hcrit C hC))

end PEqualNP.Search.Helpers
