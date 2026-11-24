import PEqualNP.Search.BPHPActiveDepth

namespace PEqualNP.Search

/-- A polynomial-length bit-PHP refutation must produce and select an equation
whose truth defeats every adaptive parity-query strategy of the stated depth.
Both inference occurrences are witnessed by their positions and earlier premises. -/
theorem BPHPActiveDepthWitnesses :
  ∀ (p : Polynomial ℕ) (N : ℕ), ∃ t : ℕ, N ≤ t ∧
  let l := 2 ^ t
  let k := l / (2 * (t + 5))
  let V := Fin (2 ^ l + 1) × Fin l
  ∀ π : List (PEqualNP.Search.QLine V),
    let site : PEqualNP.Search.QEq V → PEqualNP.Search.QEq V → PEqualNP.Search.QEq V → Prop :=
      fun u v w => ∃ (front tail : List (PEqualNP.Search.QLine V))
        (C D : PEqualNP.Search.QLine V) (α β : ℤ),
        π = front ++ ((w :: (C ++ D)) :: tail) ∧ (u :: C) ∈ tail ∧ (v :: D) ∈ tail ∧
        w = (α • u.1 + β • v.1, α * u.2 + β * v.2)
    PEqualNP.Search.IsResLinQSynRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π →
    π.length ≤ p.eval (2 ^ l) →
    ∃ e : PEqualNP.Search.QEq V,
      (∃ u v, site u v e) ∧ (∃ u v w, site u v w ∧ (u = e ∨ v = e)) ∧
      ¬ ∃ (ask : List Bool → Finset V) (out : List Bool → Bool), ∀ a : V → Bool,
        out ((List.range k).foldl (fun h _ =>
          h ++ [decide (Odd (((ask h).filter (fun v => a v = true)).card))]) []) = true ↔
            PEqualNP.Search.QEq.Holds a e := by
  intro p N
  obtain ⟨t, ht, hard⟩ := bphp_active_adaptive_queries p N
  refine ⟨t, ht, ?_⟩
  intro l k V π site ref len
  obtain ⟨e, ⟨s, rfl⟩, ⟨s', selected⟩, noStrategy⟩ := hard π ref len
  refine ⟨_, ⟨s.firstHead, s.secondHead, s.front, s.tail, s.firstContext, s.secondContext,
      s.α, s.β, s.position, s.firstEarlier, s.secondEarlier, rfl⟩, ?_, noStrategy⟩
  exact ⟨s'.firstHead, s'.secondHead, _, ⟨s'.front, s'.tail, s'.firstContext, s'.secondContext,
    s'.α, s'.β, s'.position, s'.firstEarlier, s'.secondEarlier, rfl⟩, selected⟩

end PEqualNP.Search
