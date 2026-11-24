import PEqualNP.Search.Helpers.ParitySemanticStep

/-! Using an auxiliary parity clause to repair one projected resolution step. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- The other value of the same parity form. -/
def parityNeg {V : Type} (q : LinEq V) : LinEq V := (q.1, !q.2)

@[simp] theorem parityNeg_sat {V : Type} (a : V → Bool) (q : LinEq V) :
    LinEqSat a (parityNeg q) ↔ ¬ LinEqSat a q := by
  rcases q with ⟨u, b⟩
  cases b <;> simp [parityNeg, LinEqSat]

/-- The condition that satisfaction of both projected heads entails the target. -/
def repairClause {V : Type} [DecidableEq V] (T : LinClause V) (e f : LinEq V) : LinClause V :=
  insert (parityNeg e) (insert (parityNeg f) T)

private theorem insertSat {V : Type} [DecidableEq V] (a : V → Bool) (e : LinEq V)
    (T : LinClause V) : LinClauseSat a (insert e T) ↔ LinEqSat a e ∨ LinClauseSat a T := by
  simp [LinClauseSat]

/-- Combine the two premises with the repair clause in at most eight parity lines. -/
theorem applyRepair {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {ρ : List (LinClause V)} {A B T : LinClause V} (e f : LinEq V)
    (d : IsLinDerivation F ρ) (hA : A ∈ ρ) (hB : B ∈ ρ) (hR : repairClause T e f ∈ ρ)
    (aImp : ∀ a, LinClauseSat a A → LinClauseSat a T ∨ LinEqSat a e)
    (bImp : ∀ a, LinClauseSat a B → LinClauseSat a T ∨ LinEqSat a f) :
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ T ∈ σ ∧ σ.length ≤ 8 := by
  have first (a) (ha : LinClauseSat a A) (hr : LinClauseSat a (repairClause T e f)) :
      LinClauseSat a (insert (parityNeg f) T) := by
    rw [insertSat]
    simp only [repairClause, insertSat] at hr
    rcases aImp a ha with ht | he
    · exact Or.inr ht
    · exact hr.resolve_left (fun hn => (parityNeg_sat a e).mp hn he)
  obtain ⟨s, ds, hs, ls⟩ := paritySemanticStep d hA hR first
  have second (a) (hb : LinClauseSat a B) (hm : LinClauseSat a (insert (parityNeg f) T)) :
      LinClauseSat a T := by
    rcases bImp a hb with ht | hf
    · exact ht
    · exact ((insertSat a _ _).mp hm).resolve_left (fun hn => (parityNeg_sat a f).mp hn hf)
  obtain ⟨u, du, hu, lu⟩ := paritySemanticStep ds (List.mem_append_right s hB)
    (List.mem_append_left ρ hs) second
  refine ⟨u ++ s, by simpa [List.append_assoc] using du, List.mem_append_left _ hu, ?_⟩
  rw [List.length_append]
  omega

end PEqualNP.Search.Helpers
