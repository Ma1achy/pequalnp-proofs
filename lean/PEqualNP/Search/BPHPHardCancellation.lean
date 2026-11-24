import PEqualNP.Search.BPHPPrimitiveCancellation
import PEqualNP.Search.Helpers.QProjectedRepair

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- A specific position admitting a resolution inference in the given list,
with the selected heads and the two earlier premises that justify it. -/
structure ResolutionSite {V : Type} (π : List (QLine V)) where
  front : List (QLine V)
  tail : List (QLine V)
  firstHead : QEq V
  secondHead : QEq V
  firstContext : QLine V
  secondContext : QLine V
  α : ℤ
  β : ℤ
  position : π = front ++ (((α • firstHead.1 + β • secondHead.1,
    α * firstHead.2 + β * secondHead.2) :: (firstContext ++ secondContext)) :: tail)
  firstEarlier : (firstHead :: firstContext) ∈ tail
  secondEarlier : (secondHead :: secondContext) ∈ tail

namespace ResolutionSite

variable {V : Type} {π : List (QLine V)}

def result (step : ResolutionSite π) : QLine V :=
  (step.α • step.firstHead.1 + step.β • step.secondHead.1,
    step.α * step.firstHead.2 + step.β * step.secondHead.2) ::
      (step.firstContext ++ step.secondContext)

/-- The parity clause asserting that if both normalized heads hold, the
normalized conclusion holds. Its false region is exactly the set of witnesses
to failure of this inference under the projection. -/
noncomputable def repair [Fintype V] [DecidableEq V] (step : ResolutionSite π) : ProofComplexity.LinClause V :=
  repairClause (projectLine (fun e => qParity (qPrimitive e)) step.result)
    (qParity (qPrimitive step.firstHead)) (qParity (qPrimitive step.secondHead))

theorem fails_repair_iff [Fintype V] [DecidableEq V] (step : ResolutionSite π) (a : V → Bool) :
    ¬ LinClauseSat a step.repair ↔
    LinEqSat a (qParity (qPrimitive step.firstHead)) ∧
    LinEqSat a (qParity (qPrimitive step.secondHead)) ∧
    ¬ LinClauseSat a (projectLine (fun e => qParity (qPrimitive e)) step.result) := by
  classical
  have inserted (q : ProofComplexity.LinEq V) (T : ProofComplexity.LinClause V) :
      LinClauseSat a (insert q T) ↔ LinEqSat a q ∨ LinClauseSat a T := by simp [LinClauseSat]
  simp only [repair, repairClause, inserted, parityNeg_sat, not_or, not_not]

end ResolutionSite

/-- One failed primitive cancellation must be expensive to repair from the
original pigeonhole axioms. If every repair used at most B parity proof lines,
their derivations could be inserted into the projected refutation. -/
theorem BPHPHardCancellation {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) (B : ℕ)
    (short : ((B : ℝ) + 8) * π.length + 1 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ step : ResolutionSite π, PrimitiveRankPair step.firstHead step.secondHead ∧
      (∃ a, ¬ LinClauseSat a step.repair) ∧
      ∀ δ, IsLinDerivation (linOfClause '' BPHP (2 ^ l + 1) l) δ →
        step.repair ∈ δ → B < δ.length := by
  classical
  let φ := fun (e : QEq (Fin (2 ^ l + 1) × Fin l)) => qParity (qPrimitive e)
  by_contra! none
  have repairs : BoundedProjectionRepairs φ (BPHP (2 ^ l + 1) l) π B := by
    intro front tail e f C D α β R pos left right bad
    obtain ⟨a, he, hf, miss⟩ := bad
    let step : ResolutionSite π := ⟨front, tail, e, f, C, D, α, β, pos, left, right⟩
    have head := fun h => miss ((projectLine_sat φ a _).mpr ⟨_, List.mem_cons_self, h⟩)
    have rank := rank_pair_of_projection_failure a e f α β he hf head
    have cell : ¬ LinClauseSat a step.repair := (step.fails_repair_iff a).mpr ⟨he, hf, miss⟩
    exact none step rank ⟨a, cell⟩
  obtain ⟨ρ, ref, len⟩ := projected_refutation_with_repairs φ (by intro t; simp [φ])
    (fun e hz hn a => qParity_primitive_false a e hz hn) (collision_formula_nonempty l) hπ B repairs
  have upper : (ρ.length : ℝ) ≤ ((B : ℝ)+8) * π.length + 1 := by exact_mod_cast len
  have lower := L036 l ρ hl ref
  linarith

end PEqualNP.Search
