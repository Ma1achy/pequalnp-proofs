import PEqualNP.Search.BPHPHardCancellation
import PEqualNP.Search.Helpers.ParityPointCover
import PEqualNP.ProofComplexity.L021

/-! A parity repair clause that is hard to derive has many falsifying assignments.
An adaptive parity decision tree needs many leaves to identify a violated input
on those assignments. Both conclusions apply to the same resolution position. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- The Boolean assignments falsifying the parity clause. -/
noncomputable def parityFalsifiers {V : Type} [Fintype V] (R : ProofComplexity.LinClause V) :
    Finset (V → Bool) := by
  classical
  exact Finset.univ.filter (fun a => ¬ LinClauseSat a R)

@[simp] theorem mem_parityFalsifiers {V : Type} [Fintype V] (R : ProofComplexity.LinClause V)
    (a : V → Bool) : a ∈ parityFalsifiers R ↔ ¬ LinClauseSat a R := by
  classical
  simp [parityFalsifiers]

/-- At a leaf, one common input clause is violated throughout the intersection
of its path cell with the false region of the repair clause. -/
def LeafFindsViolation {V : Type} [DecidableEq V] (F : Set (ProofComplexity.Clause V))
    (R : ProofComplexity.LinClause V) (t : ParityTree V) : Prop :=
  ∀ b B, (b, B) ∈ t.cells → ∃ C ∈ F, ∀ a, ¬ LinClauseSat a R →
    ¬ LinClauseSat a B → ¬ ClauseSat a C

private theorem search_lower_bounds {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (ProofComplexity.Clause V)) (R : ProofComplexity.LinClause V) (r : ℕ)
    (unsat : ¬ ProofComplexity.Satisfiable F) (hard : ∀ δ, IsLinDerivation (linOfClause '' F) δ →
      R ∈ δ → 3 * r + 2 < δ.length) :
    r < (parityFalsifiers R).card ∧ ∀ t : ParityTree V, LeafFindsViolation F R t → r < t.leaves := by
  classical
  have fails (a : V → Bool) : ∃ C ∈ F, ¬ ClauseSat a C := by
    by_contra! h
    exact unsat ⟨a, h⟩
  obtain ⟨ρ, hd, hm, size⟩ := parity_point_cover F R (parityFalsifiers R)
    (fun a ha => (mem_parityFalsifiers R a).mpr ha) fails [] .nil (by simp)
  have hp := hard ρ (by simpa using hd) (by simpa using hm)
  refine ⟨by omega, ?_⟩
  intro t h
  obtain ⟨δ, d, hR, sz⟩ := repair_from_parity_tree R t h
  have ht := hard δ d hR
  omega

/-- Membership in the counted region is precisely a cancellation witness: both
normalized heads hold and the entire projected result fails. -/
theorem ResolutionSite.mem_falsifiers_iff {V : Type} [Fintype V] [DecidableEq V]
    {π : List (QLine V)} (step : ResolutionSite π) (a : V → Bool) :
    a ∈ parityFalsifiers step.repair ↔
      LinEqSat a (qParity (qPrimitive step.firstHead)) ∧
      LinEqSat a (qParity (qPrimitive step.secondHead)) ∧
      ¬ LinClauseSat a (projectLine (fun e => qParity (qPrimitive e)) step.result) :=
  (mem_parityFalsifiers _ _).trans (step.fails_repair_iff a)

/-- The very same cancellation has many witness assignments and needs many
leaves to locate a violated pigeonhole input by adaptive parity queries. -/
theorem BPHPCancellationSearch {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π) (r : ℕ)
    (short : (3 * (r : ℝ) + 10) * π.length + 1 ≤
      Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ step : ResolutionSite π, PrimitiveRankPair step.firstHead step.secondHead ∧
      r < (parityFalsifiers step.repair).card ∧
      ∀ t : ParityTree _, LeafFindsViolation (BPHP (2 ^ l + 1) l) step.repair t → r < t.leaves := by
  obtain ⟨step, rank, _, hard⟩ := BPHPHardCancellation hl hπ (3 * r + 2) (by
    push_cast
    linarith)
  exact ⟨step, rank, search_lower_bounds _ _ r (L021 _ _ (by omega)) hard⟩

end PEqualNP.Search
