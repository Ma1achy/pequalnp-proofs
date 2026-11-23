import PEqualNP.Defs.SearchQSyn
import PEqualNP.Search.Helpers.QParity
import PEqualNP.Search.Helpers.ParityCut
import PEqualNP.Search.Helpers.QDeferSimp

/-! Reduction modulo two of syntactic integer R(lin). Only simplification
can turn a valid integer inference into an invalid parity inference. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The output of the integer simplification rule. -/
def stripFalseConstants (K : QLine V) : QLine V :=
  K.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))

/-- A visible obstruction to projecting a proof: some Boolean point satisfies the
parity image of a line but falsifies the image after its false constants are erased.
Both lines must occur in the proof. -/
def ParityObstruction (π : List (QLine V)) : Prop :=
  ∃ K ∈ π, stripFalseConstants K ∈ π ∧ ∃ a : V → Bool,
    LinClauseSat a (qLineParity K) ∧ ¬ LinClauseSat a (qLineParity (stripFalseConstants K))

omit [DecidableEq V] in
private theorem projected_sat (a : V → Bool) (K : QLine V) :
    LinClauseSat a (qLineParity K) ↔ ∃ e ∈ K, LinEqSat a (qParity e) := by
  classical
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨e, List.mem_toFinset.mp he, hs⟩
  · rintro ⟨e, he, hs⟩
    exact ⟨_, Finset.mem_image.mpr ⟨e, List.mem_toFinset.mpr he, rfl⟩, hs⟩

omit [DecidableEq V] in
/-- An obstruction requires an actual zero-vector equation with a nonzero even RHS. -/
theorem even_constant_of_parityObstruction {π : List (QLine V)} (h : ParityObstruction π) :
    ∃ K ∈ π, stripFalseConstants K ∈ π ∧
      ∃ e ∈ K, e.1 = 0 ∧ e.2 ≠ 0 ∧ Even e.2 := by
  obtain ⟨K, hK, hS, a, ha, hn⟩ := h
  obtain ⟨e, he, hq⟩ := (projected_sat a K).mp ha
  by_cases hz : e.1 = 0 ∧ e.2 ≠ 0
  · exact ⟨K, hK, hS, e, he, hz.1, hz.2, Int.not_odd_iff_even.mp
      (fun ho => qParity_false a e hz.1 ho hq)⟩
  · exact False.elim (hn ((projected_sat a _).mpr
      ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hz⟩, hq⟩))

private def Simulates (F : Set (Clause V)) (π : List (QLine V)) : Prop :=
  ∃ ρ : List (LinClause V), IsLinDerivation (linOfClause '' F) ρ ∧
    (∀ L ∈ π, qLineParity L ∈ ρ) ∧ ρ ≠ [] ∧ ρ.length ≤ 4 * π.length + 1

private theorem extend_sim {F : Set (Clause V)} {π : List (QLine V)} {L : QLine V}
    {ρ σ : List (LinClause V)}
    (prev : ∀ K ∈ π, qLineParity K ∈ ρ) (len : ρ.length ≤ 4 * π.length + 1)
    (d : IsLinDerivation (linOfClause '' F) (σ ++ ρ)) (hL : qLineParity L ∈ σ)
    (hs : σ.length ≤ 4) : Simulates F (L :: π) := by
  refine ⟨σ ++ ρ, d, ?_, List.ne_nil_of_mem (List.mem_append_left _ hL), ?_⟩
  · intro K hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact List.mem_append_left _ hL
    · exact List.mem_append_right _ (prev K hk)
  · simp only [List.length_append, List.length_cons]
    omega

private theorem simulate_nil {F : Set (Clause V)} (seed : F.Nonempty) : Simulates F [] := by
  classical
  obtain ⟨C, hc⟩ := seed
  exact ⟨[linOfClause C], .ax .nil ⟨C, hc, rfl⟩, by simp, by simp, by simp⟩

private theorem simulate_input {F : Set (Clause V)} {π : List (QLine V)} {L : QLine V} {C : Clause V}
    (ih : Simulates F π) (hCF : C ∈ F) (hL : ∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) :
    Simulates F (L :: π) := by
  classical
  obtain ⟨ρ, dρ, prev, _, len⟩ := ih
  have heq : qLineParity L = linOfClause C := by
    ext q
    simp only [qLineParity, linOfClause, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (hL e).mp he
      exact ⟨t, ht, (qParity_lit t).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, (hL _).mpr ⟨t, ht, rfl⟩, qParity_lit t⟩
  exact extend_sim (σ := [qLineParity L]) prev len
    (.ax dρ ⟨C, hCF, heq.symm⟩) List.mem_cons_self (by simp)

private theorem simulate_bool {F : Set (Clause V)} {π : List (QLine V)} (v : V) (ih : Simulates F π) :
    Simulates F ([litQEq (v, false), litQEq (v, true)] :: π) := by
  classical
  obtain ⟨ρ, dρ, prev, hne, len⟩ := ih
  obtain ⟨B, hB⟩ := List.exists_mem_of_ne_nil ρ hne
  apply extend_sim (σ := [qLineParity [litQEq (v, false), litQEq (v, true)]]) prev len (.weak dρ hB ?_) List.mem_cons_self (by simp)
  intro a _
  apply (projected_sat a _).mpr
  cases hv : a v with
  | false => exact ⟨litQEq (v, false), by simp, by simp [LinEqSat, Finset.filter_singleton, hv]⟩
  | true => exact ⟨litQEq (v, true), by simp, by simp [LinEqSat, Finset.filter_singleton, hv]⟩

private theorem simulate_resolution {F : Set (Clause V)} {π : List (QLine V)} {e f : QEq V} {C D : QLine V}
    (α β : ℤ) (ih : Simulates F π) (hC : (e :: C) ∈ π) (hD : (f :: D) ∈ π) :
    Simulates F (((α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)) :: π) := by
  classical
  obtain ⟨ρ, dρ, prev, _, len⟩ := ih
  let g : QEq V := (α • e.1 + β • f.1, α * e.2 + β * f.2)
  let R := g :: (C ++ D)
  have into_target (a) (t : QEq V) (htR : t ∈ R) (ht : LinEqSat a (qParity t)) :
      LinClauseSat a (qLineParity R) := (projected_sat a _).mpr ⟨t, htR, ht⟩
  apply Exists.elim (parityCut (T := qLineParity R) (qParity f) dρ
    (prev _ hC) (prev _ hD) ?_ ?_)
  · rintro σ ⟨dσ, hm, hs⟩
    exact extend_sim prev len dσ hm hs
  · intro a h
    obtain ⟨t, ht, hs⟩ := (projected_sat a _).mp h
    rcases List.mem_cons.mp ht with rfl | ht
    · by_cases hf : LinEqSat a (qParity f)
      · exact Or.inl (into_target a g List.mem_cons_self (qParity_combo a t f α β hs hf))
      · right
        revert hf
        generalize qParity f = q
        rcases q with ⟨v,b⟩
        cases b <;> simp [LinEqSat]
    · exact Or.inl (into_target a t (List.mem_cons_of_mem _ (List.mem_append_left _ ht)) hs)
  · intro a h
    obtain ⟨t, ht, hs⟩ := (projected_sat a _).mp h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Or.inr hs
    · exact Or.inl (into_target a t (List.mem_cons_of_mem _ (List.mem_append_right _ ht)) hs)

private theorem simulate_weakening {F : Set (Clause V)} {π : List (QLine V)} {C D : QLine V}
    (ih : Simulates F π) (hC : C ∈ π) (sub : ∀ e ∈ C, e ∈ D) : Simulates F (D :: π) := by
  classical
  obtain ⟨ρ, dρ, prev, _, len⟩ := ih
  apply extend_sim (σ := [qLineParity D]) prev len (.weak dρ (prev _ hC) ?_) List.mem_cons_self (by simp)
  intro a h
  obtain ⟨e, he, ha⟩ := (projected_sat a _).mp h
  exact (projected_sat a _).mpr ⟨e, sub _ he, ha⟩

private theorem simulates_of_safe {F : Set (Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (d : IsResLinQSynDerivation F π)
    (safe : ¬ ParityObstruction π) : Simulates F π := by
  classical
  have tailSafe {K : QLine V} {τ : List (QLine V)} (h : ¬ ParityObstruction (K :: τ)) :
      ¬ ParityObstruction τ := by
    rintro ⟨L, hL, hs, hw⟩
    exact h ⟨L, List.mem_cons_of_mem _ hL, List.mem_cons_of_mem _ hs, hw⟩
  induction d with
  | nil => exact simulate_nil seed
  | ax _ _ hC rep ih => exact simulate_input (ih (tailSafe safe)) hC rep
  | bool v _ ih => exact simulate_bool v (ih (tailSafe safe))
  | res α β _ hC hD ih => exact simulate_resolution α β (ih (tailSafe safe)) hC hD
  | weaken _ hC sub ih => exact simulate_weakening (ih (tailSafe safe)) hC sub
  | @simp π C _ hC ih =>
    obtain ⟨ρ, dρ, prev, _, len⟩ := ih (tailSafe safe)
    apply extend_sim (σ := [qLineParity (stripFalseConstants C)]) prev len (.weak dρ (prev _ hC) ?_) List.mem_cons_self (by simp)
    intro a ha
    by_contra hn
    exact safe ⟨_, List.mem_cons_of_mem _ hC, List.mem_cons_self, a, ha, hn⟩

/-- With no parity obstruction, an integer DAG refutation gives a parity DAG
refutation using at most four lines per integer line plus an initial axiom. -/
theorem parity_refutation_of_safe {F : Set (Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) (h : ¬ ParityObstruction π) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ 4 * π.length + 1 := by
  obtain ⟨ρ, dρ, prev, _, len⟩ := simulates_of_safe seed hπ.1 h
  exact ⟨ρ, ⟨dρ, by simpa [qLineParity] using prev [] hπ.2⟩, len⟩

/-- Without simplification the parity projection always simulates the proof,
even when some discarded false-constant lines happen to appear elsewhere in the trace. -/
theorem parity_derivation_no_simp {F : Set (Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (d : NoSimpDerivation F π) :
    ∃ ρ : List (LinClause V), IsLinDerivation (linOfClause '' F) ρ ∧
      (∀ L ∈ π, qLineParity L ∈ ρ) ∧ ρ.length ≤ 4 * π.length + 1 := by
  have simulation : Simulates F π := by
    induction d with
    | nil => exact simulate_nil seed
    | ax _ _ hC rep ih => exact simulate_input ih hC rep
    | bool v _ ih => exact simulate_bool v ih
    | res α β _ hC hD ih => exact simulate_resolution α β ih hC hD
    | weaken _ hC sub ih => exact simulate_weakening ih hC sub
  obtain ⟨ρ, der, prev, _, cost⟩ := simulation
  exact ⟨ρ, der, prev, cost⟩

end PEqualNP.Search.Helpers
