import PEqualNP.Defs.SearchQSyn
import PEqualNP.Search.Helpers.ParitySemanticStep

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- Project a disjunction equation by equation, retaining the disjunctive semantics. -/
noncomputable def projectLine (φ : QEq V → LinEq V) (K : QLine V) : LinClause V := by
  classical
  exact K.toFinset.image φ

theorem projectLine_sat (φ : QEq V → LinEq V) (a : V → Bool) (K : QLine V) :
    LinClauseSat a (projectLine φ K) ↔ ∃ e ∈ K, LinEqSat a (φ e) := by
  classical
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨e, List.mem_toFinset.mp he, hs⟩
  · rintro ⟨e, he, hs⟩
    exact ⟨_, Finset.mem_image.mpr ⟨e, List.mem_toFinset.mpr he, rfl⟩, hs⟩

/-- A result occurrence with both premises in its earlier suffix. At the
witness assignment both selected heads hold after projection and the whole
result fails, including every equation in either premise's residual context. -/
def BadProjectedResolution (φ : QEq V → LinEq V) (π : List (QLine V)) : Prop :=
  ∃ (front tail : List (QLine V)) (e e' : QEq V) (C D : QLine V) (α β : ℤ),
    let R : QLine V := (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)
    π = front ++ (R :: tail) ∧ (e :: C) ∈ tail ∧ (e' :: D) ∈ tail ∧
      ∃ a : V → Bool, LinEqSat a (φ e) ∧ LinEqSat a (φ e') ∧ ¬LinClauseSat a (projectLine φ R)

/-- Simulate one binary inference at its actual position by extending any parity
trace containing the projected premises. -/
def ProjectedSteps (φ : QEq V → LinEq V) (F : Set (Clause V)) (π : List (QLine V))
    (k : ℕ) : Prop :=
  ∀ (front tail : List (QLine V)) (e e' : QEq V) (C D : QLine V) (α β : ℤ),
    let R : QLine V := (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)
    π = front ++ (R :: tail) → (e :: C) ∈ tail → (e' :: D) ∈ tail →
    ∀ ρ, IsLinDerivation (linOfClause '' F) ρ →
      projectLine φ (e :: C) ∈ ρ → projectLine φ (e' :: D) ∈ ρ →
      ∃ σ : List (LinClause V), IsLinDerivation (linOfClause '' F) (σ ++ ρ) ∧
        projectLine φ R ∈ σ ∧ σ.length ≤ k

private theorem ProjectedSteps.tail {φ : QEq V → LinEq V} {F : Set (Clause V)}
    {K : QLine V} {π : List (QLine V)} {k : ℕ} (step : ProjectedSteps φ F (K :: π) k) :
    ProjectedSteps φ F π k := by
  intro front tail e e' C D α β R eq
  exact step (K :: front) tail e e' C D α β (congrArg (List.cons K) eq)

theorem projected_head_or_target (φ : QEq V → LinEq V) (e : QEq V) {C R : QLine V}
    (ctx : ∀ u ∈ C, u ∈ R) (a : V → Bool) (sat : LinClauseSat a (projectLine φ (e :: C))) :
    LinClauseSat a (projectLine φ R) ∨ LinEqSat a (φ e) := by
  obtain ⟨u, hu, hs⟩ := (projectLine_sat ..).mp sat
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inr hs
  · exact Or.inl ((projectLine_sat ..).mpr ⟨u, ctx u hu, hs⟩)

private def Projects (φ : QEq V → LinEq V) (F : Set (Clause V)) (π : List (QLine V)) (k : ℕ) : Prop :=
  ∃ ρ, IsLinDerivation (linOfClause '' F) ρ ∧ (∀ K ∈ π, projectLine φ K ∈ ρ) ∧
    ρ ≠ [] ∧ ρ.length ≤ k * π.length + 1

private theorem add_projected {φ : QEq V → LinEq V} {F : Set (Clause V)} {π : List (QLine V)}
    {K : QLine V} {ρ σ : List (LinClause V)} {k : ℕ}
    (prev : ∀ L ∈ π, projectLine φ L ∈ ρ) (cost : ρ.length ≤ k * π.length + 1)
    (d : IsLinDerivation (linOfClause '' F) (σ ++ ρ)) (mem : projectLine φ K ∈ σ)
    (bound : σ.length ≤ k) : Projects φ F (K :: π) k := by
  refine ⟨σ ++ ρ, d, ?_, List.ne_nil_of_mem (List.mem_append_left _ mem), ?_⟩
  · intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact List.mem_append_left _ mem
    · exact List.mem_append_right _ (prev L hL)
  · simp only [List.length_cons, List.length_append, Nat.mul_succ]
    omega

variable [Fintype V]

private theorem project_trace (φ : QEq V → LinEq V)
    (lit : ∀ t : V × Bool, φ (litQEq t) = ({t.1}, t.2))
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinEqSat a (φ e))
    {F : Set (Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (d : IsResLinQSynDerivation F π) {k : ℕ} (hk : 1 ≤ k)
    (step : ProjectedSteps φ F π k) : Projects φ F π k := by
  classical
  induction d with
  | nil =>
    obtain ⟨C, hC⟩ := seed
    exact ⟨[linOfClause C], .ax .nil ⟨C, hC, rfl⟩, by simp, by simp, by simp⟩
  | @ax π K C _ hC hK ih =>
    obtain ⟨ρ, hd, prev, _, len⟩ := ih step.tail
    have eq : projectLine φ K = linOfClause C := by
      ext q
      simp only [projectLine, linOfClause, Finset.mem_image, List.mem_toFinset]
      constructor
      · rintro ⟨e, he, rfl⟩
        obtain ⟨t, ht, rfl⟩ := (hK _).mp he
        exact ⟨t, ht, (lit t).symm⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, (hK _).mpr ⟨t, ht, rfl⟩, lit t⟩
    exact add_projected (σ := [projectLine φ K]) prev len (.ax hd ⟨C, hC, eq.symm⟩)
      List.mem_cons_self hk
  | bool v _ ih =>
    obtain ⟨ρ, hd, prev, ne, len⟩ := ih step.tail
    obtain ⟨P, hP⟩ := List.exists_mem_of_ne_nil _ ne
    apply add_projected (σ := [projectLine φ [litQEq (v,false), litQEq (v,true)]]) prev len
      (.weak hd hP ?_) List.mem_cons_self hk
    intro a _
    apply (projectLine_sat ..).mpr
    cases hv : a v with
    | false => exact ⟨litQEq (v,false), by simp, by simp [lit, LinEqSat, Finset.filter_singleton, hv]⟩
    | true => exact ⟨litQEq (v,true), by simp, by simp [lit, LinEqSat, Finset.filter_singleton, hv]⟩
  | @res π e e' C D α β _ hC hD ih =>
    obtain ⟨ρ, hd, prev, _, len⟩ := ih step.tail
    obtain ⟨σ, ds, mem, bound⟩ := step [] π e e' C D α β rfl hC hD ρ hd (prev _ hC) (prev _ hD)
    exact add_projected prev len ds mem bound
  | @weaken π C D _ hm sub ih =>
    obtain ⟨ρ, hd, prev, _, len⟩ := ih step.tail
    apply add_projected (σ := [projectLine φ D]) prev len
      (.weak hd (prev _ hm) ?_) List.mem_cons_self hk
    intro a h
    obtain ⟨e, he, hs⟩ := (projectLine_sat ..).mp h
    exact (projectLine_sat ..).mpr ⟨e, sub e he, hs⟩
  | @simp π C _ hm ih =>
    obtain ⟨ρ, hd, prev, _, len⟩ := ih step.tail
    apply add_projected (σ := [projectLine φ _]) prev len
      (.weak hd (prev _ hm) ?_) List.mem_cons_self hk
    intro a h
    obtain ⟨e, he, hs⟩ := (projectLine_sat ..).mp h
    have keep : ¬ (e.1 = 0 ∧ e.2 ≠ 0) := fun ⟨z, nz⟩ => dead e z nz a hs
    exact (projectLine_sat ..).mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true keep⟩, hs⟩

/-- All other rules project in one line once each binary step has a bounded
simulation. An initial axiom supplies a premise for Boolean tautologies. -/
theorem projected_refutation_of_steps (φ : QEq V → LinEq V)
    (lit : ∀ t : V × Bool, φ (litQEq t) = ({t.1}, t.2))
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinEqSat a (φ e))
    {F : Set (Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π) {k : ℕ} (hk : 1 ≤ k) (steps : ProjectedSteps φ F π k) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ k * π.length + 1 := by
  obtain ⟨ρ, d, prev, _, cost⟩ := project_trace φ lit dead seed ref.1 hk steps
  exact ⟨ρ, ⟨d, by simpa [projectLine] using prev [] ref.2⟩, cost⟩

/-- A literal-preserving map that sends false constants to contradictions projects
any refutation to a short parity refutation unless a resolution occurrence fails
on a Boolean assignment. -/
theorem projected_refutation_of_safe (φ : QEq V → LinEq V)
    (lit : ∀ t : V × Bool, φ (litQEq t) = ({t.1}, t.2))
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinEqSat a (φ e))
    {F : Set (Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π) (safe : ¬ BadProjectedResolution φ π) :
    ∃ ρ, IsLinRefutation F ρ ∧ ρ.length ≤ 4 * π.length + 1 := by
  apply projected_refutation_of_steps φ lit dead seed ref (by decide : 1 ≤ 4)
  intro front tail e e' C D α β R eq hC hD ρ d hA hB
  apply paritySemanticStep d hA hB
  intro a sa sb
  by_contra no
  have left := projected_head_or_target (R := R) φ e (fun u hu => List.mem_cons_of_mem _
    (List.mem_append_left D hu)) a sa
  have right := projected_head_or_target (R := R) φ e' (fun u hu => List.mem_cons_of_mem _
    (List.mem_append_right C hu)) a sb
  exact safe ⟨front, tail, e, e', C, D, α, β, eq, hC, hD, a, left.resolve_left no,
    right.resolve_left no, no⟩

end PEqualNP.Search.Helpers
