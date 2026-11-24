import PEqualNP.Defs.SearchQSyn
import PEqualNP.Defs.ProofComplexityLinK
import Mathlib.Tactic

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The disjunction of the codes for the equations of a line. -/
def projectKLine (code : QEq V → LinKLine V) : QLine V → LinKLine V
  | [] => ∅
  | e :: L => code e ∪ projectKLine code L

@[simp] theorem projectKLine_nil (code : QEq V → LinKLine V) : projectKLine code [] = ∅ := rfl

@[simp] theorem projectKLine_cons (code : QEq V → LinKLine V) (e : QEq V) (C : QLine V) :
    projectKLine code (e :: C) = code e ∪ projectKLine code C := rfl

@[simp] theorem projectKLine_append (code : QEq V → LinKLine V) (C D : QLine V) :
    projectKLine code (C ++ D) = projectKLine code C ∪ projectKLine code D := by
  induction C with
  | nil => simp
  | cons e C ih => simp [ih, Finset.union_assoc]

theorem mem_projectKLine {code : QEq V → LinKLine V} {L : QLine V} {T : LinTerm V} :
    T ∈ projectKLine code L ↔ ∃ e ∈ L, T ∈ code e := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [projectKLine_cons, Finset.mem_union, ih, List.mem_cons]
    grind

/-- Simulations are required only at occurrences with both premises in the
earlier suffix of the trace. The bound includes every intermediate line. -/
def LinKProjectedSteps (code : QEq V → LinKLine V) (k : ℕ) (F : Set (Clause V))
    (π : List (QLine V)) (M : ℕ) : Prop :=
  ∀ (front tail : List (QLine V)) (e e' : QEq V) (C D : QLine V) (α β : ℤ),
    let R : QLine V := (α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)
    π = front ++ (R :: tail) → (e :: C) ∈ tail → (e' :: D) ∈ tail →
    ∀ ρ, IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) ρ →
      projectKLine code (e :: C) ∈ ρ → projectKLine code (e' :: D) ∈ ρ →
      ∃ σ : List (LinKLine V), IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) (σ ++ ρ) ∧
        projectKLine code R ∈ σ ∧ σ.length ≤ M

private theorem LinKProjectedSteps.tail {code : QEq V → LinKLine V} {k M : ℕ}
    {F : Set (Clause V)} {K : QLine V} {π : List (QLine V)}
    (step : LinKProjectedSteps code k F (K :: π) M) : LinKProjectedSteps code k F π M := by
  intro front tail e e' C D α β R eq
  exact step (K :: front) tail e e' C D α β (congrArg (List.cons K) eq)

private def KProjects (code : QEq V → LinKLine V) (k : ℕ) (F : Set (Clause V))
    (π : List (QLine V)) (M : ℕ) : Prop :=
  ∃ ρ, IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) ρ ∧
    (∀ L ∈ π, projectKLine code L ∈ ρ) ∧ ρ ≠ [] ∧ ρ.length ≤ M * π.length + 1

private theorem prepend_block {code : QEq V → LinKLine V} {k M : ℕ} {F : Set (Clause V)}
    {π : List (QLine V)} {L : QLine V} {σ ρ : List (LinKLine V)}
    (prev : ∀ K ∈ π, projectKLine code K ∈ ρ) (len : ρ.length ≤ M * π.length + 1)
    (der : IsLinKDerivation k IsLinKWeakening (linKOfClause '' F) (σ ++ ρ))
    (mem : projectKLine code L ∈ σ) (bound : σ.length ≤ M) : KProjects code k F (L :: π) M := by
  refine ⟨σ ++ ρ, der, ?_, List.ne_nil_of_mem (List.mem_append_left _ mem), ?_⟩
  · intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact List.mem_append_left _ mem
    · exact List.mem_append_right _ (prev K hK)
  · simp only [List.length_append, List.length_cons, Nat.mul_succ]
    omega

variable [Fintype V]

private theorem compile_k_trace (code : QEq V → LinKLine V) {k M : ℕ} (hk : 1 ≤ k)
    (lit : ∀ t : V × Bool, code (litQEq t) = {({({t.1}, t.2)} : LinTerm V)})
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinKLineSat a (code e))
    {F : Set (Clause V)} (seed : F.Nonempty) {π : List (QLine V)}
    (d : IsResLinQSynDerivation F π) (hM : 1 ≤ M)
    (width : ∀ L ∈ π, ∀ T ∈ projectKLine code L, T.card ≤ k)
    (step : LinKProjectedSteps code k F π M) : KProjects code k F π M := by
  induction d with
  | nil =>
    obtain ⟨C, hC⟩ := seed
    have card : ∀ T ∈ linKOfClause C, T.card ≤ k := by
      rintro T hT
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hT
      simpa using hk
    exact ⟨[linKOfClause C], .ax .nil ⟨C, hC, rfl⟩ card, by simp, by simp, by simp⟩
  | @ax π L C _ hC rep ih =>
    obtain ⟨ρ, der, prev, _, len⟩ := ih (fun K h => width K (.tail _ h)) step.tail
    have eq : projectKLine code L = linKOfClause C := by
      ext T
      constructor
      · intro hT
        obtain ⟨e, he, ht⟩ := mem_projectKLine.mp hT
        obtain ⟨l, hl, rfl⟩ := (rep _).mp he
        rw [lit, Finset.mem_singleton] at ht
        subst T
        exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨l, hl, rfl⟩, rfl⟩
      · intro hT
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
        exact mem_projectKLine.mpr ⟨litQEq l, (rep _).mpr ⟨l, hl, rfl⟩, by simp [lit]⟩
    exact prepend_block (σ := [projectKLine code L]) prev len
      (.ax der ⟨C, hC, eq.symm⟩ (width _ List.mem_cons_self)) List.mem_cons_self hM
  | bool v _ ih =>
    obtain ⟨ρ, der, prev, ne, len⟩ := ih (fun K h => width K (.tail _ h)) step.tail
    obtain ⟨A, hA⟩ := List.exists_mem_of_ne_nil _ ne
    let L := [litQEq (v,false), litQEq (v,true)]
    apply prepend_block (σ := [projectKLine code L]) prev len
      (.weak der hA ?_ (width _ List.mem_cons_self)) List.mem_cons_self hM
    intro T _
    right
    intro a _
    refine ⟨({v}, a v), ?_, ?_⟩
    · apply mem_projectKLine.mpr
      exact ⟨litQEq (v,a v), by cases hv : a v <;> simp [L], by simp [lit]⟩
    · cases hv : a v <;> simp [LinEqSat, Finset.filter_singleton, hv]
  | @res π e f C D α β _ hC hD ih =>
    obtain ⟨ρ, der, prev, _, len⟩ := ih (fun K h => width K (.tail _ h)) step.tail
    obtain ⟨σ, ds, mem, bound⟩ := step [] π e f C D α β rfl hC hD ρ der (prev _ hC) (prev _ hD)
    exact prepend_block prev len ds mem bound
  | @weaken π C D _ hC sub ih =>
    obtain ⟨ρ, der, prev, _, len⟩ := ih (fun K h => width K (.tail _ h)) step.tail
    apply prepend_block (σ := [projectKLine code D]) prev len
      (.weak der (prev _ hC) ?_ (width _ List.mem_cons_self)) List.mem_cons_self hM
    intro T hT
    obtain ⟨e, he, hm⟩ := mem_projectKLine.mp hT
    exact Or.inl ⟨T, mem_projectKLine.mpr ⟨e, sub _ he, hm⟩, fun _ h => h⟩
  | @simp π C _ hC ih =>
    obtain ⟨ρ, der, prev, _, len⟩ := ih (fun K h => width K (.tail _ h)) step.tail
    apply prepend_block (σ := [projectKLine code _]) prev len
      (.weak der (prev _ hC) ?_ (width _ List.mem_cons_self)) List.mem_cons_self hM
    intro T hT
    obtain ⟨e, he, hm⟩ := mem_projectKLine.mp hT
    by_cases bad : e.1 = 0 ∧ e.2 ≠ 0
    · right
      intro a ha
      exact (dead e bad.1 bad.2 a ⟨T, hm, ha⟩).elim
    · exact Or.inl ⟨T, mem_projectKLine.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true bad⟩, hm⟩,
        fun _ h => h⟩

/-- Codes of width at most `k` give a bounded Res(k,⊕) refutation when each
binary inference has a local simulation of at most `M` lines. Simplification
uses termwise weakening because a term encoding a false constant is unsatisfiable. -/
theorem linK_refutation_of_dead (code : QEq V → LinKLine V) {k M : ℕ} (hk : 1 ≤ k)
    (lit : ∀ t : V × Bool, code (litQEq t) = {({({t.1}, t.2)} : LinTerm V)})
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, ¬ LinKLineSat a (code e))
    {F : Set (Clause V)} {π : List (QLine V)}
    (width : ∀ L ∈ π, ∀ e ∈ L, ∀ T ∈ code e, T.card ≤ k)
    (seed : F.Nonempty) (ref : IsResLinQSynRefutation F π) (hM : 1 ≤ M)
    (steps : LinKProjectedSteps code k F π M) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ M * π.length + 1 := by
  obtain ⟨ρ, der, prev, _, len⟩ := compile_k_trace code hk lit dead seed ref.1 hM
    (fun L hL T hT => by
      obtain ⟨e, he, hm⟩ := mem_projectKLine.mp hT
      exact width L hL e he T hm) steps
  exact ⟨ρ, ⟨der, by simpa using prev [] ref.2⟩, len⟩

/-- Exact Boolean representations in particular encode every false constant by an unsatisfiable line. -/
theorem linK_refutation_of_steps (code : QEq V → LinKLine V) {k M : ℕ} (hk : 1 ≤ k)
    (lit : ∀ t : V × Bool, code (litQEq t) = {({({t.1}, t.2)} : LinTerm V)})
    (truth : ∀ e a, LinKLineSat a (code e) ↔ QEq.Holds a e)
    {F : Set (Clause V)} {π : List (QLine V)}
    (width : ∀ L ∈ π, ∀ e ∈ L, ∀ T ∈ code e, T.card ≤ k)
    (seed : F.Nonempty) (ref : IsResLinQSynRefutation F π) (hM : 1 ≤ M)
    (steps : LinKProjectedSteps code k F π M) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ M * π.length + 1 := by
  apply linK_refutation_of_dead code hk lit _ width seed ref hM steps
  intro e hz hn a hs
  have sat := (truth e a).mp hs
  exact hn (by simpa [QEq.Holds, hz] using sat.symm)

end PEqualNP.Search.Helpers
