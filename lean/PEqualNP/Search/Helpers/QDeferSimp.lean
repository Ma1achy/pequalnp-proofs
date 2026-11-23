import PEqualNP.Defs.SearchQSyn
import PEqualNP.Search.Helpers.QPaddingCost

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A syntactic integer-resolution trace using only inputs, Boolean axioms,
linear combinations and syntactic weakening. -/
inductive NoSimpDerivation (F : Set (Clause V)) : List (QLine V) → Prop
  | nil : NoSimpDerivation F []
  | ax {π : List (QLine V)} {L : QLine V} (C : Clause V) :
      NoSimpDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) →
      NoSimpDerivation F (L :: π)
  | bool {π : List (QLine V)} (v : V) :
      NoSimpDerivation F π →
      NoSimpDerivation F ([litQEq (v, false), litQEq (v, true)] :: π)
  | res {π : List (QLine V)} {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      NoSimpDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π →
      NoSimpDerivation F (((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) :: π)
  | weaken {π : List (QLine V)} {C D : QLine V} :
      NoSimpDerivation F π → C ∈ π → (∀ e ∈ C, e ∈ D) → NoSimpDerivation F (D :: π)

theorem NoSimpDerivation.toSyn {F : Set (Clause V)} {ρ : List (QLine V)}
    (h : NoSimpDerivation F ρ) : IsResLinQSynDerivation F ρ := by
  induction h with
  | nil => exact .nil
  | ax C _ hC rep ih => exact .ax C ih hC rep
  | bool v _ ih => exact .bool v ih
  | res α β _ hC hD ih => exact .res α β ih hC hD
  | weaken _ hC sub ih => exact .weaken ih hC sub

private def Padded (F : Set (Clause V)) (π : List (QLine V)) (G : QLine V) (cap : ℕ) : Prop :=
  ∃ ρ, NoSimpDerivation F ρ ∧ (∀ L ∈ π, L ++ G ∈ ρ) ∧ ρ.length ≤ 2 * π.length ∧
    ∀ L ∈ ρ, qCost L ≤ cap

private theorem add_padded {F : Set (Clause V)} {π : List (QLine V)} {G T : QLine V} {cap : ℕ}
    (prev : Padded F π G cap)
    (step : ∀ ρ, NoSimpDerivation F ρ → (∀ L ∈ π, L ++ G ∈ ρ) →
      ∃ s : List (QLine V), NoSimpDerivation F (s ++ ρ) ∧ T ++ G ∈ s ∧
        s.length ≤ 2 ∧ ∀ L ∈ s, qCost L ≤ cap) : Padded F (T :: π) G cap := by
  obtain ⟨ρ, d, rep, len, size⟩ := prev
  obtain ⟨s, ds, mem, lens, sizes⟩ := step ρ d rep
  refine ⟨s ++ ρ, ds, ?_, ?_, ?_⟩
  · intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact List.mem_append_left _ mem
    · exact List.mem_append_right _ (rep L hL)
  · simp only [List.length_append, List.length_cons]
    omega
  · intro L hL
    exact (List.mem_append.mp hL).elim (sizes L) (size L)

private theorem pad_input {F : Set (Clause V)} {ρ : List (QLine V)} {T G : QLine V} {M : ℕ}
    (d : NoSimpDerivation F (T :: ρ)) (size : qCost T ≤ M) :
    ∃ s : List (QLine V), NoSimpDerivation F (s ++ ρ) ∧ T ++ G ∈ s ∧
      s.length ≤ 2 ∧ ∀ L ∈ s, qCost L ≤ M + 2 * qWeight G := by
  refine ⟨[T ++ G, T], .weaken d List.mem_cons_self (fun _ he => List.mem_append_left _ he),
    List.mem_cons_self, by simp, ?_⟩
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · rw [qCost_append]
    omega
  · omega

private theorem pad_single {F : Set (Clause V)} {ρ : List (QLine V)} {T G : QLine V} {M : ℕ}
    (d : NoSimpDerivation F ((T ++ G) :: ρ)) (size : qCost T ≤ M) :
    ∃ s : List (QLine V), NoSimpDerivation F (s ++ ρ) ∧ T ++ G ∈ s ∧
      s.length ≤ 2 ∧ ∀ L ∈ s, qCost L ≤ M + 2 * qWeight G := by
  refine ⟨[T ++ G], d, List.mem_cons_self, by simp, ?_⟩
  intro L hL
  obtain rfl := List.mem_singleton.mp hL
  rw [qCost_append]
  omega

private theorem pad_derivation {F : Set (Clause V)} {π : List (QLine V)} (G : QLine V)
    (M : ℕ) (h : IsResLinQSynDerivation F π) (cost : ∀ L ∈ π, qCost L ≤ M)
    (covered : ∀ L ∈ π, ∀ e ∈ L, e.1 = 0 ∧ e.2 ≠ 0 → e ∈ G) :
    Padded F π G (M + 2 * qWeight G) := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp, by simp⟩
  | ax C _ hC hrep ih =>
    apply add_padded (ih (fun L hm => cost L (.tail _ hm)) (fun L hm => covered L (.tail _ hm)))
    intro ρ d _
    exact pad_input (.ax C d hC hrep) (cost _ List.mem_cons_self)
  | bool v _ ih =>
    apply add_padded (ih (fun L hm => cost L (.tail _ hm)) (fun L hm => covered L (.tail _ hm)))
    intro ρ d _
    exact pad_input (.bool v d) (cost _ List.mem_cons_self)
  | @res π e e' C D α β _ hC hD ih =>
    apply add_padded (ih (fun L hm => cost L (.tail _ hm)) (fun L hm => covered L (.tail _ hm)))
    intro ρ d rep
    let u : QEq V := (α • e.1 + β • e'.1, α * e.2 + β * e'.2)
    let T := u :: (C ++ D)
    let S := u :: ((C ++ G) ++ (D ++ G))
    have hc : e :: (C ++ G) ∈ ρ := rep _ hC
    have hd : e' :: (D ++ G) ∈ ρ := rep _ hD
    have raw : NoSimpDerivation F (S :: ρ) := .res α β d hc hd
    have sub : ∀ x ∈ S, x ∈ T ++ G := by
      simp only [S, T, List.mem_cons, List.mem_append]
      tauto
    refine ⟨[T ++ G, S], .weaken raw List.mem_cons_self sub, List.mem_cons_self, by simp, ?_⟩
    intro L hL
    have hT : qCost T ≤ M := cost _ List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · rw [qCost_append]
      omega
    · change qCost (u :: ((C ++ G) ++ (D ++ G))) ≤ _
      rw [qCost_padded_res]
      exact Nat.add_le_add_right hT _
  | weaken _ hC sub ih =>
    apply add_padded (ih (fun L hm => cost L (.tail _ hm)) (fun L hm => covered L (.tail _ hm)))
    intro ρ d rep
    apply pad_single (M := M) _ (cost _ List.mem_cons_self)
    apply NoSimpDerivation.weaken d (rep _ hC)
    intro e he
    exact List.mem_append.mpr ((List.mem_append.mp he).imp (sub e) id)
  | simp _ hC ih =>
    apply add_padded (ih (fun L hm => cost L (.tail _ hm)) (fun L hm => covered L (.tail _ hm)))
    intro ρ d rep
    apply pad_single (M := M) _ (cost _ List.mem_cons_self)
    apply NoSimpDerivation.weaken d (rep _ hC)
    intro e he
    apply List.mem_append.mpr
    rcases List.mem_append.mp he with he | he
    · by_cases bad : e.1 = 0 ∧ e.2 ≠ 0
      · exact Or.inr (covered _ (.tail _ hC) e he bad)
      · exact Or.inl (List.mem_filter.mpr ⟨he, by simp; tauto⟩)
    · exact Or.inr he

/-- Defer every deletion of false constants to the end of the proof. The
remaining line consists of the original proof's false constants, ready for
one final simplification. Each input step contributes at most two lines. -/
theorem defer_simp_refutation {F : Set (Clause V)} {π : List (QLine V)}
    (h : IsResLinQSynRefutation F π) :
    ∃ ρ, NoSimpDerivation F ρ ∧ falseConstants π ∈ ρ ∧ ρ.length ≤ 2 * π.length ∧
      ∀ L ∈ ρ, qCost L ≤ resLinQSize π + 2 * qWeight (falseConstants π) := by
  obtain ⟨ρ, d, rep, len, size⟩ := pad_derivation (falseConstants π) (resLinQSize π) h.1
    (fun _ hm => qCost_le_of_mem hm) (fun L hL e he hb => mem_falseConstants.mpr ⟨⟨L,hL,he⟩, hb⟩)
  exact ⟨ρ, d, by simpa using rep [] h.2, len, size⟩

end PEqualNP.Search.Helpers
