import PEqualNP.Search.Helpers.ParityTree
import PEqualNP.Search.Helpers.ParityCaseSplit

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- A derivation containing the available clauses can be extended to contain the
goal using at most the given number of new lines. -/
def CanAdd {V : Type} [DecidableEq V] (F Γ : Set (LinClause V)) (G : LinClause V)
    (m : ℕ) : Prop :=
  ∀ ρ : List (LinClause V), IsLinDerivation F ρ → (∀ C ∈ Γ, C ∈ ρ) →
    ∃ σ : List (LinClause V), IsLinDerivation F (σ ++ ρ) ∧ G ∈ σ ++ ρ ∧ σ.length ≤ m

theorem CanAdd.of_imp {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)}
    {C G : LinClause V} (hC : C ∈ Γ) (h : ∀ a, LinClauseSat a C → LinClauseSat a G) :
    CanAdd F Γ G 1 := by
  intro ρ hd hav
  exact ⟨[G], hd.weak (hav C hC) h, List.mem_cons_self, Nat.le_refl 1⟩

theorem CanAdd.of_tautology {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)}
    {G : LinClause V} (hΓ : Γ.Nonempty) (h : ∀ a, LinClauseSat a G) : CanAdd F Γ G 1 := by
  obtain ⟨C, hC⟩ := hΓ
  exact CanAdd.of_imp hC (fun a _ => h a)

private theorem split_tree_at {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)}
    (t : ParityTree V) (G : LinClause V) (m : ℕ)
    (h : ∀ b C, (b, C) ∈ t.cellsAt G → CanAdd F Γ C m) :
    CanAdd F Γ G (t.leaves * (m + 1) - 1) := by
  induction t generalizing G with
  | leaf b =>
    simpa [ParityTree.leaves] using h b G List.mem_cons_self
  | node f lo hi ihLo ihHi =>
    let L : LinClause V := insert (f, true) G
    let H : LinClause V := insert (f, false) G
    have low := ihLo L (fun b C hm => h b C (List.mem_append_left _ hm))
    have high := ihHi H (fun b C hm => h b C (List.mem_append_right _ hm))
    intro ρ hd hav
    obtain ⟨σ, hdL, hL, hσ⟩ := low ρ hd hav
    obtain ⟨τ, hdH, hH, hτ⟩ :=
      high (σ ++ ρ) hdL (fun C hC => List.mem_append_right _ (hav C hC))
    have hG := hdH.res hH (List.mem_append_right τ hL) (resolve_siblings G f)
    refine ⟨G :: (τ ++ σ), by simpa [List.append_assoc] using hG, List.mem_cons_self, ?_⟩
    have hlo : 0 < lo.leaves * (m + 1) := Nat.mul_pos lo.leaves_pos (Nat.succ_pos _)
    have hhi : 0 < hi.leaves * (m + 1) := Nat.mul_pos hi.leaves_pos (Nat.succ_pos _)
    simp only [List.length_cons, List.length_append, ParityTree.leaves, Nat.add_mul]
    omega

/-- A binary decision tree combines its leaf derivations using one resolution
at each internal node. The same initial clauses remain available at every leaf. -/
theorem split_tree {V : Type} [DecidableEq V] {F Γ : Set (LinClause V)} (t : ParityTree V)
    (G : LinClause V) (m : ℕ) (h : ∀ b C, (b, C) ∈ t.cells → CanAdd F Γ (G ∪ C) m) :
    CanAdd F Γ G (t.leaves * (m + 1) - 1) := by
  apply split_tree_at t G m
  intro b C hc
  rw [ParityTree.cellsAt_eq_map] at hc
  obtain ⟨⟨b', C'⟩, hm, heq⟩ := List.mem_map.mp hc
  cases heq
  exact h b' C' hm

end PEqualNP.Search.Helpers
