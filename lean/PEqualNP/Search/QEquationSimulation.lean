import PEqualNP.Search.Helpers.LinKCaseProof
import PEqualNP.Search.Helpers.QLinKSimulation
import PEqualNP.Search.Helpers.QParityCode
import PEqualNP.Search.Helpers.ResLinQ

/-! Compile integer equations separately. The disjunction may contain arbitrarily
many equations: resolving its two heads never requires case analysis on the tails. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- An upper bound on the number of Res(k,⊕) lines added for one integer inference. -/
def equationStepCost (k : ℕ) : ℕ := (4*(k+1) + 2*2^k + 2) * 2^k

theorem equation_tree_step_compilation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π) (trees : QEq V → ParityTree V)
    (lit : ∀ t : V × Bool, treeDNF (trees (litQEq t)) = {({({t.1}, t.2)} : LinTerm V)})
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, (trees e).eval a ≠ true)
    (bounds : ∀ L ∈ π, ∀ e ∈ L, (trees e).leaves ≤ 2^k ∧
      ∀ B, (true,B) ∈ (trees e).cells → B.card ≤ k)
    (valid : ∀ (front tail : List (QLine V)) (e f : QEq V) (C D : QLine V) (α β : ℤ),
      let g : QEq V := (α • e.1 + β • f.1, α * e.2 + β * f.2)
      π = front ++ ((g :: (C ++ D)) :: tail) → (e :: C) ∈ tail → (f :: D) ∈ tail →
      ∀ a, (trees e).eval a = true → (trees f).eval a = true → (trees g).eval a = true) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let code (e : QEq V) := treeDNF (trees e)
  have width : ∀ L ∈ π, ∀ e ∈ L, ∀ T ∈ code e, T.card ≤ k := by
    intro L hm e he T hT
    obtain ⟨⟨b,P⟩, h, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hT)
    obtain ⟨hcell, hb⟩ := List.mem_filter.mp h
    change b = true at hb
    subst b
    exact Finset.card_image_le.trans ((bounds L hm e he).2 P hcell)
  have posCost : 0 < equationStepCost k := by unfold equationStepCost; positivity
  apply linK_refutation_of_dead code hk lit
    (fun e hz hn a h => dead e hz hn a ((treeDNF_sat _ _).mp h)) width seed ref posCost
  intro front tail e f C D α β R pos left right ρ hd hA hB
  let g : QEq V := (α • e.1 + β • f.1, α * e.2 + β * f.2)
  have inTail (K : QLine V) (hK : K ∈ tail) : K ∈ π :=
    pos ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hK)
  have hR : R ∈ π := pos ▸ List.mem_append_right _ List.mem_cons_self
  have he := bounds _ (inTail _ left) e List.mem_cons_self
  have hg := bounds R hR g List.mem_cons_self
  have semantic (a) (ha : LinKLineSat a (code e)) (hb : LinKLineSat a (code f)) :
      LinKLineSat a (code g) :=
    (treeDNF_sat _ _).mpr (valid front tail e f C D α β pos left right a
      ((treeDNF_sat _ _).mp ha) ((treeDNF_sat _ _).mp hb))
  have bound : ∀ T ∈ projectKLine code R, T.card ≤ k := by
    intro T hm
    obtain ⟨u, hu, hT⟩ := mem_projectKLine.mp hm
    exact width _ hR u hu T hT
  have same : projectKLine code R = code g ∪ (projectKLine code C ∪ projectKLine code D) := by
    simp [R, g]
  rw [same] at bound ⊢
  obtain ⟨σ, der, hm, len⟩ := linK_two_head_step hk (code e) (code f) (code g)
    (projectKLine code C) (projectKLine code D) (trees e) (trees g)
    (treeDNF_sat _) (treeDNF_sat _) (treeDNF_true_cell _) hg.2 semantic bound hd hA hB
  have firstBound : 4*(k+1) + 2*(trees e).leaves + 2 ≤ 4*(k+1) + 2*2^k + 2 := by
    have := he.1
    omega
  exact ⟨σ, der, hm, len.trans (Nat.mul_le_mul firstBound hg.1)⟩

/-- Exact decision trees for each occurring equation preserve every integer
combination and therefore give the required local implications. -/
theorem equation_tree_compilation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π) (trees : QEq V → ParityTree V)
    (lit : ∀ t : V × Bool, treeDNF (trees (litQEq t)) = {({({t.1}, t.2)} : LinTerm V)})
    (dead : ∀ e : QEq V, e.1 = 0 → e.2 ≠ 0 → ∀ a, (trees e).eval a ≠ true)
    (good : ∀ L ∈ π, ∀ e ∈ L, (∀ a, (trees e).eval a = true ↔ QEq.Holds a e) ∧
      (trees e).leaves ≤ 2^k ∧ ∀ B, (true,B) ∈ (trees e).cells → B.card ≤ k) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  apply equation_tree_step_compilation k hk seed ref trees lit dead
    (fun L hL e he => (good L hL e he).2)
  intro front tail e f C D α β g pos left right a he hf
  have inTail (K : QLine V) (hK : K ∈ tail) : K ∈ π :=
    pos ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hK)
  have here : g :: (C ++ D) ∈ π := pos ▸ List.mem_append_right _ List.mem_cons_self
  exact ((good _ here g List.mem_cons_self).1 a).mpr (combo_holds a e f α β
    (((good _ (inTail _ left) e List.mem_cons_self).1 a).mp he)
    (((good _ (inTail _ right) f List.mem_cons_self).1 a).mp hf))

/-- Each equation can have its own list of parity queries. Only the number of
queries for a single equation enters the simulation cost. -/
theorem parity_query_equation_simulation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (short : ∀ L ∈ π, ∀ e ∈ L, ∃ Q : List (Finset V), Q.length ≤ k ∧ QDetermined Q e) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  classical
  let usable (e : QEq V) (Q : List (Finset V)) := Q.length ≤ k ∧ QDetermined Q e
  let qs (e : QEq V) := if h : ∃ Q, usable e Q then h.choose else []
  have use (L) (hm : L ∈ π) (e) (he : e ∈ L) : usable e (qs e) := by
    have h := short L hm e he
    unfold qs
    rw [dite_eq_left h]
    exact h.choose_spec
  have dead (e : QEq V) (hz : e.1 = 0) (hn : e.2 ≠ 0) (a : V → Bool)
      (hs : (qCodeTree (qs e) e).eval a = true) : False := by
    have h := (treeDNF_sat _ _).mpr hs
    change LinKLineSat a (qCode (qs e) e) at h
    simpa [qCode_dead _ e hz hn, LinKLineSat] using h
  apply equation_tree_compilation k hk seed ref (fun e => qCodeTree (qs e) e)
    (fun t => qCode_lit _ t) dead
  intro L hm e he
  obtain ⟨len, det⟩ := use L hm e he
  exact ⟨fun a => qCodeTree_eval _ e a det, qCodeTree_leaves (qs e) e hk len,
    fun B hb => qCodeTree_cell_width (qs e) e hk len true B hb⟩

/-- Querying the support of each coefficient vector gives the sparse case. -/
theorem sparse_equation_simulation {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) {F : Set (ProofComplexity.Clause V)} (seed : F.Nonempty)
    {π : List (QLine V)} (ref : IsResLinQSynRefutation F π)
    (hs : ∀ L ∈ π, ∀ e ∈ L, (Finset.univ.filter (fun v => e.1 v ≠ 0)).card ≤ k) :
    ∃ ρ, IsLinKRefutation k F ρ ∧ ρ.length ≤ equationStepCost k * π.length + 1 := by
  apply parity_query_equation_simulation k hk seed ref
  intro L hL e he
  exact ⟨supportQueries e, by simpa only [supportQueries_length] using hs L hL e he,
    supportQueries_determine e⟩

end PEqualNP.Search
