import PEqualNP.Search.Helpers.BPHPTreeRate
import PEqualNP.Search.Helpers.DagBudget
import PEqualNP.Search.Helpers.DagRankCost
import PEqualNP.Search.Helpers.DagRootComponent
import PEqualNP.Search.Helpers.QSynUnfold

/-! Reuse along a single path in dag-like integer resolution for binary pigeonhole. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- Number of positions on a path referenced at least twice in the part of the
proof that derives the designated root. Two uses in one inference count twice. -/
noncomputable def sharedOnPath {n : ℕ} (parents : Fin n → List (Fin n)) (root : Fin n)
    (path : List (Fin n)) : ℕ :=
  (path.filter (fun j => 2 ≤ dagUses (rootParents parents root) j)).length

private theorem cost_on_one_path {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (arity : ∀ i, (parents i).length ≤ 2)
    (cost : Fin n → ℕ) (c : ℕ) (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum)
    (root : Fin n) :
    ∃ path : List (Fin n), path.head? = some root ∧ path.IsChain (fun i j => j ∈ parents i) ∧
      cost root ≤ c * n * (2*n+1) ^ sharedOnPath parents root path := by
  classical
  let deps := rootParents parents root
  let live := dagReachable deps (· = root)
  let rank := dagReuseDepth deps (· = root)
  have init : live root := dagReachable.single rfl
  have ord := rootParents_later order root
  let A := Finset.univ.filter live
  have mem_iff (i) : i ∈ A ↔ live i := by simp [A]
  obtain ⟨v, hv, greatest⟩ := Finset.exists_max_image A rank ⟨root, (mem_iff _).mpr init⟩
  obtain ⟨path, chain, _, ⟨r, head, heq⟩, hcount⟩ :=
    dagReuseDepth_path ord ((mem_iff _).mp hv)
  refine ⟨path, head.trans (congrArg some heq), chain.imp (fun _ _ e => (mem_rootParents.mp e).2), ?_⟩
  have bound := dag_cost_le_by_rank deps ord (rootParents_arity arity root)
    (rootCost parents root cost) c (rootCost_rec parents root cost c rec) root live init
    (fun _ _ h e => h.step e) rank (fun _ _ h e => dagReuseDepth_mono ord h e)
    (fun _ _ h e m => dagReuseDepth_lt ord h e m) (rank v)
    (fun i h => greatest i ((mem_iff _).mpr h))
  rw [rootCost_root] at bound
  simpa only [sharedOnPath, hcount] using bound

private theorem rate_at_empty {l N : ℕ} (hl : 17 ≤ l)
    {L : QLine (Fin N × Fin l)} (t : ResLinQTree (BPHP N l) L) (hL : L = []) :
    2 ^ (2 ^ ((l-17)/6)) ≤ t.size := by
  subst L
  exact Tree.bphp_tree_rate hl t

/-- Any indexed unfolding of the proof contains a path, starting at the chosen
empty line, on which the number of reused premises controls the tree lower bound.
Duplicate occurrences of the same proof line are separate indices. -/
theorem bphp_reuse_tradeoff {l N : ℕ} (hl : 17 ≤ l)
    {π : List (QLine (Fin N × Fin l))} (g : QSynUnfolding (BPHP N l) π)
    (root : Fin π.length) (empty : π.get root = []) :
    ∃ path, path.head? = some root ∧ path.IsChain (fun i j => j ∈ g.parents i) ∧
      2 ^ (2 ^ ((l-17)/6)) ≤ 2 * π.length * (2*π.length+1) ^ sharedOnPath g.parents root path := by
  obtain ⟨path, head, chain, hc⟩ := cost_on_one_path g.parents g.later g.arity
    (fun i => (g.tree i).size) 2 (fun i => (g.count i).trans_le
      (Nat.add_le_add_right (g.localCost_le i) _)) root
  exact ⟨path, head, chain, (rate_at_empty hl (g.tree root) empty).trans hc⟩

/-- No polynomial-length refutations with polylogarithmic shared-premise depth
exist at all widths. For any two budgets, arbitrarily large widths force the
length budget to fail or a single path to exceed the reuse budget. -/
theorem BPHPReusePath (p q : Polynomial ℕ) (N : ℕ) :
    ∃ l : ℕ, N ≤ l ∧ ∀ π : List (QLine (Fin (2 ^ l + 1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π →
      π.length ≤ p.eval (2 ^ l) →
      (Nonempty (QSynUnfolding (BPHP (2 ^ l + 1) l) π) ∧
       ∀ (g : QSynUnfolding (BPHP (2 ^ l + 1) l) π) (root : Fin π.length), π.get root = [] →
        ∃ path, path.head? = some root ∧ path.IsChain (fun i j => j ∈ g.parents i) ∧
          q.eval l < sharedOnPath g.parents root path) := by
  obtain ⟨l, hN, hl, budgets⟩ := exists_width_beating_dag_budgets p q N
  refine ⟨l, hN, ?_⟩
  intro π hπ short
  have hn : 0 < 2 ^ l := by positivity
  have seed : (BPHP (2 ^ l + 1) l).Nonempty := by
    let i : Fin (2 ^ l + 1) := ⟨0, by omega⟩
    let j : Fin (2 ^ l + 1) := ⟨1, by omega⟩
    exact ⟨_, i, j, fun _ => false, by simp [i, j], rfl⟩
  refine ⟨exists_syn_unfolding seed hπ.1, ?_⟩
  intro g root hempty
  obtain ⟨path, head, chain, large⟩ := bphp_reuse_tradeoff hl g root hempty
  refine ⟨path, head, chain, ?_⟩
  by_contra! shallow
  have est : 2 * π.length * (2*π.length+1) ^ sharedOnPath g.parents root path ≤
      2 * p.eval (2 ^ l) * (2*p.eval (2 ^ l)+1) ^ q.eval l := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ short)
    exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) shallow)
  exact budgets.not_ge (large.trans est)

end PEqualNP.Search
