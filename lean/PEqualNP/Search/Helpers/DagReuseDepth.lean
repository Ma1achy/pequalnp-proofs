import PEqualNP.Search.Helpers.DagUnfoldBound
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find

namespace PEqualNP.Search.Helpers

variable {n : ℕ} {parents : Fin n → List (Fin n)} {start : Fin n → Prop}

/-- A nonempty path of consecutive proof dependencies from a permitted start to `i`. -/
def DagPathTo (parents : Fin n → List (Fin n)) (start : Fin n → Prop)
    (i : Fin n) (p : List (Fin n)) : Prop :=
  p.IsChain (fun j k => k ∈ parents j) ∧ p.getLast? = some i ∧
    ∃ r, p.head? = some r ∧ start r

def dagReachable (parents : Fin n → List (Fin n)) (start : Fin n → Prop) (i : Fin n) : Prop :=
  ∃ p, DagPathTo parents start i p

theorem dagReachable.single {i : Fin n} (hs : start i) : dagReachable parents start i :=
  ⟨[i], .singleton _, rfl, i, rfl, hs⟩

theorem DagPathTo.step {i j : Fin n} {p : List (Fin n)}
    (hp : DagPathTo parents start i p) (e : j ∈ parents i) :
    DagPathTo parents start j (p ++ [j]) := by
  obtain ⟨chain, last, r, first, hr⟩ := hp
  refine ⟨chain.append (.singleton _) ?_, by simp, r, ?_, hr⟩
  · simpa [last] using e
  · cases p with
    | nil => simp at first
    | cons => exact first

theorem dagReachable.step {i j : Fin n} (hr : dagReachable parents start i)
    (e : j ∈ parents i) : dagReachable parents start j := by
  obtain ⟨p, hp⟩ := hr
  exact ⟨p ++ [j], hp.step e⟩

private theorem shared_count_le {i : Fin n} {p : List (Fin n)}
    (order : ∀ i j, j ∈ parents i → i < j) (hp : DagPathTo parents start i p) :
    (p.filter (fun j => 2 ≤ dagUses parents j)).length ≤ n := by
  have inc : p.IsChain (· < ·) := hp.1.imp order
  have distinct : p.Nodup := inc.pairwise.imp (fun h => ne_of_lt h)
  exact (List.length_filter_le ..).trans (by simpa using distinct.length_le_card)

/-- Maximum number of multiply referenced vertices on a dependency path to `i`.
Uses are counted in the given graph; the start predicate selects the paths. -/
noncomputable def dagReuseDepth (parents : Fin n → List (Fin n)) (start : Fin n → Prop)
    (i : Fin n) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ p, DagPathTo parents start i p ∧
    (p.filter (fun j => 2 ≤ dagUses parents j)).length = k) n

/-- A reachable vertex has a concrete path attaining its reuse depth. -/
theorem dagReuseDepth_path {i : Fin n} (order : ∀ i j, j ∈ parents i → i < j)
    (hr : dagReachable parents start i) :
    ∃ p : List (Fin n), p.IsChain (fun j k => k ∈ parents j) ∧ p.getLast? = some i ∧
      (∃ r, p.head? = some r ∧ start r) ∧
      (p.filter (fun j => 2 ≤ dagUses parents j)).length = dagReuseDepth parents start i := by
  classical
  obtain ⟨p, hp⟩ := hr
  have spec := Nat.findGreatest_spec (P := fun k => ∃ q, DagPathTo parents start i q ∧
    (q.filter (fun j => 2 ≤ dagUses parents j)).length = k)
    (shared_count_le order hp) ⟨p, hp, rfl⟩
  obtain ⟨q, hq, size⟩ := spec
  exact ⟨q, hq.1, hq.2.1, hq.2.2, size⟩

private theorem reuseDepth_step {i j : Fin n} (order : ∀ i j, j ∈ parents i → i < j)
    (hr : dagReachable parents start i) (e : j ∈ parents i) :
    dagReuseDepth parents start i + (if 2 ≤ dagUses parents j then 1 else 0) ≤
      dagReuseDepth parents start j := by
  classical
  obtain ⟨p, chain, last, first, size⟩ := dagReuseDepth_path order hr
  have path : DagPathTo parents start i p := ⟨chain, last, first⟩
  have ext := path.step e
  have le := Nat.le_findGreatest (P := fun k => ∃ q, DagPathTo parents start j q ∧
    (q.filter (fun u => 2 ≤ dagUses parents u)).length = k)
    (shared_count_le order ext) ⟨p ++ [j], ext, rfl⟩
  change ((p ++ [j]).filter (fun u => 2 ≤ dagUses parents u)).length ≤
    dagReuseDepth parents start j at le
  by_cases h : 2 ≤ dagUses parents j <;> simpa [List.filter_append, h, size] using le

theorem dagReuseDepth_mono {i j : Fin n} (order : ∀ i j, j ∈ parents i → i < j)
    (hr : dagReachable parents start i) (e : j ∈ parents i) :
    dagReuseDepth parents start i ≤ dagReuseDepth parents start j :=
  (Nat.le_add_right ..).trans (reuseDepth_step order hr e)

theorem dagReuseDepth_lt {i j : Fin n} (order : ∀ i j, j ∈ parents i → i < j)
    (hr : dagReachable parents start i) (e : j ∈ parents i) (h : 2 ≤ dagUses parents j) :
    dagReuseDepth parents start i < dagReuseDepth parents start j := by
  simpa [h] using reuseDepth_step order hr e

end PEqualNP.Search.Helpers
