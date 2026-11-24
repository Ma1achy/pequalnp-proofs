import PEqualNP.Search.Helpers.QCoordinateCases

/-! The Boolean axioms give the three possible integer differences of two bits. -/

namespace PEqualNP.Search.Helpers

variable {V : Type} [DecidableEq V]

/-- The equation `x - y = b` on Boolean coordinates. -/
def qBitDiff (x y : V) (b : ℤ) : QEq V :=
  ((litQEq (x, false)).1 - (litQEq (y, false)).1, b)

variable [Fintype V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

theorem qBitDiff_size_le (x y : V) (b : ℤ) :
    (qBitDiff x y b).size ≤ 3 + b.natAbs.size := by
  have coeff (v : V) : ((qBitDiff x y b).1 v).natAbs.size ≤
      (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
    simp only [qBitDiff, litQEq, Pi.sub_apply]
    split_ifs <;> decide
  have total := Finset.sum_le_sum (s := Finset.univ) (fun v _ => coeff v)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at total
  change 1 + _ + b.natAbs.size ≤ 3 + b.natAbs.size
  omega

private def boolLine (v : V) : QLine V := [litQEq (v,false), litQEq (v,true)]

private def guardedBool (v : V) (b : Bool) : QLine V := [litQEq (v,!b), litQEq (v,b)]

omit [Fintype V] in
private theorem guardedBool_sub (v : V) (b : Bool) :
    ∀ e ∈ boolLine v, e ∈ guardedBool v b := by
  cases b <;> simp [guardedBool, boolLine, or_comm]

private def rangeLine (x y : V) : QLine V := [qBitDiff x y 1, qBitDiff x y (-1), qBitDiff x y 0]

private theorem range_weight (x y : V) : qWeight (rangeLine x y) ≤ 11 := by
  have hp := qBitDiff_size_le x y 1
  have hn := qBitDiff_size_le x y (-1)
  have hz := qBitDiff_size_le x y 0
  simp at hp hn hz
  simp only [rangeLine, qWeight, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  omega

private theorem range_leaf (x y : V) (b c : Bool) {ρ : List (QLine V)}
    (d : IsResLinQSynDerivation F ρ) (hx : boolLine x ∈ ρ) (hy : boolLine y ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧
      litQEq (y,c) :: litQEq (x,b) :: rangeLine x y ∈ σ ∧ resLinQSize σ ≤ 43 := by
  let X := guardedBool x b
  let Y := guardedBool y c
  have dx : IsResLinQSynDerivation F (X :: ρ) := .weaken d hx (guardedBool_sub x b)
  have dy : IsResLinQSynDerivation F (Y :: X :: ρ) :=
    .weaken dx (List.mem_cons_of_mem _ hy) (guardedBool_sub y c)
  let k : ℤ := (litQEq (x,!b)).2 - (litQEq (y,!c)).2
  let D := qBitDiff x y k
  let R := [D, litQEq (x,b), litQEq (y,c)]
  let T := litQEq (y,c) :: litQEq (x,b) :: rangeLine x y
  have combine : ((1 : ℤ) • (litQEq (x,!b)).1 + (-1 : ℤ) • (litQEq (y,!c)).1,
      (1 : ℤ) * (litQEq (x,!b)).2 + (-1 : ℤ) * (litQEq (y,!c)).2) = D := by
    cases c <;> simp [D, k, qBitDiff, litQEq, sub_eq_add_neg]
  have dr : IsResLinQSynDerivation F (R :: Y :: X :: ρ) := by
    have h := IsResLinQSynDerivation.res 1 (-1) dy
      (show litQEq (x,!b) :: [litQEq (x,b)] ∈ Y :: X :: ρ from .tail _ List.mem_cons_self)
      (show litQEq (y,!c) :: [litQEq (y,c)] ∈ Y :: X :: ρ from List.mem_cons_self)
    simpa only [combine, List.cons_append, List.nil_append, R] using h
  have mem : D ∈ rangeLine x y := by cases b <;> cases c <;> simp [D,k,litQEq,rangeLine]
  have dt : IsResLinQSynDerivation F (T :: R :: Y :: X :: ρ) := by
    apply IsResLinQSynDerivation.weaken dr List.mem_cons_self
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .tail _ (.tail _ mem)
    · rcases List.mem_cons.mp he with rfl | he
      · exact .tail _ List.mem_cons_self
      · exact (List.mem_singleton.mp he) ▸ List.mem_cons_self
  refine ⟨[T,R,Y,X], dt, List.mem_cons_self, ?_⟩
  have db : D.size ≤ 4 := by
    have h := qBitDiff_size_le x y k
    have hk : k.natAbs.size ≤ 1 := by cases b <;> cases c <;> simp [k,litQEq]
    change (qBitDiff x y k).size ≤ 4
    omega
  have wt := range_weight x y
  have costs (v : V) (t : Bool) := litQEq_size (v,t)
  have cx := costs x b
  have cy := costs y c
  have cx' := costs x (!b)
  have cy' := costs y (!c)
  have cons (e : QEq V) (L : QLine V) : qWeight (e :: L) = e.size + qWeight L := rfl
  have empty : resLinQSize ([] : List (QLine V)) = 0 := rfl
  simp only [qSize_cons, empty, qCost, T, R, Y, X, guardedBool, cons, qWeight_nil]
  omega

/-- A derivation of the full range of the difference, with cost independent of the cube size. -/
theorem qBitDiff_range (x y : V) (ne : x ≠ y) :
    QCanAdd F ∅ [qBitDiff x y 1, qBitDiff x y (-1), qBitDiff x y 0] 1000 := by
  let Γ : Set (QLine V) := {L | L = boolLine x ∨ L = boolLine y}
  have casesProof := qCoordinateCases (F := F) (Γ := Γ) [x,y] (by simp [ne]) (rangeLine x y) 43
    (fun a ρ d base => range_leaf x y (a x) (a y) d (base _ (Or.inl rfl)) (base _ (Or.inr rfl)))
  intro ρ d _
  have init : IsResLinQSynDerivation F (boolLine y :: boolLine x :: ρ) := .bool y (.bool x d)
  obtain ⟨σ,ds,mem,cost⟩ := casesProof _ init (by
    intro K hK
    rcases hK with rfl | rfl
    · exact .tail _ List.mem_cons_self
    · exact List.mem_cons_self)
  refine ⟨σ ++ [boolLine y,boolLine x], by simpa using ds, List.mem_append_left _ mem, ?_⟩
  have initCost (v : V) : qCost (boolLine v) ≤ 7 := by
    have hf := litQEq_size (v,false)
    have ht := litQEq_size (v,true)
    change 1 + ((litQEq (v,false)).size + ((litQEq (v,true)).size + 0)) ≤ 7
    omega
  have add : resLinQSize (σ ++ [boolLine y,boolLine x]) =
      resLinQSize σ + (qCost (boolLine y) + qCost (boolLine x)) := by simp [resLinQSize,qCost,qWeight]
  rw [add]
  have := range_weight x y
  have := initCost x
  have := initCost y
  simp only [List.length_cons, List.length_nil] at cost
  omega

end PEqualNP.Search.Helpers
