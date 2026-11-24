import PEqualNP.Search.Helpers.QPaddingCost
import PEqualNP.Defs.SearchQSyn
import Mathlib.Tactic

/-! From a singleton integer equation, rule out any Boolean point on its support
where the equation fails. Each coordinate substitution is an integer resolution
with a Boolean axiom, followed by a contraction of the shared guard. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Substitute one Boolean value in an integer equation. -/
def substBit (e : QEq V) (v : V) (b : Bool) : QEq V :=
  (fun u => if u = v then 0 else e.1 u, e.2 - e.1 v * (if b then 1 else 0))

private theorem substBit_combo (e : QEq V) (v : V) (b : Bool) :
    ((1 : ℤ) • e.1 + (-e.1 v) • (litQEq (v,b)).1,
      1 * e.2 + (-e.1 v) * (litQEq (v,b)).2) = substBit e v b := by
  apply Prod.ext
  · funext u
    by_cases h : u = v <;> simp [substBit, litQEq, h]
  · cases b <;> simp [substBit, litQEq, sub_eq_add_neg]

theorem substBit_holds (a : V → Bool) (e : QEq V) (v : V) :
    QEq.Holds a (substBit e v (a v)) ↔ QEq.Holds a e := by
  have coef (u : V) : (substBit e v (a v)).1 u = e.1 u - (if u = v then e.1 v else 0) := by
    by_cases h : u = v <;> simp [substBit,h]
  simp only [QEq.Holds, coef, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp [substBit]

private theorem lit_size_le_three (v : V) (b : Bool) : QEq.size (litQEq (v,b)) ≤ 3 := by
  simp only [QEq.size, litQEq]
  have reduce (u : V) : (if u = v then (1 : ℤ) else 0).natAbs.size = if u = v then 1 else 0 := by
    split_ifs <;> decide
  simp_rw [reduce]
  cases b <;> simp

theorem qeq_size_cap (e : QEq V) (H R : ℕ) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (hr : e.2.natAbs ≤ R) : e.size ≤ 1 + Fintype.card V * H + R := by
  have size_le (n : ℕ) : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have bounds := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun v _ => (size_le _).trans (hc v))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at bounds
  unfold QEq.size
  exact Nat.add_le_add (Nat.add_le_add_left bounds 1) ((size_le _).trans hr)

private theorem wt_cons (z : QEq V) (G : QLine V) :
    qWeight (z :: G) = z.size + qWeight G := rfl

private theorem filter_weight (p : QEq V → Bool) (L : QLine V) :
    qWeight (L.filter p) ≤ qWeight L := by
  induction L with
  | nil => simp
  | cons e L ih => cases h : p e <;> simp [h, wt_cons] at * <;> omega

private theorem eval_aux {F : Set (Clause V)} (vs : List V) (a : V → Bool) (G : QLine V)
    (H R : ℕ) (e : QEq V) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (hr : e.2.natAbs + vs.length * H ≤ R) (support : ∀ u, u ∉ vs → e.1 u = 0)
    (bad : ¬ QEq.Holds a e) (guard : ∀ v ∈ vs, litQEq (v,!(a v)) ∈ G)
    {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ) (start : e :: G ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧ σ.length ≤ 4*vs.length+2 ∧
      ∀ K ∈ σ, qCost K ≤ 10 + Fintype.card V * H + R + qWeight G := by
  classical
  induction vs generalizing e ρ with
  | nil =>
    have hz : e.1 = 0 := funext fun u => support u (by simp)
    have ne : e.2 ≠ 0 := by
      intro h
      exact bad (by simp [QEq.Holds,hz,h])
    let strip := fun z : QEq V => decide (¬ (z.1 = 0 ∧ z.2 ≠ 0))
    have s : IsResLinQSynDerivation F (G.filter strip :: ρ) := by
      simpa [strip, hz, ne] using d.simp start
    have w : IsResLinQSynDerivation F (G :: G.filter strip :: ρ) :=
      s.weaken List.mem_cons_self (fun z h => (List.mem_filter.mp h).1)
    refine ⟨[G,G.filter strip], w, List.mem_cons_self, by simp, ?_⟩
    intro K h
    have := filter_weight strip G
    rcases List.mem_cons.mp h with rfl | h
    · unfold qCost; omega
    · obtain rfl := List.mem_singleton.mp h
      unfold qCost; omega
  | cons v vs ih =>
    let b := a v
    let t := litQEq (v,b)
    let n := litQEq (v,!b)
    let be : QLine V := [litQEq (v,false), litQEq (v,true)]
    let red := substBit e v b
    let res := red :: (G ++ [n])
    let new := red :: G
    have dB : IsResLinQSynDerivation F (be :: ρ) := d.bool v
    have dO : IsResLinQSynDerivation F ([t,n] :: be :: ρ) :=
      dB.weaken List.mem_cons_self (by intro z h; cases hb : a v <;> simp_all [be,t,n,b,or_comm])
    have dR : IsResLinQSynDerivation F (res :: [t,n] :: be :: ρ) := by
      have r := dO.res (1 : ℤ) (-e.1 v)
        (List.mem_cons_of_mem [t,n] (List.mem_cons_of_mem be start))
        (List.mem_cons_self (a := t :: [n]))
      simpa only [t, substBit_combo] using r
    have dN : IsResLinQSynDerivation F (new :: res :: [t,n] :: be :: ρ) :=
      dR.weaken List.mem_cons_self (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons_self
        · rcases List.mem_append.mp hz with hz | hz
          · exact List.mem_cons_of_mem _ hz
          · obtain rfl := List.mem_singleton.mp hz
            exact List.mem_cons_of_mem _ (guard _ List.mem_cons_self))
    have cap (u) : (red.1 u).natAbs ≤ H := by
      by_cases h : u=v <;> simp [red, substBit, h, hc]
    have rc : red.2.natAbs + vs.length * H ≤ R := by
      have sub := Int.natAbs_sub_le e.2 (e.1 v * (if b then 1 else 0))
      simp only [List.length_cons, Nat.succ_mul] at hr
      change (e.2 - e.1 v * (if b then 1 else 0)).natAbs + _ ≤ _
      have bound := hc v
      cases b <;> simp at sub ⊢ <;> omega
    have zc (u) (hu : u ∉ vs) : red.1 u = 0 := by
      by_cases h : u = v
      · simp [red,substBit,h]
      · simp [red,substBit,h,support u (by simp [hu,h])]
    obtain ⟨s, ds, hm, hs, cost⟩ := ih red cap rc zc
      (fun ok => bad ((substBit_holds a e v).mp ok))
      (fun u hu => guard u (List.mem_cons_of_mem _ hu)) dN List.mem_cons_self
    refine ⟨s ++ [new,res,[t,n],be], ?_, List.mem_append_left _ hm, ?_, ?_⟩
    · simpa [List.append_assoc] using ds
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    · intro K hK
      rcases List.mem_append.mp hK with hK | hK
      · exact cost K hK
      have q := qeq_size_cap red H R cap (by omega)
      have tn := lit_size_le_three v b
      have nn := lit_size_le_three v (!b)
      have f0 := lit_size_le_three v false
      have f1 := lit_size_le_three v true
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
      rcases hK with rfl | rfl | rfl | rfl <;>
        simp only [new,res,t,n,be,qCost,wt_cons,qWeight_append,qWeight_nil] <;> omega

/-- An equation false on a fixed point can be removed from a line whenever the
remaining disjuncts are included among the desired conclusion’s disjuncts. -/
theorem qEvaluatePointFromContext {F : Set (Clause V)} (vs : List V) (a : V → Bool) (G : QLine V)
    (H : ℕ) (e : QEq V) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (support : ∀ u, u ∉ vs → e.1 u = 0) (bad : ¬ QEq.Holds a e)
    (guard : ∀ v ∈ vs, litQEq (v,!(a v)) ∈ G)
    {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ) {C : QLine V} (start : e :: C ∈ ρ)
    (incl : ∀ z ∈ C, z ∈ G) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧
      resLinQSize σ ≤ (4*vs.length+3) *
        (10 + Fintype.card V * H + (e.2.natAbs + vs.length * H) + qWeight G) := by
  let R := e.2.natAbs + vs.length * H
  have d0 : IsResLinQSynDerivation F ((e :: G) :: ρ) :=
    d.weaken start (by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (incl z hz))
  obtain ⟨s, ds, hm, len, cost⟩ := eval_aux vs a G H R e hc (le_refl _) support bad guard d0
    List.mem_cons_self
  refine ⟨s ++ [e :: G], by simpa [List.append_assoc] using ds, List.mem_append_left _ hm, ?_⟩
  apply (qSize_le_length_mul (M := 10 + Fintype.card V * H + R + qWeight G) ?_).trans
  · apply Nat.mul_le_mul_right
    simp
    omega
  · intro K hK
    rcases List.mem_append.mp hK with hK | hK
    · exact cost K hK
    obtain rfl := List.mem_singleton.mp hK
    have z := qeq_size_cap e H R hc (by dsimp [R]; omega)
    simp only [qCost, wt_cons]; omega

/-- Eliminate the supported variables of a false singleton into an existing blocker.
The bound uses the largest coefficient magnitude, the number of variables, and
the blocker size; it does not count any derivation of the given singleton. -/
theorem qEvaluatePoint {F : Set (Clause V)} (vs : List V) (a : V → Bool) (G : QLine V)
    (H : ℕ) (e : QEq V) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (support : ∀ u, u ∉ vs → e.1 u = 0) (bad : ¬ QEq.Holds a e)
    (guard : ∀ v ∈ vs, litQEq (v,!(a v)) ∈ G)
    {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ) (start : [e] ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧
      resLinQSize σ ≤ (4*vs.length+3) *
        (10 + Fintype.card V * H + (e.2.natAbs + vs.length * H) + qWeight G) :=
  qEvaluatePointFromContext vs a G H e hc support bad guard d start (by simp)

end PEqualNP.Search.Helpers
