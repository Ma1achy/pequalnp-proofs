import PEqualNP.Search.Helpers.QEvaluatePoint
import PEqualNP.Search.Helpers.QCoordinateCut

/-! At a satisfying Boolean point, integer resolution can build an equation by
adding the weighted coordinate equations. The opposite literals of the point
remain in the output line. -/

namespace PEqualNP.Search.Helpers
open PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem reconstruct (e : QEq V) (v : V) (b : Bool) :
    ((1:ℤ) • (substBit e v b).1 + (e.1 v) • (litQEq (v,b)).1,
      1 * (substBit e v b).2 + e.1 v * (litQEq (v,b)).2) = e := by
  apply Prod.ext
  · funext u
    by_cases h : u = v <;> simp [substBit, litQEq, h]
  · simp [substBit, litQEq]

private def boolLine (v : V) : QLine V := [litQEq (v,false), litQEq (v,true)]

private def signedLine (v : V) (b : Bool) : QLine V := [litQEq (v,b), litQEq (v,!b)]

omit [DecidableEq V] in
private theorem wt (z : QEq V) (G : QLine V) :
    qWeight (z :: G) = z.size + qWeight G := rfl

private theorem bool_lines {F : Set (PEqualNP.ProofComplexity.Clause V)} {ρ : List (QLine V)}
    (d : IsResLinQSynDerivation F ρ) (v : V) (b : Bool) :
    IsResLinQSynDerivation F (signedLine v b :: boolLine v :: ρ) :=
  (d.bool v).weaken List.mem_cons_self (by
    intro z h
    cases b <;> simpa [signedLine, boolLine, or_comm] using h)

private theorem build_aux {F : Set (PEqualNP.ProofComplexity.Clause V)} (vs : List V) (a : V → Bool) (G : QLine V)
    (H R : ℕ) (w : V) (seed : litQEq (w,!(a w)) ∈ G)
    (e : QEq V) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (hr : e.2.natAbs + vs.length * H ≤ R) (support : ∀ u, u ∉ vs → e.1 u = 0)
    (good : QEq.Holds a e) (guard : ∀ v ∈ vs, litQEq (v,!(a v)) ∈ G)
    {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ e :: G ∈ σ ∧ σ.length ≤ 4*vs.length+4 ∧
      ∀ K ∈ σ, qCost K ≤ 10 + Fintype.card V * H + R + qWeight G := by
  induction vs generalizing e with
  | nil =>
    have z : e.1 = 0 := funext fun u => support u (by simp)
    have h0 : e.2 = 0 := by simpa [QEq.Holds,z] using good.symm
    let n := litQEq (w,!(a w))
    have zero : ((0:ℤ) • (litQEq (w,a w)).1 + (0:ℤ) • (litQEq (w,a w)).1,
        0 * (litQEq (w,a w)).2 + 0 * (litQEq (w,a w)).2) = e := by
      apply Prod.ext <;> simp [z,h0]
    have d0 := bool_lines d w (a w)
    have start : signedLine w (a w) ∈ signedLine w (a w) :: boolLine w :: ρ := List.mem_cons_self
    have dR : IsResLinQSynDerivation F ([e,n,n] :: signedLine w (a w) :: boolLine w :: ρ) := by
      simpa only [List.cons_append, List.nil_append, zero] using d0.res 0 0 (C := [n]) (D := [n])
        (e := litQEq (w,a w)) (e' := litQEq (w,a w)) start start
    have dG := dR.weaken (C := [e,n,n]) (D := e :: G) List.mem_cons_self (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr seed)
    refine ⟨[e::G,[e,n,n],signedLine w (a w),boolLine w], dG, List.mem_cons_self, by simp, ?_⟩
    have zero_size : e.size = 1 := by simp [QEq.size,z,h0]
    have nsize := qLit_size_le w (!(a w))
    have tsize := qLit_size_le w (a w)
    have fs := qLit_size_le w false
    have ts := qLit_size_le w true
    intro K h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;>
      simp only [qCost,wt,signedLine,boolLine,qWeight_nil,n,zero_size] <;> omega
  | cons v vs ih =>
    let b := a v
    let t := litQEq (v,b)
    let n := litQEq (v,!b)
    let red := substBit e v b
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
    obtain ⟨s, ds, hm, hs, cost⟩ := ih red cap rc zc ((substBit_holds a e v).mpr good)
      (fun u hu => guard u (List.mem_cons_of_mem _ hu))
    let res := e :: (G ++ [n])
    have dO := bool_lines ds v b
    have dR : IsResLinQSynDerivation F (res :: signedLine v b :: boolLine v :: (s++ρ)) := by
      have pr := dO.res 1 (e.1 v) (e := red) (e' := t) (C := G) (D := [n])
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm))) List.mem_cons_self
      simpa only [red, t, reconstruct] using pr
    have dG := dR.weaken (C := res) (D := e :: G) List.mem_cons_self (by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · rcases List.mem_append.mp hz with hz | hz
        · exact List.mem_cons_of_mem _ hz
        · obtain rfl := List.mem_singleton.mp hz
          exact List.mem_cons_of_mem _ (guard _ List.mem_cons_self))
    refine ⟨[e::G,res,signedLine v b,boolLine v] ++ s, by simpa using dG, ?_, ?_, ?_⟩
    · exact List.mem_cons_self
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro K hK
      rcases List.mem_append.mp hK with hK | hK
      · have q := qeq_size_cap e H R hc (by omega)
        have tn := qLit_size_le v b
        have nn := qLit_size_le v (!b)
        have f0 := qLit_size_le v false
        have f1 := qLit_size_le v true
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
        rcases hK with rfl | rfl | rfl | rfl <;>
          simp only [res,n,boolLine,signedLine,qCost,wt,qWeight_append,qWeight_nil] <;> omega
      · exact cost K hK

/-- From Boolean axioms, derive a satisfied integer equation with opposite literals
of the point as guards. At least one guard coordinate is required. -/
theorem qBuildAtPoint {F : Set (PEqualNP.ProofComplexity.Clause V)} (vs : List V) (a : V → Bool) (G : QLine V)
    (H : ℕ) (e : QEq V) (hne : vs ≠ []) (hc : ∀ u, (e.1 u).natAbs ≤ H)
    (support : ∀ u, u ∉ vs → e.1 u = 0) (good : QEq.Holds a e)
    (guard : ∀ v ∈ vs, litQEq (v,!(a v)) ∈ G)
    {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ++ρ) ∧ e::G ∈ σ ∧
      resLinQSize σ ≤ (4*vs.length+4) *
        (10 + Fintype.card V*H + (e.2.natAbs+vs.length*H) + qWeight G) := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil vs hne
  obtain ⟨s,ds,hm,hs,cost⟩ := build_aux vs a G H (e.2.natAbs+vs.length*H)
    w (guard w hw) e hc (le_refl _) support good guard d
  exact ⟨s,ds,hm,(qSize_le_length_mul cost).trans (Nat.mul_le_mul_right _ hs)⟩

end PEqualNP.Search.Helpers
