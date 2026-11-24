import PEqualNP.Search.Helpers.QBitDifference
import PEqualNP.Search.Helpers.QScaledPair

/-! Cancel a nonzero scalar in an equality between two Boolean variables.
Resolve the scaled equation against each of the two nonzero alternatives for
their difference; the only large equations written are the false constants. -/

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

omit [Fintype V] in
theorem scaledEqPair_eq_smul (c : ℤ) (x y : V) :
    scaledEqPair c x y = (c • (qBitDiff x y 0).1, 0) := by
  refine Prod.ext (funext fun v => ?_) rfl
  change (if v=x then c else 0) - (if v=y then c else 0) =
    c * ((if v=x then (1:ℤ) else 0) - (if v=y then 1 else 0))
  split_ifs <;> ring

/-- Reject a nonzero right-hand side of the unscaled vector using a given
scaled zero equation. The remaining context may contain false constants. -/
private theorem discard_value (v : V → ℤ) (r c : ℤ) (hr : r ≠ 0) (hc : c ≠ 0)
    (G : QLine V) {ρ : List (QLine V)} (d : IsResLinQSynDerivation F ρ)
    (scaled : [(c • v,0)] ∈ ρ) (candidate : (v,r) :: G ∈ ρ) :
    ∃ σ, IsResLinQSynDerivation F (σ ++ ρ) ∧ G ∈ σ ∧
      resLinQSize σ ≤ 4 + (c*r).natAbs.size + 3*qWeight G := by
  classical
  let h : QEq V := (0, -(c*r))
  let p (e : QEq V) := decide (¬ (e.1 = 0 ∧ e.2 ≠ 0))
  let K := G.filter p
  have combo : ((1:ℤ) • (c • v) + (-c) • v, (1:ℤ)*0 + (-c)*r) = h := by
    simp [h,neg_smul]
  have raw : IsResLinQSynDerivation F ((h :: G) :: ρ) := by
    simpa only [combo,List.nil_append] using IsResLinQSynDerivation.res 1 (-c) d scaled candidate
  have cut : IsResLinQSynDerivation F (K :: (h :: G) :: ρ) := by
    simpa [K,p,h,hc,hr] using IsResLinQSynDerivation.simp raw (C := h :: G) List.mem_cons_self
  have recover : IsResLinQSynDerivation F (G :: K :: (h :: G) :: ρ) :=
    .weaken cut List.mem_cons_self (fun _ he => (List.mem_filter.mp he).1)
  refine ⟨[G,K,h::G],recover,List.mem_cons_self,?_⟩
  have sz : h.size = 1+(c*r).natAbs.size := by simp [QEq.size,h]
  have wf : qWeight K ≤ qWeight G :=
    ((List.filter_sublist (p := p) (l := G)).map QEq.size).sum_le_sum (fun _ _ => Nat.zero_le _)
  change (1+qWeight G) + ((1+qWeight K) + ((1+(h.size+qWeight G))+0)) ≤ _
  omega

/-- A scaled equality between two bits yields the canonical equality, with
additional encoded cost linear in the binary length of the scale. -/
theorem qUnscaleBitEquality (x y : V) (ne : x ≠ y) (c : ℤ) (hc : c ≠ 0) :
    QCanAdd F {[scaledEqPair c x y]} [qBitDiff x y 0] (1100+2*c.natAbs.size) := by
  intro ρ d base
  let vec := (qBitDiff x y 0).1
  let T := [qBitDiff x y 0]
  let R := qBitDiff x y (-1) :: T
  have source : [(c • vec, 0)] ∈ ρ := by
    simpa only [scaledEqPair_eq_smul, vec] using base [scaledEqPair c x y] rfl
  obtain ⟨s,ds,m,bs⟩ := qBitDiff_range (F := F) x y ne ρ d (by simp)
  obtain ⟨t,dt,mt,bt⟩ := discard_value vec 1 c one_ne_zero hc R ds
    (List.mem_append_right _ source) (List.mem_append_left _ m)
  obtain ⟨u,du,mu,bu⟩ := discard_value vec (-1) c (by decide) hc T dt
    (List.mem_append_right _ (List.mem_append_right _ source)) (List.mem_append_left _ mt)
  refine ⟨u ++ (t ++ s), by simpa [List.append_assoc] using du, List.mem_append_left _ mu, ?_⟩
  have size : resLinQSize (u ++ (t ++ s)) = resLinQSize u + (resLinQSize t + resLinQSize s) := by
    simp [resLinQSize]
  have zeroBound : (qBitDiff x y 0).size ≤ 3 := by simpa using qBitDiff_size_le x y 0
  have negBound : (qBitDiff x y (-1)).size ≤ 4 := by simpa using qBitDiff_size_le x y (-1)
  have wT : qWeight T ≤ 3 := by simpa [T,qWeight] using zeroBound
  have wR : qWeight R ≤ 7 := by
    change (qBitDiff x y (-1)).size + qWeight T ≤ 7
    omega
  simp only [mul_one, mul_neg_one, Int.natAbs_neg] at bt bu
  rw [size]
  omega

end PEqualNP.Search.Helpers
