import PEqualNP.Search.Helpers.QCommonMultiple
import PEqualNP.Search.Helpers.QDeferSimp
import Mathlib.Tactic.Linarith

/-!
# Normalize a deferred simplification to one false unit

For a list G of false constants, let D be the product of their right-hand
sides. Pad G with 0=D, then scale each head into another copy of 0=D using
self-resolution. Syntactic weakening contracts identical copies. Each head
costs two more lines, and the bit length of D is bounded by G's encoded size.
-/

namespace PEqualNP.Search.Helpers

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

private def unitEq (V : Type) (D : ℤ) : QEq V := (0, D)

private theorem scale_heads (G : QLine V) (D : ℤ)
    (scale : ∀ e ∈ G, e.1 = 0 ∧ e.2 ∣ D)
    {ρ : List (QLine V)} (der : NoSimpDerivation F ρ)
    (hl : G ++ [unitEq V D] ∈ ρ) :
    ∃ s : List (QLine V), NoSimpDerivation F (s ++ ρ) ∧ [unitEq V D] ∈ s ++ ρ ∧
      s.length ≤ 2 * G.length ∧ ∀ L ∈ s,
        qCost L ≤ 1 + 3 * (unitEq V D).size + 2 * qWeight G := by
  induction G generalizing ρ with
  | nil => exact ⟨[], der, hl, le_rfl, by simp⟩
  | cons e G ih =>
    obtain ⟨hz, r, hr⟩ := scale e List.mem_cons_self
    let u := unitEq V D
    let T := G ++ [u]
    let R := u :: (T ++ T)
    have hm : e :: T ∈ ρ := hl
    have heq : (r • e.1 + (0 : ℤ) • e.1, r * e.2 + 0 * e.2) = u := by
      apply Prod.ext
      · funext v
        simp [u, unitEq, hz, Pi.add_apply, Pi.smul_apply]
      · simpa [u, unitEq, mul_comm] using hr.symm
    have raw : NoSimpDerivation F (R :: ρ) := by
      simpa only [heq] using NoSimpDerivation.res r 0 der hm hm
    have nxt : NoSimpDerivation F (T :: R :: ρ) := by
      apply NoSimpDerivation.weaken raw List.mem_cons_self
      intro x h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_append_right _ List.mem_cons_self
      · exact (List.mem_append.mp h).elim id id
    obtain ⟨s, ds, hs, hslen, hcost⟩ := ih (fun x hx => scale x (.tail _ hx)) nxt List.mem_cons_self
    refine ⟨s ++ [T, R], by simpa only [List.append_assoc, List.cons_append, List.nil_append] using ds,
      by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hs, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    · intro K hk
      have hwr : qWeight R = u.size + 2 * (qWeight G + u.size) := by
        change u.size + qWeight (T ++ T) = _
        simp [T, qWeight]
        omega
      have hwt : qWeight T = qWeight G + u.size := by simp [T, qWeight]
      have hwg : qWeight (e :: G) = e.size + qWeight G := rfl
      rcases List.mem_append.mp hk with hold | hfresh
      · have := hcost K hold
        rw [hwg]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfresh
        rcases hfresh with rfl | rfl
        · change 1 + qWeight T ≤ 1 + 3 * u.size + 2 * qWeight (e :: G)
          rw [hwt, hwg]
          omega
        · change 1 + qWeight R ≤ 1 + 3 * u.size + 2 * qWeight (e :: G)
          rw [hwr, hwg]
          omega

/-- A disjunction of false constants can be reduced to the single false
constant 0=D, without using the simplification rule. -/
theorem constant_unit {ρ : List (QLine V)} {G : QLine V} (der : NoSimpDerivation F ρ)
    (hG : G ∈ ρ) (bad : ∀ e ∈ G, e.1 = 0 ∧ e.2 ≠ 0) :
    ∃ s : List (QLine V), NoSimpDerivation F (s ++ ρ) ∧ [(0, rhsProduct G)] ∈ s ++ ρ ∧
      rhsProduct G ≠ 0 ∧ s.length ≤ 2 * G.length + 1 ∧
      ∀ L ∈ s, qCost L ≤ 7 + 5 * qWeight G := by
  let D := rhsProduct G
  let u := unitEq V D
  let T := G ++ [u]
  have pad : NoSimpDerivation F (T :: ρ) :=
    .weaken der hG (fun x hx => List.mem_append_left _ hx)
  obtain ⟨s, ds, hm, hlen, hcost⟩ := scale_heads G D (fun e he => ⟨(bad e he).1, dvd_rhsProduct he⟩)
    pad List.mem_cons_self
  have hw : u.size ≤ 2 + qWeight G := by
    have h := rhsProduct_size G
    simp only [QEq.size, u, unitEq, Pi.zero_apply, Int.natAbs_zero, Nat.size_zero, Finset.sum_const_zero, Nat.add_zero, D]
    omega
  refine ⟨s ++ [T], by simpa only [List.append_assoc, List.cons_append, List.nil_append] using ds,
    by change [unitEq V D] ∈ _; simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm,
    rhsProduct_ne_zero G (fun e he => (bad e he).2), ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro K hK
    rcases List.mem_append.mp hK with hold | hnew
    · have := hcost K hold
      change (unitEq V D).size ≤ _ at hw
      omega
    · obtain rfl := List.mem_singleton.mp hnew
      change 1 + qWeight (G ++ [u]) ≤ _
      rw [qWeight_append]
      have : qWeight [u] = u.size := by simp [qWeight]
      rw [this]
      omega

/-- Every refutation can postpone all simplifications until the single unit
0=D with nonzero D. The entire prefix is quadratic in the original bit size. -/
theorem normalized_constant_unit {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) :
    ∃ (D : ℤ) (σ : List (QLine V)), D ≠ 0 ∧ NoSimpDerivation F σ ∧
      [(0, D)] ∈ σ ∧ Nat.size D.natAbs ≤ 1 + resLinQSize π ∧
      resLinQSize σ ≤ 20 * (resLinQSize π + 1)^2 := by
  let G := falseConstants π
  let N := resLinQSize π
  obtain ⟨ρ, der, hg, hlen, cap⟩ := defer_simp_refutation hπ
  obtain ⟨s, ds, hm, hd, hslen, hcost⟩ := constant_unit der hg
    (fun e he => (mem_falseConstants.mp he).2)
  have wg : qWeight G ≤ N := qWeight_falseConstants_le π
  have lg := (qLength_le_weight G).trans wg
  have lp := qlength_le_size π
  have lenR : ρ.length ≤ 2 * N := by simpa [N] using hlen.trans (Nat.mul_le_mul_left 2 lp)
  have lenS : s.length ≤ 2 * N + 1 := hslen.trans (by change 2 * G.length + 1 ≤ _; omega)
  have costR : resLinQSize ρ ≤ (2*N)*(3*N) := (qSize_le_length_mul cap).trans
    (Nat.mul_le_mul lenR (by change N + 2 * qWeight G ≤ _; omega))
  have costS : resLinQSize s ≤ (2*N+1)*(7+5*N) := (qSize_le_length_mul hcost).trans
    (Nat.mul_le_mul lenS (by change 7 + 5 * qWeight G ≤ _; omega))
  refine ⟨_, s ++ ρ, hd, ds, hm, (rhsProduct_size G).trans (Nat.add_le_add_left wg 1), ?_⟩
  change resLinQSize (s ++ ρ) ≤ 20 * (N + 1)^2
  have cat : resLinQSize (s ++ ρ) = resLinQSize s + resLinQSize ρ := by simp [resLinQSize]
  rw [cat]
  nlinarith

/-- A full refutation in normal form: the final simplification deletes exactly
one explicit contradictory equation, and the prefix contains no simplifications. -/
theorem single_simp_unit_refutation {π : List (QLine V)} (hπ : IsResLinQSynRefutation F π) :
    ∃ (D : ℤ) (σ : List (QLine V)), D ≠ 0 ∧ NoSimpDerivation F σ ∧
      [(0, D)] ∈ σ ∧ IsResLinQSynRefutation F ([] :: σ) ∧
      Nat.size D.natAbs ≤ 1 + resLinQSize π ∧
      resLinQSize ([] :: σ) ≤ 20 * (resLinQSize π + 1)^2 + 1 := by
  obtain ⟨D, σ, hd, ds, hm, bits, size⟩ := normalized_constant_unit hπ
  refine ⟨D, σ, hd, ds, hm, ⟨?_, List.mem_cons_self⟩, bits, ?_⟩
  · simpa [hd] using IsResLinQSynDerivation.simp ds.toSyn hm
  · change 1 + resLinQSize σ ≤ _
    omega

end PEqualNP.Search.Helpers
