import PEqualNP.Search.Helpers.Width.Walk
import PEqualNP.Defs.SearchQSyn

/-!
# Semantic width of a line in syntactic integer R(lin)

A line can list redundant equations. We measure how many equations its Boolean
truth set needs, allowing any equivalent list of integer equations. The width
walk is applied to short representatives of the premises and conclusion of
each inference. At an input clause it walks to the canonical list of literals.
-/

namespace PEqualNP.Search.SemanticWidth

open Helpers Helpers.Width

/-- List the literals of a collision axiom once each. -/
private theorem short_axiom_line {N l : ℕ} {C : ProofComplexity.Clause (Fin N × Fin l)}
    (hC : C ∈ ProofComplexity.BPHP N l) :
    ∃ L : QLine (Fin N × Fin l), L.length ≤ 2 * l ∧
      ∀ e, e ∈ L ↔ ∃ t ∈ C, e = litQEq t := by
  classical
  refine ⟨C.toList.map litQEq, ?_, ?_⟩
  · simp only [List.length_map, Finset.length_toList]
    obtain ⟨i, j, α, _, rfl⟩ := hC
    apply (Finset.card_union_le _ _).trans
    have bound (k : Fin N) :
        (Finset.univ.image (fun b : Fin l => ((k, b), !α b))).card ≤ l := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin l)))
        (f := fun b => ((k, b), !α b))
    simpa [two_mul] using Nat.add_le_add (bound i) (bound j)
  · intro e
    simp [eq_comm]

variable {N l W : ℕ}
private abbrev Line (N l : ℕ) := QLine (Fin N × Fin l)

private def Agrees (K L : Line N l) : Prop :=
  ∀ a, QLine.Holds a K ↔ QLine.Holds a L

private def Safe (W : ℕ) (K : Line N l) : Prop :=
  ∀ a, InjP a (clo (16 * W ^ 2) K) → ¬ Fals a K

private theorem fals_iff {K : Line N l} {a} : Fals a K ↔ ¬ QLine.Holds a K := by
  simp [Fals, QLine.Holds]

/-- The width walk only needs pointwise soundness of an inference. -/
private theorem safe_step (hw : 0 < W) (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l)
    {K A B : Line N l} (hk : K.length ≤ W) (ha : A.length ≤ W) (hb : B.length ≤ W)
    (sA : Safe W A) (sB : Safe W B)
    (rule : ∀ a, QLine.Holds a A → QLine.Holds a B → QLine.Holds a K) : Safe W K := by
  intro q hq hF
  have split (a) (hf : Fals a K) : Fals a A ∨ Fals a B := by
    classical
    rw [fals_iff, fals_iff]
    by_contra! h
    exact (fals_iff.mp hf) (rule a h.1 h.2)
  obtain ⟨a, h | h⟩ := step W hw hnum K A B hk ha hb split q hq hF
  · exact sA a h.2 h.1
  · exact sB a h.2 h.1

private theorem resolution_holds {V : Type} [Fintype V] (a : V → Bool)
    {e e' : QEq V} {C D : QLine V} (α β : ℤ)
    (hC : QLine.Holds a (e :: C)) (hD : QLine.Holds a (e' :: D)) :
    QLine.Holds a ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) := by
  obtain ⟨f, hf, haf⟩ := hC
  obtain ⟨g, hg, hag⟩ := hD
  rcases List.mem_cons.mp hf with rfl | hf
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨_, List.mem_cons_self, combo_holds a f g α β haf hag⟩
    · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hag⟩
  · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), haf⟩

private def Short (W : ℕ) (L : Line N l) : Prop := ∃ K, K.length ≤ W ∧ Agrees K L
private def AllSafe (W : ℕ) (L : Line N l) : Prop :=
  ∀ K, K.length ≤ W → Agrees K L → Safe W K

private theorem from_premises (hw : 0 < W) (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l)
    {A B L : Line N l} (hA : Short W A) (hB : Short W B)
    (sA : AllSafe W A) (sB : AllSafe W B)
    (rule : ∀ a, QLine.Holds a A → QLine.Holds a B → QLine.Holds a L) : AllSafe W L := by
  obtain ⟨A', ha, ea⟩ := hA
  obtain ⟨B', hb, eb⟩ := hB
  intro K hk ek
  exact safe_step hw hnum hk ha hb (sA A' ha ea) (sB B' hb eb) fun a x y =>
    (ek a).mpr (rule a ((ea a).mp x) ((eb a).mp y))

private theorem walk_representatives (hw : 0 < W) (hl : 0 < l) (hwax : 2 * l ≤ W)
    (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l)
    {π : List (Line N l)} (hπ : IsResLinQSynDerivation (ProofComplexity.BPHP N l) π)
    (short : ∀ L ∈ π, Short W L) : ∀ L ∈ π, AllSafe W L := by
  induction hπ with
  | nil => simp
  | @ax π L C _ hc hrep ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h
    · obtain ⟨A, ha, ea⟩ := short_axiom_line hc
      have sA : Safe W A := by
        have hp : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ hw
        exact fun q hq hf => axiom_case _ (by omega) hl C hc A ea q hq hf
      intro K hk ek
      apply safe_step hw hnum hk (ha.trans hwax) (ha.trans hwax) sA sA
      rintro a ⟨e, he, heq⟩ _
      exact (ek a).mpr ⟨e, (hrep _).mpr ((ea _).mp he), heq⟩
    · exact ih (fun L hL => short L (List.mem_cons_of_mem _ hL)) L' h
  | bool v _ ih =>
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h
    · intro K _ ek a _ hf
      apply fals_iff.mp hf
      apply (ek a).mpr
      cases hv : a v with
      | false => exact ⟨litQEq (v, false), by simp, litQEq_holds a _ hv⟩
      | true => exact ⟨litQEq (v, true), by simp, litQEq_holds a _ hv⟩
    · exact ih (fun L hL => short L (List.mem_cons_of_mem _ hL)) L' h
  | @res π e e' C D α β _ hc hd ih =>
    have st : ∀ L ∈ π, Short W L := fun L h => short L (List.mem_cons_of_mem _ h)
    have safe := ih st
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h
    · exact from_premises hw hnum (st _ hc) (st _ hd) (safe _ hc) (safe _ hd)
        (fun a => resolution_holds a α β)
    · exact safe _ h
  | @weaken π C D _ hc sub ih =>
    have st : ∀ L ∈ π, Short W L := fun L h => short L (List.mem_cons_of_mem _ h)
    have safe := ih st
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h
    · exact from_premises hw hnum (st _ hc) (st _ hc) (safe _ hc) (safe _ hc)
        fun _ ⟨e, he, ha⟩ _ => ⟨e, sub e he, ha⟩
    · exact safe _ h
  | @simp π C _ hc ih =>
    have st : ∀ L ∈ π, Short W L := fun L h => short L (List.mem_cons_of_mem _ h)
    have safe := ih st
    intro L' hL'
    rcases List.mem_cons.mp hL' with rfl | h
    · apply from_premises hw hnum (st _ hc) (st _ hc) (safe _ hc) (safe _ hc)
      rintro a ⟨e, he, h⟩ _
      refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, h⟩
      simp only [decide_eq_true_eq]
      rintro ⟨hz, hn⟩
      exact hn (by simpa [QEq.Holds, hz] using h.symm)
    · exact safe _ h

/-- Under the walk's numerical hypotheses, some line requires more than W
integer equations in every representation of its Boolean truth set. -/
theorem semantic_width_lower {π : List (QLine (Fin N × Fin l))}
    (hπ : IsResLinQSynRefutation (ProofComplexity.BPHP N l) π)
    (hw : 0 < W) (hl : 0 < l) (hwax : 2 * l ≤ W)
    (hnum : 8 * (W * (16 * W ^ 2)) ^ 2 ≤ 2 ^ l) :
    ∃ L ∈ π, ∀ K : QLine (Fin N × Fin l),
      (∀ a, QLine.Holds a K ↔ QLine.Holds a L) → W < K.length := by
  classical
  by_contra h
  push Not at h
  have st : ∀ L ∈ π, Short W L := by
    intro L hL
    obtain ⟨K, eqv, hk⟩ := h L hL
    exact ⟨K, hk, eqv⟩
  have safe := walk_representatives hw hl hwax hnum hπ.1 st [] hπ.2 []
    (by simp) (fun _ => Iff.rfl)
  have hc := clo_card (16 * W ^ 2) ([] : Line N l)
  simp only [List.length_nil, zero_mul, Nat.le_zero, Finset.card_eq_zero] at hc
  apply safe (fun _ => false)
  · rw [hc]
    intro i hi
    simp at hi
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem bit_length_bound (m : ℕ) (hm : 8 ≤ m) : 2 * (6 * m + 17) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ i hi ih =>
    rw [pow_succ]
    omega

/-- For all bit lengths at least 59, a line of every refutation needs more than
2^floor((l-11)/6) integer hyperplanes, even after arbitrary equivalent rewriting. -/
theorem bphp_semantic_width (l : ℕ) (hl : 59 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (ProofComplexity.BPHP (2 ^ l + 1) l) π) :
    ∃ L ∈ π, ∀ K : QLine (Fin (2 ^ l + 1) × Fin l),
      (∀ a, QLine.Holds a K ↔ QLine.Holds a L) → 2 ^ ((l - 11) / 6) < K.length := by
  set m := (l - 11) / 6 with hm
  have hx := bit_length_bound m (by omega)
  apply semantic_width_lower hπ (by positivity) (by omega) (by omega)
  have expEq : 8 * (2 ^ m * (16 * (2 ^ m) ^ 2)) ^ 2 = 2 ^ (11 + 6 * m) := by
    rw [show (8 : ℕ) = 2 ^ 3 by decide, show (16 : ℕ) = 2 ^ 4 by decide]
    ring
  rw [expEq]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end PEqualNP.Search.SemanticWidth
