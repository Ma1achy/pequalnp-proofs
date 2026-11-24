import PEqualNP.Search.Helpers.BinaryRowEquation
import PEqualNP.Search.Helpers.QCoordinateCases
import PEqualNP.Search.Helpers.QEvaluatePoint
import PEqualNP.Defs.ProofComplexityBit

/-! A single equation asserting that two binary rows are equal can be eliminated
using only their 2*l bits. A point with equal rows is excluded by a collision axiom.
At every other point the integer equation is false. -/
namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- Encoded cost of the coordinate-case derivation from a singleton row equality. -/
def rowEqualityCutCost (m l : ℕ) : ℕ :=
  2 ^ (2*l) * ((4*(2*l)+3) * (10 + m*l * 2^l + (2*l) * 2^l + 4*(2*l)) + 10*(4*(2*l)+1))

/-- Cost of eliminating one row equality while retaining a context of encoded weight w. -/
def rowEqualityContextCost (m l w : ℕ) : ℕ :=
  2 ^ (2*l) * ((4*(2*l)+3) * (10 + m*l * 2^l + (2*l) * 2^l + (4*(2*l) + w)) +
    10*(w + 4*(2*l) + 1))

/-- When two rows agree, their opposite literals form a collision axiom. -/
theorem bphp_same_row_axiom {m l : ℕ} (i j : Fin m) (hne : i ≠ j)
    (a : Fin m × Fin l → Bool) (eqs : ∀ b, a (i,b) = a (j,b)) :
    ((({i,j} : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin l))).image
      (fun v => (v, a v))) ∈ BPHP m l := by
  refine ⟨i, j, fun b => !(a (i,b)), hne, ?_⟩
  ext t
  simp only [Bool.not_not, Finset.mem_image, Finset.mem_union, Finset.mem_product,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, and_true, true_and]
  constructor
  · rintro ⟨⟨z,b⟩, (rfl | rfl), rfl⟩
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inr ⟨b, by rw [eqs b]⟩
  · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(i,b), Or.inl rfl, rfl⟩
    · exact ⟨(j,b), Or.inr rfl, by rw [eqs b]⟩

/-- Delete a row equality from the head of an arbitrary line. The other disjuncts
are retained and their cost is charged each time the proof copies them. -/
theorem bphp_rowEquality_context {m l : ℕ} (i j : Fin m) (hne : i ≠ j)
    (D : QLine (Fin m × Fin l)) :
    QCanAdd (BPHP m l) {binaryRowEq i j :: D} D (rowEqualityContextCost m l (qWeight D)) := by
  classical
  let S := ({i, j} : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin l))
  let vs := S.toList
  have len : vs.length = 2*l := by simp [vs, S, hne, Finset.card_product]
  let H := 2^l
  let cap := (4*(2*l)+3) * (10 + m*l*H + (2*l)*H + (4*(2*l) + qWeight D))
  have cases := qCoordinateCases (F := BPHP m l)
    (Γ := ({binaryRowEq i j :: D} : Set (QLine (Fin m × Fin l)))) vs S.nodup_toList D cap
  apply (by simpa [rowEqualityContextCost, cap, H, len] using cases)
  intro a
  let G := (vs.map (fun v => litQEq (v, a v))).reverse
  change QCanAdd _ _ (G ++ D) cap
  intro ρ d base
  have memG (e : QEq (Fin m × Fin l)) :
      e ∈ G ↔ ∃ v ∈ S, litQEq (v, a v) = e := by
    simp [G,vs]
  have weight : qWeight G ≤ 4*(2*l) := by
    unfold qWeight
    apply le_trans (List.sum_le_length_nsmul (G.map QEq.size) 4 ?_)
    · simp [G,len, Nat.mul_comm]
    · intro z hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
      obtain ⟨v, _, rfl⟩ := (memG e).mp he
      exact qLit_size_le v _
  by_cases eqs : ∀ b, a (i,b) = a (j,b)
  · let C := S.image (fun v => (v, a v))
    have hC : C ∈ BPHP m l := bphp_same_row_axiom i j hne a eqs
    have hrepr (e) : e ∈ G ↔ ∃ t ∈ C, e = litQEq t := by
      rw [memG]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨(v,a v), Finset.mem_image_of_mem _ hv, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨v, hv, rfl⟩
    have ax := IsResLinQSynDerivation.ax C d hC hrepr
    refine ⟨[G ++ D, G], .weaken ax List.mem_cons_self (fun e he => List.mem_append_left _ he),
      List.mem_cons_self, ?_⟩
    change (1 + qWeight (G ++ D)) + (1 + qWeight G + 0) ≤ _
    rw [qWeight_append]
    have first : 2 ≤ 4*(2*l)+3 := by omega
    calc
      _ ≤ 2 * (10 + m*l*H + (2*l)*H + (4*(2*l) + qWeight D)) := by omega
      _ ≤ cap := Nat.mul_le_mul_right _ first
  · let point := fun v => !(a v)
    have bad : ¬ QEq.Holds point (binaryRowEq i j) := by
      intro h
      apply eqs
      intro b
      simpa [point] using (binaryRowEq_holds point i j).mp h b
    have off (u) (hu : u ∉ vs) : (binaryRowEq (l := l) i j).1 u = 0 := by
      apply binaryRowEq_off
      · intro he
        exact hu (by simp [vs, S, he])
      · intro he
        exact hu (by simp [vs, S, he])
    have blocker (v) (hv : v ∈ vs) : litQEq (v, !point v) ∈ G := by
      apply (memG _).mpr
      exact ⟨v, by simpa [vs] using hv, by simp [point]⟩
    obtain ⟨σ, dσ, hG, cost⟩ := qEvaluatePointFromContext vs point (G ++ D) H
      (binaryRowEq i j) (binaryRowEq_abs_bound i j) off bad
      (fun v hv => List.mem_append_left _ (blocker v hv)) d (base _ rfl)
      (fun e he => List.mem_append_right _ he)
    refine ⟨σ, dσ, hG, cost.trans ?_⟩
    simp only [len, Fintype.card_prod, Fintype.card_fin, qWeight_append]
    change (4*(2*l)+3) * (10 + m*l*H + (0+(2*l)*H) + (qWeight G + qWeight D)) ≤ _
    exact Nat.mul_le_mul_left _ (by omega)

/-- Given a line consisting solely of the equality of two distinct rows, the binary
pigeonhole collision clauses yield a syntactic integer refutation. The bound counts
only the added lines and holds for every number of pigeons. -/
theorem bphp_rowEquality_cut {m l : ℕ} (i j : Fin m) (hne : i ≠ j) :
    QCanAdd (BPHP m l) ({[binaryRowEq i j]} : Set (QLine (Fin m × Fin l)))
      [] (rowEqualityCutCost m l) :=
  by simpa [rowEqualityContextCost, rowEqualityCutCost] using bphp_rowEquality_context i j hne []

/-- For the bit pigeonhole instance with n + 1 pigeons and n = 2^l holes,
eliminating an equality between two rows has polynomial encoded cost. -/
theorem rowEqualityCutCost_le (l : ℕ) :
    rowEqualityCutCost (2^l + 1) l ≤ 400 * (2^l + 1)^6 := by
  let n := 2^l
  have hl : l ≤ n := Nat.le_of_lt Nat.lt_two_pow_self
  have pow_eq : 2 ^ (2*l) = n^2 := by rw [mul_comm 2 l, pow_mul]
  unfold rowEqualityCutCost
  rw [pow_eq]
  change n^2 * ((4*(2*l)+3) * (10 + (n+1)*l*n + (2*l)*n + 4*(2*l)) +
    10*(4*(2*l)+1)) ≤ 400 * (n+1)^6
  calc
    _ ≤ n^2 * ((4*(2*n)+3) * (10 + (n+1)*n*n + (2*n)*n + 4*(2*n)) +
        10*(4*(2*n)+1)) := by gcongr
    _ ≤ _ := by ring_nf; omega

private theorem rowEqualityContextCost_mono {m l x y : ℕ} (h : x ≤ y) :
    rowEqualityContextCost m l x ≤ rowEqualityContextCost m l y := by
  unfold rowEqualityContextCost
  gcongr

/-- Empty a previously derived line consisting entirely of collision equations
for distinct pairs. No sortedness, completeness, or uniqueness of its pairs is needed.
Costs include the copies of all surviving disjuncts at every elimination step. -/
theorem bphp_collisionLine_elimination {m l : ℕ} (L : QLine (Fin m × Fin l))
    (hL : ∀ e ∈ L, ∃ i j : Fin m, i ≠ j ∧ e = binaryRowEq i j)
    {ρ : List (QLine (Fin m × Fin l))} (d : IsResLinQSynDerivation (BPHP m l) ρ)
    (start : L ∈ ρ) :
    ∃ σ, IsResLinQSynRefutation (BPHP m l) (σ ++ ρ) ∧
      resLinQSize σ ≤ L.length * rowEqualityContextCost m l (qWeight L) := by
  induction L generalizing ρ with
  | nil => exact ⟨[], ⟨d, start⟩, by simp [resLinQSize]⟩
  | cons e L ih =>
    obtain ⟨i, j, hne, rfl⟩ := hL e List.mem_cons_self
    obtain ⟨s, ds, produced, hs⟩ := bphp_rowEquality_context i j hne L ρ d
      (fun K hK => Set.mem_singleton_iff.mp hK ▸ start)
    obtain ⟨t, refute, ht⟩ := ih (fun f hf => hL f (List.mem_cons_of_mem _ hf)) ds
      (List.mem_append_left _ produced)
    refine ⟨t ++ s, by simpa [List.append_assoc] using refute, ?_⟩
    have cost_mono : rowEqualityContextCost m l (qWeight L) ≤
        rowEqualityContextCost m l (qWeight (binaryRowEq i j :: L)) := by
      apply rowEqualityContextCost_mono
      change _ ≤ (binaryRowEq i j).size + qWeight L
      omega
    have sum_size : resLinQSize (t ++ s) = resLinQSize t + resLinQSize s := by
      simp [resLinQSize]
    rw [sum_size, List.length_cons, Nat.succ_mul]
    exact Nat.add_le_add (ht.trans (Nat.mul_le_mul_left _ cost_mono)) (hs.trans cost_mono)

/-- At n = 2^l holes, a one-pair cut costs at most an affine function of the
surviving context's weight, with coefficients polynomial in n. -/
theorem rowEqualityContextCost_le (l w : ℕ) :
    rowEqualityContextCost (2^l + 1) l w ≤
      400*(2^l+1)^6 + 21*(2^l+1)^3*w := by
  let n := 2^l
  have hl : l ≤ n := Nat.le_of_lt Nat.lt_two_pow_self
  have pow_eq : 2 ^ (2*l) = n^2 := by rw [mul_comm 2 l, pow_mul]
  have diff : rowEqualityContextCost (2^l+1) l w =
      rowEqualityCutCost (2^l+1) l + n^2*(8*l+13)*w := by
    unfold rowEqualityCutCost rowEqualityContextCost
    rw [pow_eq]
    ring
  rw [diff]
  apply Nat.add_le_add (rowEqualityCutCost_le l)
  apply Nat.mul_le_mul_right w
  calc
    _ ≤ n^2*(8*n+13) := by gcongr
    _ ≤ 21*(n+1)^3 := by ring_nf; omega

/-- A short syntactic derivation of the disjunction of row equalities suffices
for a short refutation. The resulting polynomial bound uses the size of the
entire supplied derivation, so it also covers long or repeated collision lines. -/
theorem bphp_collisionLine_to_refutation {l : ℕ}
    {ρ : List (QLine (Fin (2^l + 1) × Fin l))}
    (d : IsResLinQSynDerivation (BPHP (2^l + 1) l) ρ)
    {L : QLine (Fin (2^l + 1) × Fin l)} (start : L ∈ ρ)
    (hL : ∀ e ∈ L, ∃ i j : Fin (2^l + 1), i ≠ j ∧ e = binaryRowEq i j) :
    ∃ τ, IsResLinQSynRefutation (BPHP (2^l + 1) l) τ ∧
      resLinQSize τ ≤ resLinQSize ρ +
        resLinQSize ρ * (400*(2^l+1)^6 + 21*(2^l+1)^3*resLinQSize ρ) := by
  obtain ⟨σ, refute, hσ⟩ := bphp_collisionLine_elimination L hL d start
  refine ⟨σ ++ ρ, refute, ?_⟩
  have sum_size : resLinQSize (σ ++ ρ) = resLinQSize σ + resLinQSize ρ := by
    simp [resLinQSize]
  have w : qWeight L ≤ resLinQSize ρ := (Nat.le_add_left _ 1).trans (qCost_le_of_mem start)
  rw [sum_size, Nat.add_comm]
  apply Nat.add_le_add_left _ _
  apply hσ.trans
  apply Nat.mul_le_mul ((qLength_le_weight L).trans w)
  exact (rowEqualityContextCost_mono w).trans (rowEqualityContextCost_le l (resLinQSize ρ))

end PEqualNP.Search
