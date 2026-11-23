import PEqualNP.Defs.SearchQ
import PEqualNP.Defs.ProofComplexityLin
import Mathlib.Tactic

/-!
# Integer lines that no single parity clause represents

The falsifying assignments of a parity clause are closed under ternary XOR.
The integer equation asking for exactly one true bit in a triple fails this
test. For a family on disjoint triples, fixing fewer coordinates than there
are triples leaves an example for every choice of the fixed values.
-/

namespace PEqualNP.Search.Helpers.ParitySeparation

open PEqualNP.ProofComplexity

private def xorThree {V : Type} (a b c : V → Bool) (v : V) : Bool :=
  (a v ^^ b v) ^^ c v

private theorem xor_card_mod_two {V : Type} (s : Finset V) (a b c : V → Bool) :
    (s.filter fun v => xorThree a b c v = true).card % 2 =
    ((s.filter fun v => a v = true).card + (s.filter fun v => b v = true).card +
      (s.filter fun v => c v = true).card) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    cases ha : a v <;> cases hb : b v <;> cases hc : c v <;>
      simp [Finset.filter_insert, xorThree, hv, ha, hb, hc] at * <;> omega

/-- The complement of each parity clause is closed under the ternary affine operation. -/
theorem falsifying_affine {V : Type} (D : LinClause V) (a b c : V → Bool)
    (ha : ¬ LinClauseSat a D) (hb : ¬ LinClauseSat b D) (hc : ¬ LinClauseSat c D) :
    ¬ LinClauseSat (fun v => (a v ^^ b v) ^^ c v) D := by
  rintro ⟨q, hq, hs⟩
  have h1 : ¬ LinEqSat a q := fun h => ha ⟨q, hq, h⟩
  have h2 : ¬ LinEqSat b q := fun h => hb ⟨q, hq, h⟩
  have h3 : ¬ LinEqSat c q := fun h => hc ⟨q, hq, h⟩
  change LinEqSat (xorThree a b c) q at hs
  have hx := xor_card_mod_two q.1 a b c
  simp only [LinEqSat, Nat.odd_iff] at h1 h2 h3 hs
  cases h : q.2 <;> simp [h] at h1 h2 h3 hs <;> omega

/-- The integer equation counting true bits in one triple. -/
def exactlyOne {m : ℕ} (i : Fin m) : QLine (Fin m × Fin 3) :=
  [(fun v => if v.1 = i then 1 else 0, 1)]

private def patch {m : ℕ} (a : Fin m × Fin 3 → Bool) (i : Fin m) (u : Fin 3 → Bool)
    (v : Fin m × Fin 3) := if v.1 = i then u v.2 else a v

private theorem holds_one_iff {m : ℕ} (i : Fin m) (a : Fin m × Fin 3 → Bool) :
    QLine.Holds a (exactlyOne i) ↔
      ((if a (i, 0) then 1 else 0) + (if a (i, 1) then 1 else 0) +
        (if a (i, 2) then 1 else 0) : ℤ) = 1 := by
  simp only [QLine.Holds, exactlyOne, List.mem_singleton, exists_eq_left, QEq.Holds]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Fin.sum_univ_three]
    simp [add_assoc]
  · intro k _ hk
    simp [hk]
  · simp

/-- After an arbitrary partial assignment on fewer than m coordinates, one of
these m single-equation integer lines has no equivalent parity clause
on the remaining cube. -/
theorem no_parity_clause_after_restriction {m : ℕ} (T : Finset (Fin m × Fin 3))
    (hT : T.card < m) (fixed : Fin m × Fin 3 → Bool) :
    ∃ i : Fin m, ∀ D : LinClause (Fin m × Fin 3),
      ¬ ∀ a : Fin m × Fin 3 → Bool, (∀ v ∈ T, a v = fixed v) →
        (QLine.Holds a (exactlyOne i) ↔ LinClauseSat a D) := by
  classical
  have h : (T.image Prod.fst).card < (Finset.univ : Finset (Fin m)).card := by
    simpa using (Finset.card_image_le (s := T) (f := Prod.fst)).trans_lt hT
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  have hp (v) (hv : v ∈ T) : v.1 ≠ i := fun eq => hi (Finset.mem_image.mpr ⟨v, hv, eq⟩)
  refine ⟨i, ?_⟩
  intro D hequiv
  let a := patch fixed i (fun _ => false)
  let b := patch fixed i (fun j => decide (j ≠ 0))
  let c := patch fixed i (fun _ => true)
  let d := xorThree a b c
  have ext (u : Fin 3 → Bool) : ∀ v ∈ T, patch fixed i u v = fixed v :=
    fun v hv => by simp [patch, hp v hv]
  have extD : ∀ v ∈ T, d v = fixed v := by
    intro v hv
    simp [d, xorThree, a, b, c, ext _ v hv]
  have ha : ¬ QLine.Holds a (exactlyOne i) := by simp [holds_one_iff, a, patch]
  have hb : ¬ QLine.Holds b (exactlyOne i) := by norm_num [holds_one_iff, b, patch]
  have hc : ¬ QLine.Holds c (exactlyOne i) := by norm_num [holds_one_iff, c, patch]
  have hd : QLine.Holds d (exactlyOne i) := by norm_num [holds_one_iff, d, xorThree, a, b, c, patch]
  exact falsifying_affine D a b c (fun x => ha ((hequiv a (ext _)).mpr x))
    (fun x => hb ((hequiv b (ext _)).mpr x)) (fun x => hc ((hequiv c (ext _)).mpr x))
    ((hequiv d extD).mp hd)

end PEqualNP.Search.Helpers.ParitySeparation
