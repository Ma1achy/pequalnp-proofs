import PEqualNP.Search.BPHPParityBarrier
import PEqualNP.Search.Helpers.QPrimitiveCombination
import PEqualNP.Search.Helpers.QPrimitiveRank
import PEqualNP.Search.Helpers.QProjectedSimulation

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- The augmented rows have rank two over the rationals and rank one modulo
two after removing each row's common power of two. A variable occurs with an
odd coefficient in both rows. -/
def PrimitiveRankPair {V : Type} [Fintype V] (e f : QEq V) : Prop :=
  qParity (qPrimitive e) = qParity (qPrimitive f) ∧ (qParity (qPrimitive e)).1.Nonempty ∧
  (∀ i j, Even (qCoord (qPrimitive e) i * qCoord (qPrimitive f) j -
    qCoord (qPrimitive e) j * qCoord (qPrimitive f) i)) ∧
  (∃ i j, qCoord (qPrimitive e) i * qCoord (qPrimitive f) j ≠
    qCoord (qPrimitive e) j * qCoord (qPrimitive f) i)

theorem rank_pair_of_projection_failure {V : Type} [Fintype V] (a : V → Bool)
    (e f : QEq V) (α β : ℤ)
    (he : LinEqSat a (qParity (qPrimitive e))) (hf : LinEqSat a (qParity (qPrimitive f)))
    (hbad : ¬ LinEqSat a (qParity (qPrimitive
      (α • e.1 + β • f.1, α * e.2 + β * f.2)))) : PrimitiveRankPair e f := by
  obtain ⟨same, nonempty⟩ := primitive_combo_obstruction a e f α β he hf hbad
  obtain ⟨i, j, diff⟩ := exists_minor_of_primitive_failure a e f α β he hf hbad
  exact ⟨same, nonempty, even_minor_of_qParity_eq same, i, j,
    fun h => diff ((qMinor_zero_iff_primitive e f i j).mpr h)⟩

/-- A sufficiently short bit-PHP refutation has a resolution position where
dividing out common powers of two before parity projection breaks the inference.
The two premise rows are independent over the rationals but coincide modulo two
after normalization, and an assignment falsifies the entire projected result. -/
theorem BPHPPrimitiveCancellation {l : ℕ} (hl : 32 ≤ l)
    {π : List (QLine (Fin (2 ^ l + 1) × Fin l))}
    (hπ : IsResLinQSynRefutation (BPHP (2 ^ l + 1) l) π)
    (short : 4 * (π.length : ℝ) + 1 ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2))) :
    ∃ (front tail : List (QLine (Fin (2 ^ l + 1) × Fin l))) (e f : QEq _) (C D : QLine _)
      (α β : ℤ), let R := (α • e.1 + β • f.1, α * e.2 + β * f.2) :: (C ++ D)
      π = front ++ (R :: tail) ∧ (e :: C) ∈ tail ∧ (f :: D) ∈ tail ∧ PrimitiveRankPair e f ∧
      ∃ a, LinEqSat a (qParity (qPrimitive e)) ∧ LinEqSat a (qParity (qPrimitive f)) ∧
        ¬ LinClauseSat a (projectLine (fun x => qParity (qPrimitive x)) R) := by
  let φ := fun (e : QEq (Fin (2 ^ l + 1) × Fin l)) => qParity (qPrimitive e)
  have bad : BadProjectedResolution φ π := by
    by_contra safe
    obtain ⟨ρ, hρ, len⟩ := projected_refutation_of_safe φ (by intro t; simp [φ])
      (fun e hz hn a => qParity_primitive_false a e hz hn) (collision_formula_nonempty l) hπ safe
    have upper : (ρ.length : ℝ) ≤ 4 * (π.length : ℝ) + 1 := by exact_mod_cast len
    have lower := L036 l ρ hl hρ
    linarith
  obtain ⟨front, tail, e, f, C, D, α, β, pos, left, right, a, he, hf, miss⟩ := bad
  have head := fun h => miss ((projectLine_sat φ a _).mpr ⟨_, List.mem_cons_self, h⟩)
  exact ⟨front, tail, e, f, C, D, α, β, pos, left, right,
    rank_pair_of_projection_failure a e f α β he hf head, a, he, hf, miss⟩

end PEqualNP.Search
