import PEqualNP.Search.Helpers.Tree.Delayer

/-!
# Repeated input clauses in unfoldings of bit-PHP refutations

The Delayer lower bound applies to every bit length above its fixed threshold.
Composing consecutive semantic weakenings also makes it a lower bound on the
number of input-clause *occurrences*. Counting the possible collision clauses
then forces repeated copies of one and the same input.
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.ProofComplexity

/-- Quantitative Delayer bound at every sufficiently large bit length. -/
theorem bphp_tree_rate {N l : ℕ} (hl : 17 ≤ l) (t : ResLinQTree (BPHP N l) []) :
    2 ^ (2 ^ ((l - 17) / 6)) ≤ t.size := by
  set j := (l - 17) / 6 with hj
  apply tree_lower N (2 ^ j) (128 * (2 ^ j) ^ 2) Nat.one_le_two_pow (le_refl _) _ (by omega) t
  calc 8 * (128 * (2 ^ j) ^ 2 * 2 ^ j) ^ 2 = 2 ^ (6 * j + 17) := by
         rw [show (2 : ℕ) ^ (6 * j + 17) = 2 ^ 17 * (2 ^ j) ^ 6 by
           rw [← pow_mul, ← pow_add]; congr 1; ring]
         ring
       _ ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) (by omega)

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

/-- The input labels at the tree's leaves, including repeated uses of each clause. -/
def axiomUses : {L : QLine V} → ResLinQTree F L → List (PEqualNP.ProofComplexity.Clause V)
  | _, .ax C _ _ => [C]
  | _, .res _ _ s t => axiomUses s ++ axiomUses t
  | _, .weaken t _ => axiomUses t

private theorem uses_nonempty {L : QLine V} (t : ResLinQTree F L) : axiomUses t ≠ [] := by
  induction t <;> simp_all [axiomUses]

private theorem uses_input {L : QLine V} (t : ResLinQTree F L) :
    ∀ C ∈ axiomUses t, C ∈ F := by
  induction t with
  | ax C h _ => simpa [axiomUses]
  | res _ _ _ _ ih ih' =>
    intro C h
    rcases List.mem_append.mp h with hl | hr
    · exact ih C hl
    · exact ih' C hr
  | weaken _ _ ih => exact ih

/-- Compose all consecutive weakenings by carrying the implication to the
desired conclusion. An axiom costs at most two nodes, and a binary join costs
at most two nodes in addition to its children. -/
private theorem compress {L : QLine V} (t : ResLinQTree F L) :
    ∀ D : QLine V, (∀ a, QLine.Holds a L → QLine.Holds a D) →
    ∃ s : ResLinQTree F D, s.size + 2 ≤ 4 * (axiomUses t).length := by
  induction t with
  | ax C hc rep =>
    intro D goal
    exact ⟨.weaken (.ax C hc rep) goal, by simp [axiomUses, ResLinQTree.size]⟩
  | res α β s t ih ih' =>
    intro D goal
    obtain ⟨s', hs'⟩ := ih _ (fun _ h => h)
    obtain ⟨t', ht'⟩ := ih' _ (fun _ h => h)
    refine ⟨.weaken (.res α β s' t') goal, ?_⟩
    simp only [ResLinQTree.size, axiomUses, List.length_append]
    omega
  | weaken s step ih =>
    intro D goal
    exact ih D (fun a ha => goal a (step a ha))

/-- The large unfolding cannot be attributed entirely to unary rules. -/
theorem bphp_leaf_rate {N l : ℕ} (hl : 17 ≤ l) (t : ResLinQTree (BPHP N l) []) :
    2 ^ (2 ^ ((l - 17) / 6)) + 2 ≤ 4 * (axiomUses t).length := by
  obtain ⟨t', h⟩ := compress t [] (fun _ ha => ha)
  have := bphp_tree_rate hl t'
  omega

private def inputFamily (N l : ℕ) : Finset (PEqualNP.ProofComplexity.Clause (Fin N × Fin l)) :=
  Finset.univ.image fun v : Fin N × Fin N × (Fin l → Bool) =>
    Finset.univ.image (fun b : Fin l => ((v.1, b), !v.2.2 b)) ∪
    Finset.univ.image (fun b : Fin l => ((v.2.1, b), !v.2.2 b))

private theorem family_bound (N l : ℕ) : (inputFamily N l).card ≤ N * (N * 2 ^ l) := by
  unfold inputFamily
  apply Finset.card_image_le.trans
  simp

private theorem tree_max_uses {α : Type*} [DecidableEq α] (U : Finset α) (xs : List α)
    (hU : ∀ x ∈ xs, x ∈ U) (hne : xs ≠ []) :
    ∃ C ∈ U, xs.length ≤ U.card * xs.count C := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil xs hne
  obtain ⟨C, hC, hmax⟩ := U.exists_max_image (fun z => xs.count z) ⟨x, hU x hx⟩
  refine ⟨C, hC, ?_⟩
  have hsum : ∑ x ∈ U, xs.count x = xs.length :=
    by simpa using Multiset.sum_count_eq_card (m := (xs : Multiset α)) hU
  rw [← hsum]
  simpa using U.sum_le_card_nsmul (fun z => xs.count z) (xs.count C) hmax


/-- Some particular collision clause reappears at least the tree rate divided
by four times the number of ordered pigeon pairs and holes. -/
theorem bphp_repeated_input {N l : ℕ} (hl : 17 ≤ l) (t : ResLinQTree (BPHP N l) []) :
    ∃ C ∈ BPHP N l, 2 ^ (2 ^ ((l - 17) / 6)) + 2 ≤
      4 * (N * (N * 2 ^ l)) * (axiomUses t).count C := by
  classical
  let xs := axiomUses t
  have sub : ∀ C ∈ xs, C ∈ inputFamily N l := by
    intro C hm
    obtain ⟨i, j, α, _, he⟩ := uses_input t C hm
    exact Finset.mem_image.mpr ⟨(i, j, α), Finset.mem_univ _, he.symm⟩
  obtain ⟨C, hC, hN⟩ := tree_max_uses (inputFamily N l) xs sub (uses_nonempty t)
  have hc : C ∈ xs := by
    by_contra h
    rw [List.count_eq_zero.mpr h, Nat.mul_zero, Nat.le_zero, List.length_eq_zero_iff] at hN
    exact uses_nonempty t hN
  refine ⟨C, uses_input t C hc, ?_⟩
  calc 2 ^ (2 ^ ((l - 17) / 6)) + 2 ≤ 4 * xs.length := bphp_leaf_rate hl t
       _ ≤ 4 * ((inputFamily N l).card * xs.count C) := Nat.mul_le_mul_left _ hN
       _ ≤ 4 * ((N * (N * 2 ^ l)) * xs.count C) :=
         Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (family_bound N l))
       _ = _ := by ring

end PEqualNP.Search.Helpers.Tree
