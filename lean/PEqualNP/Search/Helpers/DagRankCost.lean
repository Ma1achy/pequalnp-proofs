import PEqualNP.Search.Helpers.DagUnfoldBound

/-! A rank increasing only at reused premises controls unfolding even when
different paths branch to many unrelated shared vertices. -/

namespace PEqualNP.Search.Helpers

/-- A rank can stay fixed along a singly referenced dependency. It must increase
along an edge into a multiply referenced dependency. Only active vertices pay. -/
theorem dag_cost_le_by_rank {n : ℕ} (parents : Fin n → List (Fin n))
    (order : ∀ i j, j ∈ parents i → i < j) (arity : ∀ i, (parents i).length ≤ 2)
    (cost : Fin n → ℕ) (c : ℕ) (rec : ∀ i, cost i ≤ c + ((parents i).map cost).sum)
    (root : Fin n) (active : Fin n → Prop) (init : active root)
    (closed : ∀ i j, active i → j ∈ parents i → active j)
    (rank : Fin n → ℕ)
    (mono : ∀ i j, active i → j ∈ parents i → rank i ≤ rank j)
    (inc : ∀ i j, active i → j ∈ parents i → 2 ≤ dagUses parents j → rank i < rank j)
    (K : ℕ) (cap : ∀ i, active i → rank i ≤ K) :
    cost root ≤ c * n * (2*n+1)^K := by
  classical
  let B := 2*n+1
  let w (i : Fin n) := if active i ∧ root ≤ i then B ^ rank i else 0
  have bpos : 0 < B := by dsimp [B]; omega
  have charge (i : Fin n) : dagUses parents i ≤ 2*n := by
    calc
      _ ≤ ∑ j : Fin n, 2 := Finset.sum_le_sum fun j _ =>
        (List.count_le_length (a := i) (l := parents j)).trans (arity j)
      _ = _ := by simp [Nat.mul_comm]
  have balance (i : Fin n) : (if i = root then 1 else 0) +
      (∑ j, w j * (parents j).count i) ≤ w i := by
    by_cases hi : i = root
    · subst i
      have noPay (j : Fin n) : w j * (parents j).count root = 0 := by
        by_cases e : root ∈ parents j
        · have := order j root e
          simp [w, not_le.mpr this]
        · simp [List.count_eq_zero.mpr e]
      simp [noPay, w, init, Nat.one_le_pow _ _ bpos]
    · simp only [ite_eq_right hi, Nat.zero_add]
      let m := max 1 (dagUses parents i)
      have hm : 0 < m := by dsimp [m]; omega
      have pay (j : Fin n) : (w j * (parents j).count i) * m ≤ w i * (parents j).count i := by
        by_cases e : i ∈ parents j
        · by_cases live : active j ∧ root ≤ j
          · have up : active i ∧ root ≤ i := ⟨closed j i live.1 e, live.2.trans (order j i e).le⟩
            have bound : w j * m ≤ w i := by
              simp only [w, ite_eq_left live, ite_eq_left up]
              by_cases h : 2 ≤ dagUses parents i
              · calc
                  B ^ rank j * m ≤ B ^ rank j * B := by
                    apply Nat.mul_le_mul_left
                    have := charge i
                    dsimp [m, B]
                    omega
                  _ = B ^ (rank j + 1) := (pow_succ _ _).symm
                  _ ≤ _ := Nat.pow_le_pow_right bpos (inc _ _ live.1 e h)
              · have eq : m = 1 := by dsimp [m]; omega
                simpa [eq] using Nat.pow_le_pow_right bpos (mono _ _ live.1 e)
            simpa only [Nat.mul_right_comm (w j)] using Nat.mul_le_mul_right ((parents j).count i) bound
          · simp [w, live]
        · simp [List.count_eq_zero.mpr e]
      apply Nat.le_of_mul_le_mul_right (c := m) _ hm
      calc
        (∑ j, w j * (parents j).count i) * m = ∑ j, w j * (parents j).count i * m := Finset.sum_mul ..
        _ ≤ ∑ j, w i * (parents j).count i := Finset.sum_le_sum (fun j _ => pay j)
        _ = w i * dagUses parents i := (Finset.mul_sum ..).symm
        _ ≤ w i * m := Nat.mul_le_mul_left _ (le_max_right _ _)
  have sumBound : (∑ i, w i) ≤ n * B ^ K := by
    calc
      _ ≤ ∑ _ : Fin n, B ^ K := Finset.sum_le_sum (fun i _ => by
        by_cases hi : active i ∧ root ≤ i
        · simpa [w, hi] using Nat.pow_le_pow_right bpos (cap i hi.1)
        · simp [w, hi])
      _ = _ := by simp
  simpa only [Nat.mul_assoc] using (dag_unfold_cost_le_of_weights parents cost c rec root w balance).trans
    (Nat.mul_le_mul_left c sumBound)

end PEqualNP.Search.Helpers
