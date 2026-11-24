import PEqualNP.Search.BPHPPermutationReduction
import PEqualNP.Search.Helpers.BPHPColumnRename

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- A single prescribed bit is set in exactly b rows. -/
def columnBalance {m l : ℕ} (j : Fin l) (b : ℕ) : QEq (Fin m × Fin l) :=
  (fun v => if v.2 = j then 1 else 0, b)

private def prefixBalance {m l : ℕ} (k b : ℕ) : QEq (Fin m × Fin l) :=
  (fun v => if v.2.val < k then (2 : ℤ)^v.2.val else 0, (b : ℤ) * ((2 : ℤ)^k - 1))

private theorem prefix_step {m l : ℕ} (k b : ℕ) (hk : k < l) :
    ((1 : ℤ) • (prefixBalance (m := m) (l := l) k b).1 +
      (2 : ℤ)^k • (columnBalance (m := m) (⟨k,hk⟩ : Fin l) b).1,
      (1 : ℤ) * (prefixBalance (m := m) (l := l) k b).2 +
      (2 : ℤ)^k * (columnBalance (m := m) (⟨k,hk⟩ : Fin l) b).2)
      = prefixBalance (k+1) b := by
  apply Prod.ext
  · funext v
    rcases v with ⟨i,j⟩
    by_cases e : j.val = k
    · have h : j = ⟨k,hk⟩ := Fin.ext e
      simp [prefixBalance, columnBalance, h]
    · have h : j ≠ ⟨k,hk⟩ := fun h => e (congrArg Fin.val h)
      have hj : j.val ≤ k ↔ j.val < k := by omega
      simp [prefixBalance, columnBalance, h, hj]
  · simp [prefixBalance, columnBalance, pow_succ]
    ring

private theorem prefix_cost {l k b : ℕ} (hk : k ≤ l) (hb : b ≤ 2^l) :
    resLinQSize [[prefixBalance (m := 2^l) (l := l) k b]] ≤
      2 + 2^l*l*2^l + 2^l*(2^l+1) := by
  let n := 2^l
  have bits (v : Fin n × Fin l) : ((prefixBalance k b).1 v).natAbs.size ≤ n := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    simp only [prefixBalance]
    split_ifs
    · simp only [Int.natAbs_pow]
      exact Nat.pow_le_pow_right (by decide) v.2.isLt.le
    · exact Nat.zero_le _
  have sum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n × Fin l))) (fun v _ => bits v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul] at sum
  have rhs : ((prefixBalance (m := n) (l := l) k b).2).natAbs.size ≤ n*(n+1) := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    change ((b : ℤ)*((2 : ℤ)^k - 1)).natAbs ≤ _
    rw [Int.natAbs_mul]
    apply Nat.mul_le_mul hb
    apply (Int.natAbs_sub_le _ _).trans
    simp only [Int.natAbs_pow, Int.natAbs_one]
    exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) hk) 1
  change resLinQSize [[prefixBalance (m := n) (l := l) k b]] ≤ 2 + n*l*n + n*(n+1)
  simp only [resLinQSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,QEq.size]
  simpa only [← Nat.add_assoc, Nat.cast_id, Nat.reduceAdd] using Nat.add_le_add (Nat.add_le_add_left sum 2) rhs

/-- Accumulate independent column balances as binary-weighted singleton lines.
The trace contains the original proofs and one addition for each included bit. -/
theorem binaryTotal_of_column_derivations {l : ℕ} (hl : 0 < l) (b S : ℕ) (hb : b ≤ 2^l)
    (cols : ∀ j : Fin l, ∃ π : List (QLine (Fin (2^l) × Fin l)),
      IsResLinQSynDerivation (BPHP (2^l) l) π ∧ [columnBalance j b] ∈ π ∧ resLinQSize π ≤ S) :
    ∃ π : List (QLine (Fin (2^l) × Fin l)), IsResLinQSynDerivation (BPHP (2^l) l) π ∧
      [binaryTotal ((b : ℤ) * ((2 : ℤ)^l - 1))] ∈ π ∧
      resLinQSize π ≤ (l+1)*(S + (2 + 2^l*l*2^l + 2^l*(2^l+1))) := by
  let V := Fin (2^l) × Fin l
  let B := 2 + 2^l*l*2^l + 2^l*(2^l+1)
  have aux (k : ℕ) (hk : k ≤ l) : ∃ π : List (QLine V), IsResLinQSynDerivation (BPHP (2^l) l) π ∧
      [prefixBalance k b] ∈ π ∧ resLinQSize π ≤ (k+1)*(S+B) := by
    induction k with
    | zero =>
      obtain ⟨π,d,hm,cost⟩ := cols ⟨0,hl⟩
      have step := d.res 0 0 hm hm
      have zero : prefixBalance (m := 2^l) (l := l) 0 b = (0,0) := by
        apply Prod.ext <;> simp [prefixBalance, Pi.zero_def]
      have done : IsResLinQSynDerivation (BPHP (2^l) l) ([prefixBalance 0 b] :: π) := by
        simpa [zero] using step
      refine ⟨_,done,List.mem_cons_self,?_⟩
      have extra := prefix_cost (k := 0) (Nat.zero_le l) hb
      change resLinQSize [[prefixBalance (m := 2^l) (l := l) 0 b]] ≤ B at extra
      have add : resLinQSize ([prefixBalance (m := 2^l) (l := l) 0 b] :: π) =
          resLinQSize [[prefixBalance (m := 2^l) (l := l) 0 b]] + resLinQSize π := by simp [resLinQSize]
      omega
    | succ k ih =>
      have lt : k < l := hk
      obtain ⟨π,d,hm,cost⟩ := ih lt.le
      obtain ⟨τ,col,hcol,small⟩ := cols ⟨k,lt⟩
      have both := qAppendDerivations d col
      have step := both.res 1 ((2 : ℤ)^k) (List.mem_append_left _ hm) (List.mem_append_right _ hcol)
      have done : IsResLinQSynDerivation (BPHP (2^l) l) ([prefixBalance (k+1) b] :: (π ++ τ)) := by
        simpa only [List.nil_append, prefix_step] using step
      refine ⟨_,done,List.mem_cons_self,?_⟩
      have extra := prefix_cost hk hb
      change resLinQSize [[prefixBalance (m := 2^l) (l := l) (k+1) b]] ≤ B at extra
      have add : resLinQSize ([prefixBalance (m := 2^l) (l := l) (k+1) b] :: (π ++ τ)) =
          resLinQSize [[prefixBalance (m := 2^l) (l := l) (k+1) b]] + resLinQSize π + resLinQSize τ := by
        simp only [resLinQSize, List.map_cons, List.map_nil, List.sum_nil, List.sum_cons, List.map_append, List.sum_append, Nat.add_zero, Nat.add_assoc]
        rfl
      rw [Nat.succ_mul]
      omega
  obtain ⟨π,d,hm,cost⟩ := aux l le_rfl
  have last : prefixBalance (m := 2^l) (l := l) l b = binaryTotal ((b : ℤ)*((2 : ℤ)^l-1)) := by
    apply Prod.ext
    · funext v
      simp [prefixBalance,binaryTotal]
    · rfl
  exact ⟨π,d,last ▸ hm,cost⟩

/-- A balanced proof for just one predetermined column suffices. Bit permutations
supply the other columns at the same cost, so weighted addition followed by
the two omitted-row proofs gives a refutation of the unbalanced instance. -/
theorem bphp_refutation_of_one_column {l : ℕ} (j : Fin l) (b : ℕ) (hb : b ≤ 2^l)
    {π : List (QLine (Fin (2^l) × Fin l))} (d : IsResLinQSynDerivation (BPHP (2^l) l) π)
    (unit : [columnBalance j b] ∈ π) :
    ∃ ρ, IsResLinQSynRefutation (BPHP (2^l+1) l) ρ ∧
      resLinQSize ρ ≤ 2*(l+1)*(resLinQSize π + (2 + 2^l*l*2^l + 2^l*(2^l+1))) + 403*(2^l+1)^6 := by
  have cols (k : Fin l) : ∃ τ : List (QLine (Fin (2^l) × Fin l)),
      IsResLinQSynDerivation (BPHP (2^l) l) τ ∧ [columnBalance k b] ∈ τ ∧ resLinQSize τ ≤ resLinQSize π := by
    let σ := Equiv.swap j k
    have eqn : qRenameEq (columnEmbedding (2^l) σ) (columnBalance j b) = columnBalance k b := by
      apply Prod.ext
      · funext v
        rcases v with ⟨i,t⟩
        rw [qRenameEq_column]
        have h : σ.symm t = j ↔ t = k := by
          rw [Equiv.symm_apply_eq]
          simp [σ]
        simp [columnBalance,h]
      · rfl
    refine ⟨_,bphp_column_rename σ d,?_,(qRenameProof_size _ _).le⟩
    simpa only [List.map_cons, List.map_nil, eqn] using qRenameProof_mem (columnEmbedding (2^l) σ) unit
  obtain ⟨τ,dτ,total,cost⟩ := binaryTotal_of_column_derivations (Nat.zero_lt_of_lt j.isLt) b _ hb cols
  obtain ⟨ρ,ref,price⟩ := BPHPPermutationReduction l _ dτ total
  refine ⟨ρ,ref,price.trans ?_⟩
  rw [Nat.mul_assoc 2]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 cost) _

end PEqualNP.Search
