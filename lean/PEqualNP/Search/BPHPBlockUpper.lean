import PEqualNP.Search.BPHPBlockStep
import PEqualNP.Search.Helpers.BlockCapacityTerminal
import PEqualNP.Search.Helpers.BlockBudget
import PEqualNP.Search.Helpers.BlockTerminalBudget
import PEqualNP.Search.Helpers.QFiniteAssembly
import PEqualNP.Search.Helpers.BPHPBlockRate
import PEqualNP.Search.BPHPTreeUpper

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

private theorem exponent_charge (b g : ℕ) : g+64*(b+1)+1 ≤ 128*(b+g+2) := by omega

/-- Compose the count-vector states in rank order, then eliminate the
overloaded prefix in the final state. Every earlier state is stored once. -/
theorem bphp_block_refutation (u v : ℕ) (hu : 0 < u) :
    ∃ π, IsResLinQSynRefutation (BPHP (2^(u+v)+1) (u+v)) π ∧
      resLinQSize π ≤ (2^(u+v)+2)^(128*(2^v + 2^u + 2)) := by
  let n := 2^(u+v)
  let b := 2^v
  let g := 2^u
  let D := n+2
  let B := D^(64*(b+1))
  let pred (s t : BlockCounts u v) := ∃ h, 0 < (t h).val ∧ s = blockPred t h
  have lower (s t) (edge : pred s t) : blockRank s < blockRank t := by
    obtain ⟨h,pos,rfl⟩ := edge
    have := blockRank_pred t h pos
    omega
  have step (t : BlockCounts u v) :
      QCanAdd (BPHP (n+1) (u+v)) {L | ∃ s, pred s t ∧ L = blockState s} (blockState t) B := by
    intro π d havePred
    obtain ⟨τ,dτ,mem,cost⟩ := blockState_step hu t π d (by
      rintro L ⟨h,pos,rfl⟩
      exact havePred _ ⟨blockPred t h,⟨h,pos,rfl⟩,rfl⟩)
    exact ⟨τ,dτ,mem,cost.trans (blockTransitionCost_le u v)⟩
  obtain ⟨π,d,mem,cost⟩ := qFiniteAssembly blockState blockRank pred lower B step
  let L := blockCapacityLine (m := n+1) v (blockRank (blockFull u v)+1) (fun _ : Fin u → Bool => b)
  have root : L ∈ π := mem (blockFull u v)
  obtain ⟨σ,dσ,empty,extra⟩ := drop_block_capacity_line v (blockRank (blockFull u v)+1) d root
  have weight : qWeight L ≤ blockStateWeightCap u v :=
    blockCapacityLine_weight v _ (fun _ => b) b (fun _ => le_rfl)
  have close : resLinQSize σ ≤ B := extra.trans (block_terminal_budget u v (qWeight L)
    L.length (qLength_le_weight L) weight)
  rw [blockCounts_card] at cost
  change resLinQSize π ≤ (b+1)^g * B at cost
  have bg : b ≤ n := Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have bd : b+1 ≤ D := by dsimp [D]; omega
  have power : (b+1)^g ≤ D^g := Nat.pow_le_pow_left bd _
  have dpos : 0 < D := Nat.succ_pos _
  have one : 1 ≤ D^g := Nat.one_le_pow _ _ dpos
  have larger : B ≤ D^g*B := by simpa only [one_mul] using Nat.mul_le_mul_right B one
  have two : 2 ≤ D := Nat.le_add_left 2 n
  refine ⟨σ++π,⟨dσ,empty⟩,?_⟩
  have append : resLinQSize (σ++π) = resLinQSize σ + resLinQSize π := by
    simp only [resLinQSize,List.map_append,List.sum_append]
    rfl
  rw [append]
  calc
    _ ≤ D^g*B + D^g*B := Nat.add_le_add (close.trans larger) (cost.trans (Nat.mul_le_mul_right _ power))
    _ = 2*(D^g*B) := (two_mul _).symm
    _ ≤ D*(D^g*B) := Nat.mul_le_mul_right _ two
    _ = D^(g+64*(b+1)+1) := by rw [pow_succ, pow_add, Nat.mul_comm D]
    _ ≤ _ := Nat.pow_le_pow_right dpos (exponent_charge b g)

/-- Balanced prefix and suffix lengths give a subexponential encoded-size
upper bound for unrestricted syntactic integer refutations. -/
theorem BPHPBlockUpper :
    ∀ l : ℕ, ∃ π : List (QLine (Fin (2^l+1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2^l+1) l) π ∧
      resLinQSize π ≤ 2^(512*(l+2)*2^((l+1)/2)) := by
  intro l
  by_cases small : l ≤ 1
  · obtain ⟨π,d,_,bound⟩ := BPHPTreeUpper l
    refine ⟨π,d,bound.trans ?_⟩
    calc
      _ ≤ 2^12 := by interval_cases l <;> decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        have h : 1 ≤ 2^((l+1)/2) := Nat.one_le_two_pow
        calc
          12 ≤ 512*(l+2) := by omega
          _ ≤ _ := Nat.le_mul_of_pos_right _ h)
  · let u := l/2
    let v := l-u
    have hu : 0 < u := by dsimp [u]; omega
    have split : u+v = l := by dsimp [v,u]; omega
    have raw := bphp_block_refutation u v hu
    rw [split] at raw
    obtain ⟨π,d,cost⟩ := raw
    exact ⟨π,d,cost.trans (bphp_block_envelope l)⟩

end PEqualNP.Search
