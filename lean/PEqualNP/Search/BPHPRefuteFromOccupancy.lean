import PEqualNP.Search.Helpers.BPHPZeroRowCut
import PEqualNP.Search.Helpers.BPHPBlockerFlip

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

private theorem renamed_zero_row {m l : ℕ} (i : Fin m) :
    qRenameEq (keepRows m l) (binaryRowCoeff i,0) = (binaryRowCoeff i.castSucc,0) := by
  refine Prod.ext ?_ (by rfl)
  funext ⟨r,b⟩
  rcases Fin.eq_castSucc_or_eq_last r with ⟨z,rfl⟩|rfl
  · change (qRenameEq (keepRows m l) _).1 ((keepRows m l) (z,b)) = _
    rw [qRenameEq_at]
    simp [binaryRowCoeff]
  · have outside : (Fin.last m,b) ∉ Set.range (keepRows m l) := by
      rintro ⟨⟨r,c⟩,eq⟩
      exact Fin.castSucc_ne_last r (congrArg Prod.fst eq)
    rw [qRenameEq_off _ _ outside]
    simp [binaryRowCoeff,Ne.symm (Fin.castSucc_ne_last i)]

/-- A proof that hole zero is occupied when the pigeon and hole counts agree
yields a refutation after adding one more pigeon, at polynomial encoded cost. -/
theorem bphp_refute_from_occupancy {l : ℕ}
    {ρ : List (QLine (Fin (2^l) × Fin l))} (d : IsResLinQSynDerivation (BPHP (2^l) l) ρ)
    (mem : zeroOccupancyLine (2^l) l ∈ ρ) :
    ∃ π, IsResLinQSynRefutation (BPHP (2^l+1) l) π ∧
      resLinQSize π ≤ 4000*(2^l+1)^7*(resLinQSize ρ+1) := by
  let n := 2^l
  let S := resLinQSize ρ
  let j := Fin.last n
  let G := rowBlock (l := l) j (fun _ => true)
  let τ := qRenameProof (keepRows n l) ρ
  let L := (zeroOccupancyLine n l).map (qRenameEq (keepRows n l))
  have dt : IsResLinQSynDerivation (BPHP (n+1) l) τ := bphp_rename_derivation Fin.castSuccEmb d
  have hm : L ∈ τ := qRenameProof_mem _ mem
  have wL : qWeight L ≤ S := (Nat.le_add_left _ 1).trans ((qCost_le_of_mem hm).trans_eq
    (qRenameProof_size _ _))
  have wG : qWeight G ≤ 4*l := rowBlock_weight j _
  have len : L.length = n := by simp [L,zeroOccupancyLine]
  have boundPos : resLinQSize ((L++G)::τ) ≤ (1+S+4*l)+S := by
    rw [qSize_cons,qCost_append,show resLinQSize τ = S from qRenameProof_size _ _]
    change 1+qWeight L+qWeight G+S ≤ _
    omega
  have raw : IsResLinQSynDerivation (BPHP (n+1) l) ((L++G)::τ) :=
    .weaken dt hm (fun _ he => List.mem_append_left _ he)
  have exactRows (e) (he : e ∈ L) : ∃ i : Fin (n+1), i ≠ j ∧ e = (binaryRowCoeff i,0) := by
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact ⟨i.castSucc,Fin.castSucc_ne_last i,renamed_zero_row i⟩
  obtain ⟨σ,ds,blocked,cost⟩ := bphp_drop_zero_rows j L exactRows raw List.mem_cons_self
  have pos : (List.ofFn (fun b : Fin l => litQEq ((j,b),true))).reverse ∈ σ++((L++G)::τ) := by
    simpa only [rowBlock,rowVars,List.map_ofFn,Function.comp_def] using blocked
  obtain ⟨π,r,hπ⟩ := bphp_refutation_of_row_blocker j ds pos
  refine ⟨π,r,hπ.trans ?_⟩
  have hl : l ≤ n := Nat.lt_two_pow_self.le
  have size : resLinQSize (σ++((L++G)::τ)) = resLinQSize σ + resLinQSize ((L++G)::τ) := by
    simp only [resLinQSize,List.map_append,List.sum_append]
  have bσ : resLinQSize σ ≤ n*(n*((4*n+3)*(10+(n+1)*n*n+n*n+4*n+(S+4*n))+
      10*((S+4*n)+4*n+1))) := by
    apply cost.trans
    rw [len]
    unfold zeroRowCutCost
    change n*(n*((4*l+3)*(10+(n+1)*l*n+l*n+4*l+(qWeight L+4*l))+
      10*((qWeight L+4*l)+4*l+1))) ≤ _
    gcongr
  rw [size]
  change n*(3*(resLinQSize σ+resLinQSize ((L++G)::τ))+10*(4*l+1)) ≤ 4000*(n+1)^7*(S+1)
  calc
    _ ≤ n*(3*((n*(n*((4*n+3)*(10+(n+1)*n*n+n*n+4*n+(S+4*n))+10*((S+4*n)+4*n+1))))+
        ((1+S+4*n)+S))+10*(4*n+1)) := by
      have hτ := boundPos.trans (show (1+S+4*l)+S ≤ (1+S+4*n)+S by omega)
      gcongr
    _ ≤ _ := by ring_nf; omega

end PEqualNP.Search
