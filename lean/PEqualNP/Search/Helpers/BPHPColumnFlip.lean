import PEqualNP.Search.Helpers.QFlip
import PEqualNP.Search.BPHPPermutationReduction

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- All bit positions in one column of the pigeon matrix. -/
def columnMask {l : ℕ} (m : ℕ) (b : Fin l) : Finset (Fin m × Fin l) :=
  Finset.univ.filter (fun v => v.2 = b)

@[simp] theorem mem_columnMask {m l : ℕ} (b : Fin l) (v : Fin m × Fin l) :
    v ∈ columnMask m b ↔ v.2 = b := by simp [columnMask]

theorem bphp_column_flip {m l : ℕ} (b : Fin l) {π : List (QLine (Fin m × Fin l))}
    (d : IsResLinQSynDerivation (BPHP m l) π) :
    ∃ σ, IsResLinQSynDerivation (BPHP m l) σ ∧
      (∀ L ∈ π, L.map (qFlipEq (columnMask m b)) ∈ σ) ∧ resLinQSize σ ≤ 3 * resLinQSize π := by
  apply flip_derivation _ _ d
  rintro C ⟨i,j,a,ne,rfl⟩
  refine ⟨i,j,(fun k => if k=b then !(a k) else a k),ne,?_⟩
  have row (r : Fin m) (k : Fin l) :
      flipLiteral (columnMask m b) ((r,k),!a k) = ((r,k), !(if k=b then !a k else a k)) := by
    by_cases h : k=b <;> simp [flipLiteral,h]
  simp only [Finset.image_union,Finset.image_image,Function.comp_def,row]

theorem qFlipCut_column {m l : ℕ} (b : Fin l) (e : QEq (Fin m × Fin l)) :
    qFlipCut (columnMask m b) e =
      (fun v => if v.2 = b then 2 * e.1 v else 0, ∑ i, e.1 (i,b)) := by
  apply Prod.ext
  · funext v
    simp [qFlipCut]
  · simp [qFlipCut,columnMask,Finset.sum_filter,Fintype.sum_prod_type]

/-- From a singleton equation in a binary pigeonhole proof, isolate any one
column. This also applies to balanced instances and arbitrary row coefficients. -/
theorem bphp_isolate_column {m l : ℕ} (b : Fin l) {π : List (QLine (Fin m × Fin l))}
    {e : QEq (Fin m × Fin l)} (d : IsResLinQSynDerivation (BPHP m l) π) (unit : [e] ∈ π) :
    ∃ σ, IsResLinQSynDerivation (BPHP m l) σ ∧
      ([(fun v => if v.2 = b then 2 * e.1 v else 0, ∑ i, e.1 (i,b))] : QLine _) ∈ σ ∧
      resLinQSize σ ≤ 7 * resLinQSize π := by
  let U := columnMask m b
  obtain ⟨τ, dτ, copy, budget⟩ := bphp_column_flip b d
  have flipped : [qFlipEq U e] ∈ τ := copy _ unit
  let ρ := π ++ τ
  have orig : [e] ∈ ρ := List.mem_append_left _ unit
  have next : [qFlipEq U e] ∈ ρ := List.mem_append_right _ flipped
  have deriv := (qAppendDerivations d dτ).res 1 (-flipSign U e) orig next
  change IsResLinQSynDerivation _ ([_] :: ρ) at deriv
  rw [qFlipCut_resolution] at deriv
  refine ⟨_,deriv,?_,?_⟩
  · rw [← qFlipCut_column]; exact List.mem_cons_self
  · have he := qCost_le_of_mem unit
    have hc := qFlipCut_size U e
    have base : resLinQSize ρ = resLinQSize π + resLinQSize τ := by simp [ρ,resLinQSize]
    rw [qSize_cons,base]
    change 1 + ((qFlipCut U e).size + 0) + _ ≤ _
    change 1 + (e.size + 0) ≤ _ at he
    omega

end PEqualNP.Search.Helpers
