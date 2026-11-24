import PEqualNP.Search.Helpers.BPHPColumnFlip
import PEqualNP.Search.Helpers.QPaddedDeduction

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Flip any set of columns in one substitution, so the bound is independent
of the number of selected columns. -/
theorem bphp_flip_columns {m l : ℕ} (bits : Fin l → Bool)
    {π : List (QLine (Fin m × Fin l))} (d : IsResLinQSynDerivation (BPHP m l) π) :
    let U := Finset.univ.filter (fun v : Fin m × Fin l => bits v.2)
    ∃ σ, IsResLinQSynDerivation (BPHP m l) σ ∧ (∀ L ∈ π, L.map (qFlipEq U) ∈ σ) ∧
      resLinQSize σ ≤ 3 * resLinQSize π := by
  intro U
  apply flip_derivation _ _ d
  rintro C ⟨i,j,a,ne,rfl⟩
  refine ⟨i,j,(fun k => if bits k then !(a k) else a k),ne,?_⟩
  have row (r : Fin m) (k : Fin l) :
      flipLiteral U ((r,k),!a k) = ((r,k), !(if bits k then !a k else a k)) := by
    cases h : bits k <;> simp [flipLiteral,U,h]
  simp only [Finset.image_union,Finset.image_image,Function.comp_def,row]

/-- If one pigeon provably differs from zero, then symmetry rules out every
value for that pigeon. Branching on its bits derives the empty line. -/
theorem bphp_refutation_of_row_blocker {m l : ℕ} (i : Fin m) {ρ : List (QLine (Fin m × Fin l))}
    (d : IsResLinQSynDerivation (BPHP m l) ρ)
    (hm : (List.ofFn (fun b : Fin l => litQEq ((i,b),true))).reverse ∈ ρ) :
    ∃ π, IsResLinQSynRefutation (BPHP m l) π ∧
      resLinQSize π ≤ 2^l * (3 * resLinQSize ρ + 10 * (4*l + 1)) := by
  let vs := List.ofFn (fun b : Fin l => (i,b))
  have distinct : vs.Nodup := List.nodup_ofFn_ofInjective (fun _ _ h => congrArg Prod.snd h)
  have leaves (a : Fin m × Fin l → Bool) :
      QCanAdd (BPHP m l) ∅ ((vs.map (fun v => litQEq (v,a v))).reverse ++ []) (3*resLinQSize ρ) := by
    let bits (b : Fin l) := !a (i,b)
    let U := Finset.univ.filter (fun v : Fin m × Fin l => bits v.2)
    obtain ⟨σ, dσ, rep, cost⟩ := bphp_flip_columns bits d
    apply QCanAdd.of_derivation dσ _ cost
    have same (b : Fin l) : qFlipEq U (litQEq ((i,b),true)) = litQEq ((i,b),a (i,b)) := by
      cases h : a (i,b) <;> simp [flipLiteral,U,bits,h]
    have mapped := rep _ hm
    change List.map (qFlipEq U) _ ∈ σ at mapped
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def,vs,same,List.append_nil] using mapped
  obtain ⟨σ,ds,mem,cost⟩ := qCoordinateCases vs distinct [] (3*resLinQSize ρ) leaves [] .nil (by simp)
  exact ⟨σ,⟨by simpa using ds,mem⟩,by simpa [vs] using cost⟩

end PEqualNP.Search.Helpers
