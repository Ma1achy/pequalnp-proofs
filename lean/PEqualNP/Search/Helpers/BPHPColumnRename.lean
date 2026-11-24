import PEqualNP.Search.Helpers.QSynRename

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Apply the same permutation of binary coordinates to every pigeon. -/
def columnEmbedding {l : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin l)) :
    (Fin m × Fin l) ↪ (Fin m × Fin l) :=
  (Function.Embedding.refl _).prodMap σ.toEmbedding

@[simp] theorem qRenameEq_column {m l : ℕ} (σ : Equiv.Perm (Fin l))
    (e : QEq (Fin m × Fin l)) (i : Fin m) (b : Fin l) :
    (qRenameEq (columnEmbedding m σ) e).1 (i,b) = e.1 (i,σ.symm b) := by
  simpa [columnEmbedding] using qRenameEq_at (columnEmbedding m σ) e (i,σ.symm b)

/-- The renamed proof derives the permuted lines from the same binary
pigeonhole clauses. Its encoded size is preserved by `qRenameProof_size`. -/
theorem bphp_column_rename {m l : ℕ} (σ : Equiv.Perm (Fin l))
    {π : List (QLine (Fin m × Fin l))} (d : IsResLinQSynDerivation (BPHP m l) π) :
    IsResLinQSynDerivation (BPHP m l) (qRenameProof (columnEmbedding m σ) π) := by
  apply qRename_derivation _ _ d
  rintro C ⟨i,j,a,ne,rfl⟩
  refine ⟨i,j,a ∘ σ.symm,ne,?_⟩
  have row (r : Fin m) :
      (Finset.univ.image (fun b : Fin l => ((r,σ b), !a b))) =
        Finset.univ.image (fun b : Fin l => ((r,b), !a (σ.symm b))) := by
    ext v
    constructor <;> intro h
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨σ b, Finset.mem_univ _, by simp⟩
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨σ.symm b, Finset.mem_univ _, by simp⟩
  simpa [qRenameClause, Finset.image_union, Finset.image_image, Function.comp_def,
    columnEmbedding] using congrArg₂ (· ∪ ·) (row i) (row j)

end PEqualNP.Search.Helpers
