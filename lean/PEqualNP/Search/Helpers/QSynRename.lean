import PEqualNP.Defs.SearchQSyn
import PEqualNP.Defs.ProofComplexityBit

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V W : Type}

/-- Rename variables in an integer equation, giving all unused variables coefficient zero. -/
noncomputable def qRenameEq (ι : V ↪ W) (e : QEq V) : QEq W :=
  (Function.extend ι e.1 0, e.2)

@[simp] theorem qRenameEq_at (ι : V ↪ W) (e : QEq V) (v : V) :
    (qRenameEq ι e).1 (ι v) = e.1 v :=
  ι.injective.extend_apply _ _ _

theorem qRenameEq_off (ι : V ↪ W) (e : QEq V) {w : W} (hw : w ∉ Set.range ι) :
    (qRenameEq ι e).1 w = 0 :=
  Function.extend_apply' _ _ _ hw

@[simp] theorem qRenameEq_rhs (ι : V ↪ W) (e : QEq V) : (qRenameEq ι e).2 = e.2 := rfl

@[simp] theorem qRenameEq_zero_iff (ι : V ↪ W) (e : QEq V) :
    (qRenameEq ι e).1 = 0 ↔ e.1 = 0 := by
  constructor
  · intro h
    funext v
    simpa only [qRenameEq_at, Pi.zero_apply] using congrFun h (ι v)
  · intro h
    funext w
    by_cases hw : w ∈ Set.range ι
    · obtain ⟨v,rfl⟩ := hw
      simp [h]
    · exact qRenameEq_off ι e hw

@[simp] theorem qRenameEq_lit [DecidableEq V] [DecidableEq W] (ι : V ↪ W) (t : V × Bool) :
    qRenameEq ι (litQEq t) = litQEq (ι t.1, t.2) := by
  refine Prod.ext ?_ (by rfl)
  funext w
  by_cases hw : w ∈ Set.range ι
  · obtain ⟨v,rfl⟩ := hw
    simp [litQEq]
  · have ne : w ≠ ι t.1 := fun h => hw ⟨t.1,h.symm⟩
    simp [qRenameEq_off ι _ hw, litQEq, ne]

@[simp] theorem qRenameEq_combo (ι : V ↪ W) (e f : QEq V) (α β : ℤ) :
    qRenameEq ι (α • e.1 + β • f.1, α*e.2 + β*f.2) =
      (α • (qRenameEq ι e).1 + β • (qRenameEq ι f).1, α*e.2 + β*f.2) := by
  refine Prod.ext ?_ (by rfl)
  funext w
  by_cases hw : w ∈ Set.range ι
  · obtain ⟨v,rfl⟩ := hw
    simp
  · simp [qRenameEq_off ι _ hw]

/-- Apply a variable injection to each equation of every line, in place. -/
noncomputable def qRenameProof (ι : V ↪ W) (π : List (QLine V)) : List (QLine W) :=
  π.map (List.map (qRenameEq ι))

@[simp] theorem qRenameProof_length (ι : V ↪ W) (π : List (QLine V)) :
    (qRenameProof ι π).length = π.length := by simp [qRenameProof]

theorem qRenameProof_mem (ι : V ↪ W) {π : List (QLine V)} {L : QLine V} (h : L ∈ π) :
    L.map (qRenameEq ι) ∈ qRenameProof ι π := List.mem_map_of_mem h

@[simp] theorem qRenameEq_size [Fintype V] [Fintype W] (ι : V ↪ W) (e : QEq V) :
    QEq.size (qRenameEq ι e) = QEq.size e := by
  classical
  let cost (w : W) := ((qRenameEq ι e).1 w).natAbs.size
  have sum : ∑ w, cost w = ∑ v, (e.1 v).natAbs.size := by
    calc
      ∑ w, cost w = ∑ w ∈ Finset.univ.map ι, cost w := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ h
        have ho : w ∉ Set.range ι := fun ⟨v,hv⟩ => h (Finset.mem_map.mpr ⟨v,Finset.mem_univ _,hv⟩)
        simp [cost, qRenameEq_off ι e ho]
      _ = _ := by simp [cost, Finset.sum_map]
  simp only [QEq.size, qRenameEq_rhs]
  rw [show (∑ w, ((qRenameEq ι e).1 w).natAbs.size) = ∑ v, (e.1 v).natAbs.size from sum]

@[simp] theorem qRenameProof_size [Fintype V] [Fintype W] (ι : V ↪ W) (π : List (QLine V)) :
    resLinQSize (qRenameProof ι π) = resLinQSize π := by
  simp [qRenameProof, resLinQSize, List.map_map, Function.comp_def]

/-- Map a literal clause along the same variable injection. -/
def qRenameClause [DecidableEq W] (ι : V ↪ W) (C : Clause V) : Clause W :=
  C.image (fun t => (ι t.1, t.2))

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem qRename_derivation (ι : V ↪ W) {F : Set (Clause V)} {G : Set (Clause W)}
    (transfer : ∀ C ∈ F, qRenameClause ι C ∈ G) {π : List (QLine V)}
    (der : IsResLinQSynDerivation F π) : IsResLinQSynDerivation G (qRenameProof ι π) := by
  induction der with
  | nil => exact .nil
  | ax C _ hC rep ih =>
    apply IsResLinQSynDerivation.ax (qRenameClause ι C) ih (transfer C hC)
    intro g
    constructor
    · rintro hg
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
      obtain ⟨t, ht, rfl⟩ := (rep _).mp he
      exact ⟨_, Finset.mem_image.mpr ⟨t,ht,rfl⟩, qRenameEq_lit ι t⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hy
      exact List.mem_map.mpr ⟨litQEq t, (rep _).mpr ⟨t,ht,rfl⟩, qRenameEq_lit ι t⟩
  | bool v _ ih =>
    simpa [qRenameProof] using IsResLinQSynDerivation.bool (ι v) ih
  | res α β _ h₁ h₂ ih =>
    simpa only [qRenameProof,List.map_cons,List.map_append,qRenameEq_combo,qRenameEq_rhs] using IsResLinQSynDerivation.res α β ih
      (qRenameProof_mem ι h₁) (qRenameProof_mem ι h₂)
  | weaken _ hC sub ih =>
    apply IsResLinQSynDerivation.weaken ih (qRenameProof_mem ι hC)
    intro _ he
    obtain ⟨e,hm,rfl⟩ := List.mem_map.mp he
    exact List.mem_map_of_mem (sub _ hm)
  | @simp π C _ hC ih =>
    have eq : (C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))).map (qRenameEq ι) =
        (C.map (qRenameEq ι)).filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) := by
      rw [List.filter_map]
      apply congrArg (List.map (qRenameEq ι))
      apply congrArg (fun (p : QEq V → Bool) => C.filter p)
      funext e
      simp only [Function.comp_apply, qRenameEq_zero_iff, qRenameEq_rhs]
    simpa only [qRenameProof,List.map_cons,eq] using
      IsResLinQSynDerivation.simp ih (qRenameProof_mem ι hC)

theorem qRename_refutation (ι : V ↪ W) {F : Set (Clause V)} {G : Set (Clause W)}
    (transfer : ∀ C ∈ F, qRenameClause ι C ∈ G) {π : List (QLine V)}
    (ref : IsResLinQSynRefutation F π) : IsResLinQSynRefutation G (qRenameProof ι π) :=
  ⟨qRename_derivation ι transfer ref.1, qRenameProof_mem ι ref.2⟩

/-- Rename the pigeon of a bit variable while retaining its bit index. -/
def rowEmbedding {N M : ℕ} (ι : Fin N ↪ Fin M) (l : ℕ) :
    (Fin N × Fin l) ↪ (Fin M × Fin l) :=
  ι.prodMap (Function.Embedding.refl _)

theorem bphp_rename_derivation {N M l : ℕ} (ι : Fin N ↪ Fin M)
    {π : List (QLine (Fin N × Fin l))} (d : IsResLinQSynDerivation (BPHP N l) π) :
    IsResLinQSynDerivation (BPHP M l) (qRenameProof (rowEmbedding ι l) π) := by
  apply qRename_derivation _ _ d
  rintro C ⟨i,j,a,ne,rfl⟩
  refine ⟨ι i,ι j,a,fun h => ne (ι.injective h),?_⟩
  simp [qRenameClause, Finset.image_union, Finset.image_image, rowEmbedding, Function.comp_def]

end PEqualNP.Search.Helpers
