import PEqualNP.Search.Helpers.BlockTupleHolds
import PEqualNP.Search.Helpers.BlockCapacityState
import PEqualNP.Search.Helpers.BPHPZeroRowCut
import Mathlib.Data.Fintype.Pigeonhole

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- Cost of removing a single tuple of r pigeons by branching on their l-bit labels. -/
def blockDropCost (m l r w : ℕ) : ℕ :=
  let q := r*l
  2^q * ((4*q+3)*(10 + m*l + 6*q + 8*l + w) + 10*(w+4*q+1))

private theorem collision_in_block {m u v : ℕ} (S : Finset (Fin m)) (h : Fin u → Bool)
    (overflow : 2^v < S.card) (p : Fin m × Fin (u+v) → Bool)
    (holds : QEq.Holds p (blockTupleEq v S h)) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ ∀ k, p (i,k) = p (j,k) := by
  classical
  have headBits := (blockTupleEq_holds v p S h).mp holds
  let suffix (i : ↥S) (k : Fin v) := p (i,Fin.natAdd u k)
  obtain ⟨i,j,ne,eqn⟩ := Fintype.exists_ne_map_eq_of_card_lt suffix (by simpa using overflow)
  refine ⟨i,i.property,j,j.property,fun eq => ne (Subtype.ext eq),?_⟩
  intro k
  refine Fin.addCases (fun b => (headBits i i.property b).trans (headBits j j.property b).symm)
    (fun b => ?_) k
  exact congrFun eqn b

private theorem drop_block_tuple {m u v : ℕ} (S : Finset (Fin m)) (h : Fin u → Bool)
    (overflow : 2^v < S.card) (D : QLine (Fin m × Fin (u+v))) :
    QCanAdd (BPHP m (u+v)) {blockTupleEq v S h :: D} D
      (blockDropCost m (u+v) S.card (qWeight D)) := by
  classical
  let l := u+v
  let vs := (S ×ˢ (Finset.univ : Finset (Fin l))).toList
  let q := S.card*l
  have len : vs.length = q := by simp [vs,q]
  have memvs (x : Fin m × Fin l) : x ∈ vs ↔ x.1 ∈ S := by simp [vs]
  let cap := (4*q+3)*(10 + m*l + 6*q + 8*l + qWeight D)
  have step := qCoordinateCases (F := BPHP m (u+v))
    (Γ := ({blockTupleEq v S h :: D} : Set (QLine _))) vs (Finset.nodup_toList _) D cap
  apply (by simpa [blockDropCost,cap,q,len,l] using step)
  intro a ρ d base
  let p : Fin m × Fin l → Bool := fun x => !a x
  let G := (vs.map (fun x => litQEq (x,a x))).reverse
  change ∃ σ, IsResLinQSynDerivation _ (σ++ρ) ∧ G++D ∈ σ ∧ resLinQSize σ ≤ cap
  have guard (x : Fin m × Fin l) (hx : x ∈ vs) : litQEq (x,a x) ∈ G :=
    List.mem_reverse.mpr (List.mem_map_of_mem hx)
  have wG : qWeight G ≤ 4*q := by
    have all := List.sum_le_length_nsmul (G.map QEq.size) 4 (by
      intro z hz
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      exact qLit_size_le _ _)
    simpa [qWeight,G,len,Nat.mul_comm] using all
  by_cases holds : QEq.Holds p (blockTupleEq v S h)
  · obtain ⟨i,hi,j,hj,ne,same⟩ := collision_in_block S h overflow p holds
    have common (k : Fin l) : a (i,k) = a (j,k) := by simpa [p] using same k
    let C := Finset.univ.image (fun k : Fin l => ((i,k),a (i,k))) ∪
      Finset.univ.image (fun k : Fin l => ((j,k),a (j,k)))
    have input : C ∈ BPHP m l := by
      refine ⟨i,j,fun k => p (i,k),ne,?_⟩
      simp [C,p,common]
    let A := rowBlock i a ++ rowBlock j a
    have rep (e : QEq (Fin m × Fin l)) : e ∈ A ↔ ∃ t ∈ C, e = litQEq t := by
      simp only [A,List.mem_append,mem_rowBlock,C,Finset.mem_union,Finset.mem_image,
        Finset.mem_univ,true_and]
      constructor
      · rintro (⟨b,rfl⟩ | ⟨b,rfl⟩)
        · exact ⟨_,Or.inl ⟨b,rfl⟩,rfl⟩
        · exact ⟨_,Or.inr ⟨b,rfl⟩,rfl⟩
      · rintro ⟨t, ht, rfl⟩
        rcases ht with ⟨b,rfl⟩ | ⟨b,rfl⟩
        · exact Or.inl ⟨b,rfl⟩
        · exact Or.inr ⟨b,rfl⟩
    have deriv := d.ax C input rep
    have sub (x : QEq (Fin m × Fin l)) (hx : x ∈ A) : x ∈ G++D := by
      apply List.mem_append_left
      rcases List.mem_append.mp hx with left | right
      · obtain ⟨k,rfl⟩ := (mem_rowBlock i a x).mp left
        exact guard _ ((memvs _).mpr hi)
      · obtain ⟨k,rfl⟩ := (mem_rowBlock j a x).mp right
        exact guard _ ((memvs _).mpr hj)
    refine ⟨[G++D,A], .weaken deriv List.mem_cons_self sub,List.mem_cons_self,?_⟩
    have wi := rowBlock_weight i a
    have wj := rowBlock_weight j a
    have mul : 10 + m*l + 6*q + 8*l + qWeight D ≤ cap := Nat.le_mul_of_pos_left _ (by omega)
    change qCost (G++D) + (qCost A+0) ≤ cap
    simp only [qCost,A,qWeight_append]
    omega
  · have hc := blockTupleEq_coeff v S h
    have off (x) (hx : x ∉ vs) := blockTupleEq_off v S h x (fun hr => hx ((memvs _).mpr hr))
    have blocked (x) (hx : x ∈ vs) : litQEq (x,!p x) ∈ G++D := by
      simpa [p] using List.mem_append_left D (guard x hx)
    obtain ⟨σ,ds,hm,price⟩ := qEvaluatePointFromContext vs p (G++D) 1 (blockTupleEq v S h)
      hc off holds blocked d (base _ rfl) (fun _ => List.mem_append_right G)
    refine ⟨σ,ds,hm,price.trans ?_⟩
    simp only [Fintype.card_prod,Fintype.card_fin,len,qWeight_append,mul_one]
    apply Nat.mul_le_mul_left
    have rhs := blockTupleEq_rhs v S h
    have capR : S.card*u ≤ q := Nat.mul_le_mul_left _ (Nat.le_add_right u v)
    omega

/-- Remove every overflowing tuple at the final capacity state. Costs count
only new lines, so any earlier derivation can be reused intact. -/
theorem drop_block_capacity_line {m u : ℕ} (v k : ℕ)
    {ρ : List (QLine (Fin m × Fin (u+v)))} (d : IsResLinQSynDerivation (BPHP m (u+v)) ρ)
    (start : blockCapacityLine v k (fun _ : Fin u → Bool => 2^v) ∈ ρ) :
    let L := blockCapacityLine (m := m) v k (fun _ : Fin u → Bool => 2^v)
    ∃ σ, IsResLinQSynDerivation (BPHP m (u+v)) (σ++ρ) ∧ ([] : QLine _) ∈ σ++ρ ∧
      resLinQSize σ ≤ L.length * blockDropCost m (u+v) (2^v+1) (qWeight L) := by
  intro L
  let budget := qWeight L
  have aux (T : QLine (Fin m × Fin (u+v))) (w : qWeight T ≤ budget)
      (shape : ∀ e ∈ T, ∃ (S : Finset (Fin m)) (h : Fin u → Bool), S.card=2^v+1 ∧ e=blockTupleEq v S h)
      {τ : List (QLine (Fin m × Fin (u+v)))} (dt : IsResLinQSynDerivation (BPHP m (u+v)) τ) (ht : T∈τ) :
      ∃ σ, IsResLinQSynDerivation (BPHP m (u+v)) (σ++τ) ∧ ([] : QLine _) ∈ σ++τ ∧
        resLinQSize σ ≤ T.length * blockDropCost m (u+v) (2^v+1) budget := by
    induction T generalizing τ with
    | nil => exact ⟨[],dt,ht,by simp [resLinQSize]⟩
    | cons e T ih =>
      obtain ⟨S,h,card,rfl⟩ := shape e List.mem_cons_self
      have wt : qWeight T ≤ budget := by change _ + qWeight T ≤ budget at w; omega
      obtain ⟨s,ds,hm,price⟩ := drop_block_tuple S h (by omega) T τ dt
        (fun _ hz => Set.mem_singleton_iff.mp hz ▸ ht)
      obtain ⟨t,db,empty,size⟩ := ih wt (fun z hz => shape z (List.mem_cons_of_mem _ hz)) ds
        (List.mem_append_left _ hm)
      refine ⟨t++s,by simpa only [List.append_assoc] using db,by simpa only [List.append_assoc] using empty,?_⟩
      have bound : blockDropCost m (u+v) S.card (qWeight T) ≤ blockDropCost m (u+v) (2^v+1) budget := by
        rw [card]; dsimp only [blockDropCost]; gcongr
      rw [show resLinQSize (t++s) = resLinQSize t + resLinQSize s by simp [resLinQSize],
        List.length_cons,Nat.succ_mul]
      exact Nat.add_le_add size (price.trans bound)
  apply aux L le_rfl _ d start
  intro e he
  obtain ⟨h,S,_,card,eqn⟩ := (mem_blockCapacityLine v k _ e).mp he
  exact ⟨S,h,card,eqn⟩

end PEqualNP.Search.Helpers
