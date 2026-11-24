import PEqualNP.Search.BPHPAffineHull
import PEqualNP.Search.Helpers.BPHPColumnFlip
import PEqualNP.Search.Helpers.BPHPColumnRename
import PEqualNP.Search.Helpers.QSynEssential
import PEqualNP.Search.Helpers.QScaledPair

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

private def weightedColumn {m l : ℕ} (b : Fin l) (c rhs : ℤ) : QEq (Fin m × Fin l) :=
  (fun v => if v.2 = b then c else 0, rhs)

private theorem rename_weighted_column {m l : ℕ} (b t : Fin l) (c rhs : ℤ) :
    qRenameEq (columnEmbedding m (Equiv.swap b t)) (weightedColumn b c rhs) =
      weightedColumn t c rhs := by
  apply Prod.ext
  · funext v
    rcases v with ⟨r,u⟩
    rw [qRenameEq_column]
    have eq : (Equiv.swap b t).symm u = b ↔ u = t := by
      rw [Equiv.symm_apply_eq]
      simp
    change (if (Equiv.swap b t).symm u = b then c else 0) = _
    rw [if_congr eq rfl rfl]
    rfl
  · rfl

private theorem omit_column_coeff {m l : ℕ} (i : Fin (m+1)) (b : Fin l) (c rhs : ℤ)
    (v : Fin (m+1) × Fin l) :
    (qRenameEq (rowEmbedding i.succAboveEmb l) (weightedColumn b c rhs)).1 v =
      if v.1 = i then 0 else if v.2 = b then c else 0 := by
  rcases v with ⟨r,t⟩
  by_cases hr : r = i
  · subst r
    have off : (i,t) ∉ Set.range (rowEmbedding i.succAboveEmb l) := by
      rintro ⟨⟨u,v⟩,eq⟩
      exact i.succAbove_ne u (congrArg Prod.fst eq)
    simp [qRenameEq_off _ _ off]
  · obtain ⟨u,rfl⟩ := Fin.exists_succAbove_eq hr
    change (qRenameEq (rowEmbedding i.succAboveEmb l) _).1
      (rowEmbedding i.succAboveEmb l (u,t)) = _
    rw [qRenameEq_at]
    simp [weightedColumn,i.succAbove_ne]

private theorem omit_column_difference {m l : ℕ} (i j : Fin (m+1)) (b : Fin l) (c rhs : ℤ) :
    let E := weightedColumn (m := m) b c rhs
    let A := qRenameEq (rowEmbedding i.succAboveEmb l) E
    let B := qRenameEq (rowEmbedding j.succAboveEmb l) E
    ((-1:ℤ) • A.1 + (1:ℤ) • B.1, (-1:ℤ)*A.2 + (1:ℤ)*B.2) = scaledEqPair c (i,b) (j,b) := by
  dsimp only
  apply Prod.ext
  · funext v
    rcases v with ⟨r,t⟩
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,omit_column_coeff,scaledEqPair,Prod.mk.injEq]
    by_cases hi : r=i <;> by_cases hj : r=j <;> by_cases hb : t=b <;> simp [hi,hj,hb] <;> split_ifs <;> simp
  · simp [weightedColumn,scaledEqPair]

/-- A balanced singleton with a nonzero coefficient yields a scaled equality
for any two selected rows and any selected bit in the instance with an extra row.
The scale is uniform in the choice of rows and bit. -/
theorem bphp_scaled_pair_from_unit {l : ℕ} {π : List (QLine (Fin (2^l) × Fin l))}
    {e : QEq (Fin (2^l) × Fin l)} (d : IsResLinQSynDerivation (BPHP (2^l) l) π)
    (unit : [e] ∈ π) (coeff : e.1 ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ c.natAbs.size ≤ 7*resLinQSize π ∧
      ∀ (i j : Fin (2^l+1)) (b : Fin l), i ≠ j →
        ∃ σ, IsResLinQSynDerivation (BPHP (2^l+1) l) σ ∧
          [scaledEqPair c (i,b) (j,b)] ∈ σ ∧ resLinQSize σ ≤ 28*resLinQSize π + 2 := by
  classical
  let n := 2^l
  obtain ⟨⟨r,b₀⟩,nonzero⟩ := Function.ne_iff.mp coeff
  have valid (a : Fin n × Fin l → Bool) (sat : Satisfies a (BPHP n l)) : QEq.Holds a e := by
    obtain ⟨f,hf,good⟩ := syn_lines_hold_of_used_axioms d a (fun C h _ => sat C h) _ unit
    simpa only [List.mem_singleton.mp hf] using good
  obtain ⟨w,hw,_⟩ := (bphp_affine_hull (Nat.zero_lt_of_lt b₀.isLt) e).mp valid
  let c := 2 * w b₀
  let rhs := ∑ i, e.1 (i,b₀)
  have nc : c ≠ 0 := mul_ne_zero (by decide) (by simpa only [← hw r b₀,Pi.zero_apply] using nonzero)
  obtain ⟨τ,dτ,hit,price⟩ := bphp_isolate_column b₀ d unit
  have canonical : [(weightedColumn (m := n) b₀ c rhs)] ∈ τ := by
    convert hit using 1
    congr 2
    refine Prod.ext ?_ rfl
    funext v
    change (if v.2 = b₀ then c else 0) = (if v.2 = b₀ then 2*e.1 v else 0)
    by_cases h : v.2 = b₀
    · rw [ite_eq_left h,ite_eq_left h,show e.1 v = w b₀ from (hw v.1 v.2).trans (congrArg w h)]
    · rw [ite_eq_right h,ite_eq_right h]
  have cb : c.natAbs.size ≤ 7*resLinQSize π := by
    have one := Finset.single_le_sum (s := Finset.univ)
      (f := fun v : Fin n × Fin l => ((weightedColumn b₀ c rhs).1 v).natAbs.size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (r,b₀))
    have value : (weightedColumn (m := n) b₀ c rhs).1 (r,b₀) = c := by simp [weightedColumn]
    rw [value] at one
    apply one.trans
    apply le_trans _ ((qCost_le_of_mem canonical).trans price)
    change _ ≤ 1 + ((1 + _ + rhs.natAbs.size)+0)
    exact (Nat.le_add_left _ 1).trans ((Nat.le_add_right _ _).trans (Nat.le_add_left _ 1))
  refine ⟨c,nc,cb,?_⟩
  intro i j b _
  let p := Equiv.swap b₀ b
  let δ := qRenameProof (columnEmbedding n p) τ
  let E := weightedColumn (m := n) b c rhs
  have hE : [E] ∈ δ := by
    simpa only [p,δ,E,List.map_cons,List.map_nil,rename_weighted_column]
      using qRenameProof_mem (columnEmbedding n p) canonical
  let inc (u : Fin (n+1)) := rowEmbedding u.succAboveEmb l
  let copy (u : Fin (n+1)) := qRenameProof (inc u) δ
  have validCopy (u) : IsResLinQSynDerivation (BPHP (n+1) l) (copy u) :=
    bphp_rename_derivation u.succAboveEmb (bphp_column_rename p dτ)
  have copied (u) : [qRenameEq (inc u) E] ∈ copy u := qRenameProof_mem (inc u) hE
  let both := copy i ++ copy j
  let line := [scaledEqPair c (i,b) (j,b)]
  have final : IsResLinQSynDerivation (BPHP (n+1) l) (line :: both) := by
    have step := (qAppendDerivations (validCopy i) (validCopy j)).res (-1) 1
      (List.mem_append_left _ (copied i)) (List.mem_append_right _ (copied j))
    simpa only [inc,E,List.nil_append,omit_column_difference] using step
  refine ⟨_,final,List.mem_cons_self,?_⟩
  have costs : resLinQSize both = 2 * resLinQSize τ := by
    have add : resLinQSize both = resLinQSize (copy i)+resLinQSize (copy j) := by simp [both,resLinQSize]
    simp [add,copy,δ,two_mul]
  have last := scaledEqPair_size c (i,b) (j,b)
  rw [qSize_cons,costs]
  change 1 + ((scaledEqPair c (i,b) (j,b)).size + 0) + _ ≤ _
  omega

end PEqualNP.Search
