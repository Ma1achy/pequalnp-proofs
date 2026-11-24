import PEqualNP.Search.Helpers.TriangleFooling
import PEqualNP.Search.Helpers.QTwoBitEquation
import PEqualNP.Search.Helpers.QPaddingCost
import PEqualNP.Search.Helpers.SemanticWeakening

/-! Exact triangle covers can be large even for a two-line derivation from actual
bit-pigeonhole axioms, under the split used for the triangle-DAG lower bound. -/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity Helpers

/-- With two reserved rows and k free rows, one weakening of a bit-PHP input
clause produces a line whose falsifying assignments need 2^k triangles. -/
theorem bphp_triangle_cover_barrier (k l : ℕ) (hl : 2 ≤ l) :
    ∃ A T : QLine (Fin (k+2) × Fin l), IsResLinQSynDerivation (BPHP (k+2) l) [T,A] ∧
      resLinQSize [T,A] ≤ 4*k + 12*l + 2 ∧
      ∀ cover : Finset (Set (Fin (k+2) × Fin l → Bool)),
        (∀ R ∈ cover, IsTri (fun v => decide (2*v.2.val < l)) R) →
        (∀ R ∈ cover, ∀ a ∈ R, ¬ QLine.Holds a T) →
        (∀ a, ¬ QLine.Holds a T → ∃ R ∈ cover, a ∈ R) → 2^k ≤ cover.card := by
  classical
  let lo : Fin l := ⟨0, by omega⟩
  let hi : Fin l := ⟨l-1, by omega⟩
  let r : Fin (k+2) := ⟨k, by omega⟩
  let s : Fin (k+2) := ⟨k+1, by omega⟩
  let row (i : Fin k) : Fin (k+2) := ⟨i.val, by omega⟩
  let clause (j : Fin (k+2)) := Finset.univ.image (fun b : Fin l => ((j,b),true))
  let C := clause r ∪ clause s
  let A := C.toList.map litQEq
  let e (i : Fin k) := twoBitMismatch (row i,lo) (row i,hi)
  let X := (Finset.univ : Finset (Fin k)).toList.map e
  let T := A ++ X
  have valid : C ∈ BPHP (k+2) l := by
    refine ⟨r,s,fun _ => false,?_,rfl⟩
    intro eq
    have h := congrArg Fin.val eq
    simp [r,s] at h
  have rep (z) : z ∈ A ↔ ∃ t ∈ C, z = litQEq t := by
    simp [A, eq_comm]
  have dA : IsResLinQSynDerivation (BPHP (k+2) l) [A] := .ax C .nil valid rep
  have dT : IsResLinQSynDerivation (BPHP (k+2) l) [T,A] :=
    .weaken dA List.mem_cons_self (fun _ h => List.mem_append_left _ h)
  have card (j) : (clause j).card ≤ l := Finset.card_image_le.trans (by simp)
  have cardC : C.card ≤ 2*l := (Finset.card_union_le _ _).trans (by have := card r; have := card s; omega)
  have wA : qWeight A ≤ 6*l := by
    have h := List.sum_le_length_nsmul (A.map QEq.size) 3 (by
      intro n hn
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hn
      obtain ⟨t,_,rfl⟩ := (rep z).mp hz
      exact litQEq_size t)
    simp only [List.length_map,A,Finset.length_toList,smul_eq_mul] at h
    change (A.map QEq.size).sum ≤ 6*l
    dsimp only [A] at *
    omega
  have sep (i : Fin k) : (row i,lo) ≠ (row i,hi) := by
    intro eq
    have h := congrArg (fun v : Fin (k+2) × Fin l => v.2.val) eq
    dsimp [lo,hi] at h
    omega
  have wX : qWeight X = 4*k := by
    simp [qWeight,X,Function.comp_def,e,fun i => twoBitMismatch_size _ _ (sep i),Nat.mul_comm]
  have bound : resLinQSize [T,A] ≤ 4*k + 12*l + 2 := by
    change (1+qWeight (A ++ X)) + ((1+qWeight A)+0) ≤ _
    rw [qWeight_append,wX]
    omega
  refine ⟨A,T,dT,bound,?_⟩
  intro cover tri safe covers
  let side (v : Fin (k+2) × Fin l) := decide (2*v.2.val < l)
  let S := {a : Fin (k+2) × Fin l → Bool | ¬ QLine.Holds a T}
  let point (w : Fin k → Bool) (x : Fin (k+2) × Fin l) := if h : x.1.val < k then w ⟨x.1.val,h⟩ else false
  have diag (w : Fin k → Bool) : point w ∈ S := by
    rintro ⟨z,hz,hit⟩
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨t,ht,rfl⟩ := (rep _).mp hz
      have reserved (j : Fin (k+2)) (hj : k ≤ j.val) (mem : t ∈ clause j) : False := by
        obtain ⟨b,_,eq⟩ := Finset.mem_image.mp mem
        rw [← eq] at hit
        have off : point w (j,b) = false := by simp [point,Nat.not_lt.mpr hj]
        simp only [QEq.Holds, litQEq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, off] at hit
        norm_num at hit
      exact (Finset.mem_union.mp ht).elim (reserved r (by rfl)) (reserved s (by dsimp [s]; omega))
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact ((twoBitMismatch_holds _ _ _).mp hit) rfl
  have cross (u w : Fin k → Bool) (h : u ≠ w) : mix side (point u) (point w) ∉ S := by
    intro miss
    obtain ⟨i,hiw⟩ := Function.ne_iff.mp h
    apply miss
    refine ⟨e i,List.mem_append_right _ (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩),
      (twoBitMismatch_holds _ _ _).mpr ?_⟩
    have sideLo : side (row i,lo) = true := by simp [side,lo]; omega
    have sideHi : side (row i,hi) = false := by simp [side,hi]; omega
    simpa [mix,sideLo,sideHi,point,row,i.isLt] using hiw
  simpa using triangle_fooling_bound side S point diag cross cover tri safe covers

/-- On the conjectured family the number of triangles is exponential in the
number of holes, already after a single syntactic weakening. -/
theorem BPHPTriangleLine (l : ℕ) (hl : 2 ≤ l) :
    ∃ A T : QLine (Fin (2^l+1) × Fin l), IsResLinQSynDerivation (BPHP (2^l+1) l) [T,A] ∧
      resLinQSize [T,A] ≤ 4*(2^l-1) + 12*l + 2 ∧
      ∀ cover : Finset (Set (Fin (2^l+1) × Fin l → Bool)),
        (∀ R ∈ cover, IsTri (fun v => decide (2*v.2.val < l)) R) →
        (∀ R ∈ cover, ∀ a ∈ R, ¬ QLine.Holds a T) →
        (∀ a, ¬ QLine.Holds a T → ∃ R ∈ cover, a ∈ R) → 2^(2^l-1) ≤ cover.card := by
  generalize he : (2 : ℕ)^l = n
  cases n with
  | zero => have := Nat.one_le_two_pow (n := l); omega
  | succ k => simpa using bphp_triangle_cover_barrier k l hl

end PEqualNP.Search
