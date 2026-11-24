import PEqualNP.Search.Helpers.QPaddingCost
import PEqualNP.Search.Helpers.QSynRename
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]

private def flippedSum (U : Finset V) (e : QEq V) : ℤ := ∑ v ∈ U, e.1 v

/-- A sign normalization makes a transformed input literal a literal again. -/
def flipSign (U : Finset V) (e : QEq V) : ℤ := if flippedSum U e = 0 then 1 else -1

omit [Fintype V] [DecidableEq V] in
private theorem flipSign_sq (U : Finset V) (e : QEq V) : flipSign U e * flipSign U e = 1 := by
  simp [flipSign]; split <;> simp

/-- Substitute `1-x` on the selected coordinates, adjusting the overall sign. -/
def qFlipEq (U : Finset V) (e : QEq V) : QEq V :=
  (fun v => flipSign U e * (if v ∈ U then -e.1 v else e.1 v),
   flipSign U e * (e.2 - flippedSum U e))

def flipLiteral (U : Finset V) (t : V × Bool) : V × Bool :=
  (t.1, if t.1 ∈ U then !t.2 else t.2)

omit [Fintype V] in
@[simp] theorem qFlipEq_lit (U : Finset V) (t : V × Bool) :
    qFlipEq U (litQEq t) = litQEq (flipLiteral U t) := by
  have total : flippedSum U (litQEq t) = if t.1 ∈ U then 1 else 0 := by
    simp [flippedSum,litQEq]
  apply Prod.ext
  · funext v
    simp only [qFlipEq,flipSign,total]
    by_cases ht : t.1 ∈ U <;> by_cases hv : v = t.1 <;>
      simp [litQEq,flipLiteral,ht,hv]
  · simp only [qFlipEq,flipSign,total]
    cases hb : t.2 <;> by_cases ht : t.1 ∈ U <;>
      simp [litQEq,flipLiteral,ht,hb]

omit [Fintype V] in
private theorem qFlip_combo (U : Finset V) (e f : QEq V) (α β : ℤ) :
    let g : QEq V := (α • e.1 + β • f.1, α*e.2 + β*f.2)
    let A := flipSign U g * α * flipSign U e
    let B := flipSign U g * β * flipSign U f
    qFlipEq U g =
      (A • (qFlipEq U e).1 + B • (qFlipEq U f).1, A * (qFlipEq U e).2 + B * (qFlipEq U f).2) := by
  intro g A B
  have total : flippedSum U g = α * flippedSum U e + β * flippedSum U f := by
    simp [flippedSum,g,Finset.sum_add_distrib,Finset.mul_sum]
  have he := flipSign_sq U e
  have hf := flipSign_sq U f
  apply Prod.ext
  · funext v
    change flipSign U g * _ = _ + _
    simp only [qFlipEq, A, B, Pi.smul_apply, smul_eq_mul]
    have cancel (s a z : ℤ) (hs : s*s=1) : a*s*(s*z) = a*z := by
      calc a*s*(s*z) = a*(s*s)*z := by ring
           _ = a*z := by rw [hs]; ring
    rw [cancel _ _ _ he, cancel _ _ _ hf]
    by_cases hv : v ∈ U <;> simp [hv,g] <;> ring
  · simp only [qFlipEq,A,B,total]
    change flipSign U g * (α*e.2 + β*f.2 - _) = _
    linear_combination -(flipSign U g * α * (e.2 - flippedSum U e)) * he -
      (flipSign U g * β * (f.2 - flippedSum U f)) * hf

private theorem qFlip_false (U : Finset V) (e : QEq V) :
    ((qFlipEq U e).1 = 0 ∧ (qFlipEq U e).2 ≠ 0) ↔ (e.1 = 0 ∧ e.2 ≠ 0) := by
  have zero : (qFlipEq U e).1 = 0 ↔ e.1 = 0 := by
    constructor
    · intro h; funext v
      have hv := congrFun h v
      by_cases z : flippedSum U e = 0 <;> by_cases hm : v ∈ U <;>
        simpa [qFlipEq,flipSign,z,hm] using hv
    · intro h; funext v; simp [qFlipEq,h]
  rw [zero]
  by_cases z : e.1 = 0
  · simp [qFlipEq,flipSign,flippedSum,z]
  · simp [z]

private theorem nat_size_add (a b : ℕ) : (a + b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have h := Nat.mul_le_mul (Nat.lt_size_self a) (Nat.lt_size_self b)
  nlinarith only [h, Nat.zero_le (a*b)]

private theorem int_bound_add (a b : ℤ) :
    (a+b).natAbs.size ≤ a.natAbs.size + b.natAbs.size :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (nat_size_add _ _)

omit [Fintype V] in
private theorem int_bound_sum (U : Finset V) (f : V → ℤ) :
    (∑v ∈ U, f v).natAbs.size ≤ ∑v ∈ U, (f v).natAbs.size := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert v U hv ih =>
    simpa [Finset.sum_insert,hv] using (int_bound_add (f v) (∑w ∈ U, f w)).trans
      (Nat.add_le_add_left ih _)

theorem qFlipEq_size (U : Finset V) (e : QEq V) : (qFlipEq U e).size ≤ 2*e.size := by
  have sign (a : ℤ) : (flipSign U e * a).natAbs = a.natAbs := by
    by_cases h : flippedSum U e = 0 <;> simp [flipSign,h]
  have coeff (v : V) : ((qFlipEq U e).1 v).natAbs = (e.1 v).natAbs := by
    by_cases hv : v ∈ U <;> simp [qFlipEq,hv,sign]
  have rhs := int_bound_add e.2 (-flippedSum U e)
  have part := int_bound_sum U e.1
  have full := Finset.sum_le_univ_sum_of_nonneg (s := U) (f := fun v => (e.1 v).natAbs.size) (by simp)
  simp only [Int.natAbs_neg] at rhs
  simp only [QEq.size, coeff]
  simp only [qFlipEq,sign,sub_eq_add_neg]
  dsimp [flippedSum] at *
  omega

private theorem flip_line_cost (U : Finset V) (L : QLine V) : qCost (L.map (qFlipEq U)) ≤ 2 * qCost L := by
  have hw : qWeight (L.map (qFlipEq U)) ≤ 2 * qWeight L := by
    induction L with
    | nil => simp
    | cons e L ih =>
      change (qFlipEq U e).size + qWeight (L.map _) ≤ 2 * (e.size + qWeight L)
      have := qFlipEq_size U e
      omega
  simp only [qCost]; omega

private def FlipSimulation (U : Finset V) (G : Set (Clause V)) (π : List (QLine V)) : Prop :=
  ∃ σ, IsResLinQSynDerivation G σ ∧ (∀ L ∈ π, L.map (qFlipEq U) ∈ σ) ∧
    resLinQSize σ ≤ 3 * resLinQSize π

private theorem flip_cons {U : Finset V} {G : Set (Clause V)} {π σ : List (QLine V)} {L : QLine V}
    (d : IsResLinQSynDerivation G (L.map (qFlipEq U) :: σ))
    (past : ∀ K ∈ π, K.map (qFlipEq U) ∈ σ) (budget : resLinQSize σ ≤ 3 * resLinQSize π) :
    FlipSimulation U G (L :: π) := by
  refine ⟨_, d, ?_, ?_⟩
  · intro K hm
    rcases List.mem_cons.mp hm with rfl | h
    · exact List.mem_cons_self
    · exact .tail _ (past K h)
  · simp only [qSize_cons]
    have := flip_line_cost U L
    omega

/-- Simultaneous complementation of a chosen set of coordinates transforms a
syntactic derivation at a cost of at most three times its original size. -/
theorem flip_derivation (U : Finset V) {F G : Set (Clause V)}
    (transfer : ∀ C ∈ F, C.image (flipLiteral U) ∈ G)
    {π : List (QLine V)} (d : IsResLinQSynDerivation F π) :
    ∃ σ, IsResLinQSynDerivation G σ ∧ (∀ L ∈ π, L.map (qFlipEq U) ∈ σ) ∧
      resLinQSize σ ≤ 3 * resLinQSize π := by
  change FlipSimulation U G π
  induction d with
  | nil => exact ⟨[], .nil, by simp, by simp [resLinQSize]⟩
  | ax C _ hc rep ih =>
    obtain ⟨σ, d, past, budget⟩ := ih
    apply flip_cons _ past budget
    apply d.ax (C.image (flipLiteral U)) (transfer C hc)
    intro g
    constructor
    · intro hg
      obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hg
      obtain ⟨t, ht, rfl⟩ := (rep _).mp hm
      exact ⟨_, Finset.mem_image_of_mem _ ht,qFlipEq_lit U t⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact List.mem_map.mpr ⟨_, (rep _).mpr ⟨t,ht,rfl⟩, qFlipEq_lit U t⟩
  | @bool π v _ ih =>
    obtain ⟨σ, d, past, budget⟩ := ih
    let L := [litQEq (v,false), litQEq (v,true)]
    have standard : IsResLinQSynDerivation G (L :: σ) := d.bool v
    have transformed : IsResLinQSynDerivation G (L.map (qFlipEq U) :: L :: σ) := by
      apply standard.weaken (C := L) List.mem_cons_self
      intro z hz
      by_cases hv : v ∈ U <;> simpa [L,flipLiteral,hv,or_comm] using hz
    refine ⟨_, transformed, ?_, ?_⟩
    · intro K h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact .tail _ (.tail _ (past K h))
    · change resLinQSize (L.map _ :: L :: σ) ≤ 3 * resLinQSize (L :: π)
      simp only [qSize_cons]
      have := flip_line_cost U L
      omega
  | @res π e f C D α β _ hC hD ih =>
    obtain ⟨σ, d, past, budget⟩ := ih
    apply flip_cons _ past budget
    simp only [List.map_cons, List.map_append, qFlip_combo]
    exact d.res _ _ (past _ hC) (past _ hD)
  | weaken _ hC incl ih =>
    obtain ⟨σ, d, past, budget⟩ := ih
    apply flip_cons _ past budget
    apply d.weaken (past _ hC)
    intro _ hg
    obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hg
    exact List.mem_map_of_mem (incl _ hm)
  | @simp π C _ hC ih =>
    obtain ⟨σ, d, past, budget⟩ := ih
    apply flip_cons _ past budget
    have commute : (C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0))).map (qFlipEq U) =
        (C.map (qFlipEq U)).filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) := by
      rw [List.filter_map]
      apply congrArg (List.map (qFlipEq U))
      apply congrArg (fun (p : QEq V → Bool) => C.filter p)
      funext e
      simp only [Function.comp_apply, qFlip_false]
    rw [commute]
    exact d.simp (past _ hC)

/-- Subtracting the flipped equation with its sign restored isolates the sum
over selected coordinates. -/
def qFlipCut (U : Finset V) (e : QEq V) : QEq V :=
  (fun v => if v ∈ U then 2 * e.1 v else 0, ∑ v ∈ U, e.1 v)

omit [Fintype V] in
theorem qFlipCut_resolution (U : Finset V) (e : QEq V) :
    ((1 : ℤ) • e.1 + (-flipSign U e) • (qFlipEq U e).1,
      (1 : ℤ) * e.2 + (-flipSign U e) * (qFlipEq U e).2) = qFlipCut U e := by
  have h := flipSign_sq U e
  apply Prod.ext
  · funext v
    by_cases hv : v ∈ U <;> simp [qFlipEq,qFlipCut,hv] <;>
      first | linear_combination e.1 v * h | linear_combination -(e.1 v) * h
  · change _ = flippedSum U e
    simp only [qFlipEq,one_mul]
    linear_combination -(e.2 - flippedSum U e) * h

theorem qFlipCut_size (U : Finset V) (e : QEq V) : (qFlipCut U e).size ≤ 3*e.size := by
  have coeff (v : V) : ((qFlipCut U e).1 v).natAbs.size ≤ 2*(e.1 v).natAbs.size := by
    by_cases hv : v ∈ U
    · simpa [qFlipCut,hv,two_mul] using int_bound_add (e.1 v) (e.1 v)
    · simp [qFlipCut,hv]
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun v _ => coeff v)
  rw [← Finset.mul_sum] at hc
  have hr := int_bound_sum U e.1
  have hf := Finset.sum_le_univ_sum_of_nonneg (s := U) (f := fun v => (e.1 v).natAbs.size) (by simp)
  change 1 + _ + (∑ v ∈ U,e.1 v).natAbs.size ≤ 3*(1+_+_)
  omega

end PEqualNP.Search.Helpers
