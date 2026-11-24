import PromiseIdeal

/-! Transporting guarded Boolean identities and two-tour errors across a projection. -/
namespace BooleanTransfer.RestrictionIdeal
open Finset MvPolynomial TourLayer CoreCoefficient PromiseIdeal

abbrev RingAt (m : ℕ) := MvPolynomial (Arc m) (ZMod 2)

inductive Label (m : ℕ) where
  | off
  | unit
  | var (e : Arc m)
  deriving DecidableEq

noncomputable def Label.value {m : ℕ} : Label m → RingAt m
  | .off => 0
  | .unit => 1
  | .var e => X e

private noncomputable def Label.power {m : ℕ} : Label m → Arc m →₀ ℕ
  | .off => 0
  | .unit => 0
  | .var e => Finsupp.single e 1

noncomputable def project {n m : ℕ} (f : Arc n → Label m) : RingAt n →+* RingAt m :=
  eval₂Hom C (fun e => (f e).value)

/-- Exponents count projected occurrences, allowing several source arcs to share a label. -/
noncomputable def footprint {n m : ℕ} (f : Arc n → Label m) (S : Finset (Arc n)) :
    Arc m →₀ ℕ := ∑ e ∈ S, (f e).power

def Live {n m : ℕ} (f : Arc n → Label m) (S : Finset (Arc n)) : Prop :=
  ∀ e ∈ S, f e ≠ .off

private theorem liveProduct {n m : ℕ} (f : Arc n → Label m) (S : Finset (Arc n)) (live : Live f S) :
    ∏ e ∈ S, (f e).value = monomial (footprint f S) (1 : ZMod 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [footprint]
  | @insert e S he ih =>
    have notOff := live e (mem_insert_self _ _)
    have tail : Live f S := fun i hi => live i (mem_insert_of_mem hi)
    rw [prod_insert he, ih tail]
    cases h : f e with
    | off => exact (notOff h).elim
    | unit => simp [footprint, he, h, Label.power, Label.value]
    | var i => simp [footprint, he, h, Label.power, Label.value, X, monomial_mul]

private theorem deadProduct {n m : ℕ} (f : Arc n → Label m) (S : Finset (Arc n))
    (dead : ¬Live f S) : ∏ e ∈ S, (f e).value = 0 := by
  classical
  obtain ⟨e,he,off⟩ : ∃ e ∈ S, f e = .off := by simpa [Live] using dead
  exact prod_eq_zero he (by rw [off]; rfl)

private theorem monoFoot {n m : ℕ} (f : Arc n → Label m) {S T : Finset (Arc n)} (h : S ⊆ T) :
    footprint f S ≤ footprint f T := by
  intro i
  simp only [footprint, Finsupp.finsetSum_apply]
  exact sum_le_sum_of_subset h

private theorem squareProd {n : ℕ} (E : Finset (Arc n)) :
    ∏ e ∈ E, (X e : RingAt n) = monomial (exponent E) 1 := by
  simpa [exponent] using (prod_X_pow (R := ZMod 2) (fun _ : Arc n => 1) E)

private theorem targetSupport {n : ℕ} (E : Finset (Arc n)) (a : Arc n →₀ ℕ)
    (le : exponent E ≤ a) : E ⊆ a.support := by
  intro i hi
  have comp := le i
  rw [exponent, Finsupp.indicator_of_mem hi] at comp
  exact Finsupp.mem_support_iff.mpr (by omega)

private theorem memTours {n : ℕ} (s : Equiv.Perm (Fin n)) {E : Finset (Arc n)}
    (cycle : s.IsCycleOn Set.univ) (inside : arcs s ⊆ E) : s ∈ tours E := by
  classical
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,cycle⟩,
    fun i => inside (by simp)⟩

noncomputable def cycles (n : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact univ.filter (fun s : Equiv.Perm (Fin n) => s.IsCycleOn Set.univ)

noncomputable def survivors {n m : ℕ} (f : Arc n → Label m) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact (cycles n).filter (fun s => Live f (arcs s))

/-- Finite routing data. The footprint equality records exact variable multiplicities
after fixed connectors have been removed. -/
structure Routing {n m : ℕ} (f : Arc n → Label m)
    (decode : Equiv.Perm (Fin n) → Equiv.Perm (Fin m)) : Prop where
  target : ∀ s ∈ survivors f, decode s ∈ cycles m
  weight : ∀ s ∈ survivors f, footprint f (arcs s) = exponent (arcs (decode s))
  injective : ∀ s ∈ survivors f, ∀ t ∈ survivors f, decode s = decode t → s = t
  onto : ∀ t ∈ cycles m, ∃ s ∈ survivors f, decode s = t

private theorem cycleSet {n : ℕ} {s : Equiv.Perm (Fin n)} :
    s ∈ cycles n ↔ s.IsCycleOn Set.univ := by classical simp [cycles]

private theorem surviveSet {n m : ℕ} {f : Arc n → Label m} {s : Equiv.Perm (Fin n)} :
    s ∈ survivors f ↔ s.IsCycleOn Set.univ ∧ Live f (arcs s) := by
  classical simp [survivors, cycleSet]

/-- The formal HC polynomial, with its multiplicities, is preserved by the cycle bijection. -/
theorem tourSum {n m : ℕ} (f : Arc n → Label m) (decode : Equiv.Perm (Fin n) → Equiv.Perm (Fin m))
    (route : Routing f decode) : project f (Statement.hc (ZMod 2) n) = Statement.hc (ZMod 2) m := by
  classical
  have arcForm (k : ℕ) : Statement.hc (ZMod 2) k =
      ∑ s ∈ cycles k, ∏ e ∈ arcs s, (X e : RingAt k) := by
    simp only [Statement.hc, cycles, arcs, prod_map]
    rfl
  rw [arcForm n, arcForm m, map_sum]
  simp only [map_prod, project, eval₂Hom_X']
  calc
    _ = ∑ s ∈ survivors f, ∏ e ∈ arcs s, (f e).value := by
      rw [survivors,sum_filter]
      apply sum_congr rfl
      intro s _
      split
      · rfl
      · exact deadProduct f _ (by assumption)
    _ = _ := by
      apply sum_bij (fun s _ => decode s)
      · exact route.target
      · exact route.injective
      · intro t ht
        obtain ⟨s,hs,eq⟩ := route.onto t ht
        exact ⟨s,hs,eq⟩
      · intro s hs
        rw [liveProduct f _ (surviveSet.mp hs).2, route.weight s hs, squareProd]

/-- Distinct surviving source tours still divide the projected error monomial
through their distinct decoded tours, also when source tours share arcs. -/
theorem transport {n m : ℕ} (f : Arc n → Label m) (decode : Equiv.Perm (Fin n) → Equiv.Perm (Fin m))
    (target : ∀ s ∈ survivors f, decode s ∈ cycles m)
    (cover : ∀ s ∈ survivors f, exponent (arcs (decode s)) ≤ footprint f (arcs s))
    (inj : ∀ s ∈ survivors f, ∀ t ∈ survivors f, decode s = decode t → s = t) :
    errorIdeal n ≤ (errorIdeal m).comap (project f) := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨_,⟨s,t,cs,ct,ne,rfl⟩,rfl⟩
  change project f (monomial (exponent (arcs s ∪ arcs t)) 1) ∈ errorIdeal m
  rw [← squareProd, map_prod]
  simp only [project, eval₂Hom_X']
  by_cases live : Live f (arcs s ∪ arcs t)
  · rw [liveProduct f _ live, membership]
    intro a ha
    have eq : footprint f (arcs s ∪ arcs t) = a := by simpa using ha
    subst a
    have hs : s ∈ survivors f := surviveSet.mpr ⟨cs,fun e he => live e (mem_union_left _ he)⟩
    have ht : t ∈ survivors f := surviveSet.mpr ⟨ct,fun e he => live e (mem_union_right _ he)⟩
    have hit (u : Equiv.Perm (Fin n)) (hu : u ∈ survivors f) (sub : arcs u ⊆ arcs s ∪ arcs t) :
        decode u ∈ tours (footprint f (arcs s ∪ arcs t)).support := by
      apply memTours _ (cycleSet.mp (target u hu))
      exact targetSupport _ _ ((cover u hu).trans (monoFoot f sub))
    exact one_lt_card.mpr ⟨decode s,hit s hs subset_union_left,decode t,hit t ht subset_union_right,
      fun eq => ne (inj s hs t ht eq)⟩
  · rw [deadProduct f _ live]
    exact (errorIdeal m).zero_mem

noncomputable def guarded {n : ℕ} (A : Set (Arc n)) : Ideal (RingAt n) :=
  Ideal.span ((fun e => (X e : RingAt n)^2 - X e) '' A)

/-- Each Boolean identity supported on a fixed-zero or fixed-one arc maps to zero. -/
theorem vanish {n m : ℕ} (f : Arc n → Label m) (A : Set (Arc n))
    (fixed : ∀ e ∈ A, f e = .off ∨ f e = .unit) : guarded A ≤ RingHom.ker (project f) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,he,rfl⟩
  change project f ((X e)^2-X e) = 0
  simp only [map_sub, map_pow, project, eval₂Hom_X']
  rcases fixed e he with h | h <;> simp [h,Label.value]

/-- Restriction followed by homogeneous extraction removes both allowed error ideals. -/
theorem extract {n m : ℕ} (f : Arc n → Label m) (A : Set (Arc n))
    (decode : Equiv.Perm (Fin n) → Equiv.Perm (Fin m)) (route : Routing f decode)
    (fixed : ∀ e ∈ A, f e = .off ∨ f e = .unit) (p : RingAt n)
    (error : p - Statement.hc (ZMod 2) n ∈ guarded A ⊔ errorIdeal n) :
    homogeneousComponent m (project f p) = Statement.hc (ZMod 2) m := by
  have le : guarded A ⊔ errorIdeal n ≤ (errorIdeal m).comap (project f) := by
    apply sup_le _ (transport f decode route.target (fun s hs => (route.weight s hs).symm.le) route.injective)
    intro q hq
    have zero : project f q = 0 := vanish f A fixed hq
    change project f q ∈ errorIdeal m
    rw [zero]
    exact (errorIdeal m).zero_mem
  have he : project f (p - Statement.hc (ZMod 2) n) ∈ errorIdeal m := le error
  rw [map_sub, tourSum f decode route] at he
  exact PromiseIdeal.layer _ he

#print axioms tourSum
#print axioms transport
#print axioms vanish
#print axioms extract
end BooleanTransfer.RestrictionIdeal
