import PEqualNP.Search.Helpers.CoordSearch
import PEqualNP.Search.Helpers.QCoordinateLeaf

/-! A deterministic coordinate search for a falsified clause gives a syntactic
integer refutation. Each decision is eliminated by resolving the two Boolean
values of its coordinate. The budget includes every path literal on every line. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.Clause V)}

private theorem path_weight_bound (p : List (V × Bool)) : qWeight (p.map litQEq) ≤ 4*p.length := by
  induction p with
  | nil => simp
  | cons x p ih =>
    change (litQEq x).size + qWeight (p.map litQEq) ≤ 4*(p.length+1)
    have := litQEq_size x
    omega

private theorem build_coordinate_search (t : CoordSearch V) (p : List (V × Bool)) (M : ℕ)
    (cap : 4*(p.length+t.depth)+1 ≤ M)
    (cert : ∀ a : V → Bool, (∀ x ∈ p, a x.1 ≠ x.2) →
      t.eval a ∈ F ∧ ¬ ClauseSat a (t.eval a))
    (ρ : List (QLine V)) (d : IsResLinQSynDerivation F ρ) :
    ∃ s, IsResLinQSynDerivation F (s ++ ρ) ∧ p.map litQEq ∈ s ∧
      resLinQSize s + 10*M ≤ 2^t.depth * (12*M) := by
  induction t generalizing p ρ with
  | leaf C =>
    obtain ⟨s,der,mem,cost⟩ := qCoordinateLeaf p C cert ρ d (by simp)
    simp only [CoordDecision.depth,Nat.add_zero] at cap
    refine ⟨s,der,mem,?_⟩
    simp only [CoordDecision.depth,pow_zero,one_mul]
    omega
  | node v lo hi ilo ihi =>
    have advance (b : Bool) (a : V → Bool) (blocked : ∀ x ∈ (v,!b)::p, a x.1 ≠ x.2) :
        a v = b ∧ ∀ x ∈ p, a x.1 ≠ x.2 := by
      have hv := blocked (v,!b) List.mem_cons_self
      exact ⟨by cases hv' : a v <;> cases b <;> simp_all, fun x hx => blocked x (.tail _ hx)⟩
    have capLo : 4*(((v,true)::p).length+lo.depth)+1 ≤ M := by
      simp only [List.length_cons]
      simp only [CoordDecision.depth] at cap
      have := Nat.le_max_left lo.depth hi.depth
      omega
    have capHi : 4*(((v,false)::p).length+hi.depth)+1 ≤ M := by
      simp only [List.length_cons]
      simp only [CoordDecision.depth] at cap
      have := Nat.le_max_right lo.depth hi.depth
      omega
    obtain ⟨s,ds,ms,bs⟩ := ilo ((v,true)::p) capLo (by
      intro a path
      obtain ⟨hv,hp⟩ := advance false a path
      simpa only [CoordDecision.eval,hv,Bool.false_eq_true,ite_false] using cert a hp) ρ d
    obtain ⟨u,du,mu,bu⟩ := ihi ((v,false)::p) capHi (by
      intro a path
      obtain ⟨hv,hp⟩ := advance true a path
      simpa only [CoordDecision.eval,hv,ite_true] using cert a hp) (s ++ ρ) ds
    obtain ⟨w,dw,mw,bw⟩ := qCoordinateCut v (p.map litQEq) du
      (List.mem_append_left _ mu) (List.mem_append_right _ (List.mem_append_left _ ms))
    refine ⟨w ++ (u ++ s), by simpa [List.append_assoc] using dw, List.mem_append_left _ mw, ?_⟩
    have wt := path_weight_bound p
    have costW : resLinQSize w ≤ 10*M := bw.trans (by omega)
    have low := Nat.mul_le_mul_right (12*M) (Nat.pow_le_pow_right (n := 2) (by decide)
      (Nat.le_max_left lo.depth hi.depth))
    have high := Nat.mul_le_mul_right (12*M) (Nat.pow_le_pow_right (n := 2) (by decide)
      (Nat.le_max_right lo.depth hi.depth))
    have size : resLinQSize (w ++ (u ++ s)) = resLinQSize w + (resLinQSize u + resLinQSize s) := by
      simp [resLinQSize]
    rw [size, CoordDecision.depth, pow_succ, mul_comm _ 2, Nat.mul_assoc, two_mul]
    omega

/-- Any adaptive search tree finding a falsified input clause everywhere gives
an integer refutation. Repeated queries and unequal branch depths are allowed. -/
theorem qRefuteOfCoordSearch (t : CoordSearch V)
    (cert : ∀ a : V → Bool, t.eval a ∈ F ∧ ¬ ClauseSat a (t.eval a)) :
    ∃ π, IsResLinQSynRefutation F π ∧ resLinQSize π ≤ 12*(4*t.depth+1)*2^t.depth := by
  obtain ⟨s,der,mem,b⟩ := build_coordinate_search t [] (4*t.depth+1) (by simp) (fun a _ => cert a) [] .nil
  refine ⟨s,⟨by simpa using der, by simpa using mem⟩,?_⟩
  rw [mul_comm (12*_)]
  omega

end PEqualNP.Search.Helpers
