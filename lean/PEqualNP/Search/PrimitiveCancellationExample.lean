import PEqualNP.Search.Helpers.QDeferSimp
import PEqualNP.Search.Helpers.QPrimitive

/-! A failure of primitive parity projection in four lines from a satisfiable
one-variable formula. The two weakenings retain the original axiom as a tail. -/

namespace PEqualNP.Search

open Helpers ProofComplexity

/-- A satisfiable input can derive two lines whose normalized parity images hold
at a point where the image of their resolvent fails. The refutation rules are
used here just to derive a line, without reaching the empty line. -/
theorem PrimitiveCancellationExample :
    ∃ (F : Set (Clause Unit)) (K : QLine Unit) (e f : QEq Unit) (a : Unit → Bool),
      Satisfiable F ∧
      NoSimpDerivation F
        [((0, -2) :: (K ++ K)), f :: K, e :: K, K] ∧
      ((1 : ℤ) • e.1 + (-1 : ℤ) • f.1, e.2 - f.2) = ((0, -2) : QEq Unit) ∧
      LinEqSat a (qParity (qPrimitive e)) ∧ LinEqSat a (qParity (qPrimitive f)) ∧
      (∀ z ∈ ((0, -2) :: (K ++ K) : QLine Unit), ¬ LinEqSat a (qParity (qPrimitive z))) := by
  let l : Unit × Bool := ((), true)
  let C : Clause Unit := {l}
  let F : Set (Clause Unit) := {C}
  let K : QLine Unit := [litQEq l]
  let e : QEq Unit := (1, 0)
  let f : QEq Unit := (1, 2)
  let a : Unit → Bool := fun _ => false
  have dax : NoSimpDerivation F [K] :=
    .ax C .nil (Set.mem_singleton _) (by intro z; simp [C, K])
  have d1 : NoSimpDerivation F [e :: K, K] :=
    .weaken dax List.mem_cons_self (fun z hz => List.mem_cons_of_mem _ hz)
  have d2 : NoSimpDerivation F [f :: K, e :: K, K] :=
    .weaken d1 (List.mem_cons_of_mem _ List.mem_cons_self) (fun z hz => List.mem_cons_of_mem _ hz)
  have diff : ((1 : ℤ) • e.1 + (-1 : ℤ) • f.1, 1 * e.2 + -1 * f.2) = ((0, -2) : QEq Unit) := by
    norm_num [e, f]
  have trace := NoSimpDerivation.res (1 : ℤ) (-1) d2
    (List.mem_cons_of_mem (f :: K) List.mem_cons_self) (List.mem_cons_self (a := f :: K))
  rw [diff] at trace
  have coeffOne (z : QEq Unit) (hz : z.1 () = 1) : qPrimitive z = z := by
    have fac := qPrimitive_coeff z ()
    rw [hz] at fac
    have order : qOrder z = 0 := by
      by_contra hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hk, pow_succ] at fac
      have : (2 : ℤ) ∣ 1 := ⟨(2 : ℤ) ^ k * (qPrimitive z).1 (), by linarith [fac]⟩
      norm_num at this
    simp [qPrimitive, order]
  refine ⟨F, K, e, f, a, ?_, trace, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ => true, ?_⟩
    intro D hm
    obtain rfl : D = C := Set.mem_singleton_iff.mp hm
    exact ⟨l, Finset.mem_singleton_self _, rfl⟩
  · simpa [sub_eq_add_neg] using diff
  · rw [coeffOne e rfl, qParity_sat]
    norm_num [a, e, Int.ModEq]
  · rw [coeffOne f rfl, qParity_sat]
    norm_num [a, f, Int.ModEq]
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact qParity_primitive_false a _ rfl (by decide)
    · have heq : z = litQEq l := by simpa [K] using hz
      subst z
      rw [qPrimitive_lit, qParity_sat]
      simp [a, l, litQEq, Int.ModEq]

end PEqualNP.Search
