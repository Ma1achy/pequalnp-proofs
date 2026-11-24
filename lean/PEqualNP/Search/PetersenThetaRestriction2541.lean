import PEqualNP.Search.PetersenTheta2541
import PEqualNP.Search.PetersenAIGRestriction
import PEqualNP.Search.PetersenAIGFirstGate
import PEqualNP.Search.PetersenNecessaryReads

namespace PEqualNP.Search.PetersenTheta2541

open PEqualNP.Search.PetersenGateWitness PEqualNP.Search.PetersenAIG2541

private def pair (a b : Fin 9) (i : Fin 9) : Bool := decide (i = a ∨ i = b)

private theorem avoids (u v : Fin 9) :
    ∃ a b : Fin 9, pair a b u = false ∧ pair a b v = false ∧ edgeFunction (pair a b) = true :=
  (by decide : ∀ u v : Fin 9, ∃ a b : Fin 9,
    pair a b u = false ∧ pair a b v = false ∧ edgeFunction (pair a b) = true) u v

private theorem zero_unchanged {v : Fin 9} {x : Fin 9 → Bool} (h : x v = false) :
    zeroAt v x = x := by
  funext i
  by_cases e : i = v <;> simp_all [zeroAt]

theorem cofactor_not_raw (v u : Fin 9) :
    ¬ RawLiteral u (fun x => edgeFunction (zeroAt v x)) := by
  rintro ⟨b,h⟩
  obtain ⟨i,j,hv,hu,he⟩ := avoids v u
  have h1 := congrFun h (pair i j)
  have h0 := congrFun h (fun _ => false)
  change edgeFunction (zeroAt v (pair i j)) = (pair i j u != b) at h1
  rw [zero_unchanged hv, he, hu] at h1
  change edgeFunction (zeroAt v (fun _ => false)) = (false != b) at h0
  rw [zero_unchanged rfl] at h0
  change false = (false != b) at h0
  exact Bool.false_ne_true (h0.trans h1.symm)

theorem edge_not_raw (u : Fin 9) : ¬ RawLiteral u edgeFunction := by
  rintro ⟨b,h⟩
  obtain ⟨i,j,hu,_,he⟩ := avoids u u
  have h1 := congrFun h (pair i j)
  have h0 := congrFun h (fun _ => false)
  change edgeFunction (pair i j) = (pair i j u != b) at h1
  rw [he,hu] at h1
  change false = (false != b) at h0
  exact Bool.false_ne_true (h0.trans h1.symm)

theorem zero_available (v j : Fin 9) : Available [] (fun x => zeroAt v x j) := by
  by_cases h : j = v
  · simpa [zeroAt,h] using (Available.const (n := 9) (gates := []) false)
  · simpa [zeroAt,h] using (Available.input (gates := []) j)

theorem lift_available (v j : Fin 9) : Available [] (fun x => liftTheta v x j) := by
  rcases lift_coord v j with constant | ⟨i,h⟩
  · rw [show (fun x => liftTheta v x j) = (fun _ => false) from funext constant]
    exact .const _
  · rw [show (fun x => liftTheta v x j) = (fun x => x i) from funext h]
    exact .input _

theorem theta_of_cofactor (v : Fin 9) (hc : HasAIG 9 11 (fun x => edgeFunction (zeroAt v x))) :
    HasAIG 7 10 theta := by
  obtain ⟨a,b,hab,hd⟩ := mate_pivotal v
  have smaller := hc.restrict_essential (i := mate v) (liftTheta v) (lift_available v)
    ⟨false,fun x => (lift_zero v x).2⟩ hab hd (cofactor_not_raw v _)
  simpa only [zeroAt_lift,lift_correct] using smaller

theorem masked_first_forces_cofactor {G R : List (Signal 9)} {u v : Fin 9} {p q : Bool}
    (neq : u ≠ v) (size : G.length ≤ 13) (tr : ReadTrace u G R)
    (mem : (fun x => (x u != p) && (x v != q)) ∈ R) (out : Available G edgeFunction) :
    HasAIG 9 11 (fun x => edgeFunction (zeroAt u x)) := by
  obtain ⟨x,y,hx,hy,agree,diff⟩ := sensitiveWithFixedInput u v neq q
  have two := tr.two_of_masked agree out diff (edge_not_raw u) mem
    (by simp only [hx, hy, bne_self_eq_false, Bool.and_false])
  obtain ⟨D,built,sz,hout⟩ := restrict_of_readTrace tr (zeroAt u) (zero_available u)
    ⟨false,fun _ => by simp [zeroAt]⟩ out
  exact ⟨D,built,by omega,hout⟩


theorem edge_not_initial : ¬ Available [] edgeFunction := by
  intro h
  rcases initial_cases h with ⟨b,hb⟩ | ⟨u,p,hp⟩
  · obtain ⟨i,j,_,_,he⟩ := avoids 0 0
    have h1 := congrFun hb (pair i j)
    have h0 := congrFun hb (fun _ => false)
    change edgeFunction (pair i j) = b at h1
    change false = b at h0
    rw [he] at h1
    exact Bool.false_ne_true (h0.trans h1.symm)
  · exact edge_not_raw u ⟨p,hp⟩

/-- A thirteen-AND AIG for the Petersen target gives a ten-AND AIG for theta.
Two gates read a first operand and another gate is lost at the second deletion. -/
theorem theta_of_petersen (aig : HasAIG 9 13 edgeFunction) : HasAIG 7 10 theta := by
  obtain ⟨pre,s,built,out,notFree,sz,_⟩ := minimal_first_nonfree aig edge_not_initial
  obtain ⟨a,b,tail,hTail,ha,hb,firstRead⟩ := built.firstRead (by simp)
  have firstEq : s = (fun x => a x && b x) := by
    simpa using congrArg (fun es : List (Signal 9) => es.getLast?) hTail
  rw [firstEq] at notFree
  obtain ⟨u,v,p,q,neq,rfl,rfl⟩ := availableInputsOfNonfreeMeet ha hb notFree
  obtain ⟨R,t,mem⟩ := firstRead u (.inl ⟨p,rfl⟩)
  exact theta_of_cofactor u (masked_first_forces_cofactor neq (by simpa using sz) t mem out)

/-- Conditional form of the flipped-input child, with no reader-count premise. -/
theorem flipped_of_no_theta (no : ¬ HasAIG 7 10 theta)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (sz : C.size ≤ 14) :
    ∃ a, PEqualNP.MetaComplexity.circuitFun 9 C (PetersenSingleRead2541.signed true a) ≠ edgeFunction a :=
  flipped_rejection_of_no_aig13 (fun h => no (theta_of_petersen h)) C fan sz

end PEqualNP.Search.PetersenTheta2541
