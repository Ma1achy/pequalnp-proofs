import PEqualNP.Search.PetersenAIG2541

/-! First-gate normalization for AND-inverter graphs. A size-minimal graph
for a function that is unavailable initially begins with a genuine AND of
two signed literals on distinct raw inputs. -/

namespace PEqualNP.Search.PetersenAIG2541

theorem Available.substitute {n : ℕ} {D E : List (Signal n)} {f : Signal n}
    (ha : Available D f) (read : ∀ g ∈ D, Available E g) : Available E f := by
  induction ha with
  | const => exact .const _
  | input => exact .input _
  | gate hg => exact read _ hg
  | inv _ ih => exact .inv ih

/-- Remove a free first signal even if several later gates read it. -/
theorem Available.removeFirstFree {n : ℕ} {s f : Signal n} {pre : List (Signal n)}
    (hf : Available (pre ++ [s]) f) (hs : Available [] s) : Available pre f := by
  apply hf.substitute
  intro w hw
  rcases List.mem_append.1 hw with before | last
  · exact .gate before
  · have e := List.mem_singleton.1 last
    subst w
    exact hs.substitute (by simp)

private theorem Built.parts {n : ℕ} {s : Signal n} {D : List (Signal n)} (h : Built (s::D)) :
    ∃ a b, s = (fun x => a x && b x) ∧ Built D ∧ Available D a ∧ Available D b := by
  cases h with
  | and prior ha hb => exact ⟨_,_,rfl,prior,ha,hb⟩

theorem Built.removeFirstFree {n : ℕ} {s : Signal n} (pre : List (Signal n))
    (hs : Available [] s) (hb : Built (pre ++ [s])) : Built pre := by
  induction pre with
  | nil => exact .nil
  | cons g pre ih =>
    obtain ⟨a,b,rfl,ht,ha,hb⟩ := Built.parts hb
    exact .and (ih ht) (ha.removeFirstFree hs) (hb.removeFirstFree hs)

/-- Choose a shortest witness. Its first gate emits a signal unavailable to
the empty graph, independent of which operand representation is later used. -/
theorem minimal_first_nonfree {n k : ℕ} {f : Signal n} (feasible : HasAIG n k f)
    (nonfree : ¬Available [] f) :
    ∃ (pre : List (Signal n)) (s : Signal n), Built (pre ++ [s]) ∧
      Available (pre ++ [s]) f ∧ ¬Available [] s ∧ pre.length+1 ≤ k ∧
      ∀ D : List (Signal n), Built D → Available D f → pre.length+1 ≤ D.length := by
  classical
  obtain ⟨D,bD,size,aD⟩ := feasible
  let P (j : ℕ) := ∃ E : List (Signal n), Built E ∧ Available E f ∧ E.length = j
  have hex : ∃ j, P j := ⟨D.length,D,bD,aD,rfl⟩
  obtain ⟨E,be,ae,small⟩ := Nat.find_spec hex
  have least (T : List (Signal n)) (bt : Built T) (at' : Available T f) : E.length ≤ T.length := by
    rw [small]
    exact Nat.find_min' hex ⟨T,bt,at',rfl⟩
  have parts : E = [] ∨ ∃ pre s, E = pre ++ [s] := by
    induction E using List.reverseRecOn with
    | nil => exact Or.inl rfl
    | append_singleton pre s _ => exact Or.inr ⟨pre,s,rfl⟩
  rcases parts with rfl | ⟨pre,s,rfl⟩
  · exact (nonfree ae).elim
  have pos : ¬ Available [] s := by
    intro hs
    have bad := least pre (be.removeFirstFree pre hs) (ae.removeFirstFree hs)
    simp at bad
  refine ⟨pre,s,be,ae,pos,?_,?_⟩
  · simpa using (least D bD aD).trans size
  · intro T bt at'
    simpa using least T bt at'

theorem initial_cases {n : ℕ} {f : Signal n} (h : Available [] f) :
    (∃ b : Bool, f = fun _ => b) ∨
    ∃ (i : Fin n) (p : Bool), f = fun x => x i != p := by
  induction h with
  | const c => exact Or.inl ⟨c,rfl⟩
  | input i => exact Or.inr ⟨i,false,by funext x; simp⟩
  | gate hm => contradiction
  | inv _ ih =>
    rcases ih with ⟨c,rfl⟩ | ⟨i,p,rfl⟩
    · exact Or.inl ⟨!c,rfl⟩
    · exact Or.inr ⟨i,!p,by funext x; change (!(x i != p)) = (x i != (!p)); cases p <;> cases x i <;> rfl⟩

private theorem unary_meet_free {n : ℕ} (u : Fin n) (p q : Bool) :
    Available [] (fun x : Fin n → Bool => (x u != p) && (x u != q)) := by
  cases p <;> cases q
  · simpa using (Available.input (gates := []) u)
  · convert (Available.const (gates := []) (n := n) false) using 1
    funext x
    cases x u <;> rfl
  · convert (Available.const (gates := []) (n := n) false) using 1
    funext x
    cases x u <;> rfl
  · simpa using (Available.inv (Available.input (gates := []) u))

/-- For any given decomposition of a nonfree first AND, its two operands are
signed literals on distinct raw inputs. -/
theorem availableInputsOfNonfreeMeet {n : ℕ} {a b : Signal n}
    (ha : Available [] a) (hb : Available [] b)
    (nonfree : ¬Available [] (fun x => a x && b x)) :
    ∃ (u v : Fin n) (p q : Bool), u ≠ v ∧
      a = (fun x => x u != p) ∧ b = (fun x => x v != q) := by
  rcases initial_cases ha with ⟨c,rfl⟩ | ⟨u,p,rfl⟩
  · exfalso
    apply nonfree
    cases c
    · exact .const false
    · simpa using hb
  rcases initial_cases hb with ⟨c,rfl⟩ | ⟨v,q,rfl⟩
  · exfalso
    apply nonfree
    cases c
    · simpa using (Available.const (gates := []) (n := n) false)
    · simpa using ha
  refine ⟨u,v,p,q,?_,rfl,rfl⟩
  rintro rfl
  exact nonfree (unary_meet_free u p q)

end PEqualNP.Search.PetersenAIG2541
