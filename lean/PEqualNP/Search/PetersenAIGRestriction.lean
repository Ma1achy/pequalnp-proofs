import PEqualNP.Search.PetersenAIG2541

/-! Under a literal substitution fixing input i, every AND reading either
polarity of i costs zero gates. Other gates may share the surviving signals
arbitrarily. A pair of assignments witnesses when another read is necessary. -/

namespace PEqualNP.Search.PetersenAIG2541

def RawLiteral {n : ℕ} (i : Fin n) (f : Signal n) : Prop :=
  ∃ b : Bool, f = fun x => x i != b

/-- The second list records every AND with a signed occurrence of i as an operand
in this particular straight-line realization, including repeated gates. -/
inductive ReadTrace {n : ℕ} (i : Fin n) : List (Signal n) → List (Signal n) → Prop where
  | nil : ReadTrace i [] []
  | read {G R : List (Signal n)} {a b : Signal n} (prior : ReadTrace i G R)
      (ha : Available G a) (hb : Available G b)
      (touch : RawLiteral i a ∨ RawLiteral i b) :
      ReadTrace i ((fun x => a x && b x) :: G) ((fun x => a x && b x) :: R)
  | skip {G R : List (Signal n)} {a b : Signal n} (prior : ReadTrace i G R)
      (ha : Available G a) (hb : Available G b)
      (na : ¬ RawLiteral i a) (nb : ¬ RawLiteral i b) :
      ReadTrace i ((fun x => a x && b x) :: G) R

theorem Built.readTrace {n : ℕ} {G : List (Signal n)} (built : Built G) (i : Fin n) :
    ∃ R, ReadTrace i G R := by
  induction built with
  | nil => exact ⟨[],.nil⟩
  | @and G a b _ ha hb ih =>
    obtain ⟨R,tr⟩ := ih
    by_cases touch : RawLiteral i a ∨ RawLiteral i b
    · exact ⟨_,.read tr ha hb touch⟩
    · exact ⟨_,.skip tr ha hb (fun h => touch (.inl h)) (fun h => touch (.inr h))⟩

/-- Inspect the earliest AND and choose the same realization when counting its
reads higher in the DAG. No well-formedness condition on external wire numbers
is needed in the semantic-signal model. -/
theorem Built.firstRead {n : ℕ} {G : List (Signal n)} (built : Built G) (hne : G ≠ []) :
    ∃ a b : Signal n, ∃ tail : List (Signal n), G = tail ++ [fun x => a x && b x] ∧
      Available [] a ∧ Available [] b ∧
      ∀ i : Fin n, RawLiteral i a ∨ RawLiteral i b →
        ∃ R, ReadTrace i G R ∧ (fun x => a x && b x) ∈ R := by
  classical
  induction built with
  | nil => contradiction
  | @and G a b old ha hb ih =>
    by_cases empty : G = []
    · subst G
      refine ⟨a,b,[],rfl,ha,hb,?_⟩
      intro i touch
      exact ⟨_,.read .nil ha hb touch,List.mem_cons_self⟩
    · obtain ⟨u,v,T,eq,hu,hv,tr⟩ := ih empty
      refine ⟨u,v,(fun x => a x && b x)::T,by rw [eq]; rfl,hu,hv,?_⟩
      intro i first
      obtain ⟨R,p,m⟩ := tr i first
      by_cases touch : RawLiteral i a ∨ RawLiteral i b
      · exact ⟨_,.read p ha hb touch,List.mem_cons_of_mem _ m⟩
      · exact ⟨_,.skip p ha hb (fun h => touch (.inl h)) (fun h => touch (.inr h)),m⟩

private theorem available_mono {n : ℕ} {G D : List (Signal n)} {f : Signal n}
    (hf : Available G f) (sub : ∀ g ∈ G, g ∈ D) : Available D f := by
  induction hf with
  | const b => exact .const b
  | input i => exact .input i
  | gate h => exact .gate (sub _ h)
  | inv _ ih => exact .inv ih

private theorem available_subst {n m : ℕ} {φ : (Fin m → Bool) → Fin n → Bool}
    (raw : ∀ j, Available [] (fun x => φ x j)) {G : List (Signal n)} {D : List (Signal m)}
    (old : ∀ g ∈ G, Available D (fun x => g (φ x))) {f : Signal n} (hf : Available G f) :
    Available D (fun x => f (φ x)) := by
  induction hf with
  | const b => exact .const b
  | input j => exact available_mono (raw j) (by simp)
  | gate h => exact old _ h
  | inv _ ih => exact .inv ih

private theorem available_fixed_and {n m : ℕ} {φ : (Fin m → Bool) → Fin n → Bool}
    {i : Fin n} (fixed : ∃ c, ∀ x, φ x i = c) {a b : Signal n} {D : List (Signal m)}
    (ha : Available D (fun x => a (φ x))) (hb : Available D (fun x => b (φ x)))
    (touch : RawLiteral i a ∨ RawLiteral i b) :
    Available D (fun x => a (φ x) && b (φ x)) := by
  obtain ⟨c,hc⟩ := fixed
  rcases touch with ⟨s,rfl⟩ | ⟨s,rfl⟩
  · cases c <;> cases s <;> simp [hc] <;> first | exact .const false | exact hb
  · cases c <;> cases s <;> simp [hc] <;> first | exact .const false | exact ha

private theorem ReadTrace.compile_subst {n m : ℕ} {i : Fin n} {G R : List (Signal n)}
    (tr : ReadTrace i G R) (φ : (Fin m → Bool) → Fin n → Bool)
    (raw : ∀ j, Available [] (fun x => φ x j)) (fixed : ∃ c, ∀ x, φ x i = c) :
    ∃ D : List (Signal m), Built D ∧ D.length + R.length ≤ G.length ∧
      ∀ g ∈ G, Available D (fun x => g (φ x)) := by
  induction tr with
  | nil => exact ⟨[],.nil,by simp,by simp⟩
  | read _ ha hb touch ih =>
    obtain ⟨D,built,size,keep⟩ := ih
    refine ⟨D,built,by simp; omega,?_⟩
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hold
    · exact available_fixed_and fixed (available_subst raw keep ha) (available_subst raw keep hb) touch
    · exact keep g hold
  | @skip G R a b _ ha hb _ _ ih =>
    obtain ⟨D,built,size,keep⟩ := ih
    let next : Signal m := fun x => a (φ x) && b (φ x)
    refine ⟨next :: D,.and built (available_subst raw keep ha) (available_subst raw keep hb),by simp; omega,?_⟩
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hold
    · exact .gate List.mem_cons_self
    · exact available_mono (keep g hold) (fun s hs => List.mem_cons_of_mem next hs)

/-- A chosen substitution fixes i, so all recorded reads of i can be removed at once. -/
theorem restrict_of_readTrace {n m : ℕ} {i : Fin n} {G R : List (Signal n)}
    (tr : ReadTrace i G R) (φ : (Fin m → Bool) → Fin n → Bool)
    (raw : ∀ j, Available [] (fun x => φ x j)) (fixed : ∃ c, ∀ x, φ x i = c)
    {f : Signal n} (out : Available G f) :
    HasAIG m (G.length - R.length) (fun x => f (φ x)) := by
  obtain ⟨D,built,size,keep⟩ := tr.compile_subst φ raw fixed
  exact ⟨D,built,by omega,available_subst raw keep out⟩

private theorem available_agree_or_raw {n : ℕ} {i : Fin n} {x y : Fin n → Bool}
    (agree : ∀ j, j ≠ i → x j = y j) {G : List (Signal n)}
    (stable : ∀ g ∈ G, g x = g y) {f : Signal n} (hf : Available G f) :
    f x = f y ∨ RawLiteral i f := by
  induction hf with
  | const => exact .inl rfl
  | input j =>
    by_cases h : j = i
    · subst j; exact .inr ⟨false,by simp⟩
    · exact .inl (agree j h)
  | gate h => exact .inl (stable _ h)
  | inv _ ih =>
    rcases ih with h | ⟨b,rfl⟩
    · exact .inl (congrArg Bool.not h)
    · exact .inr ⟨!b,by cases b <;> simp⟩

/-- A pivotal pair differing only in i must be distinguished by at least one of
the recorded reads when the output is more than a literal of i. -/
theorem ReadTrace.exists_changing {n : ℕ} {i : Fin n} {G R : List (Signal n)}
    (tr : ReadTrace i G R) {x y : Fin n → Bool} (agree : ∀ j, j ≠ i → x j = y j)
    {f : Signal n} (out : Available G f) (diff : f x ≠ f y) (proper : ¬ RawLiteral i f) :
    ∃ g ∈ R, g x ≠ g y := by
  by_contra! stable
  have gate_agree : ∀ g ∈ G, g x = g y := by
    clear out
    induction tr with
    | nil => simp
    | read prior ha hb touch ih =>
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hold
      · exact stable _ List.mem_cons_self
      · exact ih (fun s hs => stable s (List.mem_cons_of_mem _ hs)) g hold
    | skip prior ha hb na nb ih =>
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hold
      · exact congrArg₂ Bool.and
          ((available_agree_or_raw agree (ih stable) ha).resolve_right na)
          ((available_agree_or_raw agree (ih stable) hb).resolve_right nb)
      · exact ih stable g hold
  exact diff ((available_agree_or_raw agree gate_agree out).resolve_right proper)

/-- Fixing an essential variable in a function more complicated than a signed
literal saves at least one binary gate in any AIG budget. -/
theorem HasAIG.restrict_essential {n m k : ℕ} {i : Fin n} {f : Signal n}
    (aig : HasAIG n k f) (φ : (Fin m → Bool) → Fin n → Bool)
    (raw : ∀ j, Available [] (fun x => φ x j)) (fixed : ∃ c, ∀ x, φ x i = c)
    {x y : Fin n → Bool} (agree : ∀ j, j ≠ i → x j = y j)
    (diff : f x ≠ f y) (proper : ¬ RawLiteral i f) :
    HasAIG m (k - 1) (fun x => f (φ x)) := by
  obtain ⟨G,built,bound,out⟩ := aig
  obtain ⟨R,tr⟩ := built.readTrace i
  obtain ⟨s,hs,_⟩ := tr.exists_changing agree out diff proper
  have pos : 0 < R.length := List.length_pos_of_mem hs
  obtain ⟨D,bd,size,output⟩ := restrict_of_readTrace tr φ raw fixed out
  exact ⟨D,bd,by omega,output⟩

/-- If one known read is masked on a pivotal pair, a second read must distinguish it. -/
theorem ReadTrace.two_of_masked {n : ℕ} {i : Fin n} {G R : List (Signal n)}
    (tr : ReadTrace i G R) {x y : Fin n → Bool} (agree : ∀ j, j ≠ i → x j = y j)
    {f : Signal n} (out : Available G f) (diff : f x ≠ f y) (proper : ¬ RawLiteral i f)
    {s : Signal n} (masked : s ∈ R) (same : s x = s y) : 2 ≤ R.length := by
  obtain ⟨g,hg,hgxy⟩ := tr.exists_changing agree out diff proper
  by_contra! small
  rcases R with _ | ⟨r, _ | ⟨q,rs⟩⟩
  · simp at hg
  · simp only [List.mem_singleton] at hg masked
    exact hgxy (hg.symm ▸ masked ▸ same)
  · simp at small

end PEqualNP.Search.PetersenAIG2541
