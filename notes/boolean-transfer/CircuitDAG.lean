import Init

/-! A shared indexed gate may be read arbitrarily often. Three arithmetic slots per
Boolean gate give fixed addresses independent of the gate type. -/
namespace BooleanTransfer

inductive Gate (V : Type) (n : Nat) where
  | input (v : V)
  | bit (b : Bool)
  | neg (i : Fin n)
  | conj (i j : Fin n)
  | disj (i j : Fin n)

inductive Net (V : Type) : Nat → Type where
  | empty : Net V 0
  | push {n} (p : Net V n) (g : Gate V n) : Net V (n+1)

-- In the Boolean references, zero is the most recently appended gate.
def Gate.value (x : V → Bool) (previous : Fin n → Bool) : Gate V n → Bool
  | .input v => x v
  | .bit b => b
  | .neg i => !(previous i)
  | .conj i j => previous i && previous j
  | .disj i j => previous i || previous j

def Net.values (x : V → Bool) : {n : Nat} → Net V n → Fin n → Bool
  | _, .empty => Fin.elim0
  | _, .push p g => Fin.cases (g.value x (p.values x)) (p.values x)

structure Arithmetic (V P : Type) where
  var : V → P
  lit : Bool → P
  add : P → P → P
  mul : P → P → P

structure Reads (A : Arithmetic V P) where
  ev : (V → Bool) → P → Bool
  var : ∀ x v, ev x (A.var v) = x v
  lit : ∀ x b, ev x (A.lit b) = b
  add : ∀ x a b, ev x (A.add a b) = Bool.xor (ev x a) (ev x b)
  mul : ∀ x a b, ev x (A.mul a b) = (ev x a && ev x b)

inductive ValidAt (A : Arithmetic V P) (l : Nat → P) (k : Nat) : Prop where
  | var (v) : l k = A.var v → ValidAt A l k
  | lit (b) : l k = A.lit b → ValidAt A l k
  | add (i j) : i < k → j < k → l k = A.add (l i) (l j) → ValidAt A l k
  | mul (i j) : i < k → j < k → l k = A.mul (l i) (l j) → ValidAt A l k

private theorem ValidAt.copy {A : Arithmetic V P} {l l' : Nat → P} {k : Nat}
    (h : ValidAt A l k) (agree : ∀ j ≤ k, l' j = l j) : ValidAt A l' k := by
  cases h with
  | var v e => exact .var v ((agree k (Nat.le_refl _)).trans e)
  | lit b e => exact .lit b ((agree k (Nat.le_refl _)).trans e)
  | add i j hi hj e =>
    apply ValidAt.add i j hi hj
    rw [agree k (by omega), agree i (by omega), agree j (by omega), e]
  | mul i j hi hj e =>
    apply ValidAt.mul i j hi hj
    rw [agree k (by omega), agree i (by omega), agree j (by omega), e]

def address : {n : Nat} → Fin n → Nat
  | 0 => Fin.elim0
  | n+1 => Fin.cases (3*n+2) address

theorem address_lt (i : Fin n) : address i < 3*n := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [address]; omega
    · simp [address]; have := ih j; omega

/-- Constant-time word arithmetic suffices to emit the backward reference. -/
theorem address_formula (i : Fin n) : address i = 3*(n-1-i.val)+2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [address]
    · simp only [address, Fin.cases_succ, Fin.val_succ]
      rw [ih]
      omega

private def slots (A : Arithmetic V P) (p : Fin n → P) : Gate V n → P × P × P
  | .input v => (A.var v, A.lit false, A.var v)
  | .bit b => (A.lit b, A.lit false, A.lit b)
  | .neg i => (A.lit true, A.lit false, A.add (p i) (A.lit true))
  | .conj i j => (A.lit false, A.lit false, A.mul (p i) (p j))
  | .disj i j => (A.add (p i) (p j), A.mul (p i) (p j),
      A.add (A.add (p i) (p j)) (A.mul (p i) (p j)))

private def extend (l : Nat → P) (s : Nat) (t : P × P × P) (k : Nat) : P :=
  if k < s then l k else if k = s then t.1 else if k = s+1 then t.2.1 else t.2.2

private theorem extend_old (l : Nat → P) (t : P × P × P) (h : k < s) :
    extend l s t k = l k := by simp [extend, h]

@[simp] private theorem extend0 (l : Nat → P) (s : Nat) (t : P × P × P) :
    extend l s t s = t.1 := by simp [extend]

@[simp] private theorem extend1 (l : Nat → P) (s : Nat) (t : P × P × P) :
    extend l s t (s+1) = t.2.1 := by simp [extend, show ¬s+1<s by omega]

@[simp] private theorem extend2 (l : Nat → P) (s : Nat) (t : P × P × P) :
    extend l s t (s+2) = t.2.2 := by simp [extend, show ¬s+2<s by omega]

def compile (A : Arithmetic V P) : {n : Nat} → Net V n → Nat → P
  | _, .empty => fun _ => A.lit false
  | _, .push (n := n) p g =>
    extend (compile A p) (3*n) (slots A (fun i => compile A p (address i)) g)

theorem compile_valid (A : Arithmetic V P) (p : Net V n) :
    ∀ k < 3*n, ValidAt A (compile A p) k := by
  induction p with
  | empty => intro k hk; omega
  | @push n p g ih =>
    intro k hk
    let l := compile A p
    let t := slots A (fun i => l (address i)) g
    change ValidAt A (extend l (3*n) t) k
    by_cases old : k < 3*n
    · exact (ih k old).copy (fun j hj => extend_old _ _ (by omega))
    have ha (i : Fin n) : address i < 3*n := address_lt i
    have hread (i : Fin n) : extend l (3*n) t (address i) = l (address i) :=
      extend_old _ _ (ha i)
    have next : k = 3*n ∨ k = 3*n+1 ∨ k = 3*n+2 := by omega
    rcases next with h|h|h <;> subst k
    · cases g with
      | input v => exact .var v (by simp [t, slots])
      | bit b => exact .lit b (by simp [t, slots])
      | neg i => exact .lit true (by simp [t, slots])
      | conj i j => exact .lit false (by simp [t, slots])
      | disj i j => exact .add _ _ (ha i) (ha j) (by simp only [extend0, hread]; rfl)
    · cases g with
      | input v => exact .lit false (by simp [t, slots])
      | bit b => exact .lit false (by simp [t, slots])
      | neg i => exact .lit false (by simp [t, slots])
      | conj i j => exact .lit false (by simp [t, slots])
      | disj i j =>
        apply ValidAt.mul (address i) (address j)
        · have := ha i; omega
        · have := ha j; omega
        · simp only [extend1, hread]; rfl
    · cases g with
      | input v => exact .var v (by simp [t, slots])
      | bit b => exact .lit b (by simp [t, slots])
      | neg i =>
        apply ValidAt.add (address i) (3*n)
        · have := ha i; omega
        · omega
        · simp only [extend2, extend0, hread]; rfl
      | conj i j =>
        apply ValidAt.mul (address i) (address j)
        · have := ha i; omega
        · have := ha j; omega
        · simp only [extend2, hread]; rfl
      | disj i j => exact .add (3*n) (3*n+1) (by omega) (by omega) (by simp [t, slots])

theorem compile_reads (A : Arithmetic V P) (R : Reads A) (x : V → Bool) (p : Net V n) :
    ∀ i : Fin n, R.ev x (compile A p (address i)) = p.values x i := by
  induction p with
  | empty => intro i; exact Fin.elim0 i
  | @push n p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [address, Fin.cases_zero, compile, extend2, Net.values]
      cases g with
      | input v => exact R.var x v
      | bit b => exact R.lit x b
      | neg a => simp [slots, Gate.value, R.add, R.lit, ih, Bool.xor]
      | conj a b => simp [slots, Gate.value, R.mul, ih]
      | disj a b =>
        simp only [slots, Gate.value, R.add, R.mul, ih]
        cases p.values x a <;> cases p.values x b <;> rfl
    · simp only [address, Fin.cases_succ, compile, Net.values]
      rw [extend_old _ _ (address_lt j)]
      exact ih j

def ArithmeticComputes (A : Arithmetic V P) (f : P) (s : Nat) : Prop :=
  ∃ l : Nat → P, (∀ k < s, ValidAt A l k) ∧ ∃ k < s, l k = f

theorem translate (A : Arithmetic V P) (R : Reads A) (p : Net V n) (out : Fin n) :
    ∃ f, ArithmeticComputes A f (3*n) ∧ ∀ x, R.ev x f = p.values x out :=
  ⟨_, ⟨compile A p, compile_valid A p, address out, address_lt out, rfl⟩,
   fun x => compile_reads A R x p out⟩

/-- The disjunctive trace predicate in upstream Statement.Computes, with its
four operations explicit and its constant type independent of the trace. -/
def SLPComputes (X : V → P) (C : K → P) (plus times : P → P → P) (f : P) (s : Nat) : Prop :=
  ∃ l : Nat → P,
    (∀ k < s, (∃ v : V, l k = X v) ∨ (∃ a : K, l k = C a) ∨
      (∃ i < k, ∃ j < k, l k = plus (l i) (l j)) ∨
      (∃ i < k, ∃ j < k, l k = times (l i) (l j))) ∧
    ∃ k < s, l k = f

theorem toSLP {A : Arithmetic V P} {f : P} {s : Nat}
    (h : ArithmeticComputes A f s) (C : K → P) (lits : ∀ b, ∃ a, A.lit b = C a) :
    SLPComputes A.var C A.add A.mul f s := by
  obtain ⟨l, hl, out⟩ := h
  refine ⟨l, ?_, out⟩
  intro k hk
  cases hl k hk with
  | var v e => exact Or.inl ⟨v, e⟩
  | lit b e =>
    obtain ⟨a, ha⟩ := lits b
    exact Or.inr (Or.inl ⟨a, e.trans ha⟩)
  | add i j hi hj e => exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, e⟩))
  | mul i j hi hj e => exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, e⟩))

abbrev DecisionFamily := (m : Nat) → (Fin m → Bool) → Bool

/-- m is the encoded input length; C and d are fixed across all lengths. -/
def PolyBool (L : DecisionFamily) : Prop :=
  ∃ C d : Nat, ∀ m, ∃ s : Nat, ∃ p : Net (Fin m) s, ∃ out : Fin s,
    s ≤ C * (m+1)^d ∧ ∀ x, p.values x out = L m x

end BooleanTransfer
