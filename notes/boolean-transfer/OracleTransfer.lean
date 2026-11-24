import Frobenius

/-!
# Low-degree elimination of nested Frobenius oracle calls

The graph has indexed shared wires. Ordinary gates apply polynomials to earlier
wires. An oracle gate may take the output of another oracle as an argument.
The reduced evaluator calls the same oracle only at scalar constant terms.
-/

namespace BooleanTransfer.OracleTransfer

open MvPolynomial

variable {R V W U : Type*} [CommRing R]

/-- Equality of all formal coefficients of total degree at most d. -/
def Agree (d : ℕ) (a b : MvPolynomial W R) : Prop :=
  ∀ m : W →₀ ℕ, m.degree ≤ d → coeff m a = coeff m b

private theorem agreeRefl (d : ℕ) (a : MvPolynomial W R) : Agree d a a := fun _ _ => rfl

private theorem agreeAdd {d : ℕ} {a b c e : MvPolynomial W R}
    (h : Agree d a b) (k : Agree d c e) : Agree d (a+c) (b+e) := by
  intro m hm
  simp only [coeff_add, h m hm, k m hm]

private theorem agreeMul {d : ℕ} {a b c e : MvPolynomial W R}
    (h : Agree d a b) (k : Agree d c e) : Agree d (a*c) (b*e) := by
  classical
  intro m hm
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  have e := Finset.mem_antidiagonal.mp hij
  change i + j = m at e
  have deg : i.degree + j.degree = m.degree := by rw [← e, map_add]
  exact congrArg₂ (· * ·) (h i (by omega)) (k j (by omega))

/-- Substitution at any ordinary polynomial gate preserves coefficient agreement. -/
theorem substitute {d : ℕ} (a b : U → MvPolynomial W R) (h : ∀ i, Agree d (a i) (b i))
    (f : MvPolynomial U R) : Agree d (eval₂ C a f) (eval₂ C b f) := by
  apply MvPolynomial.induction_on f
  · intro c
    simp only [eval₂_C]
    exact agreeRefl _ _
  · intro p q hp hq
    simp only [eval₂_add]
    exact agreeAdd hp hq
  · intro p i hp
    simp only [eval₂_mul, eval₂_X]
    exact agreeMul hp (h i)

private theorem zeroSub (a : U → MvPolynomial W R) (f : MvPolynomial U R) :
    constantCoeff (eval₂ C a f) = eval (fun i => constantCoeff (a i)) f := by
  apply MvPolynomial.induction_on f
  · intro c; simp
  · intro p q hp hq; simp [hp, hq]
  · intro p i hp; simp [hp]

private theorem scalarPower (two : (2 : R) = 0) (j d : ℕ) (cut : d < 2^j)
    (p : MvPolynomial W R) : Agree d (p^(2^j)) (C (constantCoeff (p^(2^j)))) := by
  classical
  intro m hm
  by_cases zero : m = 0
  · subst m
    simp [constantCoeff_eq]
  · have pos : 0 < m.degree := Nat.pos_of_ne_zero (fun h => zero ((Finsupp.degree_eq_zero_iff m).mp h))
    have e := congrArg (coeff m) (Frobenius.erase_component two p j m.degree pos (hm.trans_lt cut))
    simpa only [coeff_homogeneousComponent, ite_true, eq_self, coeff_zero, coeff_C_of_ne_zero zero] using e

/-- A scalar oracle replacement uses only the values at the constant terms of
the argument polynomials. The full and reduced argument vectors may differ. -/
theorem oracle (two : (2 : R) = 0) (j d : ℕ) (cut : d < 2^j)
    (p : MvPolynomial U R) (a b : U → MvPolynomial W R)
    (h : ∀ i, Agree d (a i) (b i)) :
    Agree d (eval₂ C a (p^(2^j))) (C (eval (fun i => constantCoeff (b i)) (p^(2^j)))) := by
  intro m hm
  have changeArgs := substitute a b h (p^(2^j)) m hm
  rw [changeArgs, ← zeroSub]
  simp only [eval₂_pow]
  exact scalarPower two j d cut (eval₂ C b p) m hm

/-- An ordinary polynomial can read any earlier wires with any fanout. -/
inductive Gate (R V U : Type*) [CommRing R] (n : ℕ) where
  | input (v : V)
  | ordinary (f : MvPolynomial (Fin n) R)
  | query (args : U → Fin n)

/-- Wire zero denotes the most recently appended gate. -/
inductive Net (R V U : Type*) [CommRing R] : ℕ → Type _ where
  | empty : Net R V U 0
  | push {n} (prev : Net R V U n) (gate : Gate R V U n) : Net R V U (n+1)

noncomputable def Gate.value {n : ℕ} (x : V → MvPolynomial W R)
    (call : (U → MvPolynomial W R) → MvPolynomial W R) (prev : Fin n → MvPolynomial W R) :
    Gate R V U n → MvPolynomial W R
  | .input v => x v
  | .ordinary f => eval₂ C prev f
  | .query args => call (fun i => prev (args i))

noncomputable def Net.values (x : V → MvPolynomial W R)
    (call : (U → MvPolynomial W R) → MvPolynomial W R) :
    {n : ℕ} → Net R V U n → Fin n → MvPolynomial W R
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.value x call (prev.values x call)) (prev.values x call)

/-- Every wire of every acyclic oracle graph has the same low coefficients
after replacing all calls, including calls depending on earlier calls. -/
theorem wires (two : (2 : R) = 0) (j d : ℕ) (cut : d < 2^j)
    (p : MvPolynomial U R) {n : ℕ} (net : Net R V U n)
    (x y : V → MvPolynomial W R) (inputs : ∀ v, Agree d (x v) (y v)) :
    ∀ i, Agree d (net.values x (fun a => eval₂ C a (p^(2^j))) i)
      (net.values y (fun b => C (eval (fun u => constantCoeff (b u)) (p^(2^j)))) i) := by
  induction net with
  | empty => intro i; exact Fin.elim0 i
  | push prev gate ih =>
    refine Fin.cases ?_ ih
    cases gate with
    | input v => exact inputs v
    | ordinary f => exact substitute _ _ ih f
    | query args => exact oracle two j d cut p _ _ (fun u => ih (args u))

/-- Agreement of coefficients gives formal polynomial equality of each output layer. -/
theorem component {d : ℕ} {a b : MvPolynomial W R} (h : Agree d a b) (k : ℕ) (hk : k ≤ d) :
    homogeneousComponent k a = homogeneousComponent k b := by
  ext m
  simp only [coeff_homogeneousComponent]
  split
  · rename_i hm
    exact h m (hm ▸ hk)
  · rfl

private noncomputable def Gate.scalar {n : ℕ} (x : V → R) (q : MvPolynomial U R)
    (prev : Fin n → R) : Gate R V U n → R
  | .input v => x v
  | .ordinary f => eval prev f
  | .query args => eval (fun u => prev (args u)) q

/-- One evaluation of the original graph with scalar inputs, in gate order. -/
noncomputable def Net.scalars (x : V → R) (q : MvPolynomial U R) :
    {n : ℕ} → Net R V U n → Fin n → R
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.scalar x q (prev.scalars x q)) (prev.scalars x q)

private noncomputable def Gate.freeze {n : ℕ} (scalars : Fin n → R) (q : MvPolynomial U R) :
    Gate R V U n → Gate R V U n
  | .input v => .input v
  | .ordinary f => .ordinary f
  | .query args => .ordinary (C (eval (fun u => scalars (args u)) q))

/-- Replace each query by a literal computed in the scalar evaluation of the original graph. -/
noncomputable def Net.freeze (x : V → R) (q : MvPolynomial U R) :
    {n : ℕ} → Net R V U n → Net R V U n
  | _, .empty => .empty
  | _, .push prev g => .push (prev.freeze x q) (g.freeze (prev.scalars x q) q)

def Net.queryFree : {n : ℕ} → Net R V U n → Prop
  | _, .empty => True
  | _, .push prev g => prev.queryFree ∧ match g with
    | .query _ => False
    | _ => True

theorem removed (x : V → R) (q : MvPolynomial U R) {n : ℕ} (net : Net R V U n) :
    (net.freeze x q).queryFree := by
  induction net with
  | empty => trivial
  | push prev gate ih =>
    refine ⟨ih, ?_⟩
    cases gate <;> trivial

private theorem scalarTrace (x : V → MvPolynomial W R) (q : MvPolynomial U R)
    {n : ℕ} (net : Net R V U n) :
    ∀ i, constantCoeff (net.values x (fun b => C (eval (fun u => constantCoeff (b u)) q)) i) =
      net.scalars (fun v => constantCoeff (x v)) q i := by
  induction net with
  | empty => intro i; exact Fin.elim0 i
  | push prev gate ih =>
    refine Fin.cases ?_ ih
    cases gate with
    | input v => rfl
    | ordinary f =>
      change constantCoeff (eval₂ C _ f) = eval _ f
      rw [zeroSub]
      exact congrArg (fun a => eval a f) (funext ih)
    | query args =>
      change constantCoeff (C _) = _
      rw [constantCoeff_C]
      exact congrArg (fun a => eval a q) (funext (fun u => ih (args u)))

private theorem replay (x : V → MvPolynomial W R) (q : MvPolynomial U R)
    (call : (U → MvPolynomial W R) → MvPolynomial W R) {n : ℕ} (net : Net R V U n) :
    ∀ i, (net.freeze (fun v => constantCoeff (x v)) q).values x call i =
      net.values x (fun b => C (eval (fun u => constantCoeff (b u)) q)) i := by
  induction net with
  | empty => intro i; exact Fin.elim0 i
  | push prev gate ih =>
    refine Fin.cases ?_ ih
    cases gate with
    | input v => rfl
    | ordinary f =>
      exact congrArg (fun a => eval₂ C a f) (funext ih)
    | query args =>
      change eval₂ C _ (C _) = C _
      rw [eval₂_C]
      exact congrArg (fun a => C (eval a q)) (funext (fun u => (scalarTrace x q prev (args u)).symm))

/-- The explicitly query-free graph has the same formal low-degree layers at every wire.
All replacement constants are obtained in one scalar evaluation of the original graph.
The interpretation of query gates on the frozen graph can be chosen arbitrarily. -/
theorem eliminate (two : (2 : R) = 0) (j d : ℕ) (cut : d < 2^j)
    (p : MvPolynomial U R) {n : ℕ} (net : Net R V U n) (x : V → MvPolynomial W R)
    (call : (U → MvPolynomial W R) → MvPolynomial W R) (i : Fin n) (k : ℕ) (hk : k ≤ d) :
    homogeneousComponent k (net.values x (fun a => eval₂ C a (p^(2^j))) i) =
      homogeneousComponent k ((net.freeze (fun v => constantCoeff (x v)) (p^(2^j))).values x call i) := by
  rw [replay]
  exact component (wires two j d cut p net x x (fun _ => agreeRefl _ _) i) k hk

#print axioms substitute
#print axioms oracle
#print axioms wires
#print axioms component
#print axioms removed
#print axioms eliminate

end BooleanTransfer.OracleTransfer
