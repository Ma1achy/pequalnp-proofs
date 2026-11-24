import PEqualNP.Defs.SearchQ

/-! Encoding costs for carrying all the proof's false constant equations as a
shared disjunctive context until the last simplification. -/

namespace PEqualNP.Search.Helpers

variable {V : Type}

/-- All occurrences of equations of the form `0 = c`, for nonzero `c`. -/
noncomputable def falseConstants (π : List (QLine V)) : QLine V := by
  classical
  exact π.flatten.filter (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0))

@[simp] theorem mem_falseConstants {e : QEq V} {π : List (QLine V)} :
    e ∈ falseConstants π ↔ (∃ L ∈ π, e ∈ L) ∧ e.1 = 0 ∧ e.2 ≠ 0 := by
  classical
  simp [falseConstants, List.mem_flatten]
  grind

variable [Fintype V]

/-- Sum of equation costs, excluding the single line marker. -/
def qWeight (L : QLine V) : ℕ := (L.map QEq.size).sum

/-- Encoded cost of one line, including its line marker. -/
def qCost (L : QLine V) : ℕ := 1 + qWeight L

@[simp] theorem qWeight_append (C G : QLine V) : qWeight (C ++ G) = qWeight C + qWeight G := by
  simp [qWeight]

@[simp] theorem qCost_append (C G : QLine V) : qCost (C ++ G) = qCost C + qWeight G := by
  simp [qCost, Nat.add_assoc]

@[simp] theorem qWeight_nil : qWeight ([] : QLine V) = 0 := rfl

@[simp] theorem qSize_cons (L : QLine V) (π : List (QLine V)) :
    resLinQSize (L :: π) = qCost L + resLinQSize π := rfl

/-- Resolving padded lines produces two copies of the common tail before contraction. -/
theorem qCost_padded_res (e : QEq V) (C D G : QLine V) :
    qCost (e :: ((C ++ G) ++ (D ++ G))) = qCost (e :: (C ++ D)) + 2 * qWeight G := by
  simp only [qCost, qWeight, List.map_cons, List.sum_cons, List.map_append, List.sum_append]
  omega

theorem qCost_le_of_mem {L : QLine V} {π : List (QLine V)} (hm : L ∈ π) :
    qCost L ≤ resLinQSize π := by
  induction π with
  | nil => simp at hm
  | cons C π ih =>
    rw [qSize_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · exact (ih hm).trans (Nat.le_add_left _ _)

/-- The encoding pays at least one unit per equation occurrence. -/
theorem qLength_le_weight (K : QLine V) : K.length ≤ qWeight K := by
  induction K with
  | nil => simp
  | cons e K ih =>
    have : 1 ≤ e.size := by unfold QEq.size; omega
    change K.length + 1 ≤ e.size + qWeight K
    omega

/-- A uniform bound on line cost bounds the encoded cost of the full trace. -/
theorem qSize_le_length_mul {ρ : List (QLine V)} {M : ℕ} (hb : ∀ L ∈ ρ, qCost L ≤ M) :
    resLinQSize ρ ≤ ρ.length * M := by
  induction ρ with
  | nil => simp [resLinQSize]
  | cons L ρ ih =>
    have ht := ih (fun L hL => hb L (.tail _ hL))
    have hl := hb L List.mem_cons_self
    rw [qSize_cons, List.length_cons, Nat.succ_mul]
    omega

theorem qlength_le_size (π : List (QLine V)) : π.length ≤ resLinQSize π := by
  induction π with
  | nil => simp [resLinQSize]
  | cons C π ih => simp only [List.length_cons, qSize_cons, qCost]; omega

private theorem qWeight_filter_le (f : QEq V → Bool) (L : QLine V) :
    qWeight (L.filter f) ≤ qWeight L := by
  induction L with
  | nil => simp
  | cons e L ih =>
    cases h : f e <;> simp [h, qWeight] at * <;> omega

/-- The list of all false constants costs at most the original proof, even
before any duplicates are removed. -/
theorem qWeight_falseConstants_le (π : List (QLine V)) :
    qWeight (falseConstants π) ≤ resLinQSize π := by
  classical
  refine (qWeight_filter_le _ π.flatten).trans ?_
  induction π with
  | nil => simp [resLinQSize]
  | cons L π ih =>
    simp only [List.flatten_cons, qWeight_append, qSize_cons, qCost]
    omega

end PEqualNP.Search.Helpers
