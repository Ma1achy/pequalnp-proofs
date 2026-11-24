import PEqualNP.Defs.ProofComplexityLin

/-! A parity decision tree partitions Boolean assignments by its root-to-leaf
paths. Each path is represented by the linear clause falsified along that path. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

/-- At a node the low child is taken when the parity is zero, the high child when
it is one. A leaf returns its Boolean label. -/
inductive ParityTree (V : Type) where
  | leaf (label : Bool)
  | node (form : Finset V) (lo hi : ParityTree V)

namespace ParityTree

variable {V : Type}

/-- The Boolean output at an assignment. -/
def eval (t : ParityTree V) (a : V → Bool) : Bool :=
  match t with
  | .leaf b => b
  | .node f lo hi => if Odd (f.filter (fun v => a v = true)).card then hi.eval a else lo.eval a

/-- Number of leaves, counting distinct paths even if labels coincide. -/
def leaves : ParityTree V → ℕ
  | .leaf _ => 1
  | .node _ lo hi => lo.leaves + hi.leaves

theorem leaves_pos (t : ParityTree V) : 0 < t.leaves := by
  induction t with
  | leaf => simp [leaves]
  | node f lo hi hlo hhi => simp only [leaves]; omega

variable [DecidableEq V]

/-- Enumerate labeled paths, adding each path's blocking literals to the accumulator. -/
def cellsAt : ParityTree V → LinClause V → List (Bool × LinClause V)
  | .leaf b, G => [(b, G)]
  | .node f lo hi, G =>
      lo.cellsAt (insert (f, true) G) ++ hi.cellsAt (insert (f, false) G)

/-- All labeled leaf clauses. An assignment follows a path exactly when it falsifies
that path's blocking clause. -/
def cells (t : ParityTree V) : List (Bool × LinClause V) := t.cellsAt ∅

@[simp] theorem length_cellsAt (t : ParityTree V) (G : LinClause V) :
    (t.cellsAt G).length = t.leaves := by
  induction t generalizing G <;> simp_all [cellsAt, leaves]

@[simp] theorem length_cells (t : ParityTree V) : t.cells.length = t.leaves := by
  simp [cells]

private theorem cellsAt_union (t : ParityTree V) (G H : LinClause V) :
    t.cellsAt (G ∪ H) = (t.cellsAt H).map (fun p => (p.1, G ∪ p.2)) := by
  induction t generalizing H with
  | leaf => simp [cellsAt]
  | node f lo hi hlo hhi =>
    simp only [cellsAt, List.map_append]
    rw [← Finset.union_insert, ← Finset.union_insert, hlo, hhi]

theorem cellsAt_eq_map (t : ParityTree V) (G : LinClause V) :
    t.cellsAt G = t.cells.map (fun p => (p.1, G ∪ p.2)) := by
  simpa [cells] using cellsAt_union t G ∅

private theorem eval_of_mem_cellsAt (t : ParityTree V) (a : V → Bool) (G : LinClause V)
    {b : Bool} {C : LinClause V} (hm : (b,C) ∈ t.cellsAt G) (hf : ¬ LinClauseSat a C) :
    t.eval a = b ∧ ¬ LinClauseSat a G := by
  induction t generalizing G with
  | leaf label =>
    simp only [cellsAt, List.mem_singleton, Prod.mk.injEq] at hm
    exact ⟨hm.1.symm, hm.2 ▸ hf⟩
  | node f lo hi hlo hhi =>
    simp only [cellsAt, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨he, hg⟩ := hlo _ hm
      have hlow : ¬ Odd (f.filter (fun v => a v = true)).card := fun hodd =>
        hg ⟨(f,true), Finset.mem_insert_self _ _, by simpa [LinEqSat] using hodd⟩
      exact ⟨by simpa [eval, hlow] using he,
        fun ⟨e, hem, hes⟩ => hg ⟨e, Finset.mem_insert_of_mem hem, hes⟩⟩
    · obtain ⟨he, hg⟩ := hhi _ hm
      have hhigh : Odd (f.filter (fun v => a v = true)).card := by
        by_contra hodd
        exact hg ⟨(f,false), Finset.mem_insert_self _ _, by simpa [LinEqSat] using hodd⟩
      exact ⟨by simpa [eval, hhigh] using he,
        fun ⟨e, hem, hes⟩ => hg ⟨e, Finset.mem_insert_of_mem hem, hes⟩⟩

theorem eval_of_mem_cells (t : ParityTree V) (a : V → Bool) {b : Bool} {C : LinClause V}
    (hm : (b,C) ∈ t.cells) (hf : ¬ LinClauseSat a C) : t.eval a = b :=
  (eval_of_mem_cellsAt t a ∅ hm hf).1

private theorem exists_mem_cellsAt (t : ParityTree V) (a : V → Bool) (G : LinClause V)
    (hG : ¬ LinClauseSat a G) :
    ∃ C, (t.eval a, C) ∈ t.cellsAt G ∧ ¬ LinClauseSat a C := by
  induction t generalizing G with
  | leaf label => exact ⟨G, List.mem_cons_self, hG⟩
  | node f lo hi hlo hhi =>
    by_cases odd : Odd (f.filter (fun v => a v = true)).card
    · have hfalse : ¬ LinClauseSat a (insert (f,false) G) := by
        rintro ⟨e, hem, hes⟩
        rcases Finset.mem_insert.mp hem with rfl | hem
        · simp [LinEqSat, odd] at hes
        · exact hG ⟨e, hem, hes⟩
      obtain ⟨C, hm, hf⟩ := hhi _ hfalse
      exact ⟨C, by simpa [eval, odd, cellsAt] using Or.inr hm, hf⟩
    · have hfalse : ¬ LinClauseSat a (insert (f,true) G) := by
        rintro ⟨e, hem, hes⟩
        rcases Finset.mem_insert.mp hem with rfl | hem
        · simp [LinEqSat, odd] at hes
        · exact hG ⟨e, hem, hes⟩
      obtain ⟨C, hm, hf⟩ := hlo _ hfalse
      exact ⟨C, by simpa [eval, odd, cellsAt] using Or.inl hm, hf⟩

theorem exists_mem_cells (t : ParityTree V) (a : V → Bool) :
    ∃ C, (t.eval a, C) ∈ t.cells ∧ ¬ LinClauseSat a C :=
  exists_mem_cellsAt t a ∅ (by simp [LinClauseSat])

end ParityTree

end PEqualNP.Search.Helpers
