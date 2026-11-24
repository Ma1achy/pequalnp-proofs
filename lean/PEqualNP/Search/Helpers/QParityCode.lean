import PEqualNP.Search.Helpers.ParityTree
import PEqualNP.Search.Helpers.QSynSize
import PEqualNP.Search.Helpers.LinKGuardTaut
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact Res(k,⊕) encodings for equations whose truth depends on at most k
fixed parity queries. Different equations may use different families of queries. -/

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The disjunction of the conjunctions associated with the true leaves of a
parity decision tree. A conjunction negates each equation in the path blocker. -/
def treeDNF (t : ParityTree V) : LinKLine V :=
  ((t.cells.filter (fun p => p.1)).map fun p => guardTerm p.2).toFinset

theorem treeDNF_true_cell (t : ParityTree V) (B : LinClause V) (hb : (true,B) ∈ t.cells) :
    guardTerm B ∈ treeDNF t := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨(true,B), List.mem_filter.mpr ⟨hb, rfl⟩, rfl⟩

theorem treeDNF_sat (t : ParityTree V) (a : V → Bool) :
    LinKLineSat a (treeDNF t) ↔ t.eval a = true := by
  constructor
  · rintro ⟨T, hm, hs⟩
    obtain ⟨⟨b,B⟩, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    obtain ⟨hm, rfl⟩ := List.mem_filter.mp hb
    exact t.eval_of_mem_cells a hm ((guardTerm_sat_iff a B).mp hs)
  · intro h
    obtain ⟨B, hm, hB⟩ := t.exists_mem_cells a
    rw [h] at hm
    exact ⟨_, treeDNF_true_cell t B hm, (guardTerm_sat_iff a B).mpr hB⟩

theorem treeDNF_card (t : ParityTree V) : (treeDNF t).card ≤ t.leaves := by
  calc
    _ ≤ _ := List.toFinset_card_le _
    _ ≤ t.cells.length := by rw [List.length_map]; exact List.length_filter_le _ _
    _ = _ := t.length_cells

/-- The vector of answers to the fixed parity queries, in the supplied order. -/
def queryAnswers (Q : List (Finset V)) (a : V → Bool) : List Bool :=
  Q.map fun f => decide (Odd (f.filter (fun v => a v = true)).card)

def QDetermined [Fintype V] (Q : List (Finset V)) (e : QEq V) : Prop :=
  ∀ a z, queryAnswers Q a = queryAnswers Q z → (QEq.Holds a e ↔ QEq.Holds z e)

/-- Read the queries in order, then return the prescribed truth-table entry. -/
private def tableTree : List (Finset V) → (List Bool → Bool) → ParityTree V
  | [], test => .leaf (test [])
  | f :: Q, test => .node f (tableTree Q (fun s => test (false :: s)))
      (tableTree Q (fun s => test (true :: s)))

omit [DecidableEq V] in
private theorem table_eval (Q : List (Finset V)) (test : List Bool → Bool) (a : V → Bool) :
    (tableTree Q test).eval a = test (queryAnswers Q a) := by
  induction Q generalizing test with
  | nil => rfl
  | cons f Q ih =>
    by_cases h : Odd (f.filter (fun v => a v = true)).card <;>
      simp [ParityTree.eval, tableTree, queryAnswers, h, ih]

omit [DecidableEq V] in
private theorem table_leaves (Q : List (Finset V)) (test : List Bool → Bool) :
    (tableTree Q test).leaves = 2 ^ Q.length := by
  induction Q generalizing test with
  | nil => rfl
  | cons f Q ih => simp [tableTree, ParityTree.leaves, ih, pow_succ, Nat.mul_two]

private theorem table_cell_width (Q : List (Finset V)) (test : List Bool → Bool)
    (G : LinClause V) (b : Bool) (B : LinClause V)
    (h : (b,B) ∈ (tableTree Q test).cellsAt G) : B.card ≤ G.card + Q.length := by
  induction Q generalizing test G with
  | nil =>
    have hBG : B = G := congrArg Prod.snd (List.mem_singleton.mp h)
    simp [hBG]
  | cons f Q ih =>
    change (b,B) ∈ _ ++ _ at h
    rcases List.mem_append.mp h with h | h
    · have hb := ih _ _ h
      have hc := Finset.card_insert_le (f,true) G
      simp only [List.length_cons]; omega
    · have hb := ih _ _ h
      have hc := Finset.card_insert_le (f,false) G
      simp only [List.length_cons]; omega

private def literalTree (l : V × Bool) : ParityTree V :=
  .node {l.1} (.leaf (!l.2)) (.leaf l.2)

private theorem litQEq_holds_iff [Fintype V] (a : V → Bool) (l : V × Bool) :
    QEq.Holds a (litQEq l) ↔ a l.1 = l.2 := by
  simp only [QEq.Holds, litQEq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  cases ha : a l.1 <;> cases hb : l.2 <;> simp [ha, hb]

/-- Literal and contradictory equations have canonical trees, independent of the
suggested query family. Other equations use the table of realizable true profiles. -/
noncomputable def qCodeTree [Fintype V] (Q : List (Finset V)) (e : QEq V) : ParityTree V := by
  classical
  exact if h : ∃ l, e = litQEq l then literalTree h.choose
    else if e.1 = 0 ∧ e.2 ≠ 0 then .leaf false
    else tableTree Q fun s => decide (∃ a, QEq.Holds a e ∧ queryAnswers Q a = s)

noncomputable def qCode [Fintype V] (Q : List (Finset V)) (e : QEq V) : LinKLine V :=
  treeDNF (qCodeTree Q e)

private theorem literal_code_tree [Fintype V] (Q : List (Finset V)) (l : V × Bool) :
    qCodeTree Q (litQEq l) = literalTree l := by
  classical
  have h : ∃ z, litQEq l = litQEq z := ⟨l, rfl⟩
  simp only [qCodeTree, dif_pos h]
  rw [← litQEq_injective h.choose_spec]

@[simp] theorem qCode_lit [Fintype V] (Q : List (Finset V)) (l : V × Bool) :
    qCode Q (litQEq l) = {({({l.1}, l.2)} : LinTerm V)} := by
  rw [qCode, literal_code_tree]
  obtain ⟨v,b⟩ := l
  cases b <;> simp [treeDNF, literalTree, ParityTree.cells, ParityTree.cellsAt, guardTerm, negLinEq]

private theorem no_lit_of_false_constant (e : QEq V) (hz : e.1 = 0) :
    ¬ ∃ l, e = litQEq l := by
  rintro ⟨⟨v,b⟩, rfl⟩
  have := congrFun hz v
  simp [litQEq] at this

@[simp] theorem qCode_dead [Fintype V] (Q : List (Finset V)) (e : QEq V)
    (hz : e.1 = 0) (hn : e.2 ≠ 0) : qCode Q e = ∅ := by
  classical
  simp [qCode, qCodeTree, no_lit_of_false_constant e hz, hz, hn, treeDNF,
    ParityTree.cells, ParityTree.cellsAt]

theorem qCodeTree_lit_eval [Fintype V] (Q : List (Finset V)) (t : V × Bool) (a : V → Bool) :
    (qCodeTree Q (litQEq t)).eval a = true ↔ QEq.Holds a (litQEq t) := by
  obtain ⟨v,b⟩ := t
  rw [literal_code_tree, litQEq_holds_iff]
  cases h : a v <;> cases b <;> simp [literalTree, ParityTree.eval, Finset.filter_singleton, h]

theorem qCodeTree_eval [Fintype V] (Q : List (Finset V)) (e : QEq V) (a : V → Bool)
    (det : QDetermined Q e) : (qCodeTree Q e).eval a = true ↔ QEq.Holds a e := by
  classical
  by_cases hl : ∃ l, e = litQEq l
  · obtain ⟨⟨v,b⟩, rfl⟩ := hl
    exact qCodeTree_lit_eval Q (v,b) a
  · by_cases hd : e.1 = 0 ∧ e.2 ≠ 0
    · simp [qCodeTree, hl, hd, QEq.Holds, hd.1, Ne.symm hd.2, ParityTree.eval]
    · simp only [qCodeTree, dif_neg hl, if_neg hd, table_eval, decide_eq_true_eq]
      exact ⟨fun ⟨z, hz, hs⟩ => (det z a hs).mp hz, fun ha => ⟨a, ha, rfl⟩⟩

theorem qCode_sat [Fintype V] (Q : List (Finset V)) (e : QEq V) (a : V → Bool)
    (det : QDetermined Q e) : LinKLineSat a (qCode Q e) ↔ QEq.Holds a e :=
  (treeDNF_sat _ _).trans (qCodeTree_eval Q e a det)

theorem qCodeTree_cell_width [Fintype V] (Q : List (Finset V)) (e : QEq V)
    {k : ℕ} (hk : 1 ≤ k) (hq : Q.length ≤ k) (b : Bool) (B : LinClause V)
    (hb : (b,B) ∈ (qCodeTree Q e).cells) : B.card ≤ k := by
  classical
  by_cases hl : ∃ l, e = litQEq l
  · obtain ⟨l, rfl⟩ := hl
    rw [literal_code_tree] at hb
    simp only [literalTree, ParityTree.cells, ParityTree.cellsAt, List.singleton_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
    rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simpa using hk
  · by_cases hd : e.1 = 0 ∧ e.2 ≠ 0
    · simp only [qCodeTree, dif_neg hl, if_pos hd, ParityTree.cells, ParityTree.cellsAt,
        List.mem_singleton, Prod.mk.injEq] at hb
      simp [hb.2]
    · simp only [qCodeTree, dif_neg hl, if_neg hd] at hb
      exact (show B.card ≤ Q.length by simpa using table_cell_width Q _ ∅ b B hb).trans hq

theorem qCodeTree_leaves [Fintype V] (Q : List (Finset V)) (e : QEq V)
    {k : ℕ} (hk : 1 ≤ k) (hq : Q.length ≤ k) : (qCodeTree Q e).leaves ≤ 2 ^ k := by
  classical
  by_cases hl : ∃ l, e = litQEq l
  · obtain ⟨l, rfl⟩ := hl
    rw [literal_code_tree]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hk
  · by_cases hd : e.1 = 0 ∧ e.2 ≠ 0
    · simp [qCodeTree, hl, hd, ParityTree.leaves, Nat.one_le_two_pow]
    · simpa only [qCodeTree, dif_neg hl, if_neg hd, table_leaves] using
        (Nat.pow_le_pow_right (n := 2) (by decide) hq)

theorem qCode_card [Fintype V] (Q : List (Finset V)) (e : QEq V)
    {k : ℕ} (hk : 1 ≤ k) (hq : Q.length ≤ k) : (qCode Q e).card ≤ 2 ^ k :=
  (treeDNF_card _).trans (qCodeTree_leaves Q e hk hq)

theorem qCode_term_width [Fintype V] (Q : List (Finset V)) (e : QEq V)
    {k : ℕ} (hk : 1 ≤ k) (hq : Q.length ≤ k) (T : LinTerm V) (hT : T ∈ qCode Q e) :
    T.card ≤ k := by
  obtain ⟨⟨b,B⟩, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hT)
  exact Finset.card_image_le.trans (qCodeTree_cell_width Q e hk hq b B (List.mem_filter.mp hb).1)

/-- Query every variable with a nonzero coefficient using singleton parity forms. -/
noncomputable def supportQueries [Fintype V] (e : QEq V) : List (Finset V) :=
  ((Finset.univ.filter fun v => e.1 v ≠ 0).toList).map fun v => {v}

@[simp] theorem supportQueries_length [Fintype V] (e : QEq V) :
    (supportQueries e).length = (Finset.univ.filter fun v => e.1 v ≠ 0).card := by
  simp [supportQueries]

theorem supportQueries_determine [Fintype V] (e : QEq V) : QDetermined (supportQueries e) e := by
  intro a z answers
  have agree : ∀ v, e.1 v ≠ 0 → a v = z v := by
    intro v hv
    have mem : ({v} : Finset V) ∈ supportQueries e := List.mem_map.mpr
      ⟨v, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩), rfl⟩
    have matchBit := List.map_eq_map_iff.mp answers {v} mem
    cases ha : a v <;> cases hz : z v <;> simp_all [Finset.filter_singleton]
  unfold QEq.Holds
  have eq : (∑ v, e.1 v * (if a v then 1 else 0)) = ∑ v, e.1 v * (if z v then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hz : e.1 v = 0
    · simp [hz]
    · rw [agree v hz]
  rw [eq]

end PEqualNP.Search.Helpers
