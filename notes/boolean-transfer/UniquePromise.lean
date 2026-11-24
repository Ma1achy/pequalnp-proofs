import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Fixing random bits for a zero-versus-one promise

Inputs, seeds and query instances are abstract. Positive inputs have at least
one witness. No correctness is required of the promise decider on instances
with two or more witnesses. All counting is over finite sets of seed vectors.
-/

namespace BooleanTransfer.UniquePromise
open Finset

variable {I R J K : Type*}

/-- The exact union bound fixes the same vector of seeds for every positive input. -/
theorem fixSeeds [Fintype R] (yes : Finset I) (bad : I → Finset R) (t : ℕ)
    (bound : ∑ x ∈ yes, (bad x).card ^ t < (Fintype.card R)^t) :
    ∃ seeds : Fin t → R, ∀ x ∈ yes, ∃ i, seeds i ∉ bad x := by
  classical
  let fail := fun x => Fintype.piFinset (fun _ : Fin t => bad x)
  have bound' : (yes.biUnion fail).card < (univ : Finset (Fin t → R)).card := by
    calc
      _ ≤ ∑ x ∈ yes, (fail x).card := Finset.card_biUnion_le
      _ = ∑ x ∈ yes, (bad x).card ^ t := by simp [fail]
      _ < _ := by simpa using bound
  obtain ⟨seeds,_,outside⟩ := exists_mem_notMem_of_card_lt_card bound'
  refine ⟨seeds, fun x hx => ?_⟩
  by_contra! allbad
  exact outside (mem_biUnion.mpr ⟨x,hx,Fintype.mem_piFinset.mpr allbad⟩)

private theorem firstTerms (b g k : ℕ) :
    b^(k+1) + (k+1)*g*b^k ≤ (b+g)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      b^(k+2) + (k+2)*g*b^(k+1) ≤
          b^(k+2) + (k+2)*g*b^(k+1) + (k+1)*g^2*b^k := Nat.le_add_right _ _
      _ = (b^(k+1) + (k+1)*g*b^k)*(b+g) := by ring
      _ ≤ (b+g)^(k+2) := by rw [pow_succ _ (k+1)]; exact Nat.mul_le_mul_right _ ih

/-- If at least a 1/k fraction of seeds succeed, a block of k independent
trials has at most half as many failing vectors as total vectors. -/
theorem halfBlock (b N k : ℕ) (kpos : 0 < k) (h : b ≤ N) (fraction : N ≤ k*(N-b)) :
    2*b^k ≤ N^k := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero kpos.ne'
  calc
    2*b^(k+1) = b^(k+1) + b*b^k := by ring
    _ ≤ b^(k+1) + (k+1)*(N-b)*b^k :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (h.trans fraction)) _
    _ ≤ (b+(N-b))^(k+1) := firstTerms _ _ _
    _ = _ := by rw [Nat.add_sub_of_le h]

/-- On at most 2^m positive inputs, k(m+1) trials suffice at success rate 1/k. -/
theorem amplify [Fintype R] [Nonempty R] (yes : Finset I) (bad : I → Finset R) (k m : ℕ)
    (kpos : 0 < k) (inputs : yes.card ≤ 2^m)
    (rate : ∀ x ∈ yes, Fintype.card R ≤ k*(Fintype.card R - (bad x).card)) :
    ∃ seeds : Fin (k*(m+1)) → R, ∀ x ∈ yes, ∃ i, seeds i ∉ bad x := by
  let N := Fintype.card R
  let t := k*(m+1)
  have Npos : 0 < N := Fintype.card_pos
  have boosted (x : I) (hx : x ∈ yes) : 2^(m+1)*(bad x).card^t ≤ N^t := by
    have h := halfBlock (bad x).card N k kpos (card_le_univ _) (rate x hx)
    simpa only [t, mul_pow, ← pow_mul] using Nat.pow_le_pow_left h (m+1)
  apply fixSeeds
  have sumBound : 2^(m+1) * (∑ x ∈ yes, (bad x).card^t) ≤ 2^m * N^t := by
    calc
      _ = ∑ x ∈ yes, (2^(m+1) * (bad x).card^t) := Finset.mul_sum ..
      _ ≤ ∑ _x ∈ yes, N^t := sum_le_sum boosted
      _ ≤ 2^m * N^t := by simpa using Nat.mul_le_mul_right (N^t) inputs
  have gap : 2^m < 2^(m+1) := by rw [pow_succ]; have := Nat.two_pow_pos m; omega
  exact Nat.lt_of_mul_lt_mul_left (sumBound.trans_lt (Nat.mul_lt_mul_of_pos_right gap (pow_pos Npos _)))

/-- The seed-vector circuit is a finite OR of answers to its fixed queries. -/
def vote [Fintype K] (reduce : I → R → K → J) (check : J → Bool) {t : ℕ}
    (seeds : Fin t → R) (x : I) : Bool := decide (∃ i k, check (reduce x (seeds i) k) = true)

/-- A promise decider together with isolation and one-sided soundness decides
every input using the same fixed seeds. Multiple queries per seed are allowed. -/
theorem simulate [Fintype I] [Fintype R] [Nonempty R] [Fintype K]
    (witnesses : I → ℕ) (queryCount : J → ℕ) (reduce : I → R → K → J) (check : J → Bool)
    (zero : ∀ q, queryCount q = 0 → check q = false)
    (one : ∀ q, queryCount q = 1 → check q = true)
    (noCreation : ∀ x, witnesses x = 0 → ∀ r k, queryCount (reduce x r k) = 0)
    (k m : ℕ) (kpos : 0 < k) (width : Fintype.card I ≤ 2^m)
    (rate : ∀ x, 0 < witnesses x →
      Fintype.card R ≤ k * (Finset.univ.filter
        (fun r : R => ∃ s : K, queryCount (reduce x r s) = 1)).card) :
    ∃ seeds : Fin (k*(m+1)) → R, ∀ x, vote reduce check seeds x = true ↔ 0 < witnesses x := by
  classical
  let yes := univ.filter (fun x => 0 < witnesses x)
  let good := fun x => univ.filter (fun r : R => ∃ s : K, queryCount (reduce x r s) = 1)
  let bad := fun x => (univ : Finset R) \ good x
  have splitCard (x : I) : Fintype.card R - (bad x).card = (good x).card := by
    have h := card_le_univ (good x)
    dsimp only [bad]
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  obtain ⟨seeds, hits⟩ := amplify yes bad k m kpos ((card_le_univ _).trans width)
    (fun x hx => by rw [splitCard]; exact rate x (mem_filter.mp hx).2)
  refine ⟨seeds, fun x => ?_⟩
  rw [vote, decide_eq_true_eq]
  constructor
  · rintro ⟨i,s,accept⟩
    by_contra! no
    have falseBit := zero _ (noCreation x (Nat.eq_zero_of_le_zero no) (seeds i) s)
    exact Bool.noConfusion (accept.symm.trans falseBit)
  · intro positive
    obtain ⟨i, hit⟩ := hits x (mem_filter.mpr ⟨mem_univ _,positive⟩)
    have gr : seeds i ∈ good x := by simpa [bad] using hit
    obtain ⟨s,solo⟩ := (mem_filter.mp gr).2
    exact ⟨i,s,one _ solo⟩

/-- All directed arc sets on n+1 labelled vertices; loops may be present. -/
abbrev Digraph (n : ℕ) := Finset (Fin (n+1) × Fin (n+1))

/-- Rooting the cyclic order at vertex zero counts each directed tour once. -/
def tours {n : ℕ} (E : Digraph n) : Finset (Equiv.Perm (Fin (n+1))) :=
  univ.filter (fun σ => σ 0 = 0 ∧ ∀ i, (σ i, σ (i+1)) ∈ E)

/-- Query graphs can have different numbers of vertices. The random reduction
is supplied as a hypothesis. Its promise oracle may answer arbitrarily on
graphs with multiple tours. -/
theorem hamiltonian [Fintype R] [Nonempty R] [Fintype K] (n k : ℕ)
    (reduce : Digraph n → R → K → (Σ m : ℕ, Digraph m))
    (check : (Σ m : ℕ, Digraph m) → Bool)
    (promise : ∀ q, (tours q.2).card ≤ 1 → (check q = true ↔ (tours q.2).Nonempty))
    (empty : ∀ E : Digraph n, tours E = ∅ → ∀ r s, tours (reduce E r s).2 = ∅)
    (kpos : 0 < k)
    (rate : ∀ E : Digraph n, (tours E).Nonempty →
      Fintype.card R ≤ k * (Finset.univ.filter
        (fun r : R => ∃ s : K, (tours (reduce E r s).2).card = 1)).card) :
    ∃ seeds : Fin (k*((n+1)^2+1)) → R,
      ∀ E : Digraph n, vote reduce check seeds E = true ↔ (tours E).Nonempty := by
  have width : Fintype.card (Digraph n) ≤ 2^((n+1)^2) := by simp [Digraph, pow_two]
  have no (q : Σ m : ℕ, Digraph m) (h : (tours q.2).card = 0) : check q = false := by
    rw [← Bool.not_eq_true, promise q (by omega), ← Finset.card_pos]
    omega
  have solo (q : Σ m : ℕ, Digraph m) (h : (tours q.2).card = 1) : check q = true :=
    (promise q h.le).2 (Finset.card_pos.mp (by omega))
  obtain ⟨seeds,works⟩ := simulate (fun E : Digraph n => (tours E).card)
    (fun q : Σ m : ℕ, Digraph m => (tours q.2).card) reduce check no solo
    (fun E he r s => by
      have hz := empty E (Finset.card_eq_zero.mp he) r s
      simp [hz]) k ((n+1)^2) kpos width (fun E h => rate E (Finset.card_pos.mp h))
  exact ⟨seeds, fun E => (works E).trans Finset.card_pos⟩

#print axioms fixSeeds
#print axioms halfBlock
#print axioms amplify
#print axioms simulate
#print axioms hamiltonian

end BooleanTransfer.UniquePromise
