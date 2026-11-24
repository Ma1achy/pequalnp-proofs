import PEqualNP.Search.Helpers.CoordSearch
import PEqualNP.Defs.ProofComplexityBit
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic

namespace PEqualNP.Search.Helpers

open PEqualNP.ProofComplexity

private theorem readCoordinates {V A : Type} (n : ℕ) (xs : Fin n → V)
    (next : (Fin n → Bool) → CoordDecision V A) (D : ℕ) (small : ∀ f, (next f).depth ≤ D) :
    ∃ tree : CoordDecision V A, tree.depth ≤ n + D ∧
      ∀ a : V → Bool, tree.eval a = (next (fun i => a (xs i))).eval a := by
  induction n with
  | zero =>
    let f : Fin 0 → Bool := Fin.elim0
    exact ⟨next f, by simpa using small f, fun a => by
      have eqn : f = fun i => a (xs i) := funext (fun i => i.elim0)
      rw [eqn]⟩
  | succ n ih =>
    have sub (b : Bool) := ih (xs ∘ Fin.succ) (fun f => next (Fin.cons b f))
      (fun f => small (Fin.cons b f))
    obtain ⟨lo, dlo, elo⟩ := sub false
    obtain ⟨hi, dhi, ehi⟩ := sub true
    refine ⟨.node (xs 0) lo hi, ?_, ?_⟩
    · change max lo.depth hi.depth + 1 ≤ _
      omega
    · intro a
      have eqn : Fin.cons (a (xs 0)) (fun i : Fin n => a (xs i.succ)) = (fun i => a (xs i)) := by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      cases h : a (xs 0) <;> simp only [CoordDecision.eval,h,Bool.false_eq_true,
        ↓reduceIte, elo,ehi,Function.comp_apply] <;> rw [← h,eqn]

private theorem majority_rows (k : ℕ) (f : Fin (2^(k+1)+1) → Bool) :
    ∃ (b : Bool) (rows : Fin (2^k+1) ↪ Fin (2^(k+1)+1)), ∀ i, f (rows i) = b := by
  classical
  let block (b : Bool) := Finset.univ.filter (fun i => f i = b)
  have counts : (block true).card + (block false).card = 2^(k+1)+1 := by
    simpa [block] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2^(k+1)+1)))) (p := fun i => f i = true)
  obtain ⟨b, hcard⟩ : ∃ b : Bool, 2^k+1 ≤ (block b).card := by
    have power : 2^(k+1) = 2^k * 2 := pow_succ 2 k
    by_cases h : 2^k+1 ≤ (block true).card
    · exact ⟨true,h⟩
    · exact ⟨false,by omega⟩
  obtain ⟨inc⟩ : Nonempty (Fin (2^k+1) ↪ ↥(block b)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  exact ⟨b,inc.trans (Function.Embedding.subtype _),fun i => (Finset.mem_filter.mp (inc i).property).2⟩

private theorem treeAux {V A : Type} (l : ℕ) (xs : Fin (2^l+1) → Fin l → V)
    (output : Fin (2^l+1) → Fin (2^l+1) → (Fin l → Bool) → A) :
    ∃ tree : CoordDecision V A, tree.depth ≤ 2*(2^l-1)+l ∧
      ∀ a : V → Bool, ∃ i j h, i ≠ j ∧ (∀ b, a (xs i b) = h b) ∧
        (∀ b, a (xs j b) = h b) ∧ tree.eval a = output i j h := by
  classical
  induction l with
  | zero => exact ⟨.leaf (output 0 1 Fin.elim0), by simp [CoordDecision.depth],
      fun _ => ⟨0,1,Fin.elim0,by decide,(fun b => b.elim0),(fun b => b.elim0),rfl⟩⟩
  | succ k ih =>
    have subsets := majority_rows k
    choose color rows monochrome using subsets
    have subtree (f : Fin (2^(k+1)+1) → Bool) := ih
      (fun i b => xs ((rows f) i) b.succ)
      (fun i j pat => output ((rows f) i) ((rows f) j) (Fin.cons (color f) pat))
    choose next small correct using subtree
    obtain ⟨tree,depth,result⟩ := readCoordinates _ (fun i => xs i 0) next _ small
    refine ⟨tree, ?_, ?_⟩
    · have positive := Nat.two_pow_pos k
      rw [pow_succ] at depth ⊢
      omega
    · intro a
      let f (i : Fin (2^(k+1)+1)) := a (xs i 0)
      obtain ⟨i,j,h,ne,hi,hj,answer⟩ := correct f a
      let full : Fin (k+1) → Bool := Fin.cons (color f) h
      have allBits (r : Fin (2^k+1)) (hr : ∀ b, a (xs ((rows f) r) b.succ) = h b) :
          ∀ b, a (xs ((rows f) r) b) = full b := by
        intro b
        exact Fin.cases (by simpa [full,f] using monochrome f r) (fun t => by simpa [full] using hr t) b
      exact ⟨_,_,_,fun eqn => ne ((rows f).injective eqn),allBits i hi,allBits j hj,
        (result a).trans answer⟩

/-- Query one column of the surviving rows and retain enough rows of one color
to continue on the remaining bits. For n=2^l holes, two equal rows and their
common label can be found using at most 2(n−1)+l coordinate queries. -/
theorem bphp_collision_tree (l : ℕ) :
    ∃ t : CoordSearch (Fin (2^l+1) × Fin l), t.depth ≤ 2*(2^l-1)+l ∧
      ∀ a, t.eval a ∈ BPHP (2^l+1) l ∧ ¬ ClauseSat a (t.eval a) := by
  let C (i j : Fin (2^l+1)) (h : Fin l → Bool) : Clause (Fin (2^l+1) × Fin l) :=
    Finset.univ.image (fun b => ((i,b),!h b)) ∪ Finset.univ.image (fun b => ((j,b),!h b))
  obtain ⟨tree,depth,correct⟩ := treeAux l (fun i b => (i,b)) C
  refine ⟨tree,depth,?_⟩
  intro a
  obtain ⟨i,j,h,ne,hi,hj,result⟩ := correct a
  rw [result]
  refine ⟨⟨i,j,h,ne,rfl⟩,?_⟩
  rintro ⟨v,hv,holds⟩
  rcases Finset.mem_union.mp hv with left | right
  · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp left
    simp [hi] at holds
  · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp right
    simp [hj] at holds

end PEqualNP.Search.Helpers
