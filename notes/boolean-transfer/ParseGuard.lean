import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Order

/-! Signed parses of an unfolded Boolean AND/OR circuit and their guarded positive monomials. -/
namespace BooleanTransfer.ParseGuard

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The unfolded circuit. Two occurrences of a shared gate may choose different OR branches. -/
inductive Formula (ι : Type*) where
  | pos (i : ι)
  | neg (i : ι)
  | top
  | bot
  | and (f g : Formula ι)
  | or (f g : Formula ι)

def Formula.holds : Formula ι → Finset ι → Prop
  | .pos i, S => i ∈ S
  | .neg i, S => i ∉ S
  | .top, _ => True
  | .bot, _ => False
  | .and f g, S => f.holds S ∧ g.holds S
  | .or f g, S => f.holds S ∨ g.holds S

/-- Positive multiplicities are retained. Negative labels need only their support. -/
inductive Parses : Formula ι → (ι →₀ ℕ) → Finset ι → Prop where
  | pos (i : ι) : Parses (.pos i) (Finsupp.single i 1) ∅
  | neg (i : ι) : Parses (.neg i) 0 {i}
  | top : Parses .top 0 ∅
  | and {f g a b D E} : Parses f a D → Parses g b E → Parses (.and f g) (a+b) (D∪E)
  | left {f g a D} : Parses f a D → Parses (.or f g) a D
  | right {f g a D} : Parses g a D → Parses (.or f g) a D

theorem sound {f : Formula ι} {a : ι →₀ ℕ} {D S : Finset ι}
    (p : Parses f a D) (pos : a.support ⊆ S) (neg : Disjoint D S) : f.holds S := by
  induction p with
  | pos i => exact pos (by simp)
  | neg i => simpa [Formula.holds] using neg
  | top => trivial
  | and _ _ ih jh =>
    rw [Finsupp.support_add_eq_union, union_subset_iff] at pos
    rw [Finset.disjoint_union_left] at neg
    exact ⟨ih pos.1 neg.1, jh pos.2 neg.2⟩
  | left _ ih => exact Or.inl (ih pos neg)
  | right _ ih => exact Or.inr (ih pos neg)

/-- A true input admits a parse whose positive and negative literals it satisfies. -/
theorem complete (f : Formula ι) (S : Finset ι) (yes : f.holds S) :
    ∃ a D, Parses f a D ∧ a.support ⊆ S ∧ Disjoint D S := by
  induction f with
  | pos i =>
    refine ⟨_,_,.pos i, ?_, by simp⟩
    simpa [Formula.holds] using yes
  | neg i =>
    refine ⟨_,_,.neg i, by simp, ?_⟩
    simpa [Formula.holds] using yes
  | top => exact ⟨_,_,.top, by simp, by simp⟩
  | bot => exact False.elim yes
  | and f g ih jh =>
    obtain ⟨a,D,pa,ha,hD⟩ := ih yes.1
    obtain ⟨b,E,pb,hb,hE⟩ := jh yes.2
    refine ⟨a+b,D∪E,.and pa pb, ?_, Finset.disjoint_union_left.mpr ⟨hD,hE⟩⟩
    rw [Finsupp.support_add_eq_union]
    exact Finset.union_subset ha hb
  | or f g ih jh =>
    rcases yes with h | h
    · obtain ⟨a,D,p,ha,hD⟩ := ih h
      exact ⟨a,D,.left p,ha,hD⟩
    · obtain ⟨a,D,p,ha,hD⟩ := jh h
      exact ⟨a,D,.right p,ha,hD⟩

/-- Every consistent parse of a correct formula has a positive support containing a minterm. -/
theorem certificate {f : Formula ι} {a : ι →₀ ℕ} {D : Finset ι} (M : Finset ι → Prop)
    (correct : ∀ S, f.holds S → ∃ T, M T ∧ T ⊆ S) (p : Parses f a D)
    (consistent : Disjoint D a.support) : ∃ T, M T ∧ T ⊆ a.support :=
  correct _ (sound p Subset.rfl consistent)

noncomputable def square (S : Finset ι) : ι →₀ ℕ := Finsupp.indicator S (fun _ _ => 1)

/-- A slice keeps all multiplicities outside B and adds its one-bit labels exactly once. -/
noncomputable def term (a : ι →₀ ℕ) (B z : Finset ι) : ι →₀ ℕ :=
  a.filter (· ∉ B) + square z

def Survives (a : ι →₀ ℕ) (D B z : Finset ι) : Prop :=
  z ⊆ B ∧ a.support ∩ B ⊆ z ∧ Disjoint D z

private theorem squareSupport (S : Finset ι) : (square S).support = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [square, Finsupp.mem_support_iff, hi]

private theorem squareDegree (S : Finset ι) : (square S).degree = S.card := by
  rw [Finsupp.degree_apply, squareSupport]
  have ones : ∀ i ∈ S, square S i = 1 := fun i hi => Finsupp.indicator_of_mem hi _
  simp [Finset.sum_congr rfl ones]

theorem support (a : ι →₀ ℕ) (B z : Finset ι) :
    (term a B z).support = (a.support \ B) ∪ z := by
  rw [term, Finsupp.support_add_eq_union, squareSupport]
  congr 1
  ext i
  by_cases hi : i ∈ B <;> simp [Finsupp.mem_support_iff, hi]

private theorem retained {a : ι →₀ ℕ} {D B z : Finset ι} (live : Survives a D B z) :
    a.support ⊆ (term a B z).support := by
  rw [support]
  intro i hi
  by_cases hb : i ∈ B
  · exact mem_union_right _ (live.2.1 (mem_inter.mpr ⟨hi,hb⟩))
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hi,hb⟩)

private theorem belowSquare (S : Finset ι) (a : ι →₀ ℕ) (inside : S ⊆ a.support) :
    square S ≤ a := by
  intro i
  by_cases hi : i ∈ S
  · rw [square, Finsupp.indicator_of_mem hi]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (inside hi))
  · simp [square, hi]

private theorem mass (S : Finset ι) (a : ι →₀ ℕ) (inside : S ⊆ a.support) :
    S.card ≤ a.degree ∧ (S.card = a.degree → a = square S) := by
  have eq : square S + (a - square S) = a := add_tsub_cancel_of_le (belowSquare S a inside)
  have deg := congrArg Finsupp.degree eq
  rw [map_add, squareDegree] at deg
  refine ⟨by omega, fun tight => ?_⟩
  have rest : (a - square S).degree = 0 := by omega
  have noRest := (Finsupp.degree_eq_zero_iff _).mp rest
  simpa only [noRest, add_zero] using eq.symm

/-- A guard hits a contradictory label of every tour-free small-support parse. -/
def Guard (f : Formula ι) (M : Finset ι → Prop) (n : ℕ) (B : Finset ι) : Prop :=
  ∀ a D, Parses f a D → a.support.card ≤ n → (¬∃ T, M T ∧ T ⊆ a.support) →
    ∃ i ∈ B, i ∈ a.support ∧ i ∈ D

theorem enlarge {f : Formula ι} {M : Finset ι → Prop} {n : ℕ} {B B' : Finset ι}
    (guard : Guard f M n B) (sub : B ⊆ B') : Guard f M n B' := by
  intro a D p small none
  obtain ⟨i,hb,ha,hd⟩ := guard a D p small none
  exact ⟨i,sub hb,ha,hd⟩

theorem lowest {f : Formula ι} {M : Finset ι → Prop} {n : ℕ} {a : ι →₀ ℕ} {D B z : Finset ι}
    (uniform : ∀ T, M T → T.card = n) (guard : Guard f M n B) (p : Parses f a D)
    (live : Survives a D B z) : n ≤ (term a B z).degree ∧
      ((term a B z).degree = n → ∃ T, M T ∧ term a B z = square T) := by
  by_cases small : (term a B z).degree ≤ n
  · have cap := (mass _ _ (retained live)).1
    have someTerm : ∃ T, M T ∧ T ⊆ a.support := by
      by_contra none
      obtain ⟨i,hb,ha,hd⟩ := guard a D p (cap.trans small) none
      exact Finset.disjoint_left.mp live.2.2 hd (live.2.1 (mem_inter.mpr ⟨ha,hb⟩))
    obtain ⟨T,hT,hsub⟩ := someTerm
    obtain ⟨bound,tight⟩ := mass T _ (hsub.trans (retained live))
    rw [uniform T hT] at bound tight
    exact ⟨bound, fun eq => ⟨T,hT,tight eq.symm⟩⟩
  · exact ⟨by omega, (fun eq => (small eq.le).elim)⟩

/-- A satisfied minimum-size input contributes its squarefree monomial if its parse
has no repeated positive label outside the guard. -/
theorem clean {f : Formula ι} {M : Finset ι → Prop} {n : ℕ} {a : ι →₀ ℕ} {D T B : Finset ι}
    (uniform : ∀ U, M U → U.card = n) (correct : ∀ S, f.holds S → ∃ U, M U ∧ U ⊆ S)
    (minterm : M T) (p : Parses f a D) (pos : a.support ⊆ T) (neg : Disjoint D T)
    (once : ∀ i ∉ B, a i ≤ 1) :
    a.support = T ∧ Survives a D B (T ∩ B) ∧ term a B (T ∩ B) = square T := by
  obtain ⟨U,hU,hu⟩ := certificate M correct p (neg.mono_right pos)
  have same : U = T := eq_of_subset_of_card_le (hu.trans pos) (by rw [uniform U hU, uniform T minterm])
  have full : a.support = T := Subset.antisymm pos (same ▸ hu)
  refine ⟨full, ⟨inter_subset_right, full ▸ Subset.rfl, neg.mono_right inter_subset_left⟩, ?_⟩
  ext i
  by_cases hb : i ∈ B
  · simp [term, square, hb]
  · by_cases hi : i ∈ T
    · have nz : a i ≠ 0 := Finsupp.mem_support_iff.mp (full ▸ hi)
      have one : a i = 1 := by have := once i hb; omega
      simp [term, square, hb, hi, one]
    · have zero : a i = 0 := Finsupp.notMem_support_iff.mp (full ▸ hi)
      simp [term, square, hb, hi, zero]

#print axioms sound
#print axioms complete
#print axioms enlarge
#print axioms certificate
#print axioms support
#print axioms lowest
#print axioms clean

end BooleanTransfer.ParseGuard
