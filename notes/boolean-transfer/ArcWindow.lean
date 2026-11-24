import CoverCost
import Mathlib.Data.Fintype.Card

/-! Two finite counting steps for the separated point/line product circuit model. -/

namespace BooleanTransfer.ArcWindow

open Finset

/-- In a relation without a four-cycle, an incident rectangle has a side of size at most one. -/
theorem rectangle_is_star {P L : Type*} (edge : P → L → Prop)
    (unique : ∀ p q w z, p ≠ q → w ≠ z → edge p w → edge p z → edge q w → edge q z → False)
    (points : Finset P) (lines : Finset L)
    (sound : ∀ p ∈ points, ∀ w ∈ lines, edge p w) :
    points.card ≤ 1 ∨ lines.card ≤ 1 := by
  classical
  by_contra falsehood
  push Not at falsehood
  obtain ⟨p, hp, q, hq, pq⟩ := Finset.one_lt_card.mp falsehood.1
  obtain ⟨w, hw, z, hz, wz⟩ := Finset.one_lt_card.mp falsehood.2
  exact unique p q w z pq wz (sound p hp w hw) (sound p hp z hz)
    (sound q hq w hw) (sound q hq z hz)

/-- All nodes except the designated outputs appear among the child ports.
There are i input nodes and one further node per gate. Each gate has at most two
distinct child nodes. Hence i input nodes cost at least i minus the output count
in internal gates, regardless of sharing or duplicate designated operands. -/
theorem cone_cost {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]
    (i : ℕ) (size : Fintype.card V = i + Fintype.card G) (out : Finset V)
    (children : G → Finset {v : V // v ∉ out})
    (fanin : ∀ g, (children g).card ≤ 2)
    (covered : ∀ v : {v : V // v ∉ out}, ∃ g, v ∈ children g) :
    i ≤ Fintype.card G + out.card := by
  classical
  let samples := Finset.univ.image children
  have cover (D : Finset {v : V // v ∉ out}) (hd : D.card = 1) :
      ∃ B ∈ samples, D ⊆ B := by
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hd
    obtain ⟨g,hg⟩ := covered v
    exact ⟨children g, mem_image.mpr ⟨g,mem_univ _,rfl⟩,singleton_subset_iff.mpr hg⟩
  have bound := (CoverCost.cover_cost samples 1 cover).1
  simp only [Nat.choose_one_right] at bound
  have ports := Finset.sum_le_sum (s := samples) (fun B hB => show B.card ≤ 2 by
    obtain ⟨g, _, rfl⟩ := mem_image.mp hB
    exact fanin g)
  have ng : samples.card ≤ Fintype.card G := (Finset.card_image_le).trans_eq Finset.card_univ
  have nc : Fintype.card {v : V // v ∉ out} = Fintype.card V - out.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  simp at ports
  omega

end BooleanTransfer.ArcWindow
