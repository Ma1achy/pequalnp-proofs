import PEqualNP.Search.Helpers.QPaddingCost

namespace PEqualNP.Search.Helpers

variable {V : Type}

/-- A common integer multiple of the right-hand sides in the list. -/
def rhsProduct (G : QLine V) : ℤ := (G.map Prod.snd).prod

theorem dvd_rhsProduct {G : QLine V} {e : QEq V} (he : e ∈ G) :
    e.2 ∣ rhsProduct G :=
  List.dvd_prod (List.mem_map.mpr ⟨e, he, rfl⟩)

theorem rhsProduct_ne_zero (G : QLine V) (h : ∀ e ∈ G, e.2 ≠ 0) : rhsProduct G ≠ 0 := by
  induction G with
  | nil => simp [rhsProduct]
  | cons e G ih =>
    exact Int.mul_ne_zero (h e List.mem_cons_self) (ih fun f hf => h f (List.mem_cons_of_mem _ hf))

/-- Multiplication adds at most the bit lengths of the factors. The empty product
has value one, accounting for the extra bit in the bound. -/
theorem rhsProduct_size [Fintype V] (G : QLine V) :
    Nat.size (rhsProduct G).natAbs ≤ 1 + qWeight G := by
  induction G with
  | nil => simp [rhsProduct]
  | cons e G ih =>
    change Nat.size (e.2 * rhsProduct G).natAbs ≤ 1 + (e.size + qWeight G)
    rw [Int.natAbs_mul]
    have hmul (x y : ℕ) : Nat.size (x * y) ≤ x.size + y.size := by
      apply Nat.size_le.mpr
      rw [pow_add]
      exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self x) (Nat.lt_size_self y)
    have he : Nat.size e.2.natAbs ≤ e.size := by unfold QEq.size; omega
    exact (hmul _ _).trans (by omega)

end PEqualNP.Search.Helpers
