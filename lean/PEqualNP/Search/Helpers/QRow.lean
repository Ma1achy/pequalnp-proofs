import PEqualNP.Search.Helpers.QParity

namespace PEqualNP.Search.Helpers

/-- An augmented equation row. The extra coordinate stores the right-hand side. -/
def qCoord {V : Type} (e : QEq V) : Option V → ℤ
  | none => e.2
  | some v => e.1 v

/-- Identical parity equations have the same parity at every augmented coordinate. -/
theorem coord_modEq_of_qParity_eq {V : Type} [Fintype V] {e f : QEq V}
    (eq : qParity e = qParity f) (u : Option V) : qCoord e u ≡ qCoord f u [ZMOD 2] := by
  cases u with
  | none =>
    have hb := congrArg Prod.snd eq
    change decide (e.2 % 2 = 1) = decide (f.2 % 2 = 1) at hb
    have he : e.2 % 2 = 1 ↔ f.2 % 2 = 1 := by simpa using hb
    change e.2 % 2 = f.2 % 2
    omega
  | some v =>
    have h := congrArg (fun q => v ∈ q.1) eq
    have he : e.1 v % 2 = 1 ↔ f.1 v % 2 = 1 := by simpa [qParity] using h
    change e.1 v % 2 = f.1 v % 2
    omega

/-- Every augmented two-by-two minor of rows with identical parity vanishes modulo two. -/
theorem even_minor_of_qParity_eq {V : Type} [Fintype V] {e f : QEq V}
    (eq : qParity e = qParity f) (u v : Option V) :
    Even (qCoord e u * qCoord f v - qCoord e v * qCoord f u) := by
  have h := (coord_modEq_of_qParity_eq eq u).mul (coord_modEq_of_qParity_eq eq v).symm
  rw [mul_comm (qCoord f u)] at h
  change (qCoord e u * qCoord f v) % 2 = (qCoord e v * qCoord f u) % 2 at h
  rw [Int.even_iff]
  omega

end PEqualNP.Search.Helpers
