import PEqualNP.Search.BPHPSubsetStep
import PEqualNP.Search.Helpers.QSubsetAssembly

namespace PEqualNP.Search

open Helpers PEqualNP.ProofComplexity

/-- One state for each subset of the holes yields a singly exponential
unrestricted integer proof for every width. The cost includes every occurrence
of every coefficient, also when a state line is copied inside a transition. -/
theorem BPHPDagUpper :
    ∀ l : ℕ, ∃ π : List (QLine (Fin (2^l+1) × Fin l)),
      IsResLinQSynRefutation (BPHP (2^l+1) l) π ∧
        resLinQSize π ≤ 2^(2^l) * (1000*(2^l+1)^10) := by
  intro l
  cases l with
  | zero =>
    have ax : (∅ : ProofComplexity.Clause (Fin (2^0+1) × Fin 0)) ∈ BPHP (2^0+1) 0 :=
      ⟨0,1,fun _ => false,by decide,by simp⟩
    exact ⟨[[]],⟨.ax ∅ .nil ax (by simp),List.mem_cons_self⟩,by decide⟩
  | succ l =>
    obtain ⟨π,d,hit,price⟩ := qSubsetAssembly (subsetState (l := l+1)) _
      (subsetState_step (Nat.succ_pos l))
    exact ⟨π,⟨d,by simpa using hit Finset.univ⟩,by simpa using price⟩

end PEqualNP.Search
