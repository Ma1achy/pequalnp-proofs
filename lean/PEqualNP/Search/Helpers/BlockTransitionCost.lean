import PEqualNP.Defs.ProofComplexityBit

namespace PEqualNP.Search.Helpers

/-- Cost bounds for a shared count-vector state, its conditional extension on a
single row value, and the full case split over that row. -/
def blockStateWeightCap (u v : ℕ) : ℕ :=
  let n := 2^(u+v)
  2^u * (n+2)^(2^v+1) * (1 + (n+1)*(u+v) + (n+1)*u)

def blockBranchCap (u v : ℕ) : ℕ :=
  let l := u+v
  let n := 2^l
  let C := blockStateWeightCap u v
  let D := 4*l+C
  (C+2)*(2+2*C+4*D) + (4*l+4)*(10+(n+1)*l+(u+l)+4*l) + (1+D)

def blockTransitionCost (u v : ℕ) : ℕ :=
  let l := u+v
  2^l * (blockBranchCap u v + 10*(blockStateWeightCap u v+4*l+1))

end PEqualNP.Search.Helpers
