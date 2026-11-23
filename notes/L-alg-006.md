# Partial results on L-alg-006

The posted conjecture asks whether every polynomial is exceeded by the size of a dag-like syntactic integer R(lin) refutation of binary pigeonhole for some bit width. Write `n = 2^l` for the number of holes. The full conjecture remains open in this work. [Posted statement](https://pequalnp.com/lemma#L-alg-006)

| Lean result | Bound |
|---|---|
| [BPHPCubic](../lean/PEqualNP/Search/BPHPCubic.lean) | Every degree-at-most-three polynomial over the naturals is exceeded once the bit width exceeds the sum of its coefficients. The input clauses alone cost at least `(2l+1) n choose(n+1,2)` for positive bit width. |
| [bphp_binary_resolution_lower_bound](../lean/PEqualNP/Search/Helpers/BPHPMerge.lean) | Any trace deriving the empty line uses at least `n choose(n+1,2) − 1` binary inferences, even with shared premises. |
| [bphp_semantic_width](../lean/PEqualNP/Search/BPHPSemanticWidth.lean) | For every `l ≥ 59`, some line needs more than `2^floor((l−11)/6)` equations in every disjunction of integer equations defining the same Boolean truth set. |
| [BPHPParityBarrier](../lean/PEqualNP/Search/BPHPParityBarrier.lean) | When `l ≥ 32` and a proof has length `s` with `4s+1 ≤ exp(n/(32768 l²))`, it contains a line with a false constant equation of nonzero even right-hand side and also contains that line with false constants removed. |

The parity argument starts from the repository's exponential lower bound for parity resolution. Each integer combination can be simulated by at most four parity steps. Weakening and Boolean axioms also transfer. If all simplifications preserve the parity implication, the whole integer proof gives a short parity refutation. The theorem identifies a pair of lines and a Boolean assignment witnessing the failure of that implication in any sufficiently short proof. Integer arithmetic permits such a failure because `0 = 2` becomes true modulo two. This leaves unrestricted integer proofs as the outstanding case. [Parity simulation](../lean/PEqualNP/Search/Helpers/QParitySimulation.lean) · [Parity lower bound](../lean/PEqualNP/ProofComplexity/L036.lean)

With the pinned Lean toolchain and the Mathlib cache installed, run these commands from the checkout.

```sh
cd lean
lake build +PEqualNP.Search.BPHPCubic +PEqualNP.Search.Helpers.BPHPMerge \
  +PEqualNP.Search.BPHPSemanticWidth +PEqualNP.Search.BPHPParityBarrier
```
