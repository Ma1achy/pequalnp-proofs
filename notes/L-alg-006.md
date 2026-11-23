# Partial results on L-alg-006

The posted conjecture asks whether every polynomial is exceeded by the size of a dag-like syntactic integer R(lin) refutation of binary pigeonhole for some bit width. Write `n = 2^l` for the number of holes. The full conjecture remains open in this work. [Posted statement](https://pequalnp.com/lemma#L-alg-006)

| Lean result | Bound |
|---|---|
| [BPHPCubic](../lean/PEqualNP/Search/BPHPCubic.lean) | Every degree-at-most-three polynomial over the naturals is exceeded once the bit width exceeds the sum of its coefficients. The input clauses alone cost at least `(2l+1) n choose(n+1,2)` for positive bit width. |
| [bphp_binary_resolution_lower_bound](../lean/PEqualNP/Search/Helpers/BPHPMerge.lean) | Any trace deriving the empty line uses at least `n choose(n+1,2) − 1` binary inferences, even with shared premises. |
| [bphp_semantic_width](../lean/PEqualNP/Search/BPHPSemanticWidth.lean) | For every `l ≥ 59`, some line needs more than `2^floor((l−11)/6)` equations in every disjunction of integer equations defining the same Boolean truth set. |
| [BPHPParityBarrier](../lean/PEqualNP/Search/BPHPParityBarrier.lean) | When `l ≥ 32` and a proof has length `s` with `4s+1 ≤ exp(n/(32768 l²))`, it contains a line with a false constant equation of nonzero even right-hand side and also contains that line with false constants removed. |

A further locality bound holds without restricting coefficients or DAG reuse. Some proof line depends on more than two thirds of the hole count in pigeon rows: for every smaller set of rows, there are two Boolean assignments agreeing on those rows that give different truth values for the line. This alone gives no bound on how many such lines occur. [Semantic pigeon support](../lean/PEqualNP/Search/BPHPPigeonSupport.lean)

There is also a reduction for unrestricted proofs. For every integer refutation of encoded size `s`, there is a prime `p ≤ 16(s+1)²` and a syntactic refutation over the field of `p` elements with at most twice the original line count. The proof chooses a prime preserving nonzero right-hand sides. The sum of their bit lengths bounds the number of exceptional primes. A uniform finite-field line lower bound up to the resulting characteristic bound would therefore settle the integer conjecture. The existing parity theorem handles only characteristic two. [Finite-field reduction](../lean/PEqualNP/Search/BPHPModularReduction.lean)

The parity argument starts from the repository's exponential lower bound for parity resolution. Each integer combination can be simulated by at most four parity steps. Weakening and Boolean axioms also transfer. If all simplifications preserve the parity implication, the whole integer proof gives a short parity refutation. The theorem identifies a pair of lines and a Boolean assignment witnessing the failure of that implication in any sufficiently short proof. Integer arithmetic permits such a failure because `0 = 2` becomes true modulo two. This leaves unrestricted integer proofs as the outstanding case. [Parity simulation](../lean/PEqualNP/Search/Helpers/QParitySimulation.lean) · [Parity lower bound](../lean/PEqualNP/ProofComplexity/L036.lean)

## Rewriting proof lines as parity decision trees

A parity decision tree queries whether a chosen set of bits has odd sum. Its next query can depend on previous answers. Suppose an integer refutation has `s` lines, and each line's truth on Boolean inputs can be computed by its own such tree with at most `r` leaves. Then a parity refutation exists with at most `4sr(r+1)² + 1` lines. False leaves give blocking clauses. To simulate an inference, branch over the two premise trees and derive the clause blocking each false leaf of the conclusion. Earlier clauses remain available throughout the simulation. [Simulation](../lean/PEqualNP/Search/Helpers/ParityTreeSimulation.lean)

For bit width at least 32, the existing parity lower bound implies that if `4sr(r+1)² + 1 ≤ exp(n/(32768 l²))`, then some integer proof line requires more than `r` leaves. Under a different assumption, if the same `k` parity queries make every line representable by a single parity clause on each cell of the resulting partition, then `2^k(4s+3) > exp(n/(32768 l²))`. [Independent trees](../lean/PEqualNP/Search/BPHPParityTree.lean) · [Common partition](../lean/PEqualNP/Search/BPHPParityCover.lean)

One inexpensive integer equation can already require an exponential parity tree. For `k ≥ 4`, testing whether exactly `k` of `2k` bits are true needs more than `2^k/k` leaves. Thus the tree bound cannot establish superpolynomial integer proof size by charging a line for the leaves it requires. [Middle-slice theorem](../lean/PEqualNP/Search/Helpers/ParityMiddleSlice.lean)

With the pinned Lean toolchain and the Mathlib cache installed, run these commands from the checkout.

```sh
cd lean
lake build +PEqualNP.Search.BPHPCubic +PEqualNP.Search.Helpers.BPHPMerge \
  +PEqualNP.Search.BPHPSemanticWidth +PEqualNP.Search.BPHPParityBarrier \
  +PEqualNP.Search.BPHPPigeonSupport +PEqualNP.Search.BPHPModularReduction \
  +PEqualNP.Search.BPHPParityTree +PEqualNP.Search.BPHPParityCover \
  +PEqualNP.Search.Helpers.ParityMiddleSlice +PEqualNP.Search.Helpers.ParitySeparation
```
