# Partial results on L-alg-006

Write `n = 2^l` for the number of holes. The posted conjecture asks whether, for every polynomial `p`, there is a bit width `l` at which every DAG-like syntactic integer R(lin) refutation of binary pigeonhole has encoded size greater than `p(n)`. The full conjecture remains open in this work. [Posted statement](https://pequalnp.com/lemma#L-alg-006)

## Explicit refutations for every bit width

The best upper bound obtained here is **`2^O(√n log n)`** for unrestricted DAG-like syntactic integer resolution. More precisely, if `n=2^l`, every width admits a refutation of encoded size at most `2^(512(l+2) · 2^ceil(l/2))`. For every positive integer `k` there is a width threshold beyond which this construction has size at most `2^(n/k)`. This rules out a lower bound of `2^(c n)` holding at all sufficiently large widths for any fixed `c>0`. A superpolynomial lower bound in `n` remains possible. [Refutation](../lean/PEqualNP/Search/BPHPBlockUpper.lean) · [Quantified subexponential bound](../lean/PEqualNP/Search/BPHPSubexponential.lean)

Split each label into a prefix and a suffix with lengths differing by at most one. A prefix identifies a block of `b` holes. For each vector of counts `t`, with one allowance from `0` to `b` per block, prove that the first `1+∑t` pigeons overload some block. One disjunct witnesses overload by naming `t+1` rows in that block. Their total Hamming distance from its prefix is zero exactly when all those rows match. This is one integer equation in the original bit variables. On reading a new row, the proof can reuse the state with an allowance one lower in that row's block. In the final state, `b+1` rows with the same prefix have only `b` suffixes. Testing the bits of those rows produces a violated collision clause. [State representation](../lean/PEqualNP/Search/Helpers/BlockCapacityState.lean) · [Transition](../lean/PEqualNP/Search/BPHPBlockStep.lean) · [Final state](../lean/PEqualNP/Search/Helpers/BlockCapacityTerminal.lean)

There are `(b+1)^(n/b)` count vectors. The encoded cost per transition, and the cost of discharging the final state, are each at most `(n+2)^(64(b+1))`. Choosing about `√n` holes per block balances these costs. The explicit construction still enumerates a superpolynomial number of count vectors. [Cost bound](../lean/PEqualNP/Search/Helpers/BlockBudget.lean) · [Rate](../lean/PEqualNP/Search/Helpers/BPHPBlockRate.lean) · [Little-o estimate](../lean/PEqualNP/Search/Helpers/BlockLittleO.lean)

At every positive width the one-line disjunction of all pairwise collisions also has an integer derivation from the Boolean axioms alone of size at most `2^(522(l+2) · 2^ceil(l/2))`. This transfers the bound to the equivalent version of L-alg-006. [Boolean-axiom proof](../lean/PEqualNP/Search/CollisionSubexponential.lean)

On these same formulas, every polynomial in the encoded size of the constructed integer proofs is eventually smaller than the number of lines in **every parity-resolution refutation**. The repository's parity lower bound grows as `exp(n/(32768 l²))`, which eventually exceeds every fixed power of the integer upper bound. Thus a polynomial-cost translation of all these integer proofs into parity resolution is impossible. [Separation theorem](../lean/PEqualNP/Search/BPHPParitySeparation.lean) · [Parity lower bound](../lean/PEqualNP/ProofComplexity/L036.lean)

### Earlier constructions

There is a DAG-like syntactic integer refutation of encoded size at most **`1000(n+1)¹⁰ 2ⁿ`** for every `n = 2^l`. For each subset `H` of the holes, derive the line saying that at least one of the first `|H|+1` pigeons lies outside `H`. Read the last of those pigeons. If its label is outside `H`, it witnesses the line. If its label is `h ∈ H`, reuse the previously derived line for `H` with `h` removed. A collision clause prevents an earlier pigeon from taking `h`. There are `2ⁿ` subsets, and each transition costs at most `1000(n+1)¹⁰`. Taking `H` to be all holes gives the empty line. The exponential number of states leaves the polynomial-size question open. [Checked construction](../lean/PEqualNP/Search/BPHPDagUpper.lean) · [State transition](../lean/PEqualNP/Search/BPHPSubsetStep.lean) · [Recorded statement](L-alg-006-dag-upper.lean.txt)

Permuting bit positions and flipping chosen bits give `n l!` relabelings of the holes. Covering this construction's subset states by the images of `R` representatives requires `R n l! ≥ 2ⁿ`. For `l ≥ 5` this leaves at least `2^(n/2)` representatives. Constant-row assignments distinguish the Boolean functions of any two different subsets. This counts states in the subset construction. [Symmetry bound](../lean/PEqualNP/Search/BPHPSubsetSymmetry.lean)

A coordinate search gives a refutation of encoded size at most **`36 n² 4ⁿ`**. Query the first bit of `n+1` pigeons. At least `n/2+1` of them share that bit. Keep that many pigeons and repeat on their remaining bits. A branch of this search inspects at most `2(n−1)+l` bits before it identifies a pair of equal labels and the violated input clause. Compiling the search tree uses integer resolution, Boolean axioms, weakening and simplification. At width zero the input already contains the empty clause. Dantchev, Galesi and Martin give the majority-split tree argument for binary resolution. [Dantchev et al., Theorem 5](https://arxiv.org/abs/1809.02843) · [Checked construction](../lean/PEqualNP/Search/BPHPTreeUpper.lean) · [Recorded statement](L-alg-006-tree-upper.lean.txt)

## A single balanced equation would suffice

Let `n = 2^l`. Start with the satisfiable instance where `n` pigeons have distinct labels in `n` holes. Suppose a syntactic integer derivation of encoded size `S` proves a line consisting of one equation with at least one nonzero variable coefficient. With one extra pigeon, there is a refutation of encoded size at most **`42 n² S + 1200(n+1)⁵`**. The equation and its coefficients can vary with the bit width. Deriving any such singleton in polynomial size at every positive width would disprove L-alg-006. [Checked theorem](../lean/PEqualNP/Search/BalancedUnitRefutation.lean) · [Recorded statement](L-alg-006-balanced-unit.lean.txt)

Every balanced assignment lists each label exactly once. Swapping the rows holding two labels that differ in just one bit shows that the coefficient of that bit must be the same in every row. It follows that the integer equations true on every balanced assignment are exactly the integer linear combinations of the column balances. Each column contains `n/2` ones at positive width. Flipping a column in a proof isolates its coefficient. Two copies that omit different pigeons then yield a scaled equality between their bits. The Boolean axioms give just three possible bit differences, so eliminating the two nonzero possibilities costs only the bit length of the scale. [Affine characterization](../lean/PEqualNP/Search/BPHPAffineHull.lean) · [Column proof transformation](../lean/PEqualNP/Search/Helpers/BPHPColumnFlip.lean) · [Scale cancellation](../lean/PEqualNP/Search/Helpers/QUnscaleBitEquality.lean)

## Proving that one fixed hole is occupied

In the same balanced instance let `G₀` be the disjunction, over the `n` pigeons, that a pigeon's binary label equals zero. L-alg-006 holds exactly when for every polynomial `p` there is a positive width at which every derivation of `G₀` from the balanced input clauses has encoded size greater than `p(n)`. A refutation with one extra pigeon of size `S` gives a balanced derivation of `G₀` of size at most **`(1000(n+1)⁴ + 2S)S`**. Conversely, a balanced derivation of size `T` gives a refutation of size at most **`4000(n+1)⁷(T+1)`**. In the first direction, set the extra pigeon's bits to zero. In the second, an additional pigeon cannot use hole zero if one of the balanced pigeons occupies it. Flipping columns excludes each possible label of the extra pigeon in turn. [Equivalence](../lean/PEqualNP/Search/BalancedOccupancyEquivalence.lean) · [Refutation to occupancy](../lean/PEqualNP/Search/BPHPBalancedOccupancy.lean) · [Occupancy to refutation](../lean/PEqualNP/Search/BPHPRefuteFromOccupancy.lean)

An interpolation identity gives a compact algebraic proof of the balanced sum from occupancy of every hole. With labels `Xᵢ` and holes `0,…,n−1`, the product `∏ᵢ(h−Xᵢ)` vanishes when hole `h` is occupied. The discrepancy `∑ᵢ Xᵢ−n(n−1)/2`, multiplied by `(n−1)!`, is an integer linear combination of these `n` products with signed binomial coefficients. The identity holds as a polynomial in the labels. Converting this addition of products into the project's rule for combining selected linear equations remains open. [Polynomial identity](../lean/PEqualNP/Search/BPHPOccupancyCertificate.lean)

## One equation must be hard to evaluate by parity queries

Fix any polynomial line budget `p(n)`. At arbitrarily large bit widths of the form `l = 2^t`, every refutation within that budget contains an equation for which every correct adaptive parity-query algorithm needs **more than `floor(l/(2(t+5)))` queries** in the worst case. The same equation occurs as the result of an integer linear combination and as an operand of a resolution step. The theorem identifies each occurrence together with its earlier premises. Querying its nonzero variable coefficients directly gives an evaluator, so the equation must also use more than this many variables. The lower bound concerns one equation inside a proof whose disjunctions and DAG reuse are unrestricted. [Growing depth bound](../lean/PEqualNP/Search/BPHPActiveDepthWitnesses.lean) · [Support bound](../lean/PEqualNP/Search/BPHPGrowingSupport.lean)

The proof compiles each equation independently into a disjunction of terms, one per accepting leaf of its decision tree. A term for a path of depth `k` contains at most `k` parity equations. Case analysis on the result and one operand simulates a binary integer inference without branching on the rest of either disjunction. For `k ≥ 1`, an `s`-line proof whose individual equations all admit depth `k` gives a Res(k,⊕) proof of at most `(4(k+1)+2·2^k+2)·2^k·s+1` lines. The project's lower bound for Res(k,⊕) then rules out polynomial-length proofs for each fixed `k`. An equation can have large query depth and small integer encoding, so this still leaves the unrestricted lower bound open. [Simulation](../lean/PEqualNP/Search/QEquationSimulation.lean) · [Adaptive depth](../lean/PEqualNP/Search/BPHPEquationDecisionDepth.lean) · [Parity proof lower bound](../lean/PEqualNP/ProofComplexity/L061.lean)

## Two targets for constructing a short proof

In the **balanced** instance there are `n` pigeons and `n` holes. The collision clauses force their binary labels to form a permutation of `0,…,n−1`, so their sum is `n(n−1)/2`. If there is an integer derivation of that single sum equation of encoded size `S`, there is a refutation with `n+1` pigeons of size at most **`2S+403(n+1)^6`**. Take two copies of the derivation, omitting a different pigeon from each. Subtracting the sums says the omitted pigeons have equal labels. Branching on just their `2l` bits yields the empty line using the original collision clauses. The semantic sum identity and the proof conversion are verified. The size of a derivation of the identity is open. [Permutation-sum theorem](../lean/PEqualNP/Search/PermutationSumRefutation.lean) · [Exact checker statement](L-alg-006-permutation-sum.lean.txt)

For the instance with `n+1` pigeons, write one disjunction `G` containing the integer equation “the binary labels of rows `i` and `j` are equal” for every ordered pair `i ≠ j`. This line is true under every Boolean assignment. L-alg-006 holds exactly when, for every polynomial `p`, there is a **positive** bit width at which every derivation of `G` **from the Boolean axioms alone**, using the same integer inference rules, has encoded size greater than `p(n)`. A single polynomial bounding the sizes of such derivations at every positive width would refute the conjecture. [Equivalence](../lean/PEqualNP/Search/CollisionTautologyEquivalence.lean)

At positive bit width, a pigeonhole refutation of encoded size `S` yields a derivation of `G` of size at most **`64000 S³`**. Conversely, a derivation of `G` of size `T` yields a refutation of size at most **`3300 T⁴`**. [From a refutation to the collision statement](../lean/PEqualNP/Search/BPHPCollisionTautology.lean) · [From the collision statement to a refutation](../lean/PEqualNP/Search/BPHPCollisionCost.lean)

## Transferring bounds from other proof systems

For the standard split of each row's bits between two parties and `l ≥ 2`, an integer derivation of just two lines can already have a final line whose falsifying assignments require at least `2^(n−1)` triangles to cover exactly. The two lines together cost at most `4(n−1)+12l+2`. A triangle here is a communication relation whose sets of possible inputs for the second party are nested as the first party's input varies. This example obstructs a direct conversion that replaces each integer line by a small cover of its falsifying assignments. Hrubeš and Pudlák prove an exponential lower bound for Cutting Planes on this binary encoding. [Two-line example](../lean/PEqualNP/Search/BPHPTriangleLine.lean) · [Set-disjointness example](../lean/PEqualNP/Search/Helpers/QTriangleCover.lean) · [Hrubeš and Pudlák, Theorem 3](https://www.math.cas.cz/~pudlak/RandomCP_FOCS.pdf)

## Earlier lower bounds

| Lean result | Bound |
|---|---|
| [BPHPCubic](../lean/PEqualNP/Search/BPHPCubic.lean) | Every degree-at-most-three polynomial over the naturals is exceeded once the bit width exceeds the sum of its coefficients. The input clauses alone cost at least `(2l+1) n choose(n+1,2)` for positive bit width. |
| [bphp_binary_resolution_lower_bound](../lean/PEqualNP/Search/Helpers/BPHPMerge.lean) | Any trace deriving the empty line uses at least `n choose(n+1,2) − 1` binary inferences, even with shared premises. |
| [bphp_semantic_width](../lean/PEqualNP/Search/BPHPSemanticWidth.lean) | For every `l ≥ 59`, some line needs more than `2^floor((l−11)/6)` equations in every disjunction of integer equations defining the same Boolean truth set. |
| [BPHPParityBarrier](../lean/PEqualNP/Search/BPHPParityBarrier.lean) | When `l ≥ 32` and a proof has length `s` with `4s+1 ≤ exp(n/(32768 l²))`, it contains a line with a false constant equation of nonzero even right-hand side and also contains that line with false constants removed. |

A further locality bound holds without restricting coefficients or DAG reuse. Some proof line depends on more than two thirds of the hole count in pigeon rows: for every smaller set of rows, there are two Boolean assignments agreeing on those rows that give different truth values for the line. This alone gives no bound on how many such lines occur. [Semantic pigeon support](../lean/PEqualNP/Search/BPHPPigeonSupport.lean)

There is also a reduction for unrestricted proofs. For every integer refutation of encoded size `s`, there is a prime `p ≤ 16(s+1)²` and a syntactic refutation over the field of `p` elements with at most twice the original line count. The proof chooses a prime preserving nonzero right-hand sides. The sum of their bit lengths bounds the number of exceptional primes. A uniform finite-field line lower bound up to the resulting characteristic bound would therefore settle the integer conjecture. The repository’s checked parity theorem handles characteristic two. Pang gives lower bounds for every fixed prime in a stronger finite-field system. The prime supplied by the integer reduction can grow with proof size. [Pang, Theorem 7.2(e)](https://arxiv.org/abs/2610.00837) · [Finite-field reduction](../lean/PEqualNP/Search/BPHPModularReduction.lean)

The parity argument starts from the repository's exponential lower bound for parity resolution. Each integer combination can be simulated by at most four parity steps. Weakening and Boolean axioms also transfer. If all simplifications preserve the parity implication, the whole integer proof gives a short parity refutation. The theorem identifies a pair of lines and a Boolean assignment witnessing the failure of that implication in any sufficiently short proof. Integer arithmetic permits such a failure because `0 = 2` becomes true modulo two. This leaves unrestricted integer proofs as the outstanding case. [Parity simulation](../lean/PEqualNP/Search/Helpers/QParitySimulation.lean) · [Parity lower bound](../lean/PEqualNP/ProofComplexity/L036.lean)

## Rewriting proof lines as parity decision trees

A parity decision tree queries whether a chosen set of bits has odd sum. Its next query can depend on previous answers. Suppose an integer refutation has `s` lines, and each line's truth on Boolean inputs can be computed by its own such tree with at most `r` leaves. Then a parity refutation exists with at most `4sr(r+1)² + 1` lines. False leaves give blocking clauses. To simulate an inference, branch over the two premise trees and derive the clause blocking each false leaf of the conclusion. Earlier clauses remain available throughout the simulation. [Simulation](../lean/PEqualNP/Search/Helpers/ParityTreeSimulation.lean)

For bit width at least 32, the existing parity lower bound implies that if `4sr(r+1)² + 1 ≤ exp(n/(32768 l²))`, then some integer proof line requires more than `r` leaves. Under a different assumption, if the same `k` parity queries make every line representable by a single parity clause on each cell of the resulting partition, then `2^k(4s+3) > exp(n/(32768 l²))`. [Independent trees](../lean/PEqualNP/Search/BPHPParityTree.lean) · [Common partition](../lean/PEqualNP/Search/BPHPParityCover.lean)

One inexpensive integer equation can already require an exponential parity tree. For `k ≥ 4`, testing whether exactly `k` of `2k` bits are true needs more than `2^k/k` leaves. Thus the tree bound cannot establish superpolynomial integer proof size by charging a line for the leaves it requires. [Middle-slice theorem](../lean/PEqualNP/Search/Helpers/ParityMiddleSlice.lean)

## Reuse on paths to the contradiction

Fix an occurrence of the empty line in a refutation with `s` lines. Keep only dependencies reachable from that occurrence and count references in that part of the proof. For bit width `l ≥ 17`, some dependency path starting at the empty line visits `k` multiply referenced positions with

```text
2^(2^floor((l−17)/6)) ≤ 2s (2s+1)^k.
```

If the same position supplies both premises to a resolution, those are two references. The ordered path visits a position at most once. For any polynomial line budget in the number of holes and any polynomial path-reuse budget in the bit width, arbitrarily large widths exceed at least one budget. In particular, an unrestricted polynomial-size proof family would need deep sharing on a single path. The proof unfolds the indexed DAG and applies the tree lower bound, pruning unused lines before it counts references. [Reuse theorem](../lean/PEqualNP/Search/BPHPReusePath.lean) · [Tree bound](../lean/PEqualNP/Search/Helpers/BPHPTreeRate.lean)

## A single final simplification

Consider a syntactic integer refutation of encoded size `S`. Carry a common list of its false constant equations through the proof. Resolution makes two copies of the common list, and syntactic weakening contracts them to one. The resulting proof reaches a disjunction of false constants using no simplification, at a cost of at most `6S²`. A single simplification then derives the empty line. [Proof](../lean/PEqualNP/Search/DeferredSimplification.lean) · [Exact checker statement](L-alg-006-final-step.lean.txt)

The last disjunction can also be reduced to a **single equation** `0 = D`. Take the product of its nonzero right-hand sides as a common multiple. Integer combinations and contraction convert the disjunction into the singleton. The bit length of `|D|` is at most `S+1`, and the full proof, including the last simplification, costs at most `20(S+1)² + 1` in the posted size measure. These transformations apply to arbitrary input formulas. Consequently, L-alg-006 is equivalent to a superpolynomial size lower bound for simplification-free derivations of such singletons from binary pigeonhole. The lower bound for these derivations remains open. [Single-unit theorem](../lean/PEqualNP/Search/SingleUnitSimplification.lean) · [Exact checker statement](L-alg-006-final-unit.lean.txt) · [Equivalence](../lean/PEqualNP/Search/BPHPFalseUnit.lean)

For binary pigeonhole, the parity lower bound also restricts the value of `D`. If a simplification-free derivation of the singleton has `s` lines, `l ≥ 32` and `4s+2 ≤ exp(2^l/(32768 l²))`, then `D` is even. An odd right-hand side would stay contradictory modulo two and yield a parity refutation with at most `4s+2` lines. A nonzero even right-hand side becomes zero modulo two, so this argument leaves that case open. [False-unit parity theorem](../lean/PEqualNP/Search/BPHPFalseUnitParity.lean)

## A collision search inside one resolution inference

Before reducing an equation modulo two, divide its coefficients **and its right-hand side** by their largest common power of two. Leave the zero equation at zero. Now every false constant projects to a contradiction, including `0 = D` for even nonzero `D`. Fix `l ≥ 32` and write `E = exp(2^l/(32768 l²))`. In any integer refutation with `s` lines satisfying `4s+1 ≤ E`, some resolution inference combines two equations whose normalized augmented rows are independent over the rationals and equal modulo two. They share an odd variable coefficient. Every two-column determinant is even and at least one is nonzero. A four-line derivation from the satisfiable one-variable formula `x=1` already exhibits this kind of cancellation. [Minor theorem](../lean/PEqualNP/Search/BPHPPrimitiveMinor.lean) · [Four-line example](../lean/PEqualNP/Search/PrimitiveCancellationExample.lean)

An assignment witnesses the failure of such a projected inference when it satisfies both selected equations and falsifies the entire projected conclusion. The parity clause that excludes these witnesses can be derived from the pigeonhole axioms. If all these clauses had derivations of at most `B` lines, inserting them into the integer proof after projection would give a parity refutation of at most `(B+8)s+1` lines. Thus whenever `(B+8)s+1 ≤ E`, one resolution inference has a clause whose every parity derivation needs more than `B` lines. [Repair theorem](../lean/PEqualNP/Search/BPHPHardCancellation.lean)

There is a search problem on the witnesses for that inference. Given a witness, use parity queries to identify two pigeons assigned the same hole and the hole they share. For each natural `r` with `(3r+10)s+1 ≤ E`, one inference has more than `r` distinct witnesses, and every adaptive parity decision tree solving this search on its witnesses needs more than `r` leaves. [Search theorem](../lean/PEqualNP/Search/BPHPCancellationSearch.lean)

Choose any set of `k` pigeons and let `I` count the witnesses for the same inference that assign those pigeons distinct holes. Then `r < 2^(lk) + I`. In particular, whenever `2^(lk) ≤ r`, some witness avoids every collision internal to the chosen set. To prove the count, query the chosen pigeons first. A collision among them labels the leaf immediately. On the remaining leaves, distinguish just the exceptional witnesses, charging each at most once. What remains open is whether an integer DAG can produce such a hard inference in polynomial size. [Counting theorem](../lean/PEqualNP/Search/BPHPCancellationMultiplicity.lean) · [Exact witness statement](L-alg-006-cancellation-witnesses.lean.txt)

## Repeated use of a step that shortens a line

For `l ≥ 17`, let `T = 2^(2^floor((l−17)/6))`. Fix a syntactic justification for each position in a refutation with `s` lines and encoded size `S`. Unfold the dependencies from a chosen occurrence of the empty line. For every natural number `M` with `4MsS < T+2`, one unary inference that shortens the list of equations appears more than `M` times in that tree. The original DAG can store this inference once. Width counts list entries, including duplicates. [Shrinking-line theorem](../lean/PEqualNP/Search/BPHPShrinkingLine.lean)

The same bound applies inside a simplification-free derivation of a false singleton, with `s` and `S` measured in that derivation. Here the repeatedly copied inference is a weakening that preserves every distinct equation in its premise and shortens the list. It must therefore remove duplicate occurrences. The proof charges the input leaves in the unfolded tree to local width losses and counts the copies contributed by each position in the original proof. [Repeated contraction](../lean/PEqualNP/Search/BPHPShrinkingLine.lean) · [Counting copies](../lean/PEqualNP/Search/Helpers/DagCopies.lean)

With the pinned Lean toolchain and the Mathlib cache installed, run these commands from the checkout.

```sh
cd lean
lake build +PEqualNP.Search.BPHPCubic +PEqualNP.Search.Helpers.BPHPMerge \
  +PEqualNP.Search.BPHPSemanticWidth +PEqualNP.Search.BPHPParityBarrier \
  +PEqualNP.Search.BPHPPigeonSupport +PEqualNP.Search.BPHPModularReduction \
  +PEqualNP.Search.BPHPParityTree +PEqualNP.Search.BPHPParityCover \
  +PEqualNP.Search.Helpers.ParityMiddleSlice +PEqualNP.Search.Helpers.ParitySeparation \
  +PEqualNP.Search.BPHPReusePath +PEqualNP.Search.BPHPShrinkingLine \
  +PEqualNP.Search.BPHPFalseUnit +PEqualNP.Search.BPHPFalseUnitParity \
  +PEqualNP.Search.SingleUnitSimplification +PEqualNP.Search.BPHPPrimitiveMinor \
  +PEqualNP.Search.PrimitiveCancellationExample +PEqualNP.Search.BPHPCancellationWitnesses \
  +PEqualNP.Search.BPHPCancellationMultiplicity +PEqualNP.Search.BPHPActiveDepthWitnesses \
  +PEqualNP.Search.PermutationSumRefutation +PEqualNP.Search.CollisionTautologyEquivalence \
  +PEqualNP.Search.BPHPCollisionCost +PEqualNP.Search.BPHPColumnBalance \
  +PEqualNP.Search.BalancedUnitRefutation +PEqualNP.Search.BalancedOccupancyEquivalence \
  +PEqualNP.Search.BPHPTriangleLine +PEqualNP.Search.Helpers.QTriangleCover \
  +PEqualNP.Search.BPHPOccupancyCertificate +PEqualNP.Search.BPHPTreeUpper \
  +PEqualNP.Search.BPHPDagUpper +PEqualNP.Search.BPHPSubsetSymmetry \
  +PEqualNP.Search.BPHPBlockUpper +PEqualNP.Search.BPHPSubexponential \
  +PEqualNP.Search.CollisionSubexponential +PEqualNP.Search.Helpers.BlockLittleO \
  +PEqualNP.Search.BPHPParitySeparation
```

From the checkout root, the project's checker can verify the following theorems against their recorded statements.

```sh
node tools/check-lean.mjs lean/PEqualNP/Search/DeferredSimplification.lean \
  notes/L-alg-006-final-step.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/SingleUnitSimplification.lean \
  notes/L-alg-006-final-unit.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPPrimitiveMinor.lean \
  notes/L-alg-006-parity-minor.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPCancellationWitnesses.lean \
  notes/L-alg-006-cancellation-witnesses.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPEquationSupport.lean \
  notes/L-alg-006-equation-support.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPEquationDecisionDepth.lean \
  notes/L-alg-006-equation-decision-depth.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPActiveDepthWitnesses.lean \
  notes/L-alg-006-active-depth.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/PermutationSumRefutation.lean \
  notes/L-alg-006-permutation-sum.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/CollisionTautologyEquivalence.lean \
  notes/L-alg-006-collision-equivalence.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BalancedUnitRefutation.lean \
  notes/L-alg-006-balanced-unit.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPBalancedOccupancy.lean \
  notes/L-alg-006-balanced-occupancy.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BalancedOccupancyEquivalence.lean \
  notes/L-alg-006-balanced-occupancy-equivalence.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPTreeUpper.lean \
  notes/L-alg-006-tree-upper.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPDagUpper.lean \
  notes/L-alg-006-dag-upper.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPSubsetSymmetry.lean \
  notes/L-alg-006-subset-symmetry.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPBlockUpper.lean \
  notes/L-alg-006-block-upper.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPSubexponential.lean \
  notes/L-alg-006-subexponential.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/CollisionSubexponential.lean \
  notes/L-alg-006-collision-subexponential.lean.txt check
node tools/check-lean.mjs lean/PEqualNP/Search/BPHPParitySeparation.lean \
  notes/L-alg-006-parity-separation.lean.txt check
```
