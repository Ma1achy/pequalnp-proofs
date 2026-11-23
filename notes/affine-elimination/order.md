# Exact output counts for two orders on the inner-product family

For each positive k define q(x,y) = Σᵢ xᵢyᵢ over F₂. Both source formulas project to q=0. The procedure here is exactly the pairwise graph projection, RREF, deduplication, contained-flat deletion and parallel-coset merging in `flat_elimination.py`. No new variables are introduced during projection. An affine clause forbids one affine flat.

## Source encodings

* In the concise encoding, introduce tᵢ=xᵢ∧yᵢ using (¬tᵢ∨xᵢ), (¬tᵢ∨yᵢ), (tᵢ∨¬xᵢ∨¬yᵢ). Require Σtᵢ=0. This gives 3k+1 factors over 3k variables.
* In the strict binary-clause plus parity encoding, introduce aᵢ,bᵢ,tᵢ. Require xᵢ=tᵢ+aᵢ and yᵢ=tᵢ+bᵢ. Forbid each pair among (aᵢ,bᵢ,tᵢ) from both being 1. Require Σtᵢ=0. The four allowed local triples (aᵢ,bᵢ,tᵢ) are 000, 100, 010 and 001, giving the four distinct pairs (xᵢ,yᵢ). The unique extension has tᵢ=xᵢyᵢ. This gives 5k+1 factors over 5k variables.

Both use O(k log(k+1)) bits under a sparse indexed-literal encoding. Under the experiment's dense encoding, the concise and strict inputs respectively have 7k+1 and 8k+1 original equation rows, each using n+1 bits, plus the self-delimiting headers. Thus dense input size is Θ(k²).

## The easy order

Eliminate all terminal variables xᵢ,yᵢ first, then aᵢ,bᵢ where present, then the products tᵢ. In the strict encoding each terminal occurs only in one parity equation. Its elimination discards that equation. Every occurrence of aᵢ,bᵢ in the remaining clauses is negative. All graphs incident to one such variable prescribe the same forbidden value, so they generate no consistent pair. The remaining global parity disappears when its first variable is projected.

In the concise encoding, the two clauses involving xᵢ can only conflict on tᵢ=0 and tᵢ=1 simultaneously. They disappear, leaving only (¬tᵢ∨yᵢ) at that index. Projecting yᵢ removes it. Again the single remaining parity disappears. For k≥2 the input flats at each stage of these orders have distinct coefficient row spaces and no proper containments. In particular the global parity involves at least two different blocks and cannot contain or be contained in a local flat. For k=1 the global constraint t₁=0 allows initial containment deletions, after which the same steps only remove constraints. The number of normalized flats never exceeds the raw input count.

## The auxiliary-first order

Eliminate (a₁,b₁), …, (aₖ,bₖ) in the strict encoding and then t₁,…,tₖ in both. The bad projected set is q=1. Its optimal cover by arbitrary affine flats has exactly 2ᵏ−1 members, as shown in `obstruction.md`. The implemented output sizes admit more specific formulas.

**Strict gadget.** Eliminating a and b substitutes a=x+t and b=y+t into the three forbidden pairs, because each defining parity permits exactly one auxiliary value everywhere. Pairs between two negative occurrences of a, or two negative occurrences of b, cannot conflict. Directly the resulting three forbidden pivot graphs on t, written as requirements on t when their domains hold, are

| Domain label | Domain | Required value of t |
| --- | --- | --- |
| X | x=0 | 0 |
| Y | y=0 | 0 |
| D | x=y | x |

For example the forbidden pair a=b=1 becomes the graph on x=y requiring t=x. On intersections of domains the required values agree, including at x=y=0. At least one domain holds for every (x,y).

After processing j products, 0≤j<k, one residual flat for each word in {X,Y,D}ʲ describes when the tail parity disagrees with Σ xᵢ over its D positions, restricted to the Cartesian product of its domains. The untouched local factors remain. To verify induction, the active tail parity graph pairs with each of the three local graphs for the next block. Pairing two local graphs gives no conflict on their common domain. Pairing two tail graphs at incompatible earlier products gives an empty intersection, and on any common domain they prescribe the same parity because both compute the same actual products.

At these intermediate stages, the tail still has a live t variable. Projecting the direction space of a residual onto any processed block gives its labeled line direction, since one live t can absorb the parity equation. Thus distinct words have different directions while all residuals have the same rank. The local flats cannot subsume these residuals or be subsumed by them. For j≥1 a residual has an earlier domain restriction and allows arbitrary x,y in each untouched block. For j=0 and k≥2 the global parity contains t from at least two different blocks. The equations of different local graphs have distinct direction spaces, and distinct gadgets concern separate variables. During initial a,b substitutions each fresh local row still involves variables from just that block, with the only three possible surviving pair restrictions listed above. These observations exclude extra pair merges or containment deletions throughout the induction. For k=1, the input unit t₁=0 can subsume some local flats before processing. Eliminating its auxiliary variables leaves precisely the forbidden point x₁=y₁=1, as is also verified directly by the script.

At j=k, each surviving word forbids its domain cut by the equation Σ_{i:D} xᵢ=1. Exactly the 2ᵏ words without a D give an empty flat. All other flats have dimension k−1. When at least two D positions occur, the projection of the direction space onto each local coordinate pair is the labeled line X, Y or D. A free move at one D can be compensated at another D. When there is exactly one D, its coordinates are fixed to (1,1) and its local direction projection is zero. All other positions retain their X or Y directions. Consequently the remaining words have distinct direction spaces. Equal dimension rules out proper containment. **The final count is exactly 3ᵏ−2ᵏ**, even though every emitted flat already has the largest possible dimension in q=1.

**Concise gadget.** Use X and Y as above with t=0. Replace D by P, the point x=y=1 with t=1. The same induction applies. A final word survives precisely when it has an odd number of P positions. For distinct words, different P-versus-line positions conflict whenever an X or Y domain in the other word occurs there. With the same P positions, distinct choices of X or Y give incomparable flats of equal rank and distinct directions. More generally the direction projection at each coordinate block distinguishes X, Y and P (zero local direction for P); the live tail parity does not couple earlier free coordinates here. Thus there is no simplification among distinct surviving words. The count is the odd part of (2+1)ᵏ, namely **(3ᵏ−1)/2**. The direct k=1 simplification again gives a single forbidden point.

The order theorem concerns this algorithm and the specified orders. The optimal-cover theorem concerns every explicit affine-clause representation of the designated projection. Circuits, additional quantified variables and other projection prefixes have different representation requirements.

## A small irredundant cover that the simplifier cannot merge

In three dimensions take the three forbidden lines given by z=x=0, z=y=0, and z=x+y=0. Their union is exactly the proper plane z=0. All three pass through the origin and have distinct directions. Each contains one point belonging to neither of the others. Thus every single deletion changes the function, containment and parallel merging do nothing, and one different affine flat represents the whole union. The formula is satisfiable at every point with z=1. Three is the least ambient dimension for a proper flat to admit this particular failure: in at most two dimensions a proper nonempty flat is a point or a two-point line. A line covered by its proper subflats consists of two parallel singleton cosets, which the reducer can merge. This minimality statement is restricted to cases whose optimum is one proper nonempty flat.

## Reproduction and checks

Run `python quadratic_experiment.py` in this directory. It writes `quadratic-results.json`. Every order is run through the final SAT decision. A separate oracle directly builds the unique extensions of the even inner-product assignments. At stages with at most 12 variables remaining the runner checks every assignment against the oracle's projection onto that stage. The chosen x,y projection is always checked in full. The script asserts both exact counts above, strict-gadget output ranks, the easy-order peak bound, and the three-line example. For k≤3 it independently enumerates all affine flats contained in the odd set by extending smaller flats with parallel cosets. Every nontrivial affine flat can be obtained from a hyperplane and its translate, so this enumeration covers all dimensions. It confirms both the largest flat size and an optimal disjoint cover by the nonzero x fibers.

| k | Optimum at x,y projection | Concise auxiliary-first count | Strict auxiliary-first count | Strict terminal-first peak |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 1 | 1 | 4 |
| 2 | 3 | 4 | 5 | 11 |
| 3 | 7 | 13 | 19 | 16 |
| 4 | 15 | 40 | 65 | 21 |
| 5 | 31 | 121 | 211 | 26 |
| 6 | 63 | 364 | 665 | 31 |

The JSON includes the original encoded input length, encoded length at each stage, flat and row counts, maximum clause width, row and coefficient bit lengths, and operation event counts. The counts describe deterministic runs rather than wall time or a lower bound on all implementations.
