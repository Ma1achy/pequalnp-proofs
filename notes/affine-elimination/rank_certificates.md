# Projection certificates with bounded helper rank

Consider a conjunction of m affine clauses on n variables. Each clause forbids one affine flat. Designate h variables as helpers w, with visible variables y. Discard inconsistent forbidden systems, whose flats are empty. For every other flat assume that the coefficient matrix restricted to the h helper columns has rank at most r, where 0≤r≤h. Set

$$
D(h,r)=\sum_{d=0}^r {h\choose d}.
$$

Every projected forbidden assignment has a certificate using at most D(h,r) original flats. It follows constructively that the projected relation has a cover by at most

$$
K = 1+\sum_{s=1}^{\min(m,D(h,r))} {m\choose s}2^{rs}
$$

forbidden flats. The extra one simplifies the runtime bound for empty instances. The factor is deliberately loose, particularly for rank one, where direct linear-inconsistency witnesses give the smaller bound in the helper-block theorem. Holding h and r fixed, K is polynomial in m. For varying h the exponent is a parameter, and the cost includes explicit enumeration of helper assignments.

## Proof and algorithm

Fix y at which no helper assignment satisfies the conjunction. The fibers of the forbidden flats cover the helper cube. Take any inclusion-minimal subcover at this y. Each selected fiber has a private point belonging only to that fiber among the chosen ones. Otherwise removing that fiber would preserve coverage.

A nonempty fiber of rank q≤r is specified by q independent affine equations in w. Its indicator is, over F₂, the product of q degree-one satisfaction indicators, with the constant-one indicator for q=0. Reducing powers by wⱼ²=wⱼ gives a multilinear polynomial of degree at most r that agrees on the cube. This evaluation space has dimension at most D(h,r), since it is spanned by all square-free monomials of those degrees. The selected indicators are linearly independent as functions. Evaluating a vanishing linear combination at the private point of member j forces its coefficient to vanish. The subcover therefore has at most D(h,r) members. This proof only bounds a certificate size. The algorithm finds all certificates it needs by enumerating subsets and offset patterns.

For each original consistent flat, eliminate among its helper coefficient rows, carrying the visible coefficients and constants. The result consists of a visible affine domain and q independent equations A w = f(y), with f an affine vector. From each q=0 input carry its forbidden visible domain directly. For q>0 and every q-bit pattern p compute the visible flat on which the domain holds and f(y)=p, discarding empty results by Gaussian elimination. Alongside that flat, store the helper fiber {w : A w=p} as a mask of 2ʰ bits by enumeration. Across feasible patterns, these visible flats partition the domain of their input.

Enumerate subsets of 2 through D(h,r) noncylindrical inputs. A noncylindrical input alone has a proper helper fiber and cannot cover the cube. For each choice of one feasible pattern per selected input, test whether their helper masks have union equal to the whole helper cube. If so, emit the intersection of the visible flat for each selected pattern, discarding empty intersections by Gaussian elimination. Any emitted intersection is forbidden at every y it contains, because every w then lies in some selected forbidden fiber. For the other direction take a y with no satisfying w. It lies in a carried cylinder, or its bounded-size minimal subcover has exactly one feasible pattern per chosen member at y, so its intersection is emitted. Duplicates and redundant emitted flats are permissible. There are at most 2ʳ feasible patterns per input and hence at most K total outputs, counting single cylinders among the size-one terms.

When the visible projection is q(x,y)=Σᵢxᵢyᵢ=0 on 2k terminal variables, the established minimum cover of its odd set is 2ᵏ−1. Thus for m≥1 and fixed h,r the input must have m = Ω_{h,r}(2^{k/D(h,r)}) affine clauses. For 1<r<h this is a lower bound. An exponent-matching construction is open here. The rank-one result has a matching construction. At r=h the direct enumeration of one failed clause for each helper assignment already gives a bound of m^{2ʰ} without the offset constant. None of these statements proves the optimal number of helper clauses at unrestricted, varying rank and budget.

## Bit costs

The implementation is `rank_certificates.py`. Let L be the total number of raw input equation rows. Use the same dense bit-row model as `flat_elimination.py`, with n+1 bits per row. For a conservative uniform bound define H=2ʰ and

$$
B=2+n+m+L+H+D(h,r)+rD(h,r)+\lceil\log_2(2+K)\rceil.
$$

Precomputation uses H explicitly indexed helper assignments and up to 2ʳ≤H masks of H bits per surviving noncylindrical input. Computing a single helper dot product takes O(n+1) bit operations by masking and parity in a fixed-length row, with a further O(H) bound for marking an entry in a helper mask. Helper Gaussian elimination on a flat has at most n pivots. For each of at most mH possible source patterns, testing its visible system uses at most 2n rows. The initial raw systems use at most L rows in aggregate. These are polynomial in B, with the explicit bound below including this precomputation.

There are at most K subset-pattern iterations, plus at most K subset loop entries. Each pattern processes at most D masks of H bits. Its intersection has at most Dn visible rows after the per-option RREF. Row elimination of R rows with at most n pivots can use O((R+1)(n+1)³) bit operations, allowing sorting pivot keys and comparisons of n-bit masks. For a literal implementation using collision-resolving dictionaries and costly address arithmetic, a looser O((R+1)(n+1)⁴ (1+log₂(2+K))) allowance suffices by a linear scan among at most n pivot entries per access and by charging address/counter widths. A direct deterministic array of pivots yields the same polynomial bound without hashing assumptions. With R≤Dn≤B² and all row/mask indices and running counters using O(B) bits, a uniform conservative total is **O(K B⁸) bit operations**, including preprocessing, enumerating patterns, generating indices, constructing output and its variable-length storage. An output containing up to K reduced flats of at most n rows needs O(K B³) bits including addressing overhead. The other working space fits O(B⁶) bits (pivot data, input, guards, patterns and masks). These bounds refer to the explicit implementation strategy and make no optimal-order, minimal-witness-search or free-large-integer assumptions.

With at least one dense raw row, n,m,L are bounded by the original dense input length N (each flat also has a nonempty width header). For fixed h,r, the computation is polynomial in N with an exponent depending on h,r. With zero raw rows, the formula is constant and the empty-variable-list or full-space output follows immediately from whether any empty-system forbidden flat occurs; the implementation handles this case before constructing n-bit coefficient masks. In a sparse encoding, compactly renumber occurring variables and designated helpers before constructing dense masks.

## Checks and sharp examples for certificate size

Run `python rank_certificates.py`. The independent oracle enumerates all total assignments, computes the projection of satisfying assignments as a set, then compares every visible assignment to the returned cover. The script tests every family of at most two distinct forbidden flats on three variables with two designated helpers, including the empty flat and the whole-space flat, for each admissible rank cutoff (1,797 cases counting the separate cutoffs). It checks 256 further deterministic cases with seed 248133, varying h, r, coordinate positions and degenerate inputs. It verifies a rank-limit rejection on a nonempty flat above the promised rank.

* In dimension two, three rank-one fibers can cover the helper plane irredundantly. A visible bit in the test toggles the three-way conflict.
* In dimension three all seven lines through zero together cover the cube. Each line has helper codimension two and a distinct private nonzero point. Removing any line leaves its endpoint uncovered. Here D(3,2)=7 is attained.
* For arbitrary h, forbidding all 2ʰ singleton helper assignments gives a cover for which every member is essential, attaining D(h,h)=2ʰ. Deleting any one singleton restores a satisfying assignment. The script verifies this family with all single deletions for h=1,2,3.

These examples establish sharp certificate cardinalities in the indicated cases. They concern inclusion-minimal covers of a helper cube at a fixed visible assignment.

## Two helpers, with any per-clause rank

Let c, ℓ, p be the numbers of original consistent forbidden flats of helper coefficient rank 0, 1 and 2, respectively, for two designated helpers. Let m=c+ℓ+p. At each visible assignment the active fibers have shapes given by the whole helper square, a line of two points, or a singleton. The following explicit upper bound on the number of projected forbidden flats distinguishes how often the largest helper rank is used. Here C(a,b) denotes the binomial coefficient, set to zero for b>a.

**Projected clause bound**

    c + 2 C(ℓ,2) + 4 [C(ℓ,3) + p C(ℓ,2) + ℓ C(p,2)] + 24 C(p,4).

A whole-square fiber suffices by itself and its visible domain is carried unchanged. If a minimal cover contains a line, retain the line and for each of its two outside points retain one member covering that point. Minimality implies that there were at most three members in total. A minimal cover using only singletons consists of four singleton fibers at the four distinct helper assignments.

To count the offset patterns that can remain in minimal covers, first fix the identities of the inputs and hence their fiber directions.

* Two lines can cover the square only if they have the same direction and opposite offsets. There are at most two assignments of the offsets.
* Three lines in a minimal cover must have distinct directions, since identical lines are redundant and complementary parallel lines suffice by themselves. Three lines of distinct directions have union size 3 plus the number of points at which all three meet, by inclusion-exclusion. A cover therefore determines a common point, with just four possibilities.
* Two lines and one singleton must have nonparallel lines. Their union covers three points, leaving the location of the singleton determined, with four choices of the two line offsets together.
* One line and two singletons must cover the two points outside the line by the two distinct singleton inputs. There are two possible offsets for the line and two possible orders for the singletons.
* Four singleton inputs have at most 4!=24 possible bijections to the helper points.

For a fixed offset and input, its feasible visible locus is an affine flat, as in the general theorem. A fixed tuple of offsets for the selected inputs contributes at most one simultaneous visible flat. Conversely any forbidden visible assignment has some minimal cover. This proves the displayed bound without any general semantic minimization. As a coarse corollary the minimum 2ᵏ−1 for inner-product projection implies

    2ᵏ − 1 ≤ m + m² + (2/3)m³ + p⁴.

Indeed the three triple terms count disjoint kinds of triples, bounded together by C(m,3). In particular any sequence of two-helper encodings having m=o(2^{k/3}) must have p=Ω(2^{k/4}). If p=o(2^{k/4}), then m=Ω(2^{k/3}). The balanced-block construction already matches the latter rate with p=0. The optimum for unrestricted p remains open here.

**Specialized cost.** The default for h=r=2 uses the five subset shapes in the list. It generates quartets directly from the p singleton inputs. Its total candidate subsets are

    S = C(ℓ,2) + C(ℓ,3) + p C(ℓ,2) + ℓ C(p,2) + C(p,4).

After Gaussian preprocessing, every candidate has at most 256 offset patterns. Test the union of the at most four four-bit masks and check minimality by omitting each member once. Only a minimal cover requires an intersection of visible systems. The candidate and output bounds include all local directions, feasible-offset pruning, overlap between visible domains and duplicate outputs. The algorithm returns a cover that can contain redundant flats from different certificates. Its optional flag `specialize_square=False` reproduces the general subset procedure for comparison.

Let L be the original number of raw rows and m₀ the original number of inputs before dropping inconsistent flats. Let b=2+n+⌈log₂(m₀+2)⌉+⌈log₂(L+2)⌉. Input normalization and options for the four helper values take O((1+m₀+L)b⁶) bit operations. In detail, each row has n+1 bits, each original flat has at most n pivot rows after RREF, and each of the at most four options per flat requires another RREF on at most 2n rows. For each candidate offset intersection, at most 4n canonical rows enter RREF. The pivot sorting and dictionary lookup bounds used above, with addresses and counters of O(b) bits since S=O((1+m₀)⁴), give O(b⁶) bit operations per intersection. Construct the tuples of lines and singleton inputs once and enumerate combinations from them. Loop setup and pattern unions fit the same per-candidate bound. Thus total bit time is **O((1+m₀+L+S)b⁶)** and memory is O((1+m₀+L+F)b³) bits where F is the displayed projected clause bound. This states a cost for the complete enumeration, even when most intersections are empty.

**Exhaustive shape check and measured counts.** On the four-point square the ten nonempty proper flats consist of six lines and four points. Enumerating all 1,024 of their subfamilies by ordinary set union and single-deletion tests gives exactly 26 inclusion-minimal covers. There are 3 of shape (2 lines,0 points), 4 of shape (3,0), 12 of shape (2,1), 6 of shape (1,2) and 1 of shape (0,4). The optional whole square adds its singleton-family cover.

Running `python rank_certificates.py` also compares the two projectors on fixed examples with two visible offset bits and a third visible bit controlling the common activation domain. Every visible assignment is checked against existential enumeration. Both algorithms retain every consistent output witness separately, so their output counts can exceed the minimum.

| Lines | Singleton inputs | Generic subsets → specialized | Quartets | Offset patterns tested | Emitted flats |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 6 | 4 | 375 → 132 | 210 → 1 | 14,764 → 2,588 | 750 → 90 |
| 1 | 5 | 50 → 15 | 15 → 5 | 3,720 → 1,600 | 13 → 5 |
| 0 | 4 | 11 → 1 | 1 → 1 | 608 → 256 | 1 → 1 |
