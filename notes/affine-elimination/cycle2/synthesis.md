# Finite helper budgets for even inner product

Let q(x,y)=x·y on 2k visible bits. Each clause excludes a single affine flat of the visible and helper bits. The relation must project pointwise to q=0. Empty clauses and unused helper bits are allowed.

| Product pairs k | No helpers | One helper | Two helpers |
| ---: | ---: | ---: | ---: |
| 2 | 3 | **3** | **3** |
| 3 | 7 | **6** | **5** |

The two-helper five-clause optimum is attained by the subsequent four-point-plus-line construction. [Explicit witness and proof](five_points.md)

The zero-helper column is the Cohen–Shinkar bound. The optimal one-helper six-clause construction splits the three products into blocks of sizes one and two and equates each block parity to the same helper bit. For each left input to a block, one affine clause prohibits the mismatching parity. This uses two clauses on the first block and four on the second. A two-helper encoding may ignore its second helper. For k=2 the unassisted three-clause construction suffices. The synthesis trace preserves the six-clause block construction and bounded solver outcomes. The five-clause witness, its packed rows, both helper orders and the counts of surviving witnesses are in [the separate replay trace](mixed_line.json).

## One helper and three product pairs require six clauses

There are 28 odd visible points and every affine flat contained in the odd set has at most four points. A proper visible affine hyperplane contains at most 16 odd points; an affine flat of dimension at most four contains at most 10. To see the latter two bounds, the Walsh sum of q at mask (a,b) is 8 times (−1) to the power a·b, by first summing over y. Over a coset defined by d independent equations, the signed bias is the average of these Walsh coefficients over the 2ᵈ corresponding masks, with signs supplied by the coset. The term for the zero mask is +8. For d=1 the bias is ≥0, giving at most 16 odd points. For d=2 the bias is ≥−4, giving at most 10. Lower-dimensional flats lie inside some four-flat.

An input flat is a visible cylinder or forbids the helper value fᵢ(v) on a visible affine domain Dᵢ. Call the latter an active graph when v∈Dᵢ. Its value fᵢ is affine on that domain and can be extended affinely to all visible coordinates. Suppose five clauses suffice. A graph with full visible domain fixes the only surviving helper value everywhere. Substituting it leaves at most four visible affine clauses, which cannot cover 28 odd points. Discard this possibility. The other graph pairs give affine conflicts Dᵢ∩Dⱼ∩{fᵢ+fⱼ=1}. Every conflict is contained in the odd set and has at most four points.

With c cylinders and 5−c graphs, at most c+binom(5−c,2) projected flats can occur. For c≥2 this is smaller than the required seven. For c=1 it is exactly seven. All seven must then contain four odd points and be mutually disjoint. Each of the four graph domains contains the twelve distinct odd points of its three incident conflicts. Thus all four domains must be hyperplanes. Two hyperplane-domain graphs can never conflict: the conflict is cut out by at most three equations in six coordinates, so if nonempty it would have at least eight points. This excludes c=1.

There remain five graphs. Call hyperplane domains large and all other domains small. Assign each odd point one conflicting pair. This requires 56 graph incidences, with no large–large pair and at most four assigned points per pair. Small domains each supply at most ten and large ones at most sixteen.

* With zero large domains the total capacity is at most 50.
* With at least three large domains at most two small ones supply at most 20 points, but every one of the 28 assigned pairs must use a small domain.
* With two large domains the six large–small pairs can supply at most 24 points. At least four other points therefore use two small domains, giving at least 32 small incidences. The three small domains supply at most 30.
* With one large domain H the total capacity is exactly 56. Every bound is attained. Thus H contains 16 odd points, each of the four small domains S contains ten, and at every odd point exactly two graphs are active. Each of H's four pairs must account for four odd points. For any S, the odd subset of S∩H is exactly the conflict for H,S and is a four-point affine plane. Since S contains ten odd points it has dimension four. Its intersection with H cannot have dimension four, as then all ten odd points of S would be inside H. It follows that S∩H is a three-flat on which q is affine (its four ones form a plane). On the parallel three-flat in S, q is also affine: a translate of a quadratic differs from the quadratic by an affine function. Each restriction has zero, four or eight ones. Their sum cannot be ten.

All five-clause cases fail, and padding an encoding with a neutral clause covers smaller budgets. This proves the exact six. The argument also excludes every two-helper five-clause encoding whose line fibers all use the same normal and whose other clauses are cylinders, because its effective helper space is one bit.

The independent finite check enumerates all 26,387 nonempty affine flats in six dimensions. It finds maximal odd counts 1, 2, 4, 6, 10, 16, 28 by increasing dimension. It also checks every one of the 30 affine hyperplane sections of each of the 336 four-flats having ten odd points. No four-odd-point section among those 10,080 sections has its odd points in an affine plane.

## Four clauses cannot suffice with two helpers

At each visible point, an active forbidden fiber on the four-element helper square is the whole square, a line of one of three directions, or a point. A cylinder alone gives one affine visible conflict. An inclusion-minimal cover involving a line uses two or three inputs. For fixed input identities and line directions its offset relation is affine. Indeed two parallel lines must have opposite offsets; three lines of distinct directions must concur; a singleton with two lines must lie outside both nonparallel lines; and outside a line two singletons must differ by the nonzero line direction. Each condition is a conjunction of affine equations. Four point fibers require all four labels to be different. Split by the three nonzero values of the difference of the first pair. For each difference d, the other pair must also differ by d, and a point from each pair must occupy opposite cosets of span(d). These conditions form one affine system. Intersecting each offset relation with its active domains still gives a single affine flat per piece.

The program enumerates all multisets of m types from {cylinder, three line normals, point}, then all subsets of up to four inputs. For each subset it enumerates its feasible offsets on the helper square, tests coverage and minimality by direct set union, and checks that the offset set is affine or a union of the three quartet pieces. Summing gives the following maxima over type multisets.

| m | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Maximum count of candidate projected flats | 1 | 2 | 3 | 6 | 15 |

Thus for k=2 (minimum three projected flats) two input clauses cannot suffice, and for k=3 (minimum seven projected flats) four cannot suffice. The complete table including all type multiplicities and all profiles passing the count at m=5 is in the JSON. The initial five-clause two-helper candidates that pass this count and the one-helper constraint have no cylinder, at least one point fiber and at least two helper directions overall. Specifically the possible counts (line counts, point count) are ((2,1,1),1), ((2,1,0),2), ((1,1,1),2), ((2,0,0),3), ((1,1,0),3), ((1,0,0),4) and ((0,0,0),5), up to permuting the three normals. Any full-domain line would fix one affine helper coordinate, reducing to at most four clauses with one helper, and so is excluded. The three candidates with a parallel pair and at least one point were subsequently ruled out. The all-point profile was also excluded. A witness exists for the one-line/four-point profile. [Parallel-pair exclusion](mixed_parallel.md) · [All-point exclusion and the witness](five_points.md)

## Further exclusion for five singleton fibers

When all five singleton domains are full, shear the helper coordinates by the first affine label to give it constant value zero. Concatenate the other four labels as an affine map T from six visible bits to eight bits. The odd locus must equal the preimage of the predicate that zero and the four labels together exhaust the helper square. A nonzero vector in the kernel of the linear part of T would be a translation symmetry of q, impossible because the polar form of q is nondegenerate. Thus T must inject onto an affine six-flat in eight dimensions.

The verifier lists each possible direction by a unique reduced row echelon basis, then each coset by a representative zero on its pivot positions. It checks all 43,180 six-flats and finds at most 24 points per flat satisfying the predicate. This excludes the required 28. If all five clauses are singleton fibers and three domains are proper, the number of active incidences on odd inputs is at most 3·16+2·28=104. Covering four helper words at each of 28 odd points needs 112. Thus the full-domain check left exactly one or two proper domains in the all-point profile. The subsequent geometric argument excludes both. [All-point exclusion](five_points.md) Equality with the rainbow predicate is essential for the injectivity argument in the full-domain case.

## Bounded solver synthesis

For an independent finite search, assign a membership bit Mᵢ(p) to every lifted point p and clause i. Each set may be empty. For every nonzero difference d introduce a direction bit. Requiring that any two members separated by d activate this bit, and that an active difference preserves all membership, makes each nonempty set an affine coset. Indeed the difference to a fixed member is then a period for every member, so translating that member to the origin gives a subspace. Conversely every affine set satisfies these clauses with its direction bits.

For odd inputs require a containing excluded flat for every helper choice. For an even input require some helper value outside all excluded flats. The witnesses at zero and the six unit vectors (four units for k=2) may all be fixed to zero: these visible inputs are even, and an affine helper shear interpolates their chosen witness values on this affine basis. Sorting the flat incidence rows breaks clause-label symmetry. A decoded SAT result is checked against every CNF clause, converted back to affine equations and verified on every visible input.

From the research directory run:

~~~sh
python3 cycle2/synthesis.py --probe --output cycle2/synthesis-results.json
python3 cycle2/synthesis_points.py
~~~

The optional probe uses CaDiCaL from the command search path or from `--solver PATH`. Its default 2,000-conflict budget produced a checked three-clause k=2 witness with two helpers. At k=3 the five-clause searches with one and two helpers both returned UNKNOWN. The independent argument above settles the one-helper case. The explicit five-clause construction subsequently settled the two-helper case. [Checked mixed-profile construction](five_points.md) No solver timeout or conflict limit enters a proof. The finite CNF uses O(m·2^{2n}) clauses for n lifted bits and is for small synthesis experiments. The full-domain six-flat enumeration uses 43,180×64 direct membership tests, and its short JSON keeps the complete weight histogram.
