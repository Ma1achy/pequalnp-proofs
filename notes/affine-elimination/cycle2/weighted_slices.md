# At most eight active singleton graphs force a cubic clause bound on common isotropic slices

Consider the same two-helper encoding of even inner product on V=F₂^{2k}. An input of helper rank two forbids one affine graph on its visible domain. An input of helper rank one forbids a line a·w=b(v) in the helper square. Split that line into two graphs on the same domain by choosing e with a·e=1 and the unique nonzero d in ker a. Their labels are b(v)e and b(v)e+d. Let P=p+2ℓ be the number of graphs after splitting all lines, with p and ℓ the original rank-two and rank-one counts. An active graph contributes one to the visible assignment's **multiplicity**, including graphs with equal labels. Retain helper-free cylinders separately.

First suppose all visible domains depend only on x. For each fixed nonzero x the graphs active throughout its y slice are identical as a list of indices; their labels may depend on every y coordinate and on x. No cylinder can be active, since that would make every y forbidden. For each y with x·y=1 their labels cover the helper square, and for x·y=0 they omit a color. Necessarily the multiplicity t on this slice is at least four.

**Theorem.** At most 3 C(P,2) nonzero values of x have t≤5, and at most 3 C(P,2)+15 C(P,3) have t≤8. Thus a design with maximum multiplicity at most five needs P=Ω(2^{k/2}); maximum multiplicity at most eight requires P=Ω(2^{k/3}). Even without a maximum, a design with P=o(2^{k/3}) must activate at least nine graphs on all but an o(1) fraction of x. These assertions concern the visible domains. There is no block-locality condition on the affine labels.

## Collision moments on a slice

For the four helper colors let n₀,…,n₃ be the number of active labels of each color at y. The number of equal unordered pairs of labels is A=Σ C(nⱼ,2), and the number of equal unordered triples is B=Σ C(nⱼ,3). Covering requires every nⱼ≥1. For 4≤t≤8 the two cases have separating integer scores:

| t | Score | Maximum on covering histograms | Minimum on histograms missing a color |
| ---: | --- | ---: | ---: |
| 4 | A | 0 | 1 |
| 5 | A | 1 | 2 |
| 6 | 4A−B | 11 | 12 |
| 7 | 5A−2B | 22 | 23 |
| 8 | 13A−5B | 80 | 81 |

These are finite inequalities over four-part integer partitions. They can be verified by enumerating n₀ from 0 to t, n₁ from n₀ to t−n₀, n₂ from n₁ to t−n₀−n₁, then keeping n₃=t−n₀−n₁−n₂≥n₂. The script independently uses combinations with replacement. The total numbers of tested sorted histograms in the five rows are 5, 6, 9, 11 and 15.

The two averages of the indicated score under uniform y on x·y=1 and x·y=0 therefore differ. By linearity of expectation some pair or triple equality event has unequal probabilities on the two hyperplanes. For a pair i,j the event fᵢ=fⱼ on this slice is an affine system on y with at most two independent rows. For a triple add fᵢ=fₗ, giving at most four. The coefficient rows of these differences are fixed by the input graph indices and do not depend on x. The constant offsets may vary with x. If x were outside the coefficient row span of this system, there would be a direction in its kernel with x·v=1. Translation by v would swap the two hyperplanes while preserving every equality and hence its probability. Thus x is a nonzero combination of the pair's at most two or the triple's at most four rows. Each pair contributes at most three possible x; each triple contributes at most fifteen, across all fixed slices. A union bound proves the theorem. For t=4,5 only pairs occur.

The moment test reaches a precise limitation at t=9. Among histograms missing a color, mix (0,0,0,9) and (0,3,3,3) with weights 4/27 and 23/27. Among covering histograms mix (1,1,1,6) and (1,1,2,5) equally. Both mixtures have (E A,E B)=(13,15). Hence no real linear combination of the two moments strictly separates all nine-label histograms. These mixtures need not arise from actual affine graphs. They only refute that particular separation argument.

## Visible domains with low aggregate polar rank

Let W be the span of all visible domain symplectic normals, including those of cylinders, and let ρ=rank(B restricted to W) for the nondegenerate polar form of q on V. Let d=k−ρ/2. There is an isotropic direction space U of dimension d inside W^⊥. To see this, write c=dim W. Then W^⊥ has dimension 2k−c and shares the radical W∩W^⊥ of dimension c−ρ with W. Its quotient by that radical is nondegenerate, with 2k−2c+ρ dimensions. Take one vector from each symplectic basis pair there and adjoin the radical. This gives U with dimension (c−ρ)+(2k−2c+ρ)/2=d.

Every input's visible domain is constant on each U-coset. For a coset with base point v, q(v+u)=q(v)+λᵥ(u), where λᵥ=q restricted to U + B(v,·) restricted to U is a linear functional on U because U is isotropic. The affine map v↦λᵥ surjects onto U* by nondegeneracy, has equal-size fibers, and is constant on each U-coset. The fraction with λᵥ=0 is 2^{−d}. On every nonconstant coset no cylinder can be active. Apply the moment argument in U coordinates replacing x by λᵥ. The restrictions of the label-difference slopes to U still depend only on the pair or triple of input graph indices. This yields the unconditional bounds on the fraction of all *visible assignments* with the indicated multiplicities:

    Pr[t≤5] ≤ (1+3 C(P,2))/2ᵈ
    Pr[t≤8] ≤ (1+3 C(P,2)+15 C(P,3))/2ᵈ.

For example, with ρ bounded and P=o(2^{k/3}), at least nine singleton graphs must be active at nearly every visible point. When every domain depends on x only we can take U to be the full y-direction space, giving the first theorem directly. A large ρ can make the bound trivial, and it gives no unrestricted two-helper lower exponent beyond the previously stated counting inequality.

Computing W, its polar rank, and a maximal isotropic U uses Gaussian elimination, the dense Gram matrix, and symplectic pair elimination. One can find a nonzero pairing, clear its pairings with the remaining basis by row additions and repeat at most k times, adjoining the unpaired radical. These computations use polynomial bit time in the dense input size and n=2k+2. For instance O((1+n+L+m)⁶) bit operations comfortably accommodates explicit pivot scanning and dense coefficient updates. The numeric upper bounds follow by these rank computations and integer arithmetic. The necessary normal candidates can also be listed by trying up to 15 combinations of at most four precomputed d-bit slope rows per triple in O((1+P)³(1+n+L+m)⁶) bit operations. The theorem computes a bound on multiplicity probabilities and does not count all low-multiplicity points in an arbitrary encoding.

Run `python3 cycle2/weighted_slices.py`. It checks the complete histogram tables and the nine-label obstruction, 12,288 affine row-span implications for equality events, and uniformity of slice normals in 160 deterministic tests of the polar-space reduction.
