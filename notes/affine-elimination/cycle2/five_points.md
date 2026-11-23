# Five affine clauses attain the optimum with two helpers

Let q(x,y)=x₁y₁+x₂y₂+x₃y₃, with arithmetic in F₂. The minimum number of affine clauses projecting to q=0 on all six visible inputs is **five with two helpers**. The corresponding counts with zero and one helper are seven and six. Five full-domain-or-guarded singleton fibers alone cannot attain the two-helper optimum. Four full-domain singleton fibers and one guarded line suffice. The counting lower bound for arbitrary two-helper clauses, and the exact one-helper lower bound, are in the finite-budget proof. [Finite helper budgets](synthesis.md)

## The five clauses

Write helper words as w=(w₀,w₁), put e=(0,1), and define a=(x₁,x₂), b=(y₂,y₁). Then d=det(a,b)=x₁y₁+x₂y₂. The clauses forbid these five affine flats:

1. w=0.
2. w=a.
3. w=b.
4. w=a+b+x₃e.
5. x₃=1 and w₀=y₃+a₀+b₀.

Each forbidden set has two independent equations, so every clause has affine width two. When x₃=0 the line is inactive and the first four labels are 0,a,b,a+b. They exhaust the helper square exactly when a,b are independent, equivalently when d=1. This is q=1 on that slice.

When x₃=1, the four labels are 0,a,b,a+b+e. Exactly one side of the square, meaning a pair of values with the same first coordinate, is fully occupied. Its first coordinate is

```
s = det(a,b) + a₀ + b₀.
```

To prove this, count multiplicities. On each side the total multiplicity is even because the four first coordinates XOR to zero. The parities of the multiplicities of the two points of a side therefore agree. The four second coordinates XOR to one, so precisely one side has odd multiplicity at each of its two points. This side is full. The other side cannot also be full: it would then contain at least two copies of each point and the four labels could not cover both sides this way. The parity of the multiplicity at (1,1) is the sum of the coordinate products of the four labels. Expanding gives d+a₀+b₀. This parity is one exactly when the full side has first coordinate one, proving the expression for s.

The fifth forbidden flat fills the opposite side precisely when y₃+a₀+b₀=1+s. Thus projection rejects exactly when d+y₃=1, also q=1 on this slice. Together the two cases give the desired pointwise equivalence. Every encoding with at most four arbitrary clauses and two helpers projects to a cover of at most six visible flats, whereas q=1 requires seven, proving optimality. The result is finite for three product pairs. It does not supply an asymptotic rate for the unrestricted two-helper problem. [Lower-bound count](synthesis.md)

## Why five singleton fibers cannot achieve the same count

A rank-two helper flat forbids one affine label w=fᵢ(v) on its visible affine domain Dᵢ. Extend the affine maps from their domains to all six coordinates, choosing any extensions. At each odd input v all four helper values must be covered. We use two facts about q. Its polar form B is nondegenerate, so a flat on which q is constant has an isotropic direction of dimension at most three. On a hyperplane H, the restriction of B to its five-dimensional direction K has rank four and radical spanned by the symplectic dual u of the defining linear form. Indeed K=u^⊥ and K^⊥=span(u)⊂K. The derivative q(v+u)+q(v)=q(u)+B(v,u) is constant on each side and flips across the two sides. In particular q on the side with derivative one has no nonzero translation symmetry: every period would have to be in the radical and u fails.

There are 28 odd inputs. A proper affine domain contains at most 16, by the single-hyperplane Walsh bound in the finite-budget note. Three proper domains among five supply at most 3·16+2·28=104 active incidences, short of the 112 needed. Thus there are at most two proper domains. A useful spanning observation is that the odd points in every hyperplane H affinely span H. Otherwise a four-dimensional coset in H would contain only even points, contrary to isotropy.

**Two proper domains.** Every odd point belongs to their union, since only three other labels remain. If any v were outside both, one could pick, for each domain, a defining equation violated at v. The intersection of the two opposite hyperplanes would have dimension at least four, avoid both domains, and contain no odd point. Therefore the two proper domains cover all of space and are complementary hyperplanes. On each hyperplane four fixed labels are active. Their sum vanishes at each odd input where all four labels are distinct, and hence on the entire hyperplane by the spanning observation. Shearing by the first label gives labels 0,a,b,a+b with a,b affine pairs. Rejection is det(a,b)=1, depending on four affine bits on this five-dimensional hyperplane. It has a nonzero translation period. On the side with derivative one along its radical, q has no such period. This rules out two proper domains.

**One proper domain D.** Let c be the affine sum of the four full-domain labels. It vanishes at every odd input outside D. If codim D≥2, those points span the whole visible space. Otherwise they would lie in a hyperplane H. There exists v outside H and D, since D has at most 16 points and H has 32. Intersect H's complementary hyperplane with the complementary hyperplane of one defining equation of D violated at v. This produces an even-only flat of dimension at least four. Consequently c=0 globally. After shearing, the four full labels are 0,a,b,a+b, covering one, two or four points. One extra singleton cannot complete a deficient square. The projected answer would be determined by four affine bits, but the nondegenerate q on six coordinates has no nonzero period.

For the remaining case let D be a hyperplane and H its complement. On H the sum c vanishes because the odd inputs there span it. Shear the first three full-domain labels to 0,a,b. The fourth becomes a+b+c, with c=0 on H. Thus q=det(a,b) there. Since its polar rank is four, the linear part of the four-bit map (a,b) on the five-dimensional direction of H has rank four. Its one-dimensional kernel is the radical, along which q has derivative zero on H. The opposite side D has derivative one along that same vector. The map (a,b) on D is also surjective, with the same kernel. Choose the two points of D with a=b=0. At both points the first three full-domain labels coincide, so all five singletons together cover at most three helper values. However the two points differ by the radical and one has q=1. This contradiction excludes one proper domain.

**No proper domain.** Shear by the first of the five labels. The other four together define an affine map from six visible coordinates to eight label bits. Its linear part must be injective, because its kernel consists of periods of the putative predicate q. Its image is a six-flat. On the eight label bits consider R, the set where the four labels together with fixed zero contain all four colors. Its size is 60 by inclusion–exclusion on missing nonzero colors. Every nonconstant character sum over R has absolute value at most 12. It follows that every codimension-two affine slice contains at most (60+3·12)/4=24 points in R, short of the required 28.

Here are details of the character bound. Write a nonzero frequency as four two-bit frequencies tⱼ. Let l be the number of nonzero tⱼ and r the rank of all four. Put C=3 if their sum is zero and C=−1 otherwise. Inclusion–exclusion over the three missing colors gives the signed sum
```
−(−1)^l 3^(4−l) C + 16(2^(2−r)−1) − 1.
```
For one omitted nonzero color h, a zero-frequency coordinate sums to 3 and a nonzero-frequency coordinate sums to minus its character at h. Summing the resulting product over h≠0 gives the term involving C. With two omitted colors only 0 and one nonzero h remain, giving 16 precisely when h is orthogonal to all four frequencies. With three omissions all labels equal zero. If r=1 all nonzero frequencies coincide, so their sum vanishes exactly for l even and the absolute value is 12. If r=2, l≥2; at l=2 the sum of the two distinct nonzero frequencies is nonzero, and for l=3,4 substitution gives absolute value at most eight. This proves the full-domain bound analytically. Independent enumeration of every six-flat also attains 24. [Six-flat histogram](synthesis-points-results.json)

## Checks

Run `python3 cycle2/five_points.py` from the research directory. It checks the sixteen (a,b) pairs, all 64 visible inputs and 256 lifted assignments, every single deletion, all 255 nonzero rainbow character sums, and both hyperplanes for each of the 63 nonzero normals. The four full point fibers and the line have packed rows (128,256), (130,260), (160,272), (162,284), (9,226), in variable order x₁,x₂,x₃,y₁,y₂,y₃,w₀,w₁. Among the accepted inputs, twelve have one helper witness, twenty-two have two, and two have three. Single deletions create respectively 19, 19, 19, 19 and 16 spurious odd inputs. The generic all-pairs eliminator produces 5, 10 and 15 flats before, between and after projecting the two helpers. Its final cover was checked pointwise and the optimal helper-free cover has seven flats.

The six-clause block construction remains a valid upper bound and enforces different witness behavior. The five-clause construction uses affine constraints spanning multiple product blocks. Publication priority of this finite optimum and encoding is unverified.
