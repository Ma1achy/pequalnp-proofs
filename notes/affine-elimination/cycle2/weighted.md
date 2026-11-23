# How much of odd inner product can a two-helper certificate cover?

Let q(x,y)=x·y on V=F₂^{2k}. Assume a conjunction of m affine clauses on V and two helper bits w projects exactly to q=0. Discard empty forbidden flats. Classify each remaining forbidden flat by the rank 0, 1 or 2 of its helper columns. Over its visible affine domain Dᵢ, a rank-zero flat forbids the whole helper square, a rank-one flat forbids a line aᵢ·w=bᵢ(v) of fixed nonzero normal and affine offset, and a rank-two flat forbids the single point fᵢ(v) for an affine pair fᵢ of bits. The *visible domain codimension* dᵢ is the number of independent constraints defining Dᵢ. It can vary independently of helper rank.

## Packing the minimal certificate regions

At a visible v with q(v)=1 the active fibers cover the helper square. Each nonempty region where a specified subfamily covers all four helpers is contained in q=1. Take inclusion-minimal covers at each point. For a candidate subfamily S let J be the intersection of its visible domains. The table describes the minimal-cover locus inside J. Here g bounds its number of disjoint affine pieces and t bounds how many equations must be added to J to specify any one piece.

| Fiber types | Condition for a minimal cover at v | g | t |
| --- | --- | ---: | ---: |
| One whole square | Its domain holds | 1 | 0 |
| Two lines | Same normal and opposite offsets | 1 | 1 |
| Three lines | Three distinct normals, with concurrent equations | 1 | 1 |
| Two lines, point s | Different normals, with s outside each line | 1 | 2 |
| Line of normal a and offset b, points s and s′ | a·s=1+b and s+s′ equals the unique nonzero element of ker a | 1 | 3 |
| Four points f₁,…,f₄ | Σfᵢ=0 and det(f₂+f₁, f₃+f₁)=1 | 3 | 5 |

Any cover containing a line has a subcover with at most three members, by retaining the line and one fiber for each outside point. Two nonparallel lines miss a unique point. Three lines of distinct directions are necessary only when they all meet at one point: inclusion-exclusion gives union size 3 plus the size of the triple intersection. Their concurrency is one affine compatibility equation on the offsets because the third normal is the sum of the first two. For a line and two points the points must be distinct and both outside it, giving exactly the displayed conditions. The comparable direction choices cannot give other minimal covers. With only singleton fibers, four distinct points are necessary.

Four distinct points exhaust the plane, sum to zero, and the differences u=f₂+f₁ and a=f₃+f₁ are independent. Conversely those properties force the four points to be distinct. For each of the three nonzero choices U for u, impose Σfᵢ=0, u=U and det(U,a)=1. These give at most five affine bit equations in total and are disjoint across U. All conditions use affine equations on the visible variables after the fixed helper normal and the finite direction choice are supplied.

Writing c, ℓ, p for the rank-zero, rank-one and rank-two input counts gives this improved uniform count of projected flats:

    c + C(ℓ,2) + C(ℓ,3) + p C(ℓ,2) + ℓ C(p,2) + 3 C(p,4).

Here C(a,b) is the binomial coefficient. The general offset-pattern enumeration remains correct. The table combines its compatible offset patterns into larger explicit flats using only the stated affine equations.

## Weight by domain rank and polar rank

For each nonempty J write c_S=codim J. The normal space W_S consists of the domain row vectors identified via the nondegenerate quadratic polar form B((x,y),(x′,y′))=x·y′+x′·y. In coefficient-mask terms one exchanges the x and y halves before treating a row vector as its symplectic normal. Then the direction of J is W_S^⊥, with orthogonality measured by B. Let ρ_S be the rank of the restriction of B to W_S.

A nonempty piece of the table lies in q=1 and has an extended normal space W′ containing W_S with dim W′≤c_S+t. Since q is constant on the piece, its second difference in any two direction vectors is zero. Thus its direction W′^⊥ is isotropic and W′^⊥⊆W′. The radical of B restricted to W′ equals W′^⊥, yielding

    rank(B on W′) = 2(dim W′−k).

Restriction to W_S can only decrease rank. In addition an affine flat inside q=1 has dimension at most k−1, so dim W′≥k+1. This is the known odd inner-product flat bound, proved separately. The two necessary conditions for a nonempty piece give

    c_S ≥ k − t + max(1, ρ_S/2).

In particular a quartet must have c_S≥k−4 and ρ_S≤2(c_S+5−k). At k=8, four domain normals spanning two complete symplectic pairs have c_S=4 and ρ_S=4; these domains cannot support a bad quartet in an exact encoding.

A subfamily covers at most both g·2^{k−1} points (the odd-flat bound) and |J|=2^{2k−c_S} points. Dividing the union bound for all odd points by 2^{k−1} gives a domain-sensitive version:

    2ᵏ−1 ≤ Σ_S min(g, 2^{k+1−c_S}) · [c_S ≥ k−t+max(1,ρ_S/2)].

Sum over the supported shapes of the table, skipping empty J. The indicator only supplies necessary conditions; other terms can also be empty. Computing the actual RREF of each disjoint piece instead gives its exact volume. Different S may overlap, so the sum is an upper bound for the union.

## Necessary domain dimensions near the quarter exponent

Put μ=(1−2^{−k})/2, the density of odd visible points. Let M=m+C(m,2)+C(m,3), an upper bound for the number of nonquartet affine pieces. Suppose p≥1, choose an integer s≥0, and set T=ceil(log₂ p)+s. At most M/(2ᵏ−1) of the odd points have a nonquartet certificate. Under the uniform law on all visible points, a rank-two domain of codimension greater than T has probability at most 2^{−T−1}. The union of all such domains has probability at most p·2^{−T−1}; conditioning on odd points costs a factor 1/μ. Consequently at least the following fraction of odd points require quartets and belong to no active rank-two domain of codimension greater than T:

    θ = max(0, 1 − M/(2ᵏ−1) − 2^{−s}/(1−2^{−k})).

At each such point, every necessary quartet satisfies all of the following:

* Each of its four individual codimensions lies in [k−4−3T, T]. Indeed c_S≤Σdᵢ, c_S≥k−4 and every dᵢ≤T.
* Its combined domain row space has dependence Σdᵢ−c_S≤4T−k+4. This measures how many dimensions are lost when the four row spaces are summed.
* Its combined symplectic normal space has polar rank at most 2(4T+5−k). Each of the four individual normal spaces has at most the same polar rank.

These conditions concern a positive proportion of inputs as well as a positive proportion of assignments when p is near its counting lower bound. For each of the good odd points, at least four qualifying rank-two domains contain it. Each qualifying domain has density at most 2^{−(k−4−3T)}. By summing visible-point incidences, at least 4μθ·2^{k−4−3T} individual inputs have both the indicated domain codimension and the individual polar rank bound.

For example, if m=o(2^{k/3}) and p≤C·2^{k/4} for a fixed C, take s=3. A positive constant fraction of odd points then require quartets all of whose domain codimensions are k/4+O_C(1), whose four normal spaces lose O_C(1) dimensions in their sum, and whose combined polar rank is O_C(1). There are Ω_C(2^{k/4}) individual rank-two inputs meeting those local requirements. If all rank-two domains instead have codimension strictly below (k−4)/4, no quartet can contribute at all and m=Ω(2^{k/3}).

Another restriction follows if every rank-two domain normal space has polar rank at least R. Monotonicity gives ρ_S≥R for each quartet, so one of its four domains must have codimension at least (k−5+max(1,R/2))/4. For m=o(2^{k/3}), the quartet-covered points of the full cube have density bounded below by a positive constant. Summing just the measures of these high-codimension domains gives p=Ω(2^{(k−5+max(1,R/2))/4}). This restriction has content when R grows, although the elementary bound dᵢ≥R may be stronger for some parameter choices.

## Tight local configuration

For k≥4 take visible bits x₁,…,xₖ,y₁,…,yₖ. Intersect four domains imposing x₃=⋯=x_{k−2}=0 in total, distributing those k−4 equations arbitrarily among the four domains. The common codimension is k−4; the symplectic normals are isotropic. Define u=(x₁,x₂), a=(y₂,y₁), and r=(x_{k−1},xₖ). Give the four rank-two inputs singleton labels 0, u, a, u+a+r on their respective domains. A cover requires all four domains, r=0, and det(u,a)=1. On that region q=x₁y₁+x₂y₂=1. Each of the three nonzero values of u gives a flat of size 2^{k−1}. The full event covers exactly 3·2^{k−1} odd points. It simultaneously attains the coarse per-quartet volume and the lower bound c_S=k−4. This example can be extended to an exact encoding by adding a visible singleton forbidden flat for every other odd point. That extension demonstrates local sharpness without supplying a small whole-instance encoding.

## Cost and reproduction

The counts and rank filters can be calculated from the specified input, with no search for optimal covers. For h=2 solve the helper columns on each nonempty input by elimination and retain the visible domain, fixed line normal and affine offset or pair of affine offsets. Enumerate the S shapes from the table exactly as in the square specialization. Each candidate has at most 4n domain rows and at most five additional affine rows per piece. RREF of the combined domain gives c_S and a basis of W_S after the half-swap. Construct the Gram matrix B(eᵢ,eⱼ) on at most n basis vectors, then compute its rank with Gaussian elimination. These operations and the actual generation of up to three reduced pieces fit O(b⁶) bit operations per candidate, with b=2+n+ceil(log₂(m₀+2))+ceil(log₂(L+2)), L the original number of dense input rows and m₀ the original number of inputs. Summing signed counts of point volumes uses integers of O(k+log(m₀+2)) bits since there are O((1+m₀)⁴) candidates. Preprocessing costs O((1+m₀+L)b⁶). The total bit time is O((1+m₀+L+S)b⁶), where here S counts candidate subsets of the six shapes before skip tests on line directions, including the individual cylinders. One can stream the weighted bound with O((1+m₀+L)b³) bits including input and guard storage. Materializing all F output pieces adds O(Fb³) bits. These are upper bounds for checking the certificate profile of a supplied exact encoding; verifying equivalence of an arbitrary input to inner product is a separate task.

Run `python3 cycle2/weighted_checks.py` from the research directory. The script exhausts 748 ordered helper-fiber configurations for the five nontrivial shapes, checks 642 odd-flat/normal-subspace combinations in four visible dimensions, and enumerates every visible assignment for the tight example at k=4,…,8. It checks 24, 48, 96, 192 and 384 covered odd points respectively, all split into three equally sized pieces.

The executable filter is `cycle2/weighted_profile.py`. Its `capacity(k, raw)` takes dense affine clauses with the two helpers last and returns point-capacity and rejection counts. A capacity below (2ᵏ−1)2^{k−1} disproves exactness. Run `python3 cycle2/weighted_profile.py` for the fixed checks. On the balanced two-helper encodings at k=3,4,5 the loose point budgets 44,192,720 fall to 32,128,512, respectively, compared with the true odd counts 28,120,496. In the k=8 tight quartet the filter retains all 384 possible points. Replacing its isotropic normals by two complete symplectic pairs leaves the coarse budget at 384 and makes the rank-weighted budget zero.
