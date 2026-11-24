# Formal lower bounds for layers of subquadratic surplus

Let $L_{N,N+k}$ be the degree-$N+k$ component of the canonical multilinear polynomial for directed Hamiltonian-cycle existence. A gadget with $b$ vertices and $b+s$ allowed arcs can shift the surplus by $s$ when its scaled decision polynomial is a single term $t^{b+s}$. Dense gadgets give much larger shifts per vertex than a bidirected cycle.

**Result.** In each fixed prime characteristic $p$, for every $k\ge3$ one can use $B\le4p^{3/2}\sqrt{k}$ padding vertices. If $n=N-B\ge2$, a variable-and-constant projection of $L_{N,N+k}$ is exactly $\mathrm{hc}_n$. In characteristic two $B\le8\sqrt{k}$ suffices, with only zero and one as constants. In characteristic zero the binary vertex bound also applies, with one further homogeneous-component extraction. In every fixed characteristic and for every sequence $3\le k(N)=o(N^2)$, the pinned theorem therefore gives a superpolynomial **formal arithmetic circuit lower bound** for this single layer, with $n/N\to1$. [Reference lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L34-L46)

## A directed graph with a pure diagonal in characteristic p

Let $a=p^j$ and make $p$ vertex classes, numbered cyclically, of size $a$. Include all directed arcs from each class to its successor, with no other arcs. There are $b=pa$ vertices and $e=pa^2$ arcs. This graph contains a spanning tour. Visit the classes in order, once for each successive index inside a class, and close up. Independent cyclic translations inside each class and rotation of the classes generate a group of order $p a^p$, a power of $p$. It is transitive on the arcs since a rotation aligns the source classes and independent translations align the two endpoints. When $p=2$ this is the bidirected complete bipartite graph.

Write the restricted canonical decision polynomial as $D(z)=\sum_S c_S z_S$. Graph automorphisms preserve the decision function, so uniqueness of the multilinear polynomial makes $c_S$ constant on each orbit of arc subsets. Set every arc variable to the same *formal* indeterminate $t$. The contribution of an orbit is its size times $c_S t^{|S|}$. Every orbit of more than one subset has size divisible by $p$. A singleton orbit must be an invariant arc set, and transitivity on arcs makes its only possibilities the empty set and the full set. The empty graph has decision value zero. The full graph has decision value one, so evaluating at $t=1$ determines the remaining coefficient. Thus

$$
D(t,\ldots,t)=t^{pa^2}
$$

in the ordinary univariate polynomial ring over the field. This is an identity of formal polynomials before any reduction in $t$. The top coefficient of the corresponding integer multilinear polynomial reduces to $1$ modulo $p$. The fixed-subset count uses the standard finite group orbit argument from work on graph-property evasiveness and alternating enumerators. Rivest and Vuillemin give the weightwise orbit divisibility and a Hamiltonicity application. Alternatively, write the diagonal as the sum of $t^{|S|}(1-t)^{e-|S|}$ over all accepted arc sets $S$. The same orbit cancellation leaves the full set alone. Lean proves this diagonal identity for every invariant property that rejects the empty set and accepts the full set. [Rivest and Vuillemin, Sections 3–4](https://people.csail.mit.edu/rivest/pubs/RV76b.pdf#page=6) · [Döring, Marx and Wellnitz, Lemmas 2.3–2.4](https://pure.mpg.de/rest/items/item_3581074_2/component/file_3629435/content#page=4) · [Diagonal identity in reliability theory](https://orbilu.uni.lu/bitstream/10993/1456/1/SignaturesReliabilityFunctions.pdf#page=5) · [Formal diagonal theorem](OrbitPadding.lean)

## Realizing every integer surplus

The preceding gadget costs $pa$ vertices for surplus $s(a)=pa(a-1)$. Start with $k\ge3$. As long as possible, choose the largest $a\in\{p,p^2,\ldots\}$ with $s(a)\le k-3$, and repeat on $k-s(a)$. Spend the final residual $r\ge3$ on a bidirected cycle of length $r$. Assign one counterclockwise edge weight $-1$ and every other gadget edge weight $1$. Its scaled polynomial is $t^{2r}$ in every characteristic. All parts have integral positive size and the prescribed total surplus. [Cycle calculation](layer-projection.md#two-opposite-orientations)

Write $B(k)$ for the resulting number of vertices. In the base case $k\le s(p)+2\le p^3$, so $B(k)=k\le p^{3/2}\sqrt{k}$. In a recursive step, maximality gives $k\le s(pa)+2<p^3a^2$. Since $a\ge2$,
$$
\sqrt{k}-\sqrt{k-s(a)}
=\frac{s(a)}{\sqrt{k}+\sqrt{k-s(a)}}
\ge\frac{pa^2}{4\sqrt{k}}
\ge\frac{a}{4\sqrt p}.
$$
Multiplication by $4p^{3/2}$ pays the $pa$ vertices of this step. Induction gives $B(k)\le4p^{3/2}\sqrt{k}$.

For $p=2$ the same greedy rule has $B(k)=k$ through $k=26$, since a side-two bipartite gadget costs four vertices for four surplus arcs. Beyond that range $a\ge4$, $k<8a^2$, and $\sqrt{k}\le3a\le4(a-1)$. Then $\sqrt{k}-\sqrt{k-s(a)}\ge a/4$, so $8$ times the drop pays the $2a$ vertices. This proves the sharper $B(k)\le8\sqrt{k}$. In particular $3\le k\le N^2/256$ suffices to leave at least $N/2$ base vertices.

## Extracting the tour layer

Take a complete loopless base on $n=N-B(k)$ vertices and splice all chosen gadgets successively. Each splice swaps the destinations of the arcs entering its two roots. The retained variables remain distinct through all splices. On zeroing the unavailable arcs the full decision polynomial is the product of the base polynomial and all gadget decision polynomials. [Bijection and product proof](layer-projection.md#splicing-two-directed-graphs)

Scale each base edge by $t x_e$ and each gadget edge by its chosen scalar times $t$. In positive characteristic the resulting polynomial in $K[x][t]$ is
$$
 F_n(tx)\,t^{B(k)+k}.
$$
The coefficient of $t^{N+k}$ on the left is exactly the claimed variable-and-constant specialization of the *formal* layer $L_{N,N+k}$. On the right it is $L_{n,n}=\mathrm{hc}_n$. Polynomial-valued coefficients preserve the identity even over a finite field. Only the proof uses $t$, so the actual circuit projection adds no gates.

In characteristic zero use the same templates as in characteristic two. The full-edge integer coefficient of each binary bipartite gadget is odd, and that of each bidirected cycle is $-1$. Give all retained gadget arcs weight one. In the specialized $L_{N,N+k}$, a monomial with base degree exactly $n$ must use every one of the $B(k)+k$ retained gadget arcs, since the original monomials are multilinear. Its coefficient is consequently the corresponding coefficient of $\mathrm{hc}_n$ times the product $c$ of the gadget top coefficients. This integer is nonzero in characteristic zero. Extract base degree $n$ and scale by $c^{-1}$. For $S$ original slots, truncating each gate to degrees $0$ through $n$ by ordinary convolution uses at most $1+(n+1)^2S$ slots before the final constant and multiplication. This polynomial overhead preserves the superpolynomial lower bound, with a possible change to its constant in the exponent. [Gate count](balanced.md#a-restricted-transfer-with-a-constructive-gate-bound)

The positive-characteristic projections also preserve the reference approximate-circuit definition. The dense-regime conclusions assert hardness. The VNP upper bound proved in this companion covers logarithmic surplus. The full complexity classification at larger surplus remains open here, as does extending the single constant-and-variable projection of the dense layers to characteristic zero. [Approximate-circuit argument and logarithmic VNP bound](layer-projection.md)

## Verification

Lean proves the fixed-subset and orbit cancellation statements for a general invariant property under a transitive prime-power group action. The group action on each directed template, the choice of sizes and the asymptotic circuit implications are written arguments. The executable checks construct a spanning tour and a transitive arc action in nine examples at characteristics two, three and five, exhaust the decision and Möbius tables of the four smallest examples, and check the binary greedy bound through $k=100{,}000$ and at 192 further size boundaries. [Lean orbit theorems](OrbitPadding.lean) · [Executable checks](check_orbit_padding.py)
