# Hard high-degree layers of the exact-tour language in deterministic logspace

Let $D_m$ be the ordered arcs between distinct vertices on $[m]$, for $m\ge2$. A Boolean graph is accepted precisely when its **entire edge set is one directed Hamiltonian cycle**. Check that every vertex has exactly one outgoing arc, then follow successors from vertex zero for $m$ steps. Accept if the first return is at step $m$. Each successor can be determined by a fresh input scan. This uses $O(\log m)$ working bits and polynomial time on an explicit matrix. Reject malformed input lengths. In an encoding with diagonal bits, also reject any present self-loop.

Write $Q_m$ for the canonical multilinear polynomial of this language over a field $K$, and $J_{m,d}=[Q_m]_d$ for its formal degree-$d$ component. The same formulas hold over the integers. If $\mathcal T_m$ is the set of directed spanning cycles counted up to rotation, then
$$
Q_m(X)=\sum_{T\in\mathcal T_m}X_T\prod_{e\in D_m\setminus T}(1-X_e),
\qquad
J_{m,m}=\sum_{T\in\mathcal T_m} X_T=\operatorname{hc}_m(X).
$$
Here $X_T=\prod_{e\in T}X_e$. The summands are disjoint point indicators on the Boolean cube. In particular, the coefficient of $X_S$ for $|S|=m+k$ is $(-1)^k$ times the number of spanning cycles in $S$. Each graph admits at most one accepted input interpretation, even if a larger selected graph contains several tours. [Lean base identity in characteristic two](EasyTourLayer.lean)

## Realizing any surplus with few new vertices

Choose $n\ge2$ base vertices and replace their root by an ordered path $p_0,\ldots,p_h$, making $N=n+h$ vertices. The $n-1$ old nonroot vertices will be called outside vertices. Keep distinct old variables for all $n(n-1)$ ordered base arcs. Send every old arc into the root to $p_0$, and every old arc out of the root from $p_h$. Denote the $h$ consecutive path arcs by $F$. Each keeps a distinct path variable.

Take any $k$ distinct optional arcs from the following two disjoint sets.

* Each outside vertex can send an arc to each of $p_1,\ldots,p_h$.
* Each $p_j$ can send an arc to each $p_i$ with $0\le i<j\le h$.

This permits every integer $0\le k\le K(n,h)$, where
$$
K(n,h)=h(n-1)+\frac{h(h+1)}2
       =\binom{N}{2}-\binom n2 .
$$
To construct the set, order the two lists lexicographically and take their first $k$ elements. Write $Z$ for their variables. The old, path and optional arc positions are pairwise distinct. Fix the other arcs absent by assigning zero.

**All spanning cycles avoid the optional arcs.** Root a proposed cycle at $p_0$. For each $i<h$, every outgoing arc of $p_i$ besides $p_i\to p_{i+1}$ returns to an already visited vertex in the path prefix. A return to $p_0$ would close the cycle before any of the $n-1\ge1$ outside vertices has been visited. Induction forces a first segment $p_0,\ldots,p_h$. The same argument excludes a backward departure from $p_h$. Once the first outside vertex is reached, an outside-to-path optional arc would visit a noninitial path vertex for a second time. Thus every template cycle is the unique expansion of a base cycle, and every base cycle expands. The argument applies to every selected subgraph, including when a path arc is missing.

Consequently the canonical polynomial after deleting off-template coordinates factors, in the indicated disjoint indeterminates, as
$$
Q_N\big|_{\rm template}
=Q_n(X)\left(\prod_{e\in F}Y_e\right)\prod_{z\in Z}(1-z).
$$
An input accepted by the exact-tour predicate has all path arcs present, all optional arcs absent, and a base graph consisting of a single tour. These conditions also suffice. The product is multilinear and agrees on every Boolean assignment, proving the formal identity integrally. The gadget part has top coefficient $(-1)^k$, which is a unit in every field. At $h=0$ the construction permits $k=0$ and acts as the identity. For fixed $n$ and arbitrary $k\ge0$, increasing $h$ until $K(n,h)\ge k$ always succeeds.

## Recovering the tour polynomial from one source layer

Set off-template entries to zero **before or after** taking $J_{N,N+k}$. Deleting and renaming coordinates preserves homogeneous degree. Then set every $Y_e=1$ and every $z=1$ in this single source layer, obtaining a polynomial $B(X)$ in the base variables. Extract its ordinary homogeneous degree $n$:
$$
[B(X)]_n=(-1)^k\operatorname{hc}_n(X).
$$
Indeed a base term of degree $n$ must accompany all $h+k$ gadget variables to reach $N+k=n+h+k$. Its gadget coefficient is $(-1)^k$. More explicitly, with out-of-range components zero,
$$
B(X)=\sum_{j=0}^k(-1)^{k-j}\binom{k}{j}J_{n,n+j}(X).
$$
In particular evaluating the whole factor $\prod(1-z)$ at one before taking the source layer would lose the information when $k>0$. The displayed reduction uses an ordinary homogeneous-component computation after a variable-and-constant substitution. It gives no general gate-preserving projection.

From a size-$S$ circuit for $J_{N,N+k}$, retain degrees $0,\ldots,n$ at each gate after the substitutions. Add componentwise, multiply by truncated convolution and output degree $n$. The number of binary arithmetic gates is $O((n+1)^2(S+1))$, including the final possible sign change. This uses no divisions or interpolation points and works over finite fields. Comparing with the pinned formal tour-polynomial lower bound gives a source lower bound of $n^{\Omega((\log n)^{1/3})}$ for all sufficiently large $n$ in each fixed characteristic. The polynomial overhead only changes the implicit constant in the exponent. The same operation works coefficientwise over the Laurent-series field in the reference approximate model. Each unwanted negative error coefficient is zero in the source, and the zero-error coefficient is preserved under the ground-field linear operations of specialization and homogeneous extraction. The source and target are formal polynomials throughout. [Reference exact and approximate statements](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L20-L61)

For prescribed $N,k$ with $k\le\binom N2-1$, choose $n$ maximal subject to $2\le n\le N$ and $\binom n2\le\binom N2-k$. Then $h=N-n$ is the least padding meeting the capacity above. When $k=o(N^2)$, $h=O(1+k/N)$ and $n=N-o(N)$. For instance, for large $N$ one can instead take $h=\lceil 2k/(N-1)\rceil$, which is $o(N)$ and has $K(N-h,h)=h(2N-h-1)/2\ge k$. More generally $k\le\alpha N^2$ for fixed $\alpha<1/2$ gives $n\ge(\sqrt{1-2\alpha}-o(1))N$. Thus in all these regimes the source layers require $N^{\Omega((\log N)^{1/3})}$ arithmetic gates for each fixed characteristic despite the language's deterministic logspace decider. A loopless template with the $n(n-1)$ distinct old coordinates, $h$ internal path arcs and $k$ distinct optional coordinates necessarily satisfies $k\le N(N-1)-n(n-1)-h=h(N+n-2)$. This explains the order $k/N$ of the padding cost for this representation.

For the $N^2$-bit matrix convention, setting all diagonals to zero gives exactly the loopless construction over the same field. Alternatively all $N$ diagonal bits are automatically forbidden in every accepted exact tour and may be added to the optional list, raising its capacity by $N$ without changing the proof. On the full loopless ground set, the highest possible individual layer has a single possible monomial, with coefficient $(-1)^{N(N-2)}(N-1)!$. A hardness claim uniform in all surpluses on a *fixed* $N$ would therefore be false. Realizing every $k$ here allows $N$ to grow.

## A polynomial number of Boolean substitutions suffices over every field

There is also a black-box reduction to evaluations of the *single* source layer $J_{N,N+k}$. For each $b=0,\ldots,k$, set exactly the first $b$ optional variables to one, the others to zero, and all forced path variables to one. Denote the resulting polynomial by $B_b(X)$. The elementary symmetric polynomial of degree $q$ on the optional entries takes the integer value $\binom bq$. Consequently
$$
 B_b(X)=\sum_{q=0}^b(-1)^q\binom bq\,J_{n,n+k-q}(X),\qquad
 \boxed{\displaystyle\operatorname{hc}_n(X)
 =\sum_{b=0}^k(-1)^b\binom kb\,B_b(X).}
$$
For the second equality, the coefficient multiplying $J_{n,n+k-q}$ is
$$
 (-1)^q\sum_{b=q}^k(-1)^b\binom kb\binom bq
 =\binom kq\sum_{j=0}^{k-q}(-1)^j\binom{k-q}j .
$$
It vanishes when $q<k$ and equals one when $q=k$. This proves the identity over the integers, including $k=0$, and therefore in any characteristic. It requires $k+1$ ground-field oracle calls and $O(k+1)$ additional arithmetic gates. Each call only renames arc variables and assigns zero or one. The linear combination uses ground-field constants. Thus the reduction works even over a field too small to supply distinct interpolation points. A size-$S$ source circuit gives an $O((k+1)(S+1))$ target circuit by this route. For instance, when $k$ is a positive power of two, only $b=0$ and $b=k$ contribute in characteristic two.

**Membership and completeness.** Each family $J_{N,N+k(N)}$ is in VNP over every field, including widths beyond the graph's capacity, whose layers are zero. For a nonzero layer, guess two Boolean edge masks $S,T$. Require $|S|=N+k(N)$, $T\subseteq S$, and that the graph with exactly the arcs $T$ is a directed spanning cycle. These are polynomial-time Boolean checks. Guess all internal wire values of the deterministic checking circuit and enforce its gates by their constant-degree truth-table indicators. Each valid mask pair has exactly one consistent accepting transcript. Multiply those indicators by $(-1)^{k(N)}\prod_e(1-S_e+S_e X_e)$ and sum over the Boolean guesses. The coefficient of $X_S$ counts each embedded tour $T$ once with the sign prescribed by the point formula. The verifying arithmetic polynomial has polynomial size and formal degree. The chosen surplus may be hardwired at each size, as appropriate to the nonuniform definition of VNP. [VNP definition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L86-L94)

For every fixed $\alpha<1/2$ and nonnegative sequence $k(N)\le\alpha N^2$ eventually, this proves VNP-completeness under polynomial-size oracle reductions over every field. To obtain $\operatorname{hc}_m$, use $N$ a sufficiently large fixed multiple of $m$, so the recovered base has $n\ge m$ vertices. The tour polynomial on $n$ vertices projects onto $\operatorname{hc}_m$ by stretching one base vertex into a forced path, assigning one to its internal arcs and zero to unavailable arcs. The family of tour polynomials is VNP-complete under polynomial projections. This argument classifies polynomials of a deterministic logspace decision language. It gives no Boolean circuit lower bound for that language. [Forced-path weight identity](ForcedTourWeight.lean) · [Hamiltonian-cycle polynomial completeness, Hrubeš](https://users.math.cas.cz/~hrubes/PDFs/Mult.pdf#page=2)


The Lean coefficient identities and the finite graph checks target the projection and its integer signs. The graph construction and complexity conclusions are written proofs. [Lean identities](ExactTourPadding.lean) · [Executable graph checks](exact_tour_padding.py)
