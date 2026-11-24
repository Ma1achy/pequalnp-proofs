# Repeated arcs in a small circuit for the unique-tour promise

Let $P_n$ be the **formal output** of an arithmetic circuit over $\mathbb F_2$ on the loopless arcs of an $n$-vertex digraph. Assume its size is at most $n^a$ for some fixed $a$ and that on every Boolean graph with at most one directed Hamiltonian cycle it returns the correct existence bit. For a monomial $M$ of $P_n$ with nonzero coefficient, let $\operatorname{rep}(M)$ be the set of arcs with exponent at least two. A matching is a set of directed arcs with all their endpoints distinct.

There is an absolute $\gamma>0$ such that the following holds for all sufficiently large $n$, with the threshold allowed to depend on $a$. Put $r=\lfloor\gamma(\log_2 n)^{1/3}\rfloor$. For every monomial whose repeated arcs contain an $r$-matching, choose **one** such matching by a fixed rule, for example the lexicographically first on the original vertex labels. The family of different matchings so chosen has cardinality at least
$$
                       (n/10)^r=2^{\Omega((\log n)^{4/3})}.
$$
In particular, this many distinct formal monomials contain $r$ pairwise vertex-disjoint repeated arcs. The assertion applies to any such polynomial-size family if one exists. It permits unrestricted behavior on graphs with multiple tours and makes no assumption about which Boolean identities occur in the circuit.

## A sparse template with disjoint variable positions

Take $m=\lfloor\sqrt{n/2}\rfloor$, $q=m(m-1)$, and assume $m\ge3$. For each of $m$ base vertices $v$, form a city with an anchor and two directed $(m-1)$-cycles of ports, one incoming and one outgoing. The anchor can enter any outgoing port, and each incoming port can exit to the anchor. For $v\ne w$, add a single marked arc from the outgoing port for $w$ in city $v$ to the incoming port for $v$ in city $w$. These $q$ marked arcs have no common endpoints. The initial template has $2q+m\le n$ vertices and $5q$ arcs. Stretch one anchor to a forced path, redirecting incoming arcs to its first vertex and outgoing arcs from its last, to use exactly $n$ vertices. The final arc count is
$$
           e_G=5q+n-(2q+m)=n+3q-m\le 5n/2 .
$$

Specialize every unmarked template arc to one, every absent arc to zero, and each marked arc to its own base variable $Y_{vw}$. This is a zero, one and variable substitution. A spanning tour can enter an outgoing ring only once, from its own anchor, so it must visit the whole ring before departing along a mark. An incoming ring can exit only once, to its own anchor, so it also constitutes one contiguous segment. A base tour's chosen outgoing port determines the last port of each outgoing ring, and its chosen incoming port determines the first port of each incoming ring. Thus the directed ring orders give exactly one lift, and contracting the cities is its inverse. This holds for every chosen subset of marks and is unaffected by the forced path. In particular a graph with zero or one base tour gives a graph with that same count on $n$ vertices. [Template construction and checks](weighted_slots.py)

## Repeats after every relabelling

Relabel the fixed template by any permutation $\sigma$ of the $n$ vertices and specialize $P_n$ as above, obtaining $Q_\sigma(Y)$. It still has a circuit of size at most $n^a=m^{O_a(1)}$. It is correct on the zero-versus-one promise for $m$-vertex graphs. Its canonical multilinear representative has degree-$m$ component equal to the formal $\operatorname{hc}_m$. Indeed every arc set of size at most $m$ has at most one tour. On a support of size $m$, all proper subsets have no tour, and the Boolean subset-inversion coefficient is one exactly when the support itself is a tour.

Use the following sparse clipping implication. If *every nonzero formal output monomial of $Q_\sigma$ with support size at most $m$* has at most $b$ distinct repeated variables, then $\operatorname{hc}_m$ has an ordinary arithmetic circuit of size at most
$$
       1+(m+1)^2(n^a+3b+2)(1+2q)^b .
$$
The general clipping identity recovers the degree-$m$ component of the canonical representative of any polynomial under this output promise. The identification with $\operatorname{hc}_m$ here uses only correctness on sets of size at most $m$. Subsets of smaller size matter in the clipping hypothesis as well, since partial clipping can leave powers whose formal degree reaches $m$. [Sparse clipping identity and gate count](sparse-repeats.md) · [Pinned arithmetic lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L33-L46)

The formal lower bound exceeds $m^{c(\log_2m)^{1/3}}$. For $b\le m$, comparing logarithms gives $b\ge(c/2)(\log_2m)^{1/3}-O_a(1)$ when $b$ is the largest repeat count among those output monomials. Since $m=\Theta(\sqrt n)$, choosing, for instance, $\gamma=c/8$ ensures that at least one such monomial has at least $r$ repeats, for every $\sigma$. The threshold is uniform over relabellings because the same size upper bound applies.

A nonzero term of $Q_\sigma$ has at least one contributing formal monomial $M$ of $P_n$. Its support lies entirely in the relabelled template, since every off-template variable is zero. The marked variables are renamed injectively, so exponents on them are unchanged. Consequently for **each** relabelling there exists an original monomial supported on $\sigma G$, meeting at most $m$ marked positions, and repeating at least $r$ of those positions. The marks' distinct endpoints turn these repeats into a matching. The original monomial may involve many unmarked template arcs. Cancellation among specialized terms does not invalidate the existence of a contributor to a surviving term.

## Counting the distinct matching patterns

Let $\mathcal R$ be the family of fixed matchings from all eligible monomials of $P_n$. Each $\sigma G$ contains at least one $R\in\mathcal R$. For the contributing $M$, its prechosen matching need not be among the marks of $\sigma G$, but all its arcs lie in $M$'s support and therefore in $\sigma G$. Its choice was made independently of $\sigma$.

For one fixed directed $r$-matching $R$, the preimages of its ordered endpoints under a uniform random $\sigma$ are uniformly distributed over
$$
                         (n)_{2r}=\frac{n!}{(n-2r)!}
$$
ordered tuples of distinct vertices. Order $R$'s arcs and list each tail before its head. At most $e_G^r$ such tuples put all the arcs in $G$, since each ordered pair must be a directed template arc. Hence
$$
  \Pr[R\subseteq\sigma G]\le \frac{e_G^r}{(n)_{2r}}
   \le \left(\frac{10}{n}\right)^r
$$
for $r\le n/4$, using $e_G\le5n/2$ and $(n)_{2r}\ge(n/2)^{2r}$. The union of these events covers all relabellings. The union bound gives the stated lower bound on $|\mathcal R|$.

This forces repeated arcs to be disjoint, to occur together in a single formal monomial, and to be distributed over many matching patterns. Counting the patterns by itself cannot lower-bound the size of the DAG that generates them. For example, the polynomial $\prod_e(1+X_e+X_e^2)$ has a circuit of $O(n^2)$ gates, is identically one on Boolean inputs, and contains $\prod_{e\in R}X_e^2$ for every matching $R$. Specializing any unmarked arc to zero or one leaves that factor equal to one. Thus even simultaneous proliferation of repeat patterns on all these templates can occur in a succinct product. Promise correctness and the algebra of the rest of the circuit still have to enter any unrestricted gate lower bound.
