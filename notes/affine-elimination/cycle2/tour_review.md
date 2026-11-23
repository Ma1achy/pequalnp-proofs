# Audit of the Hamiltonian-tour cut lower bound

Let $E=\{(i,j):i,j\in[m],\,i\ne j\}$. A visible input selects arcs of the complete loopless directed graph. Its accepted inputs must be exactly the indicator vectors of directed Hamiltonian cycles. Additional Boolean coordinates may be existentially quantified, with any number of witnesses per tour. Consider any affine-clause encoding of this predicate and any order of its visible and helper coordinates. At a cut let $r$ be the rank, on the suffix coordinates, of the coefficient rows of the original factors touching the prefix.

**Result.** At every cut having at least $\delta m^2$ visible arcs on each side, with fixed $\delta>0$, one has $r=\Omega_\delta(m\log m)$ for all sufficiently large $m$. In particular every order has such a cut for a fixed absolute $\delta$. A polynomial-size encoding with a supplied order attains maximum rank $O(m\log m)$. The lower bound uses a theorem in Zhijun Zhang's October 2026 preprint. The reduction and hypotheses below were checked independently. The preprint's proof of its rectangle recurrence was not independently re-proved in this audit.

## The precise external bound

Zhang's $\mathrm{bConn}_{2k}$ on $a,b\in S_k$ is one exactly if $b^{-1}a$ is a single $k$-cycle. Section 4 defines $S_k$ as the maximum $\log_2|X\times Y|$ over **every** rectangle $X\times Y$ contained in the 1-inputs. From Lemma 4.3 the proof of Theorem 4.1 obtains
$$
 S_k\le (8/5)k\log_2k+O(k\log\log k).
$$
There is no exceptional set of sparse rectangles in this bound. A rectangle supported on selected row and column families is also a rectangle of the full matrix, provided all its pairs are positive there. This is crucial: the communication lower bound for the full matrix, without this stronger maximum-size estimate, would not by itself give the desired result under the restriction below. The approximate-rectangle theorem of Section 5 has different hypotheses and is unnecessary. See printed pages 9–10, PDF pages 11–12. [Zhijun Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346v1](https://arxiv.org/pdf/2610.32346v1)

## Rectangles from the syndrome at one cut

Treat prefix variables as one party's and suffix variables as the other's. A basis matrix on the suffix coordinates has rank $r$. For suffix syndrome $t$, fix a representative $z_t$ with that syndrome. Define $P_t$ to consist of prefix assignments that satisfy all touched factors with $z_t$. For any suffix with that same syndrome, *every* touched row takes the same suffix value, so the choice of $z_t$ is immaterial. Define $S_t$ to consist of suffix assignments with syndrome $t$ satisfying all untouched factors. The joint accepted extended relation is $\bigcup_t(P_t\times S_t)$. Projecting away prefix and suffix helpers separately replaces each product with the product of its two projections. The resulting at most $2^r$ products are all exact 1-rectangles on the visible cut. This step permits helper assignments on both sides, arbitrary interleavings, repeated witnesses, and overlapping rectangles after projection.

## Dense bicolored cut

Color visible prefix arcs red and visible suffix arcs blue. In the half-edge cut each color has at least $m^2/3$ arcs for sufficiently large $m$; choose $k=\lfloor m/100\rfloor$. Select $k$ ordered red arcs followed by $k$ ordered blue arcs, requiring all $4k$ endpoints distinct. At each choice the previously used vertices eliminate at most $4k\cdot 2(m-1)\le8km$ arcs of either color, so each step has at least $m^2/4$ choices. Removing within-color order divides by exactly $(k!)^2$. Label the vertex classes as red sources $A$, red targets $B$, blue sources $C$, blue targets $D$, and unused vertices. At most $5^m$ such labelings occur. Some fixed $A,B,C,D$ have at least
$$
 H\ge (m^2/4)^{2k}/((k!)^2 5^m)
       \ge 2^{2k\log_2k-O(m)}
$$
pairs of red and blue matchings. Each red matching is a bijection $f:A\to B$ of all-red arcs, and each blue matching is a bijection $g:C\to D$ of all-blue arcs. With the four endpoint sets fixed, the eligible pairs form the Cartesian product of the eligible red family and the eligible blue family. No assumption that there is a red or blue complete bipartite subgraph is being used.

For a general fixed density $\delta$, taking $k=\lfloor\delta m/16\rfloor$ instead leaves at least $(\delta/2)m^2$ choices per step. The same calculation gives $\log_2 H\ge2k\log_2 k-O_\delta(m)$. The argument hence applies throughout the central portion of the order.

## Connectors, unused vertices, and the restricted permutation matrix

Fix any bijection $\beta:B\to C$ and average over all bijections $\gamma:D\to A$. Given $f,g$, following the selected arcs once around the four classes induces $\gamma g\beta f$ on $A$. It is uniform in $S_k$ as $\gamma$ varies, since $g\beta f$ is bijective. Exactly $(k-1)!$ of $k!$ permutations are single cycles. Thus some fixed $\gamma$ gives at least $H/k$ yes-pairs. Uniformity is needed separately for each pair; no independence across pairs is used.

If there are unused vertices, replace one fixed $\gamma$ arc with a directed path through all unused vertices in any fixed order. Subdividing a fixed arc preserves the cycle count. The graph on all $m$ vertices is now a Hamiltonian directed cycle exactly if $\gamma g\beta f$ is a $k$-cycle. Set arcs outside these variable matchings and fixed connectors to zero. Connectors may have either color; each party sets the bits it owns to the required constants. The four endpoint classes and unused vertices are disjoint, so a connector never overrides a variable matching bit. Varying $f$ affects only prefix-visible bits and varying $g$ affects only suffix-visible bits.

Identify $A,C$ separately with $[k]$. The row permutation $a=\beta f:A\to C$ depends injectively on $f$ alone. The column permutation $b=(\gamma g)^{-1}:A\to C$ depends injectively on $g$ alone. Then $b^{-1}a=\gamma g\beta f$. Taking local preimages of a visible tour rectangle, then relabeling by these injections, gives a genuine 1-rectangle in Zhang's *full* matrix. Nonparticipating permutations may simply be absent from its row or column set. All $H/k$ restricted yes-pairs must therefore be covered by at most $2^r$ rectangles each of at most $2^{S_k}$ entries. Consequently
$$
 r\ \ge\ \log_2(H/k)-S_k\
 \ge (2/5)k\log_2 k-O_\delta(m+k\log\log k)
 =\Omega_\delta(m\log m).
$$
The greedy construction and the pigeonhole and averaging choices are **existence arguments for a lower bound**. The syndrome algorithm receives no task of finding these matchings. The lower bound already holds at the selected cut in its supplied order.

## Upper bound and checks

Give each vertex a position in $\{0,\dots,m-1\}$ using $\lceil\log_2m\rceil$ helper bits. Constrain the positions to be in range and pairwise distinct, and pin vertex 1 to position 0 for a unique extension. For every off-diagonal edge bit $e_{ij}$, require $e_{ij}=1$ exactly when the position of $j$ follows that of $i$ modulo $m$. Encode each local truth table via ordinary clauses excluding its invalid assignments. A check uses at most $1+2\lceil\log_2m\rceil$ bits, giving $O(m^4)$ clauses overall with polynomial sparse or dense bit cost. A permutation of the positions yields one directed tour, and every tour supplies the unique positions by following it from vertex 1. For $m\ge2$ this describes the specified edge predicate.

Use all visible bits first. Any touched factor at a visible cut concerns only its own already-processed edge and position bits. Even if a local truth table is expanded into many rows, none touches a future edge. Consequently all suffix row vectors of touched factors live on the at most $m\lceil\log_2m\rceil$ helper coordinates. Beyond the last visible edge there are only those coordinates left. This yields the matching maximum-rank bound. It is a result on explicit syndrome-table width; it does not bound arbitrary SAT representations or the optimal algorithm for finding a tour.

A finite consistency check took $k=2,3,4$, fixed the connector $\beta$ to reversal, and enumerated every triple $(f,g,\gamma)$. Starting at the first vertex, direct traversal of the four matching layers with two further vertices subdividing one $\gamma$ arc agreed in every case with the single-cycle test on $\gamma g\beta f$. For every fixed $f,g$ the number of successful connectors was exactly $(k-1)!$, over respectively 8, 216 and 13,824 triples. These checks exercise the composition and subdivision steps. The asymptotic counting claim rests on the proof and the cited rectangle theorem.
