# How many Hamiltonicity layers can an easy language match?

Consider the canonical multilinear polynomial over $\mathbb F_2$ of the decision function “contains a directed Hamiltonian cycle” on labelled $m$-vertex graphs. Call its homogeneous components in degrees $0,\ldots,d$ its **degree prefix**. Two facts give different answers depending on the cutoff.

* For every fixed nonnegative integer $C$, there is a deterministic logspace language matching the entire prefix through $m+C\lfloor\log_2m\rfloor$ at every $m\ge2$.
* For every fixed real $\delta>0$, a polynomial-time language matching the entire prefix through $m+\lfloor m^\delta\rfloor$ at all sufficiently large $m$ exists **if and only if P = NP**. With polynomial-size nonuniform circuits in place of polynomial time, the corresponding condition is $\mathrm{NP}\subseteq\mathrm{P/poly}$.

The polynomial-width condition is an equivalence. We prove neither existence nor nonexistence of such an algorithm. The argument leaves intermediate widths, such as $(\log m)^2$, unresolved.

## The prefix records a sparse-input decision problem

An input is the set $E$ of its present arcs. The coefficient on the squarefree monomial indexed by $S$ is $\bigoplus_{U\subseteq S} f(U)$. Thus agreeing on inputs of size at most $d$ gives equality of every homogeneous component through $d$. Conversely, evaluating a multilinear polynomial on $E$ sums the coefficients of the monomials indexed by subsets of $E$. If $|E|\le d$, coefficients above degree $d$ make zero contribution. Consequently equality of this whole prefix is equivalent to giving the same decision answers on that Hamming ball. This equivalence concerns canonical polynomials. It imposes no condition on the size of circuits for the components themselves. [Lean coefficient equivalence and equality of homogeneous components](BallAgreement.lean) · [Canonical graph polynomial](TourLayer.lean)

Use $m(m-1)$ adjacency bits in a fixed order for loopless digraphs, with a size header if desired. Reject malformed encodings. In the formalization using all $m^2$ bits, self-loops can be ignored for $m\ge2$. A witness graph for the converse can always be loopless. One may also apply the sparse algorithm to the full adjacency matrix, counting only off-diagonal arcs, to obtain agreement on the full matrix Hamming ball.

## A logspace language matching logarithmically many extra layers

For fixed $C$, reject graphs with more than $m+C\lfloor\log_2 m\rfloor$ edges. On the remaining inputs decide Hamiltonicity exactly as follows. Reject if any vertex has outdegree zero. For each vertex $v$ with outdegree $d_v>0$, choose one of its outgoing arcs by index, using $b_v=\lceil\log_2 d_v\rceil$ bits. A vertex with just one possible successor needs zero bits. The total number of bits satisfies
$$
b=\sum_v b_v \le \sum_v(d_v-1)=|E|-m\le C\lfloor\log_2m\rfloor .
$$
The first inequality follows from $d_v\le2^{d_v-1}$. Enumerate all $b$-bit strings, disregarding a successor index outside its row's range. For each valid choice, follow the successor of the current vertex starting from vertex zero. Accept precisely when its first return to zero occurs after $m$ moves. A return after $m$ steps with no earlier return has visited $m$ distinct vertices, since a repeated intermediate vertex would trap the walk on a cycle excluding zero. Conversely a tour supplies an accepting successor choice. No table of visited vertices is needed.

The choice string and its counter use $O(b)$ bits. The vertex, step counter, edge counts and offsets use $O(\log m)$ bits. Recompute each row's block offset and find its indexed neighbor by rescanning the read-only adjacency input. This costs $O(2^b\,\mathrm{poly}(m))$ time and $O(b+\log m)$ working bits, hence deterministic logspace and polynomial time for each fixed $C$. The same calculations work for a supplied excess bound $k$, with $b\le k$ whenever the search runs. [Executable scan-based algorithm and exhaustive tests](sparse_tour.py)

At cutoff $d=m+C\lfloor\log_2m\rfloor<m(m-1)$ the example can first differ in degree **exactly** $d+1$. Extend any directed tour to a graph of $d+1$ edges. That graph is accepted by Hamiltonicity and rejected by the cutoff language. All its proper subsets have matching answers, so the ANF difference has coefficient one there. For $d$ at least the number of arcs the functions agree everywhere. At $C=0$ the comparison language tests whether the input consists exactly of a single tour. Its degree-$m$ identity with the upstream polynomial and its sparse-repeat transfer are separately Lean-checked. [Exact tour identity](EasyTourLayer.lean)

## Matching polynomially many extra layers

Directed Hamiltonian cycle on explicitly encoded digraphs is NP-complete. Fix $\delta>0$ and an integer $h\ge1$ with $h\delta\ge2$. Given a loopless $n$-vertex input with $e$ arcs, set $m=n^h$. Replace a chosen vertex by a directed path on $m-n+1$ vertices. Redirect its old incoming arcs to the first vertex and its old outgoing arcs from the last. If $m=n$, use the original graph. The added path edges are forced in every spanning cycle. Expanding or contracting the path gives the equivalence of tour existence on the two graphs. [Karp, *Reducibility Among Combinatorial Problems*, directed Hamilton circuit](https://doi.org/10.1007/978-1-4684-2001-2_9)

The new graph has $e'=e+(m-n)$ arcs. Thus
$$
e'-m=e-n\ \le\ n^2\ \le\ \lfloor m^\delta\rfloor .
$$
The output adjacency length is $O(n^{2h})$ and it takes polynomial time to write for fixed $h$. Its number of vertices depends only on $n$. A polynomial-time language matching the indicated prefix gives the correct answer on every such graph, which decides unrestricted directed Hamiltonicity in polynomial time. Agreement for all sufficiently large $m$ suffices, since the finitely many small sizes can be hardwired. Conversely, if P = NP, Hamiltonicity itself is an admissible comparison language.

A polynomial-size nonuniform comparison circuit for each padded input length can be composed with the padding map and the polynomial-time many-one reductions from NP. This gives the nonuniform conclusion. In the reverse direction $\mathrm{NP}\subseteq\mathrm{P/poly}$ already supplies an appropriate family for Hamiltonicity itself. These conclusions require matching **all degrees up to the cutoff**, including those below $m$.

## Verification boundary

Lean checks the equivalence between coefficient agreement and pointwise agreement on the ball, and the resulting equalities of formal homogeneous components. The logspace analysis, exact first differing layer, and complexity-class equivalences are mathematical proofs. The tests cover 37,125 graph/budget pairs, 28,511 coefficients inside the proposed prefixes, and 1,201 coefficients in the first differing layers. All 12,495 small graph/padding comparisons preserved both the edge surplus and the exact number of tours. The results leave open whether an unrestricted polynomial-size Boolean family decides Hamiltonicity.
