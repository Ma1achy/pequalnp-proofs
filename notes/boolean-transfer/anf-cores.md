# Counting the nonzero Hamiltonicity ANF coefficients at fixed arc surplus

Let $H_m$ be directed Hamiltonian-cycle existence on a labelled loopless simple digraph with $m\ge2$ vertices. For an arc set $E$, write $\alpha(E)\in\mathbb F_2$ for the coefficient of $\prod_{e\in E}x_e$ in the unique multilinear representative of $H_m$. Equivalently, set all other arc variables to zero and take the full-edge coefficient of that restriction. A degree-$m+k$ monomial corresponds to an $E$ of surplus $k=|E|-m$.

For $k>0$, the arc sets with $\alpha(E)=1$ are exactly the graphs obtained by **replacing vertices of a core by nonempty ordered paths**. A core is a loopless simple digraph $C$ on $p$ vertices with $p+k$ arcs, minimum indegree and outdegree at least two, and $\alpha(C)=1$. All incoming arcs of a core vertex enter the first vertex of its path, and all outgoing arcs leave the last. The partition into paths is unique. In particular,
$$
\lceil 1+\sqrt{1+k}\rceil\le p\le k .
$$
The full-edge coefficient of each candidate core is a finite parity calculation on at most $2k$ arc bits. The minimum-degree condition alone does not decide that parity.

## Why the core is forced

**Every arc is used.** The full-edge coefficient satisfies $\alpha(E)=\bigoplus_{U\subseteq E}H_m(U)$. If an arc $e$ belongs to no spanning tour of $E$, inserting or deleting $e$ in any subgraph leaves Hamiltonicity unchanged. Pairing subgraphs that differ at $e$ gives $\alpha(E)=0$. Consequently a graph of positive surplus with nonzero coefficient has at least one spanning tour and every arc occurs in one. [Boolean coefficient identity](BallAgreement.lean)

**The forced arcs form paths.** Suppose $u\to v$ is the sole outgoing arc of $u$. It occurs in every tour. Any other arc entering $v$ could occur in no tour, so $u\to v$ is also the sole incoming arc of $v$. The reverse implication follows by interchanging incoming and outgoing. In fact these are precisely the arcs common to all tours, since the presence of a different outgoing arc at $u$ supplies a tour using that alternative.

Mark all these arcs. They have indegree and outdegree at most one at every vertex. A marked cycle would have to be a spanning cycle, and then every vertex would have original outdegree one and $k=0$. Thus at positive surplus the marked arcs give a unique partition into directed paths, with an isolated vertex counted as a path of length zero. Every path starts at a vertex of original indegree at least two and ends at a vertex of original outdegree at least two. Every unmarked arc runs from the last vertex of one path to the first vertex of a path. If there were just one path, its last vertex could have at most one outgoing arc, since only its first vertex can receive one and the graph is simple. Thus there are at least two paths. An arc returning to its own path's first vertex would close a proper cycle and could belong to no tour. It follows that all unmarked arcs connect distinct paths.

Contract each path to a vertex. An ordered pair of paths permits only the original arc from its last to the other's first vertex, so the quotient has no parallel arcs. Its indegrees and outdegrees are precisely the original indegrees at path starts and outdegrees at path ends. There are $m-p$ marked arcs for $p$ paths, leaving $p+k$ core arcs. The inequalities $2p\le p+k\le p(p-1)$ give the bounds on $p$. This is the forced-path kernel specialized to arc sets that can have nonzero coefficient. None of the unmarked arcs has to be discarded in this case. [Kernel and proof of the tour bijection](surplus-kernel.md)

**The coefficient survives in both directions.** Consider any core candidate and any such path expansion. Write $Y$ for the internal path arcs and $X$ for the interpath arcs. Under every assignment to $Y,X$, a missing internal path arc precludes a tour. When all internal arcs are present, contracting the paths gives a tour bijection with the selected subgraph of the core. In particular its Boolean decision function is represented exactly by
$$
\left(\prod_{e\in Y}y_e\right)\operatorname{ANF}(H_p|_C)(X).
$$
The displayed polynomial is multilinear since the two variable sets are disjoint. Uniqueness of the multilinear representative equates the full-edge coefficient with $\alpha(C)$. In the expansion, each internal edge is uniquely outgoing at its source and uniquely incoming at its target. At every path start the original core indegree is at least two, and at every path end the original core outdegree is at least two. Thus reconstructing the paths recovers the same partition even when some paths are singletons. [Signed coefficient theorem](CoreCoefficient.lean) · [Formal weighted forced-arc identity](ForcedTourWeight.lean)

Arbitrary subdivision of an optional arc has a different effect. In a bidirected triangle the clockwise and anticlockwise tours have disjoint arc sets and give a full-edge coefficient of one. Subdividing just one clockwise arc forces its use to visit the new vertex. The anticlockwise edges then occur in no tour, and the expanded graph has coefficient zero. Vertex stretching is the operation used here.

## The labelled count

Let $A_k(m)$ be the number of nonzero monomials of degree $m+k$. Let $c_{p,k}$ count eligible cores **on a fixed labelled set of $p$ vertices**, including the full-edge parity condition. For $k>0$,
$$
\boxed{\displaystyle A_k(m)=m!\sum_{p=1}^{\min(k,m)}
       \binom{m-1}{p-1}\frac{c_{p,k}}{p!}.}
$$
To see this, label the paths $1,\ldots,p$. Choose their labelled core and a composition of $m$ into $p$ positive vertex counts, then take a permutation of the $m$ labels and cut it into paths of those sizes in that order. This gives $c_{p,k}\binom{m-1}{p-1}m!$ marked constructions. Each resulting labelled graph has precisely $p!$ representations because its intrinsic path partition permits exactly $p!$ label assignments. This holds even for cores with nontrivial automorphisms.

For $k<0$ one has $A_k(m)=0$, since no set of fewer than $m$ arcs can contain a tour. At $k=0$, the only nonzero monomials are the individual directed tours, giving $A_0(m)=(m-1)!$. If surplus $k$ forces $m+k>m(m-1)$, the formula yields zero. Adding diagonal variables to the encoding leaves all counts unchanged, since every term containing a loop has coefficient zero for $m\ge2$.

For every fixed $k\ge3$, $A_k(m)/m!$ is a polynomial in $m$ of **exact degree $k-1$**, with leading coefficient $c_{k,k}/(k!(k-1)!)$. Indeed the bidirected undirected $k$-cycle is a core at $p=k$. Its only directed Hamiltonian cycles are its two orientations with disjoint arc sets. Their Boolean disjunction has full-edge coefficient one, and there are $(k-1)!/2$ such labelled cores. For positive integral $m<p$, the polynomial $\binom{m-1}{p-1}$ vanishes, so the same polynomial formula applies at those sizes.

## First layers and a parity obstruction

* Surpluses $1$ and $2$ have no eligible $p$, giving $A_1(m)=A_2(m)=0$.
* At $k=3$, the only possible core is the bidirected triangle. Thus $A_3(m)=m!\binom{m-1}{2}/6$.
* At $k=4$, the only possible $p$ is four. The eight core arcs leave two incoming and two outgoing arcs per vertex. Its complement within the complete loopless digraph is a permutation without fixed points. Deleting a pair of disjoint two-cycles gives a bidirected four-cycle with coefficient one. If the deleted arcs form a directed four-cycle, its reverse is the only surviving spanning tour. Each of the four other possible tours uses an arc of the deleted cycle, as seen by rooting their orders at one vertex. The reverse misses four retained arcs, so the coefficient vanishes. Thus $c_{4,4}=3$ and $A_4(m)=m!\binom{m-1}{3}/8$.

Even coverage of every arc by a tour plus the degree conditions can give coefficient zero. In the complete bidirected four-vertex graph there are six directed tours. The Boolean decision function is their disjunction, so its full coefficient is the parity of the subfamilies whose edge union is the entire graph. Every arc belongs to exactly two tours. Two different tours share an arc unless they are opposite orientations, as seen from the six rooted cyclic orders. An edge-covering family may therefore omit no tours, one arbitrary tour, or one opposite pair. There are $1+6+3=10$ such families. Its full coefficient is zero.

## Finite calculation

Core counts can be computed for any fixed $k$ by enumerating labelled simple graphs on $p\le k$ vertices with $p+k$ arcs. For each candidate, the Möbius sum tests at most $2^{2k}$ subgraphs, each decidable by a standard subset and endpoint recurrence for spanning directed paths in $O(2^p p^2)$ indexed operations. This yields finite constants in the formula for every fixed surplus.

The reproducible computation gives the following counts on a fixed labelled vertex set. A blank entry denotes zero. Each row, together with the boxed formula, gives the exact layer size for every number of vertices $m\ge2$.

| Surplus $k$ | $p=3$ | $p=4$ | $p=5$ | $p=6$ |
| --- | ---: | ---: | ---: | ---: |
| 3 | 1 | | | |
| 4 | | 3 | | |
| 5 | | 8 | 96 | |
| 6 | | 12 | 480 | 1,920 |

To compute these constants, adjoin rooted cyclic tours one by one using $f\gets f+x_T+fx_T$ in the squarefree Boolean ring. Multiplication takes edge unions and addition takes symmetric differences. A union that exceeds the degree cutoff can be discarded permanently. Filter the resulting supports by incoming and outgoing degrees. Independently, an endpoint recurrence decides the full truth tables on two through five vertices. A Boolean Möbius transform followed by counting by degree recovers all 44 layers, including zero layers, across 1,052,740 labelled graphs. It gives respectively 1, 3, 53 and 14,519 nonzero monomials. Each layer agrees with the path formula. A third computation independently verifies the diagonal core counts by marking a tour and enumerating its complementary permutation. [Reproduce the three counts](anf_cores.py)
