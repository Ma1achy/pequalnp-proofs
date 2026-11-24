# Directed Hamiltonicity with few arcs beyond the number of vertices

For a loopless simple digraph on $n\ge2$ vertices and $e$ arcs, put $k=\max(0,e-n)$. A deterministic algorithm either decides directed Hamiltonicity or returns a loopless simple digraph on at most $k$ vertices and at most $2k$ arcs. In the latter case it gives a bijection between directed Hamiltonian cycles, counting cycles up to rotation. The reduction takes $O(n+e)$ indexed operations on adjacency lists, or polynomial bit time on the explicit input. Terminal YES and NO answers may be replaced by fixed two-vertex instances if an ordinary many-one kernel is desired. That convention gives bounds $k+2$ vertices and $2k+2$ arcs including the terminals.

Forced-arc contraction has prior art. Kowalik and Majewski use it for the asymmetric travelling salesman problem. Their Theorem 1.1 gives deterministic polynomial space and $O^*(2^{0.441(e-n)})$ time in the average-outdegree parameter. Our use here is to compare *canonical degree-prefix agreement* with a specific subexponential rate, together with a Lean proof of the tour bijection. [Kowalik and Majewski, Theorem 1.1 and §3.2](https://arxiv.org/pdf/2007.12120) · [Lean proof](SurplusKernel.lean)

## A direct construction from forced paths

Ignore all diagonal bits of a full adjacency matrix before computing $e$. A tour on at least two vertices cannot traverse a self-loop. Reject if any vertex has zero indegree or outdegree, which also resolves every case $e<n$. Mark the unique outgoing arc of every vertex of outdegree one. Write $F$ for this set. Each tour must contain every marked arc. Reject if two marked arcs enter the same vertex, since a tour enters it exactly once.

In $(V,F)$, each vertex now has at most one predecessor and one successor. If there is a marked cycle, return YES if it covers all vertices and NO otherwise. A proper marked cycle cannot be part of a spanning cycle. This handles $k=0$ directly, including digraphs consisting of several disjoint directed cycles.

In the remaining case the marked arcs partition all vertices into directed paths, with an isolated vertex counting as a path. The first vertex of each path has no marked incoming arc, and its last vertex has no marked outgoing arc. Let $p$ be the number of paths. Each terminal vertex has original outdegree at least two. Since all original outdegrees are positive,
$$
p\ \le\ \sum_{v}(\deg^+(v)-1)=e-n=k.
$$
If $p=1$, a tour exists precisely when there is an original arc from the last vertex of the path to the first. Test that arc directly.

For $p\ge2$, give the paths labels in increasing order of their first vertex. For distinct paths $P,Q$, insert an arc $P\to Q$ exactly when the graph contains the arc from the last vertex of $P$ to the first vertex of $Q$. This defines a simple digraph directly from the input. The path labels and arcs do not depend on an order of contractions. An arc returning to the start of the same path would prematurely close a cycle and is omitted. There are no parallel arcs since each ordered pair of paths has a unique pair of endpoints.

A tour in the original graph traverses every marked path uninterrupted and uses only the retained arcs to move between paths. A tour in the reduced graph expands uniquely into a tour by restoring each marked path. These maps are inverse. There are $n-p$ marked arcs and each retained arc is a distinct unmarked arc, so
$$
|V'|=p\le k,\qquad |E'|\le e-(n-p)=k+p\le2k .
$$
Both bounds are attained by this construction on every simple digraph in which all vertices have indegree and outdegree two. It has $e=2n,\ k=n$, and every marked path is a singleton. The size bound counts vertices and arcs. Serializing their endpoint labels in an edge list takes $O((k+1)\log(k+2))$ bits, and writing a dense adjacency matrix takes $O((k+1)^2)$ bits.

Compute indegrees and outdegrees, record marked predecessors and successors, then follow paths from vertices with no marked predecessor. Any unvisited vertices lie on marked cycles. A final pass over the original arcs produces the quotient. With adjacency-list indexing these steps take linear total time. The cases $n=0,1$ lie outside the graph encoding of the degree-prefix theorem. They can be decided according to the chosen language convention before applying the reduction.

## Equivalent iterative reduction

A second algorithm repeatedly chooses a vertex $u$ whose sole successor is $v$, with $n\ge3$. Delete the other incoming arcs of $v$, contract $u\to v$, and delete a loop created by $v\to u$, if present. The reverse arc would close a two-cycle on a proper subset of the vertices. All surviving arcs entering the fused vertex originally entered $u$, and all leaving it originally left $v$. No parallel arcs are introduced. Contracting or restoring the forced ordered pair preserves tours bijectively. The vertex count drops by one, and at least one arc disappears, so $e-n$ does not increase. Test for zero degrees and solve $n=2$ directly before each contraction. If the process stops with an unresolved graph, it has minimum outdegree at least two. Its size then satisfies $n'\le e'-n'\le k$ and $e'\le2k$. The direct construction above obtains the same bounds by processing the original forced paths together.

## What intermediate degree prefixes would imply

Fix a rational $a>1$ and let $w(n)=\lfloor(\log_2 n)^a\rfloor$. Each of the following statements implies the other two. Time bounds are deterministic worst-case bounds, and the input graph is explicit.

1. A language in P matches the canonical $\mathbb F_2$ polynomial of directed Hamiltonicity through degree $n+w(n)$ for every sufficiently large $n$.
2. Directed Hamiltonicity has an algorithm running in $\operatorname{poly}(n)\,2^{O(k^{1/a})}$.
3. Directed Hamiltonicity has an algorithm running in $2^{O(t^{1/a})}$, where $t=n+e$ counts vertices and arcs.

Whole-prefix agreement is equivalent to decision agreement on graphs with at most $n+w(n)$ arcs by the Boolean Möbius transform. [Coefficient equivalence and padding construction](degree-prefix.md)

**From 1 to 2.** On an $n$-vertex graph with $e$ arcs compute the least integer $j\ge0$ with $j^a\ge k$ and set $m=\max(n,2^j)$. For fixed rational $a=p/q$, the comparison is the integer test $j^p\ge k^q$. Split one chosen vertex into a path to increase the vertex count from $n$ to $m$. All incoming arcs end at its first vertex, all outgoing arcs leave its last vertex, and consecutive path vertices have forced forward arcs. This operation preserves tour existence and adds exactly $m-n$ arcs. Hence the new arc count is $m+e-n\le m+k\le m+w(m)$. Encoding the new matrix and running the comparison language takes polynomial time in $m$, which is $\operatorname{poly}(n)\,2^{O(k^{1/a})}$. Finitely many exceptional small sizes can be decided directly. For diagonal-bit encodings write zeros on the diagonal.

**From 2 to 1.** Simulate the surplus algorithm on arbitrary adjacency input, limiting its running time to $n^D$ steps for a sufficiently large fixed $D$ and giving a fixed answer on timeout. On graphs in the ball, $k\le(\log_2 n)^a$, so the bound from statement 2 is polynomial in $n$. Choose $D$ to cover this bound eventually. This defines a polynomial-time comparison language on every well-formed input. Reject malformed inputs. On a full matrix, ignoring the diagonal can only lower $k$. The simulation does not need to compute the width at the boundary.

**Between 2 and 3.** The bound in 2 implies 3 since $k\le t$ and $\operatorname{poly}(n)\le2^{O(t^{1/a})}$. Conversely, the kernel runs in polynomial time and presents the algorithm of 3 with $t'\le3k$, or returns a terminal decision. Thus it gives 2.

For example, a polynomial-time language agreeing through $n+\lfloor(\log_2 n)^2\rfloor$ exists exactly when directed Hamiltonicity admits $2^{O(\sqrt{n+e})}$ time. The equivalence leaves both sides open. It concerns combinatorial size $n+e$. An explicitly listed arc may require $\Theta(\log n)$ bits and arbitrary dense graphs may have $\Theta(n^2)$ arcs. An equivalent restriction of statement 3 is the same time bound on inputs with at most twice as many arcs as vertices. To see sufficiency, pad a kernel with $p$ vertices and $h$ arcs by the same forced path to $m=\max(p,h-p)$ vertices, retaining $h-p+m\le2m$ arcs and $m=O(k)$.

## Nonuniform families

The corresponding promise-circuit formulation indexes circuits by both the vertex count $n$ and a supplied excess budget $b$. Require circuits of size $2^{O(b^{1/a})}\operatorname{poly}(n)$, with constants independent of $n,b$, that answer correctly whenever $e-n\le b$. From a polynomial-size matching family, pad every graph of a fixed pair $(n,b)$ to the same number of vertices. Each bit of its padded adjacency matrix is an original input bit or a constant, so the matched-length circuit can be used on this whole promise. Conversely at each length choose the circuit for the allowed budget, which has polynomial size. A density check can reject all inputs outside the promise if desired. This is an equivalence of circuit families. The [ETH corollary](prefix-eth-sources.md) uses a uniform algorithm.

## Factorization on a fixed graph template

Keep the arcs of a labelled template as independent Boolean inputs and fix all other arcs to zero. If $u$ has only the possible successor $v$, then disabling the bit $x_{uv}$ prevents any tour. When that bit is enabled, each available tour uses it. Contract $u,v$ and use the original bits for all surviving arcs. For templates of at least three vertices the reverse arc can be discarded. Both tour existence and the exact number of tours on each subgraph are therefore $x_{uv}$ times the corresponding function on the contracted subgraph.

Lean proves the full formal polynomial identity for the anchored tour sum over any commutative semiring, by the tour bijection and the factorization of each weight. [Weighted sum and formal polynomial](ForcedTourWeight.lean) For the decision function the canonical multilinear representative satisfies the same identity: the factor $x_{uv}$ and the relabelled polynomial use disjoint variables, so their product is multilinear and has the correct value at every Boolean assignment. Thus a fixed forced path contributes a monomial factor, shifting the ordinary homogeneous layers by its length. This is an identity on subgraphs of a **fixed template**; the unrestricted canonical decision polynomial on all complete-graph inputs is the subject of the earlier [degree-prefix result](degree-prefix.md).

## Finite checks

Run `python3 surplus_kernel.py` in this directory. The verifier compares tour counts for both kernels and expanded tours for the direct quotient with exhaustive rooted permutation enumeration on every loopless graph with one through four vertices and 60 fixed test graphs with five through nine vertices, totaling 4,225 graphs. It also checks single-step expansion bijections for 6,349 individual contractions. On three fixed templates it also checks all 3,104 edge subgraphs and 6,208 integer multilinear coefficients of the decision and count functions. The one-vertex base convention accepts no loopless tour. These computations check the implementations on the specified cases. Lean checks the single-step anchored-list bijection, the surplus and terminal-size inequalities, and the formal polynomial factor. The full kernel algorithm and the time-complexity equivalences are written proofs. [Kernel implementations and tests](surplus_kernel.py)
