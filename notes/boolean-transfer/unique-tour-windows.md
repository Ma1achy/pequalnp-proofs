# Dense unique-tour restrictions and what accepting parses must contain

Use loopless directed graphs on $n\ge2$ labelled vertices. Root every directed Hamiltonian cycle $T$ at vertex zero, writing its unique order as $v_0=0,v_1,\ldots,v_{n-1}$, with closing arc $v_{n-1}\to0$. Let $B_T$ contain every backward arc $v_j\to v_i$ with $i<j$, except the closing arc already in $T$. Set
$$
 h=|B_T|=\binom n2-1,\qquad U_T=T\cup B_T,\qquad
 I_T=\{E:T\subseteq E\subseteq U_T\}.
$$
The promise covers **all** subgraphs $E\subseteq U_T$, including those missing required arcs. The interval $I_T$ consists of the positive inputs in that template.

## The only possible tour and the exact graph count

Any spanning cycle in $U_T$ must start at zero. After visiting the prefix $v_0,\ldots,v_i$ for $i<n-1$, the only possible step to an unvisited vertex is $v_i\to v_{i+1}$. Every backward alternative revisits a vertex or closes the cycle early. After visiting all $n$ vertices the closing arc is necessary. It follows that
$$
    H(E)=1\quad\Longleftrightarrow\quad T\subseteq E
    \qquad (E\subseteq U_T),
$$
where $H$ is directed Hamiltonicity. Every positive graph in $I_T$ has exactly one spanning cycle. In particular, $I_T$ and $I_{T'}$ are disjoint for distinct cycles $T,T'$. The negative template subgraphs can overlap.

There are $(n-1)!$ rooted orders and $2^h$ choices of backward arcs for each. Their positive union has exactly $(n-1)!\,2^h$ labelled graphs, of which $(n-1)!\binom hs$ have $n+s$ arcs for $0\le s\le h$. Over every field the canonical multilinear polynomial of any predicate correct on this promise restricts to the single monomial $\prod_{e\in T}x_e$ when coordinates outside $U_T$ are set to zero. Both polynomials agree at every Boolean point of the template.

## The covering inequality for signed parses

Write a Boolean circuit over AND, OR and NOT in negation normal form, constructing a wire and its complement in parallel if necessary. Shared wires are allowed. A parse of its positive output chooses one child at each unfolded OR and both children at each unfolded AND. Its leaves impose a conjunction of positive and negative input literals. Discard inconsistent conjunctions. An input satisfying the leaves is accepted, and every accepted input satisfies some parse. Equivalently, the following argument applies directly to any cover by accepting signed certificates. [Boolean parse conventions](guarded-parses.md)

Let $\pi$ be a consistent parse active at some $E\in I_T$. Every arc of $T$ must occur as a **positive** literal in $\pi$. A negative literal for such an arc would already be false at $E$. If the arc were absent from the parse, switching that one input bit to zero would keep every literal true. The new graph would remain a subgraph of $U_T$ and would have no tour. This contradicts promise correctness. Consequently a given parse can be active in at most one of the positive intervals. Activity in a second interval would put two distinct spanning tours in a graph having just one.

For a parse active in $I_T$, let $b_T(\pi)$ be the number of **distinct** optional arc coordinates in $B_T$ specified by either polarity. All other specified coordinates have fixed values throughout the interval. The parse is satisfied at exactly $2^{h-b_T(\pi)}$ of its graphs. If $\mathcal P_T$ is any family of such parses covering $I_T$, the union bound gives
$$
                      \sum_{\pi\in\mathcal P_T}2^{-b_T(\pi)}\ \ge\ 1 .
$$
Separate covers are required for all $(n-1)!$ tours. This gives an exact lower bound of $(n-1)!$ on the number of terms of a DNF correct on the whole promise. The usual DNF with one positive tour term per rooted order achieves the bound, including all negative promised inputs. A shared Boolean DAG can generate many terms in its unfolded parses.

## A polynomial-time predicate agrees on every template subgraph

Start at vertex zero with only zero marked visited. At each of the next $n-1$ steps, inspect the outgoing arcs from the current vertex to unvisited vertices. Reject unless there is exactly one such neighbor. Move there and mark it visited. Finally accept if the last vertex has an arc to zero. Accepting returns an explicit spanning tour, so the test is sound on every graph. It uses $O(n^2)$ adjacency-bit inspections with indexed rows and a visited array. Sequential input scans also give polynomial time.

In fact its **entire accepted set** is $\bigcup_T I_T$. A graph in an interval forces the successive greedy moves and supplies the closing arc. Conversely, if greedy accepts with order $T$, the tour arcs are present and no nonconsecutive forward arc can be present. Such an arc would have supplied a second unvisited neighbor at its source. All other permissible arcs are backward, placing the graph in $I_T$. Thus greedy agrees with Hamiltonicity on every graph in $\bigcup_T\{E:E\subseteq U_T\}$, including the negative graphs there. On the complete digraph for $n\ge3$ it rejects at the first step although spanning tours exist.

For this greedy language a DNF with one signed term per interval also suffices. Its term fixes the tour arcs present and every off-template arc absent. Hence even a language with precisely the disjoint positive intervals and the factorial signed-DNF requirement has uniform polynomial-time algorithms and polynomial-size Boolean circuits. The window and parse properties alone cannot yield a superpolynomial lower bound for unrestricted Boolean gates. Greedy can reject after an arc is added, so this example makes no corresponding claim for monotone circuits.

## Reproduction

Run `python3 unique_tour_windows.py` in this directory. For each $2\le n\le5$, it independently enumerates rooted cycles contained in every ambient graph, checks the unique-tour equivalence on every template subgraph, counts every cardinality layer of the disjoint positive intervals, and compares their union with the greedy response on every graph. For $n\le4$ it enumerates every consistent signed cube over all arc bits, retains those that meet a positive interval and avoid all promised negatives, and verifies positive support, interval exclusivity and exact mass. [Executable checks](unique_tour_windows.py)

| Vertices | Ambient graphs | Template subgraphs, counted per template | Graphs in positive intervals | Signed cubes tested |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 4 | 4 | 1 | 9 |
| 3 | 64 | 64 | 8 | 729 |
| 4 | 4,096 | 3,072 | 192 | 531,441 |
| 5 | 1,048,576 | 393,216 | 12,288 | — |

All 11,701 active promise-valid signed cubes in the tested sizes satisfied the predicted mass exactly. The statements for arbitrary $n$ follow from the arguments above.
