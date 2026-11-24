# A parsimonious reduction from signed exact-one formulas to directed tours

Given an explicit list of $v$ declared Boolean variables and a list of clauses, an assignment satisfies a clause when exactly one of its literal **occurrences** is true. Clauses can have any arity and signs. The construction below gives a loopless simple directed graph whose Hamiltonian cycles are in bijection with satisfying assignments. Cycles are counted up to cyclic rotation, equivalently by listing each one starting at a fixed root. Both maps in the bijection take polynomial time. [Graph builder and verifier](unique_tour_gadget.py)

## Graph construction

Start with two distinct vertices $r,j_0$ and arc $r\to j_0$. In order, give each variable and then each clause one block between the current junction $j$ and a fresh next junction $j'$. Finally add the arc from the last junction back to $r$.

* **Variable block.** For a variable with $g$ occurrences, let $h=\max(1,g)$. Put a bidirected path $u_0,\ldots,u_h$ between the junctions. Add $j\to u_0,j\to u_h,u_0\to j',u_h\to j'$. Forward traversal represents true and reverse traversal false. Assign each occurrence its own consecutive path edge. Designate the one orientation used when that literal is false as the occurrence's **false arc**. For a positive literal this is the reverse orientation, and for a negative literal the forward orientation. A declared variable with no occurrences retains both orientations of its one path edge.
* **Clause block.** Allocate one formal slot $j\to j'$ per occurrence in the clause. An empty clause has no slots. Each slot will be replaced, so even slots with the same endpoints become distinct options in the simple graph.
* **Pair each occurrence's false arc and clause slot.** For false arc $a\to b$ and clause slot $c\to d$, remove both and introduce three fresh vertices $L,M,R$. Add
  $$
    L\leftrightarrow M\leftrightarrow R,\qquad
    a\to L,\quad R\to b,\quad c\to R,\quad L\to d.
  $$
  Each double arrow denotes the two directed arcs. All replacements use separate vertices.

All terminal junctions, variable path vertices and internal switch vertices have distinct labels, subject only to the specified shared junctions. After replacing every slot, there are no loops or repeated ordered arcs. For $c$ clauses, $k$ total literal occurrences, and $u$ declared variables with no occurrences, the output has exactly
$$
       2+2v+c+4k+u\ \text{vertices}
       \quad\text{and}\quad
       2+4v+9k+2u\ \text{arcs}.
$$
The construction has linear combinatorial size and takes polynomial bit time, including if it is serialized as an adjacency matrix.

## The bijection

In any spanning cycle, the predecessor and successor of $M$ must be $L,R$ in one order. Using the same neighbor twice would form a proper two-cycle, with at least $r$ left outside. Thus the entire switch is traversed either as $a,L,M,R,b$ or as $c,R,M,L,d$. Each traversal is unique and realizes exactly one paired option. Contract all these traversals. This gives a cycle through the original junction and variable path vertices, along with the identity of each used slot.

In the contracted cycle, the only entrance to a given variable path is from its preceding junction. A spanning cycle must visit the whole path before exiting to the next junction. It consequently traverses the path in its entirety from one endpoint to the other. This gives one Boolean value per variable, even for a variable with no occurrences. At each clause block exactly one slot is used to pass from its junction to the next. The switch forces a clause slot to be used precisely when its paired false arc is unused, which means exactly when its literal is true. Hence the decoded assignment satisfies every exact-one clause.

Conversely, orient each path according to a satisfying assignment, take the unique true slot of each clause, and follow the junctions from $r$ back to $r$. Exactly one of the paired options is used for each occurrence. Expanding those options in their forced orientations gives one spanning cycle and recovers the original assignment. Distinct values of a free variable give distinct path traversals. With no variables or clauses the graph is a two-vertex cycle and the empty assignment is its unique witness. An empty clause prevents any tour.

The graph therefore preserves the exact count, including zero, one and multiple witnesses. Numbering the root first removes the rotational multiplicity in an unanchored list encoding. The graph is directed, so distinct directed cycles are separate witnesses.

## Published setting and verification

Plesník's planar directed Hamiltonicity reduction also uses exclusive-or connections. Bosboom and coauthors explain why ordinary 3SAT clauses permit several traversals for the same satisfying assignment, and instead give a parsimonious construction for positive 1-in-3SAT on planar 3-regular digraphs of maximum indegree and outdegree two. Their footnote 4 explains how expanding a used variable's exclusive-or connection removes schematic parallel edges. The serial construction here only needs simple directed graphs and uses three fresh vertices per occurrence. The published planar degree restrictions apply to their construction. [Plesník, 1979](https://doi.org/10.1016/0020-0190%2879%2990023-1) · [Bosboom et al., Theorem 3.1 and footnote 4](https://www.jstage.jst.go.jp/article/ipsjjip/28/0/28_987/_pdf#page=6)

Run `python3 unique_tour_gadget.py`. The verifier enumerates graph tours using only adjacency rows. It propagates unique predecessor and successor choices, rejects proper subtours, and branches on the remaining candidate successors. A separate rooted-permutation counter checked that search on all 4,164 loopless directed graphs with two through four vertices. For 815 formulas, direct Boolean truth tables and graph enumeration agreed on every witness: all 500 tours decoded to distinct satisfying assignments, and every satisfying assignment appeared. The formula tests include signed repeated literals, free variables, empty clauses, exhaustive clause multisets with at most two variables and clauses of width at most three (up to two clauses), and 80 seeded instances of width at most four.
