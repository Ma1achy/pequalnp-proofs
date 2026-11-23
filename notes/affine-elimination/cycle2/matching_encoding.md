# A permutation-matrix encoding with affine boundary rank \(m+2\)

Let \(m\ge1\). A visible \(m\times m\) Boolean matrix \(x\) represents a selected subset of the edges of \(K_{m,m}\). The target predicate is that these edges form a perfect matching. For every \(m\ge3\) the encoding below has **exactly \(m+2\)** as its maximum touched-row suffix rank in the specified order. It has \(2m^2\) clauses and a unique helper extension for every accepted matrix. Together with the separate lower bound \(m-O(\log m)\) for this relation's syndrome width, this gives leading coefficient one as \(m\) grows. The representation permits a selected permutation with several cycles.

## Equations, order and projection

At row \(i\) take constants \(s_{i0}=0,\ s_{im}=1\) and internal flags \(s_{i1},\ldots,s_{i,m-1}\). For \(1\le j\le m\) require
\[
  s_{ij}=s_{i,j-1}+x_{ij}\quad\text{over }\mathbb F_2.
\]
For \(2\le j\le m\) also require \(\neg s_{i,j-1}\lor\neg x_{ij}\). At the first column this exclusion already holds. Finally include the \(m\) unit affine equalities \(\sum_{i=1}^m x_{ij}=1\) over \(\mathbb F_2\), one per column.

In any row, the first selected edge turns its flag from 0 to 1. Afterward a flag of 1 precludes another selected edge, and the recurrence retains 1. Ending at 1 therefore requires exactly one edge in every row. The matrix has exactly \(m\) selected edges in total. Since every column has positive odd cardinality, each has exactly one. Conversely a permutation matrix satisfies all these conditions by setting its flags to cumulative row parities. The interior flags are determined by the matrix, so every accepted visible matrix has one extension. This is pointwise equivalence under existential projection of the flags.

The order is row-major, with interleaving within each row
\[
x_{i1},s_{i1},x_{i2},s_{i2},\ldots,x_{i,m-1},s_{i,m-1},x_{im}.
\]
For a prefix \(E\) the boundary space is the span of suffix coefficient rows of original clauses touched by \(E\). A touched column contributes at most its one restricted parity row, hence at most \(m\) dimensions in total. Completed rows contribute zero local rows, and local factors from subsequent rows are untouched. In the current row after a flag \(s_{ij}\), the next transition and collision can expose only \(x_{i,j+1}\) and \(s_{i,j+1}\) on the suffix. After an edge \(x_{ij}\), only \(s_{ij}\) can survive in touched local rows. At a row boundary the local support is empty. Therefore all local rows together contribute at most two dimensions. The same argument covers the folded endpoint constants.

For \(m\ge3\), take the prefix ending at \(s_{2,1}\). Every column is touched in row 1. Its suffix row contains its own distinct uneliminated coordinate \(x_{3j}\), while none of the local rows uses row 3. In row 2 the step for \(j=2\) gives the nonzero restricted row \(x_{2,2}+s_{2,2}\), and its collision factor gives the row \(x_{2,2}\). These two are independent. Thus the rank of this cut is \(m+2\). At \(m=1\) the peak is zero. At \(m=2\) the orders have six positions; the two column forms and one shrinking local boundary yield peak two by direct row reduction in the companion program.

## Sizes, evaluation and verification

There are \(m^2\) visible edges and \(m(m-1)\) free flags, so \(n=2m^2-m\). Each affine equality is a single-row forbidden flat, and each binary clause is a two-row flat. There are \(m^2\) row XOR constraints, \(m(m-1)\) exclusions and \(m\) column parities. This gives exactly \(2m^2\) raw clauses, \(3m^2-m\) raw rows and \(6m^2-4m\) variable occurrences including long parities. Width in the sense of literals per affine clause is at most two; the support of a single affine literal can have \(m\) entries. All coefficients are bits. At \(m=1\) the row and column give identical raw constraints, which the count includes.

The sparse input length with explicit signed variable indices is \(O(m^2\log(m+1))\) bits. The shared dense row codec uses \(O(m^4)\) bits. A sequential builder can emit all equations by scanning the \(n\) variable positions for each of \(O(m^2)\) rows, with \(O(\log(m+1))\)-bit counters, in \(O((m+1)^5)\) bit operations. The generic syndrome decision procedure takes \(O(2^{m+2}(m+1)^{10})\) bit operations by substitution into its conservative \(O(2^rS^5)\) theorem. The width result concerns the general algorithm under this representation and order. Ordinary bipartite matching has polynomial-time algorithms.

Run the following command from the research directory.

~~~sh
python3 cycle2/matching_encoding.py
~~~

The test constructs the actual dense input and asks the existing syndrome implementation for its basis at **every** prefix. A separate scope scan checks the two-coordinate local assertion and the number of touched, nonzero column rows. For \(m\le3\) the model oracle enumerates permutations, lifts them to row flags, and checks all joint assignments and every suffix of every prefix. For \(m=4\), all 65,536 visible matrices are tested with their uniquely recurrence-determined interior row flags. For larger sizes the test checks widths and representation sizes.

| \(m\) | Variables | Raw clauses | Dense input bits | Peak rank | Full assignments checked | Prefix suffix-points checked |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 2 | 16 | 0 | 2 | 3 |
| 2 | 6 | 8 | 106 | 2 | 64 | 127 |
| 3 | 15 | 18 | 456 | 5 | 32,768 | 65,535 |
| 4 | 28 | 32 | 1,392 | 6 | — | — |
| 5 | 45 | 50 | 3,392 | 7 | — | — |
| 6 | 66 | 72 | 7,076 | 8 | — | — |
| 8 | 120 | 128 | 22,676 | 10 | — | — |

## The graph-availability predicate

If each visible bit \(a_{ij}\) describes an available edge, use the same constraints on **existential** edge selectors \(x_{ij}\) and row flags, together with \(x_{ij}\Rightarrow a_{ij}\) for all cells. Projecting both selectors and flags accepts exactly graphs containing a perfect matching. The flag extension is unique for each selected permutation, so a graph can have several extensions. This version uses \(3m^2-m\) variables, \(3m^2\) raw constraints and \(5m^2-m\) raw flat rows.

Place each \(a_{ij}\) immediately before its \(x_{ij}\) in the given order. The implication is untouched before \(a_{ij}\), contributes only the single coordinate \(x_{ij}\) immediately afterward, and has no suffix coordinates once \(x_{ij}\) is processed. At that middle cut any touched row transition or collision already has its support inside \(\{x_{ij},s_{ij}\}\). Thus the same upper bound \(m+2\) holds, and the previous row-2 cut certifies equality for \(m\ge3\). To query one fixed graph one may add unary constraints on \(a_{ij}\); each has zero suffix row as soon as it is touched.

The verifier runs the general solver for every graph at \(m=1,2,3\), totaling 530 availability assignments, and compares against explicit permutation containment. Peak ranks for \(m=1,\dots,5\) are \(1,2,5,6,7\), with dense encoding lengths \(29,248,1149,3586,8771\) bits. [Cut lower bound](assignment_lower.md)
