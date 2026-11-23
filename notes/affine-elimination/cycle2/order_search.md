# Choosing an order for affine boundary rank

**The threshold problem for the touched-row boundary rank is NP-complete even for satisfiable positive 2-CNF whose clause graph is planar and has maximum degree three.** This concerns the rank parameter of the table procedure in `syndrome.py` on the supplied representation. On the hard instances every touched conjunction is made true by setting the eliminated variables to one, so the semantic touched table can be constant even when its syntactic index rank is large.

For an explicit family of clauses over affine literals on a variable set V, let S⊆V be the eliminated prefix. For every original clause whose coefficient support meets S, take every coefficient row of that clause and restrict it to the columns V∖S. Define r(S) as the rank over F₂ of these restricted rows. Constant clauses contribute no rows of positive rank. The width of a permutation is the maximum of r(S) over its prefixes, including the empty prefix and all of V. Both end ranks are zero. Signs/RHS bits affect satisfiability, while r(S) uses only coefficients and their grouping into clauses.

## A reduction preserving positive binary clauses

From an undirected simple graph G form one variable xᵥ per vertex and one clause xᵤ∨xᵥ per edge uv. The all-ones assignment satisfies every clause. For a prefix S, an edge inside S contributes two zero restricted rows. A crossing edge contributes the coordinate unit vector of its endpoint outside S. An edge disjoint from S is untouched. Thus the boundary row space has as a basis exactly the units at vertices outside S with a neighbor in S. In particular

```
r(S) = |{v ∉ S : some u ∈ S is adjacent to v}|.
```

Ordinary vertex separation of a layout measures the largest number of vertices inside a prefix which have a neighbor outside it. At each cut the reverse layout has V∖S as a prefix, so its inside count is exactly r(S). Minimizing over layouts, the optimum equals vertex separation, and hence pathwidth with the convention “largest bag size minus one.” Kinnersley establishes the equality; the graph-to-clause translation above identifies this particular affine boundary with it. The standard layout convention and Kinnersley's result are also stated in section 5.3 of the exact-layout paper. [Kinnersley, 1992](https://doi.org/10.1016/0020-0190(92)90234-M) · [Bodlaender et al., section 5.3](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2009/2009-023.pdf)

Monien and Sudborough's primary paper states NP-completeness of Vertex Separation on planar graphs of maximum degree three. Copying one clause per edge is a polynomial bit-time reduction preserving the threshold, with each variable in at most three clauses. For a proposed order, computing Gaussian ranks at its n+1 prefixes takes polynomial bit time in the explicit, renumbered input. This gives membership in NP. The NP-completeness statement lets the width threshold vary with the input. It is compatible with exact algorithms for bounded width, the existing supplied-order theorem and polynomial 2-SAT decision. The reduction and the hard instances' satisfiability require no conjectured lower bound on general SAT. [Monien and Sudborough, 1988, primary abstract](https://doi.org/10.1016/0304-3975(88)90028-X)

## Exact search

Let D(S) be the smallest peak rank on any chain of single-variable additions from ∅ to S. Splitting at the last variable gives

```
D(∅) = 0
D(S) = max(r(S), min{D(S∖{v}) : v ∈ S}).
```

The lower bound follows by truncating any order of S. Conversely append v to a minimizing predecessor order to attain the right side. Numerical subset order already places all predecessors first. A stored last variable allows reconstruction. If a predecessor has value at most r(S), the lower bound r(S) is attained and the scan can stop. This uses the classical subset dynamic programming template for min–max ordering costs. The application here supplies the affine-row rank cost and checks it against the actual syndrome table indices. [Bodlaender, Fomin, Koster, Kratsch and Thilikos, *A Note on Exact Algorithms for Vertex Ordering Problems on Graphs*, Theorem 1](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2009/2009-023.pdf)

The implementation groups coefficient row lists by their original full clause support. Groups with identical support always become touched together, so one Gaussian basis per support suffices. Restriction to residual columns is linear, preserving the span after basis replacement. At a subset the solver masks the compressed rows in touched groups and inserts them into a fresh pivot array. Once rank equals the suffix dimension no further row can increase it. Inconsistent original clauses with nonzero support contribute their listed rows, as in the table procedure. The width being optimized is for the given list of scopes and rows. Semantic minimization or equivalent rewrites can change it.

There is a useful independent-component reduction. Join variables sharing a factor scope and let C run over the resulting connected components, including isolates. At every cut the row spaces belonging to different components occupy disjoint columns. Therefore r(S)=Σ_C r_C(S∩C). Restrict any global order to one component to lower-bound its global peak by that component's optimum. Conversely, concatenate optimal component orders. All finished components have rank zero and all unstarted ones have rank zero. The global optimum is exactly the maximum component optimum. Unused variables can appear anywhere. This proof applies to affine factors of arbitrary arity.

Let L be the number of input row occurrences, m the input clause count, n the number of declared variables after compact renumbering, and B=2+n+m+L. Let s_C denote the size of a component containing a nonconstant scope. On a bit-cost random-access machine a conservative time bound is O((1+Σ_C 2^{s_C})B⁵), with O(B³+2^{max_C s_C} B) working bits, taking the maximum as zero if there are no active scopes. For preprocessing, building components, remapping IDs and reducing a row against at most n pivots are polynomial bit-time scans with O(B)-bit rows and addresses. At a subset at most L restricted rows each perform at most n row reductions, and at most n possible predecessors are read. An address into a subset array needs at most n+O(log B) bits. The displayed polynomial factor includes these costs, loop counters, input scans and tuple/list handling. Only one component's exponential tables are live at a time. The routine returns a permutation over all declared variables, so its output costs at least n indices. Its bounds use an explicit or compactly renumbered variable universe.

A sequential-tape variant retains the same exponential base. Process subsets by cardinality, send each computed value to all immediate supersets as records containing their mask and the chosen last vertex, and merge-sort by target mask. One scan takes the best predecessor for each target, evaluates its rank, and writes its value and parent. At most n·2^{s_C} records of O(B) bits are sent in a component, with O(B) sorting passes per layer. A scan of the stored parents for each of at most n backtracking steps suffices. This variant fits O((1+Σ_C 2^{s_C})B⁶) bit time and O(B³+2^{max_C s_C} B²) bits. Both exact search methods remain exponential in a connected input's variable count.

## Reproduction

Run from the research directory.

~~~sh
python3 cycle2/order_search.py
~~~

The run checks all 1,100 labeled simple graphs on zero through five vertices. It independently enumerates each cut's full linear span, compares its rank with the graph's exterior neighbor count at all 33,867 cuts, and compares the DP optimum with all 124,470 graph/order pairs. It also uses seed 78301 for 140 affine-clause inputs on zero through six variables, including constant, dependent and potentially inconsistent factors. It checks all 2,540 cuts, all 17,480 orders, the reconstructed peak, and every prefix basis rank returned by the decision solver `syndrome_prefixes` on the reconstructed order.

| Graph | Optimal rank | Component subsets evaluated | Predecessors examined | Row XORs |
| --- | ---: | ---: | ---: | ---: |
| 9-vertex path | 1 | 512 | 902 | 368 |
| 9-vertex cycle | 2 | 512 | 991 | 408 |
| 9-vertex star | 1 | 512 | 519 | 762 |
| 9-vertex clique | 8 | 512 | 2,304 | 1,263 |
| 3×3 square grid | 3 | 512 | 1,269 | 626 |
| Three disjoint edges | 1 | 12 | 12 | 0 |

The 9-vertex star exhibits the order effect directly. Eliminating its center first exposes all eight leaves, whereas eliminating leaves before the center has peak one. The clique has first-cut rank eight for every order. In both examples satisfiability is immediate. The known graph results and the subset-DP template predate this investigation. The contribution here is their exact connection to the affine table cost, the general componentwise solver and its verified output.
