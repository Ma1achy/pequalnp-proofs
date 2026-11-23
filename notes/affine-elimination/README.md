# Exact elimination of Boolean variables from affine clauses

Independent research notes on a contributor fork. The Lean files and executable checks below can be replayed locally. Upstream accepts proofs of statements assigned by its desk. [Upstream contribution rules](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/CONTRIBUTING.md)

**Outcome, 23 November 2026.** A sparse conjunction of binary clauses and parity equations has a projection requiring exactly $2^k-1$ affine clauses. Allow one existential helper bit and the minimum becomes $\Theta(2^{k/2})$. Both sizes are superpolynomial in the original input length for this family. The same inputs have an order that solves SAT with linearly many clauses at each stage. The bounds concern a designated projected predicate. Unrestricted polynomial-time SAT remains open. [Obstruction](obstruction.md) · [Helper bounds](helpers.md)

The second cycle proves the exact five-clause optimum for three inner-product pairs with two helpers and the optimal syndrome rank for directed tour incidence. [Cycle-two results and reproduction](cycle2/README.md)

## Invariant and operation

An affine clause fails on one affine flat, the simultaneous zero set of its literals. The conjunction accepts a point iff it avoids all stored flats. To eliminate $z$, carry every $z$-independent flat. Inside each other flat solve one row for $z=f_i(y)$ and XOR it into the other rows to obtain its domain $D_i(y)$. Emit the forbidden flats
$$
D_i\cap D_j\cap\{f_i(y)+f_j(y)=1\},\quad i<j.
$$
Outside the carried flats, precisely these points forbid both possible values of $z$. Consequently $R_i(y)\iff\exists x_{\rm eliminated}\,F(x_{\rm eliminated},y)$ at every step. In the exercise this gives $a\lor c\lor\neg(b\oplus d)$. At the last step an empty cover means SAT and a cover of the unique zero-dimensional point means UNSAT. [Lean proof](Projection.lean) · [Solver and bit costs](experiments.md)

The gate-list front end encodes arbitrary formulas over AND, OR, NOT and constants. Each input has unique consistent gate values before the output is asserted. The dense initial encoding costs $O((N+1)^2)$ bits in the source length $N$. RREF, containment and merging parallel cosets preserve the represented function. Three concurrent lines covering a plane give a satisfiable example where those operations stop at three flats although one suffices. [Formula front end](formula_sat.py) · [Counterexample](order.md)

## An unavoidable cut and an avoidable overhead

For each product impose $(x_i\lor\neg t_i)$, $(\neg x_i\lor\neg u_i)$ and $u_i=t_i+y_i$ over $\mathbb F_2$. These force $t_i=x_i y_i$. Adding $\sum_i t_i=0$ gives $3k+1$ constraints in $O(k\log(k+1))$ sparse input bits. Eliminating all $u,t$ leaves even inner product $q=\sum_i x_i y_i=0$. The odd set has $(2^k-1)2^{k-1}$ points. Its largest affine flat has $2^{k-1}$ points, and fixing each nonzero $x=s$ gives the optimal disjoint cover. This numerical optimum is Cohen and Shinkar's Theorem 1.5. Every nonempty forbidden flat has codimension at least $k+1$. [Proof and primary source](obstruction.md) · [Cohen and Shinkar](https://eccc.weizmann.ac.il/report/2014/099/download/)

| $k=6$, all runs through final SAT decision | Original dense bits | Clauses at $x,y$ projection | Dense bits at projection | Peak clauses |
| --- | ---: | ---: | ---: | ---: |
| Compact gadget above, auxiliaries first | 850 | 63 | 11,488 | 63 |
| Five-variable gadget, auxiliaries first | 1,632 | 665 | 148,988 | 665 |
| Same five-variable input, $x,y$ first | 1,632 | — | — | 31 |

The compact gadget makes the same eliminator attain the optimum at the expensive cut. Overlapping guards in the five-variable gadget produce exactly $3^k-2^k$ clauses there. A Boolean circuit permitting a parity of products describes the residual in $O(k)$ gates. [Order analysis](order.md) · [Compact-gadget traces](mux-results.json)

## Structural results

- **Supplied variable order.** Let $r$ be the maximum rank of the remaining-variable columns of all coefficient rows from original constraints already touched by elimination. The explicit flat solver takes $2^{O((r+1)^2)}\operatorname{poly}(N+1)$ bit time. A separate table on the values of a basis takes $O(2^r S^5)$ bit operations for $S=1+n+m+L$, where $m$ counts clauses and $L$ their literal occurrences. This covers initialization, every intermediate and the final decision. One 256-coordinate boundary needed four table entries. Another input of 348 bits needed 65,536 entries despite having a one-clause residual. [Theorem and counterexamples](construction.md)
- **Fixed helper budget.** With $h$ helpers and at most one independent helper equation per forbidden flat, the minimum clause count for even inner product is $\Theta_h(2^{k/(h+1)})$. Inconsistency at a visible point has a certificate using at most $h+1$ active equations. Balanced blocks of products give a matching encoding. One helper automatically meets the rank condition. For arbitrary rank, $m^{2^h}\ge2^k-1$. [Proof](helpers.md) · [Lean lower-bound transfer](HelperCover.lean)
- **Block-local clauses.** Partition the products into $B\ge2$ nonempty blocks of sizes $b_i$ and permit each clause to read only one visible block and any helpers. At least $B-1$ helpers are necessary. At exactly that budget the optimal clause count is $\sum_i2^{b_i}$. Attaining both minima forces the witness-to-parity labeling to be affine. For four one-product blocks a prescribed nonlinear labeling raises the minimum from 8 to 12, checked by enumerating 2,451 five-bit flats. [Rigidity theorem](rigidity.md)
- **Two unrestricted helpers.** If $p$ of the $m$ clauses have rank two on the helper columns, then $2^k-1\le m+m^2+\tfrac23m^3+p^4$. The optimal exponent remains $k/3$ when $p=o(2^{k/4})$. The helper square has exactly 26 minimal covers by proper affine flats. A necessary four-member cover consists entirely of singleton fibers. [Proof, census and implementation](rank_certificates.md)

## Verification and project status

Run `python3 reproduce.py` from this folder with Python 3.10+ and Lean 4.36.0. The runner compiles both Lean files and compares all four saved JSON traces with regenerated results. Checks include 1,106 circuit/output cases, 9,492 exhaustive one-step comparisons, 74,403 pointwise checks across rank-table prefixes, and SAT/UNSAT cases for parity, 2-SAT, one-in-three SAT and pigeonhole. The traces preserve seeds, sizes, widths, row bit lengths and operation counts. To decide a JSON circuit, use `python3 formula_sat.py --input circuit.json`. [Replay driver](reproduce.py) · [Experiments](experiments.md)

Lean checked the pairwise invariant, both baseline identities and the general transfer of explicit-cover bounds through existential bits. The numerical, order, rank and rigidity results have written proofs and finite computational checks. The primary-source review identifies the known inner-product bound and earlier XNF, resolution and compilation results. Publication priority for the further deductions is unverified. [Literature record](literature.md)

**Next question.** Can two unrestricted helpers and clauses coupling different visible blocks achieve $o(2^{k/3})$ clauses for even inner product? The general lower exponent is $k/4$. Any improvement would require $\Omega(2^{k/4})$ clauses of helper rank two.
