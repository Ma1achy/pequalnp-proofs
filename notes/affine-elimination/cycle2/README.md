# Two existential bits and exact elimination

For even inner product on three product pairs, the minimum number of affine clauses is **seven without helpers, six with one helper and five with two**. An affine clause forbids one affine flat. The five-clause encoding uses four affine functions of the visible bits to forbid four individual helper words, plus one conditional line in the two-bit helper space. Direct enumeration checks every visible assignment and every witness. At two helpers, the general lower bound of $\Omega(2^{k/4})$ and upper bound of $O(2^{k/3})$ for $k$ product pairs still leave an asymptotic gap. [Finite proof and witness](five_points.md) · [Lower bounds](synthesis.md) · [Both elimination traces](mixed_line.json)

## Further results

| Setting | Result |
|---|---|
| Geometry of affine clauses | A cover of the odd inner-product set using $M$ flats in $T$ directions satisfies $2M\ge R+R^2/T$ for $R=2^k-1$. For two existential bits, the number and directions of rank-two clauses constrain any improvement over $2^{k/3}$. A second bound weights certificates by their visible domains and polar ranks. [Directions](geometric.md) · [Weighted certificate bounds](weighted.md) · [Multiplicity on isotropic slices](weighted_slices.md) · [Cross-block restrictions](constructions.md) |
| Choosing an elimination order | The decision problem for a bound on the maximum suffix-row rank is NP-complete even for satisfiable positive 2-CNFs with planar subcubic clause graphs. The exact subset search and graph reduction concern the supplied representation. [Proof and implementation](order_search.md) |
| Directed tour incidence | Visible bits indicate the **selected arcs** of a single tour on $m$ labelled vertices. Over all exact affine-clause encodings, helper budgets and orders, the minimum achievable maximum suffix-row rank is $\Theta(m\log m)$. The lower bound uses Zhang's 2026 preprint on the maximum size of a bipartite connectivity rectangle. [Theorem and position encoding](tour_encoding.md) · [Reduction audit](tour_review.md) |
| A generator of all tours | A total controlled-swap circuit generates every tour of the complete loopless digraph. Its defining CNF is satisfiable for every control setting. Reverse topological elimination of all variables takes polynomial bit time in the flat solver, while every full syndrome-table order encounters rank $\Omega(m\log m)$. Requiring the tour to use only arcs available in a supplied host graph adds constraints on the output. [Generator, solver and input sizes](generator_flat.md) |
| Perfect matchings | An $m\times m$ permutation-matrix encoding has rank $m+2$ in its supplied order for $m\ge3$. The separate availability version asks whether a supplied matrix **contains** a matching. A permutation may have multiple cycles. [Encodings and witnesses](matching_encoding.md) · [Rectangle lower bounds](assignment_lower.md) |
| Weighted computation | With one cost per visible selected arc, min-plus weights compute the minimum tour cost and permit repeated witnesses. Summing products over a field instead counts extensions of each tour; with a unique extension its monomial has coefficient one. A free helper can cancel that coefficient in characteristic two. [Semiring hypotheses and circuit bound](sources.md) · [Weighted checks](weighted_syndrome.py) |

The generator and the position encoding both describe tour incidence. Their helper multiplicities and elimination orders differ. The graph input to the usual Hamiltonian-cycle decision problem specifies available arcs and can contain many tours. A formal Hamiltonian-cycle polynomial counts tours with their field coefficients. These distinctions determine which of the preceding bounds apply.

## Reproduction

From this directory, use Python 3.10 or later and Lean 4.36.0 on the command search path. Python uses only the standard library and modules from the parent research directory. The replay compiles the Lean interface-cover lemma, runs every cycle-two Python suite and compares regenerated data with the saved results.

~~~sh
python3 replay.py
~~~

To also replay the archived, 2,000-conflict solver probes, put CaDiCaL 2.1.2 on the command search path and run the following command. A path to a particular Lean executable can be supplied with `--lean`.

~~~sh
python3 replay.py --solver cadical
~~~

The optional synthesis search exhausted its conflict budget for the five-clause instances at $k=3$. The exact optima come from the separate construction and lower-bound proofs. The detailed replay record lists per-command resources and timings, and the accompanying Lean theorem formalizes the interface rectangle-cover argument. [Verification record](review.md) · [Lean statement and proof](InterfaceCover.lean) · [Earlier elimination procedure](../README.md)
