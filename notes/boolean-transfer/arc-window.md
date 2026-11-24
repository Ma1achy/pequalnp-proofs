# A 64-gate lower bound from two-leaf witnesses in L-meta-1494

The posted problem asks about unrestricted monotone circuits with fan-in at most two. The exact minimum is **64 gates** whenever each required incident pair has an accepting parse with just its two distinct variables as leaves. This includes syntactically multilinear monotone circuits of arbitrary depth and allows shared gates. A hypothetical 63-gate circuit must therefore repeat an input in every accepting parse for at least one incident pair. [Posted gap L-meta-1494](https://data.pequalnp.com/data/desk/gaps.json)

Index the 13 points and 13 lines separately by the residues modulo 13. Point $p$ is incident to line $w$ when $p-w$ lies in $D=\{0,1,3,9\}$. The posted soundness promise applies when the selected points contain at most two on each line. It requires any accepted promised input to contain a selected incident pair. Completeness requires acceptance on the two-variable input for each incident pair. In particular, **all** assignments with exactly one point and one line are within the soundness promise.

## Restricted circuit model

An output OR combines the results of product (AND) gates. Each product reads one positive OR of point inputs and one positive OR of line inputs, with singleton ORs represented by input wires. The two sets of summaries may be computed by shared fan-in-two OR circuits, and the top OR circuit may be any fan-in-two DAG. Every product counted below reaches the output. This condition restricts gate dependencies. General monotone circuits can feed products into further products or into new side summaries.

Constant or missing-wire values cause no difficulty in this model. Remove constant-zero terms, propagate constants, and remove unused gates, repeated arguments and unary copies. A live term with one side identically true and the other nonzero violates soundness on either a single point or a single line (or on the empty input). A constant-true top term fails the empty input. Thus all surviving products have nonempty point and line supports. An OR gate whose support is a singleton can be replaced by its input everywhere. These simplifications cannot increase gate count. The output has at least one surviving product by completeness.

## Proof

1. **Each product gives a star.** Let $P_j,L_j$ be its two supports. On the input selecting just $(p,w)$, the product fires for every $(p,w)\in P_j\times L_j$. Soundness makes this rectangle incident everywhere, and completeness makes the union of the rectangles the entire incidence relation. There are 52 incident pairs. The ordered differences of two distinct elements of $D$ are
   $$
   12,10,4,\quad 1,11,5,\quad 3,2,7,\quad 9,8,6.
   $$
   Each nonzero residue occurs once. Two distinct lines therefore have at most one common point, and two distinct points have at most one common line. Hence either $P_j$ or $L_j$ is a singleton. Give the rectangle its singleton vertex as centre and its other support as leaves. For a single edge either endpoint can be chosen. Write $t$ for the number of distinct surviving product gates. The 13 diagonal pairs $(w,w)$ form a matching, and a single star covers at most one of them, so $t\ge13$.

2. **A shared OR with at least two input variables belongs to at most one centre.** For a centre $v$, let $m_v$ be the number of its products and $U_v$ the union of their leaf supports, of size $k_v$. Every gate feeding one of their leaf operands depends only on a subset of the neighbours of $v$, because positive ORs take unions. If the same nontrivial gate fed operands of stars at two distinct centres on the same side, its support would include two common neighbours. Centres on opposite sides have their leaves in disjoint variable sets. After the singleton simplification, the OR gates in the leaf computations for distinct centres are therefore disjoint. Sharing inside one centre remains unrestricted.

3. **Count the gates feeding leaf operands.** Fix $v$ and take the union of the ancestor circuits of its $m_v$ leaf operands. It has $k_v$ distinct input variables and $g_v$ internal OR gates. At most $m_v$ distinct nodes are designated operand outputs. Every other node is a child of an internal gate. The $g_v$ child sets, each of size at most two, thus cover at least $k_v+g_v-m_v$ nodes. The singleton case of the finite sample covering inequality gives $k_v+g_v-m_v\le2g_v$, or $g_v\ge k_v-m_v$. This argument also counts operands that are input wires, duplicated outputs and outputs that feed another operand. Each covered incidence occurs in at least one of the sets of $k_v$ centre–leaf pairs. Thus $\sum_v k_v\ge52$, while $\sum_v m_v=t$. The preceding disjointness gives at least $52-t$ preproduct OR gates. [Finite covering inequality](CoverCost.lean) · [OR-cone count](ArcWindow.lean)

4. **Count the final OR circuit.** Its $t$ distinct input nodes are the product gates. With one designated output the same covering inequality requires at least $t-1$ top OR gates. Counting the preproduct ORs, the products and the top ORs gives at least
   $$
   (52-t)+t+(t-1)=51+t\ge64.
   $$
   This reasoning requires no assumption that the intermediate OR stages are trees.

For the matching construction, take one star for each line. OR its four point neighbours using three gates, then AND the result with the line bit. OR the 13 resulting terms using 12 gates. The total is $13(3+1)+12=64$, and this circuit computes the incidence decision function on every input.

## Why arbitrary depth is allowed in the syntactically multilinear case

A circuit is syntactically multilinear if the sets of input variables feeding the two sides of every AND are disjoint. This condition concerns the variables that can reach an operand. Remove constants and copies by propagation and regard reads of nonexistent wires as false, as in the posted model. These operations only shrink the supports. All remaining gates evaluate to false on the empty assignment. [Upstream definition of syntactic multilinearity](https://github.com/brilliant-hq/pequalnp-proofs/blob/f3e69b796950be3379af6d3c070a5da412b9fdcd/lean/PEqualNP/Defs/SyntacticMultilinear.lean)

For each wire $g$ let $S(g)$ be the variables whose singleton assignment makes it true. An input has its singleton as $S(g)$. At an OR these sets take unions. At a binary AND the set is empty, since a single true input can reach at most one child. Thus, whenever $S(g)$ is nonempty, a positive OR circuit realizes the predicate “a member of $S(g)$ is selected.” It uses just original OR gates with nonempty singleton sets, deleting branches with empty sets and suppressing copies. All such predicates can be computed together with the original sharing.

Work backwards from the output through OR gates only, and stop on first meeting an AND. The output and every OR retained in this part have empty singleton sets, since otherwise a singleton would reach the output, contradicting the posted soundness condition. No bare input is encountered. Take a terminal AND with children $g,h$. On an input selecting two distinct variables, this AND can fire only if one variable makes $g$ true by itself and the other makes $h$ true by itself. Both children require a selected variable and their syntactic supports are disjoint. Conversely, selecting a member of $S(g)$ and a member of $S(h)$ suffices by monotonicity. If either set is empty, the AND never contributes on a pair and can be dropped here.

For a remaining AND every pair from $S(g)$ and $S(h)$ passes unconditionally through the top OR path. A pair of points with no line, or a pair of lines with no point, is a promised negative input. Accordingly one of these nonempty sets consists entirely of points and the other consists entirely of lines. Replace this AND by the product of its singleton predicates from the preceding construction. The top OR circuit applied to these products accepts exactly the same point–line pairs as the original circuit. Its rectangles are incident everywhere, so it also satisfies the soundness promise. Each retained positive-singleton OR is distinct from every retained top OR, which has empty singleton set. Every terminal AND is charged once. The separated circuit therefore costs no more than the original, even when ancestors are shared. The lower bound of 64 follows. The line-star construction attains it with disjoint supports at every AND.

## A weaker requirement on the ordinary degree-two terms

Fix a circuit satisfying the posted conditions. Propagate Boolean constants and remove unary copies. By completeness and soundness the output is nonconstant. For each surviving input wire use its variable; encode OR as ordinary addition and AND as multiplication in the polynomial semiring with nonnegative integer coefficients. Write $P_g$ for the formal polynomial of wire $g$. All surviving gates have positive minimum degree. Each output monomial comes from a parse of the DAG in which an OR chooses one input and an AND takes both. When the same wire is used twice in a parse its two occurrences are counted separately. Evaluation of $P_g$ at a Boolean input is positive exactly when the logical gate is true. Its value can exceed one.

**Theorem.** Suppose that for each of the 52 incident pairs $(p,w)$, the ordinary degree-two component of the output polynomial contains $x_p y_w$ with positive coefficient. Then the circuit has at least 64 gates, with arbitrary sharing and with no disjointness assumption on AND operands.

A parse for such a degree-two monomial has precisely two input leaves and exactly one binary AND occurrence. Everything above that AND in the parse is an OR-only path to the output. Each arm below it is an OR-only path to a variable. For any wire $g$, let $A(g)$ be the variable labels accessible from $g$ by following only OR gates to input wires. These labels are precisely the variables with positive linear coefficient in $P_g$. At an OR the sets take unions, and at an AND the set is empty.

Take the AND gates reached by walking backwards from the output only through ORs. For a reached AND with children $g,h$ and both $A(g),A(h)$ nonempty, every choice $i\in A(g)$, $j\in A(h)$ yields an accepting parse using those two leaves. If $i=j$ the corresponding input activates just one variable, which violates soundness. If both variables are points or both are lines, they form a promised negative input. Thus the two nonempty sets lie on opposite sides, and all pairs between them must be incident. Reached ANDs with an empty arm supply no degree-two terms. The hypothesis guarantees that the resulting incident rectangles cover every required pair.

The OR predicates for all their arms can be computed together by retaining OR wires with $A(g)\ne\varnothing$, discarding branches with empty $A$, and reusing shared wires. Every top OR on an OR-only path to the output has empty $A$, since an OR-only path all the way from an input to the output would accept its singleton. Hence top and arm ORs use distinct gates of the original circuit. Retain one AND per contributing gate and remove dead terms and copies from the top OR. This constructs the separated product circuit within the original budget. The preceding star count gives 64. The line-star circuit witnesses equality and represents every incident pair by a two-leaf parse.

In particular, for **any** hypothetical circuit of size at most 63, some required incident pair has zero coefficient in the ordinary degree-two component. Completeness gives an accepting parse on the assignment selecting just that pair; rejecting singletons forces every accepting parse on it to use both labels. Thus all of those parses have monomials $x_p^a y_w^b$ with $a,b\ge1$ and $a+b\ge3$. On Boolean inputs repeated factors collapse under $z^2=z$. This makes the missing ordinary squarefree term a concrete instance of the repeated-variable obstruction. The argument uses the support of the nonnegative arithmetic expansion. Signed or finite-field arithmetizations can have coefficient cancellation. The canonical multilinear decision polynomial, discussed next, always has coefficient one on this pair.

## What the promise forces for unrestricted circuits

Write $F(P,Q)$ for the incidence decision and $J(P)$ for the assertion that the selected points contain a collinear triple. The exact posted conditions for a monotone function $C$ are equivalent to
$$
F\le C\le F\lor J.
$$
Completeness on incident pairs gives the first inequality on all inputs by monotonicity. Soundness gives the upper inequality whenever $J$ is false, and it holds automatically when $J$ is true.

Over any commutative ring, take the squarefree coefficients of the Boolean decision tables by signed subset inversion. For any support $U$ whose points contain no collinear triple, every subset $T$ of $U$ still satisfies the soundness promise. Hence the coefficient of $x_U$ in the multilinear representative of $C-F$ is zero, since every evaluation difference in its signed subset sum vanishes. Consequently the polynomial difference belongs to the ordinary ideal generated by all 52 squarefree collinear-triple monomials. Each line gives four triples, and distinct lines cannot share a triple. In particular all terms of point degree zero, one or two match, with arbitrary degrees in the line variables. This applies to shared unrestricted circuits. It concerns the canonical multilinear polynomial and does not bound the cost of computing it. [Hereditary-domain coefficient lemma](ArcRestrictions.lean) · [Signed coefficient extraction](CoreCoefficient.lean)

There is also a circuit conversion with a known increase in size. The four sets
$$
\{0,1,2,5\},\quad\{3,4,7,9\},\quad\{6,8,10,12\},\quad\{11\}
$$
partition the points, and each meets every line in at most two points. For any $P,Q$ the exact incidence value is the OR, over these four masks $B$, of $C(P\cap B,Q)$. Every masked evaluation is promised, and each selected incident pair survives in one of the masks. With $s$ original gates, four specialized copies and three binary OR gates suffice, for $4s+3$ gates. In the posted list model a reference past the end of the final list reads false, so masked source inputs need no extra gate. Intermediates are renumbered within their own copy, and originally out-of-range or forward reads are sent to that same false reference. [Circuit wire semantics](https://github.com/brilliant-hq/pequalnp-proofs/blob/f3e69b796950be3379af6d3c070a5da412b9fdcd/lean/PEqualNP/Defs/CircuitLowerBounds.lean#L58-L65)

Four is optimal for this type of mask cover. If five points formed an arc, each of its points would lie on four different lines to its four partners. These exhaust the lines through that point, so each line in the plane would meet the arc in zero or two points. The four lines through any exterior point partition the putative five-point arc into even parts, a contradiction. Three masks therefore cover at most 12 points. [General hereditary cover identity](ArcRestrictions.lean)

The Lean companion formalizes the finite OR-cone count and the star property of incident rectangles in a relation without a four-cycle. The arbitrary-depth reductions, the necessity of a repeated-input witness, the gate accounting and the connection to the posted circuit type are written proofs. The two unrestricted consequences above do not establish a gate-preserving conversion for general monotone circuits. That step remains open in this argument.


## Finite search on the assigned statement

The finite test has 52 incident pairs and 560 maximal forbidden assignments. The respective counts of point arcs of sizes zero through four are 1, 13, 78, 234, and 234. The reproducible encoder describes unrestricted monotone circuits of at most 63 gates on these rows. It produces 123,165 variables and 7,172,154 clauses. Four 64-gate constructions pass all 612 rows. Testing 1,128,596 specified local gate replacements produced no 63-gate circuit. CaDiCaL 2.1.2 returned `UNKNOWN` in both a 30-second run and a second 180-second run with seed 27 on the full 63-gate instance. This yields neither a 63-gate witness nor an unsatisfiability certificate.

Run `python3 arc_window_search.py` for the boundary, witnesses and local rewrites. Add `--cnf /tmp/incidence-63.cnf` to emit the optional 147,508,154-byte DIMACS. Its SHA-256 is `1b09fee8cd79a326a3fc22adb391cf2ee826952ea10085474bfa9d6e2e1ef610`. [Finite search and encoding](arc_window_search.py) · [Coefficient support and finite point masks](WindowCoefficients.lean)


## A checked lower bound for unrestricted circuits

Every monotone circuit satisfying the two actual desk hypotheses has at least **38** gates. The proof specializes the gate-count argument of upstream L-meta-740 to singleton and two-vertex tests. These 351 assignments give 26 live inputs and at least 13 distinct branching wires, with their sum bounded by the gate count plus one. Monotonicity supplies the needed values on supersets of incident pairs. The Lean proof uses the actual upstream definitions. Its conclusion excludes circuits of size at most 37. The desk asks to exclude all circuits of size at most 63.

To reproduce this separate result, build `PEqualNP.Defs` in the upstream Lean 4.36.0 checkout at `f3e69b7`, then run `lake env lean -DwarningAsError=true /absolute/path/to/ArcWindowLowerBound.lean` from its `lean` directory. The 4.33.1 companion suite checks the other modules in this note. [Lean proof against upstream definitions](upstream-comparison/ArcWindowLowerBound.lean) · [Source of the gate-count argument](https://github.com/brilliant-hq/pequalnp-proofs/blob/f3e69b7/lean/PEqualNP/Outside/L_meta_740.lean)
