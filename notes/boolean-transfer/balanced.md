# Balanced products under Boolean agreement

## Source statement and its use

At commit 11b6c7e3c927df2658f513b6b68ea7f8929c62c5, §2.5 (p. 10) singles out coefficient extraction in the flat-case argument. Lemma E.4 (p. 33) and the mapping in Appendix Q (p. 67) identify its formal counterpart as Paper.lem_balanced. The printed paper assumes a commutative ring. The Lean declaration accepts a commutative semiring. [Paper, pinned PDF](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/paper.pdf) · [Lean statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Flat.lean#L233)

There are $k\ge2$ blocks with a common finite label type $T$. For $S\subseteq[k]$ and labels $x:[k]\to T$, the formal quantity $c_S(P,x)$ is the coefficient of $\prod_{a\in S}X_{a,x(a)}$ in $P$, all other exponents zero. The polynomial $\operatorname{linearPart}(P)$ sums these coefficient-weighted monomials for $S=[k]$. It selects **exactly** one degree-one variable from every block. Hence, for instance, even a squarefree monomial containing two different variables from the same block can be discarded. [Exponent and coefficient definitions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/CaseI/Multi.lean#L26) · [Polynomial reconstruction](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Flat.lean#L180)

Given an $L$-gate formal circuit for $P$, E.4 expresses $\operatorname{linearPart}(P)$ as a sum over balanced $S$ ($k\le3|S|\le2k$) of at most $L$ products **per** $S$. Each factor is degree exactly one in each of its own blocks, using only $S$ or only its complement. At an addition, coefficients add. At a product, formal exponents add, so
$$
 c_S(PQ,x)=\sum_{A\subseteq S}c_A(P,x)c_{S\setminus A}(Q,x).
$$
The disjoint split lets the gate induction balance one factor while keeping the other on the opposite blocks. The coefficient version feeds the tensor bound in prop_flat_lower_sum. In the application at line 523, the resulting coefficient tensor is identified with the **specific** network tensor using fklTen_val. A circuit for an arbitrary cube-equivalent representative supplies no such identification. [Product rule and gate induction](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/CaseI/Multi.lean#L65) · [Coefficient form](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Flat.lean#L264) · [Tensor use](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Flat.lean#L523)

## Counterexample and an invariant with a different product rule

Over $\mathbb F_2$, $(X_1^2-X_1)\prod_{a=2}^k X_a$ vanishes on the cube. Its formal one-per-block component is $-\prod_aX_a\ne0$ for singleton blocks. Its canonical multilinear representative is zero. More strongly, given any circuit for $P$, one multiplication of its output with itself computes $P^2$ with identical Boolean evaluations. Frobenius doubles every exponent, so its one-per-block component is zero. Taking $P$ to be the nonzero network polynomial destroys precisely the coefficient tensor needed at the downstream identification. E.4 continues to hold for the formal polynomial $P^2$ itself.

Define the invariant $\widetilde c_S(f,x)$ by extracting the same coefficient **after** Boolean multilinear reduction. With only the designated variables nonzero, it equals the XOR of $f$ at the $2^{|S|}$ assignments on their subsupports. Over $\mathbb F_2$ this subset transform is its own inverse. At a product the correct formula is
$$
 \widetilde c_S(fg,x)=\sum_{A,B\subseteq S,\ A\cup B=S}
       \widetilde c_A(f,x)\widetilde c_B(g,x).
$$
This follows because squarefree supports combine by union modulo the Boolean ideal. The sum gate remains linear. Already $f=g=X_1$ gives a missing unit coefficient in the proposed disjoint formula. For an example at the full two-block component, take $f=X_1X_2$, $g=X_1$. Their reduced product has full coefficient one, whereas every disjoint-split summand vanishes. The overlap retains dependence on the same block on both sides of the product. These examples refute quotient invariance of the formal operation and the disjoint-split gate identity for its invariant replacement. They do not logically refute the existential possibility of a different balanced decomposition with a different proof. Computing a single invariant coefficient by $2^{|S|}$ circuit evaluations does not construct that decomposition.

## A restricted transfer with a constructive gate bound

**Theorem (mathematical proof).** In a straight-line $+,\times$ DAG over $\mathbb F_2$, assign every gate its *syntactic support*, the union of input-variable names occurring in its ancestor subgraph. Let $H$ contain every variable occurring in both child supports of at least one multiplication gate, and write $t=|H|$. A length-$L$ such DAG has a circuit of length at most
$$
 S_t=2^t(L+t+1)+2t
$$
for its unique formal multilinear representative on the Boolean cube. The statement allows arbitrary reuse, cancellations, and formal degree in the variables in $H$.

**Proof.** For each assignment $\alpha\in\{0,1\}^H$ copy the DAG once, replacing leaves in $H$ by their constants. Call the resulting formal polynomial $P_\alpha$. At each product, the remaining variable supports are disjoint. Induction on gate index shows that every specialized gate is multilinear, even if its output feeds multiple later gates. Form
$$
 M=\sum_{\alpha}\left(\prod_{i\in H:\alpha_i=1}X_i\right)
              \left(\prod_{i\in H:\alpha_i=0}(1+X_i)\right)P_\alpha .
$$
Each summand is multilinear since $P_\alpha$ uses no variable in $H$. On a Boolean input exactly its selected assignment's summand survives. Thus $M$ has the original function on the cube. Multilinear uniqueness follows by separating a final variable as $A+X_jB$ and evaluating at zero and one, inductively, or by subset inversion. For $t>0$, allocate the $t$ variables, their $t$ complements and a constant one once. Each specialization takes at most $L$ gates, its indicator-times-value at most $t$ multiplications, and combining all values costs $2^t-1$ additions. This gives $S_t$. For $t=0$ the original circuit suffices. Syntactic supports can be found by propagating $n$-bit masks forward through the supplied DAG on $n$ occurring variables; no semantic disjointness test or minimization is needed. Copying the indexed instructions and writing addresses costs $2^t\,\mathrm{poly}(n+L)$ bit operations, for example $O(2^t(n+L+1)^5)$ with scans and binary counters.

In particular E.4 applies to the invariant one-per-block component with at most $S_t$ terms per balanced subset. For a fixed $C$, $t\le C\log_2 N$ and $L=\mathrm{poly}(N)$ make this a polynomial construction in encoded input length $N$. The restriction is substantial. A length-$O(n)$ circuit can multiply $\prod_i X_i$ by itself, putting every variable in $H$. This example shows that the interpolation cost analysis can be exponential even when a smaller multilinear circuit happens to exist.

## Consequence for an NP decision language

Use labelled directed graphs on $m\ge2$ vertices, represented by $m^2$ adjacency bits, and the ordinary decision predicate “contains a directed Hamiltonian cycle”. It belongs to NP: the witness is a cyclic ordering that can be checked against the selected arcs. Its values can differ from those of the parity polynomial $\mathrm{hc}_m$. Nevertheless, the **degree-$m$ homogeneous part of its canonical multilinear representative** is exactly the *formal* $\mathrm{hc}_m$ over $\mathbb F_2$. For any edge set $S$ of size $m$, all proper subsets have too few edges to contain a tour. Thus the ANF coefficient on $S$, the sum of its subassignment values, is one precisely for a tour edge set. All coefficients below degree $m$ vanish. Distinct cyclic permutations in the pinned definition have distinct directed edge sets, since the set specifies each vertex's successor. Loops do not occur in these tours. The extraction uses no bound on higher degrees. [Pinned HC and arithmetic lower-bound statements](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L35)

Given a formal circuit of size $S$ for that representative, retain degrees $0,\ldots,m$ at every gate. Addition is componentwise. For degree $j$ a product uses $j+1$ multiplications and $j$ additions by convolution. Across all degrees a multiplication gate uses at most $(m+1)^2$ gates. An initial shared zero suffices for absent components. This constructs a formal circuit of size at most $1+(m+1)^2S$ for $\mathrm{hc}_m$, with no assumption on higher degrees. Combined with the pinned MainTheorem in characteristic two, every size-$L$ arithmetic representation of the **decision predicate** with the syntactic overlap defined above obeys, for all sufficiently large $m$,
$$
 1+(m+1)^2 S_t > m^{c(\log_2 m)^{1/3}}
$$
for the positive source constant $c$. Hence $L\le m^d$ for any fixed $d$ forces $t\ge c(\log_2m)^{4/3}-O_d(\log m)$, using $t\le m^2$. In a Boolean AND/OR/NOT DAG, taking the syntactic overlap across each AND and OR suffices after the standard shared-gate arithmetic translation (a NOT introduces only a constant addition). This rules out polynomial-size decision circuits in the log-overlap class. A general polynomial-size Boolean circuit is allowed to reuse all its variables nonlinearly, so the obstruction remains a restricted-model result. The counting decision distinction is handled by minterm extraction, without identifying parity with existence on general graphs.

**Verification boundary.** MinTerm.lean proves the general first-layer and lower-layer coefficient claims for a finite list of equal-size minterms, plus the subset inversion identity. Lists represent sets in a common distinct-coordinate order. On those lists the library's sublist relation is subset inclusion. TourLayer.lean separately proves that the degree-$m$ homogeneous component of any cube-correct multilinear representative is precisely the upstream HC polynomial. The two circuit-size constructions and the resulting asymptotic consequence above are mathematical arguments. From this directory, the pinned command below compiled the file and printed its axiom dependencies. Subset inversion is axiom-free. The minterm statements use only the three standard axioms allowed by the upstream checker. [Lean minterm proof](MinTerm.lean) · [Upstream HC identity](TourLayer.lean)

~~~sh
/workspace/.boolean-transfer-tools/lean-4.33.1-linux/bin/lean -o /tmp/MinTerm433.olean MinTerm.lean
~~~
