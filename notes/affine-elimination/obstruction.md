# A sharp obstruction for affine clauses, with a cut-by-cut bound

Consider an explicit conjunction of clauses over the remaining variables. Each literal is an affine Boolean function, true when its value is 1. A clause is false on a single affine flat, the solution set of its simultaneous zero equations. Normalizing those equations gives independent rows, detects an empty flat, and removes different encodings of the same flat. A conjunction therefore describes the complement of a union of affine flats. The minimum number of clauses is exactly the minimum number of flats covering precisely the violating assignments. The width of a normalized clause is the rank of its system, equal to the codimension of its nonempty flat. The claims below allow arbitrary affine coefficients and unlimited computational effort to choose a minimum cover.

## Mixed family

For each of $k\ge1$ blocks introduce $x_i,y_i,t_i,u_i$, impose
$$
 (x_i\lor\neg t_i)\land(\neg x_i\lor\neg u_i)
 \land(u_i=t_i\oplus y_i),
 \qquad \bigoplus_{i=1}^k t_i=0
$$
where the last equation is imposed once globally. When $x_i=0$, the first clause gives $t_i=0$. When $x_i=1$, the second gives $u_i=0$ and hence $t_i=y_i$. Conversely each input pair extends uniquely by $t_i=x_i y_i$ and $u_i=t_i\oplus y_i$. The formula has $4k$ variables, $3k+1$ constraints and $8k$ variable occurrences. For instance, an index of fixed length $\lceil\log_2(4k)\rceil$, a constant number of type/sign bits per occurrence or constraint, and unary arities use $N=O(k\log(k+1))$ bits. All coefficients use one bit. An alternative gadget used in the general eliminator experiment takes $t,a,b$ pairwise incompatible via three ordinary binary clauses, with $x=t\oplus a$, $y=t\oplus b$. The choice $t=xy,a=x\oplus t,b=y\oplus t$ is again the unique extension. Forgetting local helpers in either gadget leaves exactly the same graph $t=xy$.

Projecting all helper and product variables yields the even inner-product predicate $q(x,y)=\bigoplus_i x_i y_i=0$. At this cut the minimum number of affine clauses is **exactly $2^k-1$** and every clause with a nonempty false set has normalized width at least $k+1$. This is superpolynomial in the indexed original input length. Cohen and Shinkar established the exact $2^k-1$ flat cover of odd inner product as a bound on the number of terms in a DNF of parities. The application here uses its complemented output and a sparse mixed encoding to identify expensive elimination cuts. [Cohen and Shinkar, *The Complexity of DNF of Parities*, ECCC TR14-099](https://eccc.weizmann.ac.il/report/2014/099/)

**Proof.** The bad set $D=\{q=1\}$ has $(2^k-1)2^{k-1}$ points. Each nonzero $x$ permits exactly half of the $y$'s, and $x=0$ permits none. Over $V=\mathbb F_2^{2k}$ the polar form
$$
 B((x,y),(x',y'))=x\cdot y'+x'\cdot y
$$
is nondegenerate, as testing vectors supported in one coordinate recovers each coefficient. If $a+U\subseteq D$, the four points $a,a+u,a+v,a+u+v$ give $B(u,v)=0$ for every $u,v\in U$. Thus $U\subseteq U^\perp$ and $\dim U\le k$. At equality $U=U^\perp$. Constancy on $a+U$ implies $q(u)=B(a,u)$ for $u\in U$. On each other coset $c+U$, the value $q(c+u)=q(c)+B(c+a,u)$ is balanced because $c+a\notin U^\perp$. The all-one coset $a+U$ would then make ones a majority on $V$, contradicting the size of $D$. Hence each flat contains at most $2^{k-1}$ points and has codimension at least $k+1$. For every $s\ne0$ the equations $x=s,\ s\cdot y=1$ cut out a flat of exactly that size. They partition $D$, attaining both bounds.

## Order-sensitive theorem after the local helpers are gone

Consider any order on the $3k$ variables $x_i,y_i,t_i$ after eliminating the $u_i$. For each block inspect its **remaining** variables at a cut. Let $J$ index blocks retaining $t_i$. The other blocks have either both inputs $(H)$, one input $(S)$, or no inputs $(E)$. Write $s_i$ for the sole surviving input of a block in $S$ and $h=|H|$.

For $j\in J$, let $L_j$ be the projected AND graph. With both inputs present this is $t_j=x_j y_j$ (three ordinary clauses). With one input $v$ this is $t_j\Rightarrow v$ (one clause). With neither input it is true. The exact projected formula is
$$
 \left(\bigwedge_{j\in J}L_j\right)\ \land\
 \left([E\ne\varnothing]\ \lor\ \bigvee_{i\in S}s_i\ \lor\
 \left[\bigoplus_{i\in H}x_i y_i\ \oplus\ \bigoplus_{j\in J}t_j=0\right]\right).
$$
Indeed the hidden product in $H$ has a forced value. Each singleton input $s_i=0$ forces its hidden product to zero, while $s_i=1$ allows either product value. Each empty block allows both values. Choices in distinct blocks are independent except for the global parity equation, so one free bit suffices to meet that equation. This proves the formula simultaneously for every prefix, including all variables eliminated.

Let $m$ be the minimum number of affine clauses needed for that projected predicate.

* If $E\ne\varnothing$, $m\le3|J|$.
* If $E=\varnothing$ and $J=\varnothing$, $m=2^h-1$.
* If $E=\varnothing$ and $J\ne\varnothing$, $2^h\le m\le 2^h+3|J|$.

**Upper bounds.** Use the stated local clauses. When the parity condition matters, enumerate all fixed $x_H=v\in\{0,1\}^h$. Add one forbidden flat with equations $x_H=v$, every singleton input zero, and $v\cdot y_H\oplus\bigoplus_{j\in J}t_j=1$. Skip the inconsistent case $v=0,J=\varnothing$. This yields explicitly listed clauses. When every block is in $H$ it generates the optimum cover above.

**Lower bounds.** With $J=\varnothing$, fixing all singleton inputs to zero recovers even inner product on $2h$ bits. For $h=0$ the formula is identically true. With $J\ne\varnothing$, leave one product output $t_j=z$ free on an affine section satisfying the local graph. If both inputs remain, choose $x_j=z,y_j=1$. If one remains, choose it equal to $z$. Give every other $J$ block all-zero surviving bits and set the singletons to zero. The resulting predicate on $(x_H,y_H,z)$ is $q_H=z$. Every affine clause restricts to an affine clause under this substitution. The violating graph $z=1+q_H$ has $2^{2h}$ points. Projection to the $2h$ inputs is injective on the graph. For a flat in the graph its image is an affine flat on which $q_H$ agrees with an affine function (the inverse of the injective affine projection, followed by the output coordinate). Its direction is therefore isotropic for the nondegenerate polar form and has dimension at most $h$. This covers at most $2^h$ graph points per clause, forcing at least $2^h$ clauses. This argument also covers $h=0$.

**Cost for this named family.** Given the gate identities and the specified order, enumerate the upper-bound construction directly from the remaining-coordinate mask at each step. With dense $(3k+1)$-bit rows, each output flat uses at most $2k+1$ rows for $k\ge1$ (local three-row flats included). At most $3k+2^h$ flats are emitted for $E=\varnothing$, and at most $3k$ otherwise. Writing rows by scanning the $k$ blocks, updating masks and a binary counter by scans on $O(k)$-bit words, gives a conservative $O((k+1)^4(k+2^h))$ bit-operation bound per cut, with the exponential term replaced by 1 for $E\ne\varnothing$. Output storage is $O((k+1)^2(k+2^h))$ bits under the same convention. The helper-first phase can replace each completed gadget by its three-clause AND graph independently, retaining the other gadgets and the global parity. There are $4k$ steps in total. This is a specialized compiler using a known family and given order. It assumes no algorithm for discovering this factorization in arbitrary input.

Eliminating all $t_i$ immediately after all $u_i$ makes $h=k$. Alternatively eliminate $x_1,y_1,t_1$ immediately after all $u_i$. This keeps $h=0$ up to the first empty block, after which the global parity disappears. This latter order has polynomially sized residuals throughout. The formulas themselves are satisfiable, witnessed by all zeros. The theorem concerns the cost of preserving each full residual predicate. Sharing affine forms, deleting all redundant clauses, or changing affine coordinates preserves the lower bound whenever the output still lists clauses. General Boolean circuits can compute the residual with $k$ ANDs and $O(k)$ XORs. The theorem makes no bound for such factored outputs, arbitrary helper variables, unrestricted orders, or SAT decision.

## The compact gadget attains the minimum with the general elimination rule

Apply the implemented graph-pair rule, RREF, deduplication, containment deletion, and same-direction merging to the compact four-variable gadget. Eliminate all $u_i$, then $t_1,\ldots,t_k$. For $k\ge2$, after $r$ helpers the state has exactly $3k+1-r$ clauses. After all helpers and $j<k$ products the count is exactly $2^j+2(k-j)$. At $j=k$ the output is the optimum $2^k-1$. The three-graph encodings in the companion order analysis instead produce $(3^k-1)/2$ and $3^k-2^k$ at this same projection. [Encoding comparison](order.md)

**Proof.** Only the local parity and one binary clause mention $u_i$. Colliding their forbidden values replaces those two clauses by the single requirement $x_i=1\Rightarrow t_i=y_i$. Together with $x_i=0\Rightarrow t_i=0$, the two active domains partition the input. Their forbidden graphs have distinct directions. In an untouched block the two binary forbidden flats and the parity-violation hyperplane have distinct directions, and no one contains another, as their equations show. Factors from different blocks cannot contain one another. For $k\ge2$ the global parity involves a distinct free product bit outside each individual block, so a local flat cannot force its violation, and its violation does not force a local guard or local parity violation. This proves the helper-phase count.

After $j$ product steps, each word $s\in\mathbb F_2^j$ supplies one forbidden flat
$$
 x_{1:j}=s,\qquad s\cdot y_{1:j}+\sum_{i>j}t_i=1.
$$
The case $j=0$ is the input parity. The two local graphs for the next $t_i$ have disjoint guards. Tail graphs for distinct words likewise have disjoint guards. Each tail graph collides with each local graph once, producing exactly its two extensions labeled by the next $x_i$. At $j<k$ all tail equations are consistent because the tail has a live $t_i$. The coefficient row space of the word identifies $s$ via the $y$-coefficients in the tail equation, so two words have different directions. Their ranks are equal. At $j>0$ a tail flat restricts a processed input and allows every unprocessed $x_i$ value. Every untouched local graph fixes its own $x_i$ and allows every processed input value. This rules out containment, while the respective projections of their directions onto an unprocessed $x_i$ distinguish the directions for local-vs-tail comparisons. The $j=0$ comparison follows from the helper-phase argument. At $j=k$ only the all-zero word is inconsistent, and the other $s$ give the distinct maximum-dimensional flats of the optimal cover. For $k=1$ the initial global violation $t_1=1$ already contains the local violation $t_1=1,x_1=0$. Deleting that flat leaves three normalized clauses, then two after projecting $u_1$, and finally the single bad point $x_1=y_1=1$.

This encoding reduces the excess output caused by overlapping domain guards. The optimum itself remains exponential at the designated cut. The graph-pair implementation still tests pairs with incompatible guards. For example with $j<k$ processed products it tests $\binom{2^j+2}{2}$ graph pairs on the next product for $k\ge2$. The exactly counted output therefore does not imply an output-linear implementation.

## Independent checks

Run `python3 verify_inner_product.py` in this directory. The script uses the Python standard library and the local affine-clause eliminator. The checks are deterministic. Both gate encodings are checked for unique extensions for all four input pairs. The program enumerates every nonempty affine flat in dimensions $2,4,6$ using the unique reduced-row-echelon basis of its direction and a coset representative zero on all pivots. It also constructs the disjoint optimal cover. Finally it tests the explicit upper-bound compiler at **every** retained-coordinate subset after helpers are gone, against the actual projected full model set, on every remaining assignment.

| $k$ | Flats enumerated | Odd points | Flats contained in the odd set, by dimension starting at 0 | Cut/assignment pairs checked |
|---:|---:|---:|---|---:|
| 1 | 11 | 1 | 1, 0, 0 | 27 |
| 2 | 307 | 6 | 6, 15, 0, 0, 0 | 729 |
| 3 | 26,387 | 28 | 28, 378, 315, 0, 0, 0, 0 | 19,683 |

For $1\le k\le6$ the same script runs the general eliminator on the compact mux gadget through the SAT decision, checks the exact stage counts, and compares the canonical bad-cut state against the directly constructed optimal cover. Run `python3 verify_inner_product.py --mux-trace` for every intermediate encoded size, width, coefficient and row bit lengths, and reducer event counts. At $k=6$ the input uses 850 dense bits. The designated cut has 63 flats, width 7, and 11,488 dense bits in the original fixed 24-variable layout. The peak is 63 flats.

The cut formula and quantitative order analysis specialize the known flat-cover bound to this mixed testbed. Priority for this order-sensitive formulation is unverified.

## Scope of a quadratic representation

Shared inputs among product gates still yield one multilinear quadratic $q$ after all gate outputs are projected, provided the only remaining requirement is their parity. In this restricted case there is also a polynomial representation under every further coordinate projection. Let $w$ denote the coordinates to eliminate and $z$ those to retain. If the unique multilinear normal form of $q$ has a quadratic monomial in two $w$ coordinates, then for every fixed $z$ that monomial survives. The function of $w$ is nonconstant and attains both Boolean values, so the projected equation $q=0$ is identically true. Otherwise write $q(z,w)=q(z,0)+\sum_i a_i(z)w_i$ with affine coefficients $a_i$. Its projection is exactly $[q(z,0)=0]\lor\bigvee_i[a_i(z)=1]$. Every coefficient can be read directly from the input quadratic table. Recomputing from that table and the prefix mask produces each explicit projected predicate using $O(n^2)$ coefficient bits and, conservatively, $O((n+1)^3)$ bit operations per cut by sequential scans. At the last cut the result is a Boolean constant. This accounts for the small factored description of inner product. Additional constraints can couple the witnesses used to satisfy different equations. The next question is how the optimal **flat cover** of a shared-input projection depends on the rank of its restricted quadratic form when a cut leaves some products explicit.
