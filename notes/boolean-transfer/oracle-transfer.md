# A black-box obstruction to extracting the tour polynomial from a Boolean circuit

Work over $\mathbb F_2$. Let $f:\{0,1\}^r\to\{0,1\}$ be any Boolean function and let $P$ be any formal polynomial agreeing with $f$ on the cube. Fix $d\ge1$, choose $j=\lceil\log_2(d+1)\rceil$, and put $q=2^j>d$ and $Q=P^q$. The oracle $Q$ still agrees with $f$ on every Boolean input. If $P$ has a circuit of size $s$, then $Q$ has one of size at most $s+j$ by repeated output squaring. [Checked one-substitution Frobenius identity](Frobenius.lean) · [Checked circuit cost](SquaringCost.lean)

A **straight-line polynomial oracle circuit** has visible indeterminates $X_1,\ldots,X_M$, ground-field constants, binary addition and multiplication, and gates $Q(B_1,\ldots,B_r)$. Each $B_i$ may be any preceding wire, including a polynomial computed using earlier oracle answers. Substituted polynomials can have arbitrary degree. Every ordinary operation used to build a polynomial available outside an oracle call belongs to the circuit. The theorem even allows an arbitrary finite number of oracle calls, with free argument references and arbitrary fan-out. Its lower bound counts ordinary binary arithmetic operations.

## Collapsing nested calls through degree $d$

Let $\mathfrak m=(X_1,\ldots,X_M)$. Evaluate every wire at $X=0$, proceeding in gate order, and replace each oracle gate by its resulting scalar. Preserve all ordinary gates, then discard wires unreachable from the output. Call the resulting ordinary polynomial $B(X)$, and the original output $A^Q(X)$. Then
$$
                  A^Q(X)\equiv B(X)\pmod{\mathfrak m^{d+1}}.
$$
In fact the congruence holds modulo the smaller ideal $(X_1^q,\ldots,X_M^q)$. The same statement holds with any field of characteristic two supplying constants and coefficients for the extractor.

For an oracle call with argument polynomials $B_i$, write $P(B_1,\ldots,B_r)=c+U(X)$, with $c=P(B_1(0),\ldots,B_r(0))$ and $U(0)=0$. Frobenius gives
$$
       Q(B_1,\ldots,B_r) = c^q+U^q .
$$
Every monomial of $U^q$ is divisible by some $X_i^q$. Thus the call agrees with its scalar in the stated quotient, even when every one of its arguments uses prior calls. At ordinary gates the quotient map respects addition and multiplication. Induction on the gate list proves the assertion on every wire and the constant terms agree exactly. Over the base field $\mathbb F_2$, the scalar for a call is simply $f(B_1(0),\ldots,B_r(0))$, since the tuple is Boolean. For a fixed circuit layout over that field, its collapsed layout and scalar labels therefore work for every initial representative of the same $f$. [Pinned Lean proof of elimination at every wire](OracleTransfer.lean)

The earlier obstruction treated one chosen polynomial substitution followed by truncation. The induction above permits nested substitutions, ordinary gates that retain the visible variables, and different nonuniform circuits for different representatives. Such circuits may produce nonconstant low-degree answers. Every such answer already comes from their ordinary arithmetic and scalar constants. [Earlier single-call obstruction](source-map.md#exact-use-in-k3)

## Lower bounds on the ordinary gates

Take $d=n\ge2$ and target the upstream formal Hamiltonian-cycle polynomial $\operatorname{hc}_n(X)$, homogeneous of degree $n$. Suppose the oracle circuit has $a$ ordinary binary gates and its degree-$n$ component equals $\operatorname{hc}_n$. The collapsed $B$ has the same degree-$n$ component. After pruning, the ordinary DAG has at most $a+1$ distinct live scalar and variable leaves. Indeed its underlying graph is connected to one output. With $a'\le a$ remaining binary nodes and $\ell$ leaves, it has at most $2a'$ incoming wires and at least $a'+\ell-1$ undirected edges. The single-leaf case satisfies the same bound. Thus even arbitrarily many scalar oracle answers do not provide arbitrarily many used constant slots.

Retain homogeneous parts $0,\ldots,n$ at each ordinary gate. A sum costs at most $n+1$ binary additions. At a product, the part of degree $i$ uses $i+1$ multiplications and $i$ additions, totaling $(n+1)^2$ gates over all $i\le n$. Leaves each use one reference slot plus a shared zero for their absent parts. Hence $\operatorname{hc}_n$ has an ordinary circuit of size at most
$$
                        ((n+1)^2+1)a+2 .
$$
If the source exact lower bound at $n$ is $L_{\rm ex}(n)=n^{c(\log_2 n)^{1/3}}$, it follows that $a>(L_{\rm ex}(n)-2)/((n+1)^2+1)$ for all sufficiently large $n$. This bound allows arbitrary unwanted terms above and below the target layer. [Checked formal lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L33-L46) · [Pinned proof](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Solution.lean#L26-L45)

**Stronger bound for exact output.** Suppose the entire degree-through-$n$ truncation of $A^Q$ equals $\operatorname{hc}_n$, as happens in particular when the output polynomial equals $\operatorname{hc}_n$. The same then holds for $B$. Over $\mathbb F_2((\epsilon))$, use the circuit
$$
                      \epsilon^{-n}B(\epsilon X).
$$
It formally approximates $\operatorname{hc}_n$ in the reference's sense. Every component below $n$ vanishes, the coefficient of $\epsilon^0$ is exactly the tour polynomial, and all higher components have positive $\epsilon$-degree. The ordinary circuit for $B$ has at most $2a+1$ slots. Each of at most $a+1$ distinct visible variables needs one scaling multiplication, and two shared Laurent constants and one final multiplication suffice. Thus the reference approximate size is at most $3a+5$, giving
$$
                          a>(L_{\rm ap}(n)-5)/3 ,
$$
where the pinned approximate theorem supplies its own positive constant and threshold in $L_{\rm ap}(n)=n^{c'(\log_2 n)^{1/3}}$. The same argument uses $K((\epsilon))$ if the extractor has ground constants in a characteristic-two extension $K$. [Approximate circuit convention](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L48-L61)

## Consequence for a Boolean transfer

Apply this to $f$ equal to directed Hamiltonian-cycle existence on $n$ vertices. For every formal representative $P$ of that decision function, the particular representative $P^q$ forces the bounds above for any polynomial-oracle extraction of the formal tour polynomial. The layout of the extractor may depend on $P^q$, the desired function, $n$, and arbitrary scalar advice. Its number of uses of $P^q$ is unrestricted. The lower bound still follows from the one ordinary pruned circuit for that particular layout. A putative polynomial-size Boolean decider would provide a polynomial-size arithmetic representative by gate arithmetization, and adding the $O(\log n)$ squarings would preserve polynomial size. This rules out a purported polynomial-overhead black-box transfer that handles every such representative. It does not establish a lower bound on the Boolean decider itself.

The same obstruction applies to a language already in deterministic logspace. A graph whose entire edge set is a single tour has canonical degree-$n$ component $\operatorname{hc}_n$. It even has a representative of polynomial formal degree and size *before* squaring. For a Boolean adjacency matrix $X$ require exactly one outgoing bit in each row, using the sum of its singleton point indicators, and take the product of the row tests. Multiply this by
$$
            (X^n)_{00}\prod_{i=1}^{n-1}\big(1-(X^i)_{00}\big).
$$
On functional rows, $(X^i)_{00}$ indicates return of the unique root walk after $i$ steps. The first-return condition at $n$ forces that walk to visit all $n$ vertices. The formula has formal degree $O(n^2)$ and a division-free circuit of $O(n^3)$ gates, using the row vector at each time to compute the next row vector. Diagonal entries may be included, since a functional graph that first returns at time $n\ge2$ has none. Squaring to $q\le2n$ leaves polynomial formal degree as well. Thus a polynomial-degree promise on the oracle representative alone permits this obstruction. [Verified canonical layer for the logspace language](EasyTourLayer.lean)

These are statements about symbolic polynomial composition and division-free arithmetic. Coefficient extraction from an oracle output, inverse Frobenius, inspection of a representative's gates, and input-dependent branching are different operations. The finite-point scalar transcript can be fixed nonuniformly without enumerating it efficiently. The previous lower bound on Boolean value queries addresses recovering a truncation of an *unknown* cube function. The present lower bound concerns ordinary arithmetic gates even with a fixed known function and arbitrarily many symbolic oracle queries. [Earlier Boolean value-query result](boolean_jet.md#what-survives-of-the-papers-evaluation-lemma)

## A fixed extractor over any field

Over an arbitrary field $K$ there is a related adversarial representative for a **fixed** circuit layout with $t$ oracle gates. Evaluate the layout at $X=0$, supplying $f(u)$ when a query's scalar tuple $u$ is Boolean, and zero otherwise. Follow the gate order, so this also determines the arguments of nested queries. For each distinct non-Boolean $u$ in that transcript choose a coordinate $i$ with $u_i\notin\{0,1\}$ and form
$$
       m_u(Y)=1-\frac{Y_i(Y_i-1)}{u_i(u_i-1)} .
$$
This polynomial is one on every Boolean tuple and zero at $u$. The denominator is a nonzero ground scalar. Thus $P'=P\prod_u m_u$ preserves the cube and gives exactly the simulated scalar answers at all queried tuples.

Let $S(y)=3y^2-2y^3$ and set $Q=S^{\circ j}(P')$, where $j=\lceil\log_2(d+1)\rceil$ counts compositions. The identities $S(y)=y^2(3-2y)$ and $1-S(y)=(1-y)^2(1+2y)$ hold integrally. If a gate polynomial has the form $b+V$, where $b\in\{0,1\}$ and $V\in\mathfrak m^e$, applying $S$ gives $b+V'$ with $V'\in\mathfrak m^{2e}$. At each query in the chosen layout, induction on the preceding constant terms ensures that $P'$ of the actual arguments has the prescribed Boolean constant. The iterates therefore give that same constant modulo $\mathfrak m^{d+1}$. The full scalar-replacement and circuit-size arguments above now apply over $K$. Constructing $Q$ from a size-$s$ circuit uses $s+O(t+\log(d+1))$ slots, including the mask constants. The construction requires only division-free gates after those scalars are chosen. Its degree is at most $3^j(\deg P+2t)$ for nonzero $P$.

The quantifiers differ from characteristic two's Frobenius construction. Here the layout is fixed first and must work for the altered $Q$. If an extractor chooses a different layout from the representative or its size, this argument alone gives no guarantee for that new layout. When all scalar query tuples are Boolean, the same iterated $S$ works without masks for every layout satisfying that condition.

## Why general coefficient gates change the model

For $m\ge2$, introduce a vertex marker $z_i$ and let $M_{ij}=z_i X_{ij}$ on loopless arcs, with $M_{ii}=0$. As a literal integral coefficient identity,
$$
 [z_0z_1\cdots z_{m-1}]\,(M^m)_{00}
     = \operatorname{hc}_m(X).
$$
Each term of the matrix entry is a length-$m$ closed walk rooted at zero. Each departure from vertex $i$ contributes one $z_i$. The indicated marker monomial requires every vertex to occur exactly once as a departure, yielding each directed Hamiltonian cycle once. Computing the matrix entry by iterating a root row vector costs $O(m^3)$ ordinary gates. The requested coefficient is also obtained by differentiating once in each distinct marker and setting all markers to zero. Therefore a model with one general mixed-coefficient gate, or $m$ unit-cost formal differentiation gates on arbitrary previous polynomials, computes the formal tour polynomial cheaply without consulting any decision oracle. The pinned lower bound counts ordinary arithmetic gates and supplies no such primitives. The identity concerns a formal sum of tours. On Boolean arc data that sum gives a field-valued tour count, so the computation supplies no ordinary Boolean decision circuit for existence. [Walk polynomial and circuit count](degree-obstructions.md)

Differentiating the **raw characteristic-two oracle** behaves differently. All its ordinary first partial derivatives vanish, since every exponent in $P^q$ is a multiple of $q\ge2$. Even a Hasse derivative of arbitrary multiorder $\nu$ is zero unless $\nu=q\mu$ coordinatewise, in which case it equals $(D^\mu P)^q$. Compare coefficients of the auxiliary variables $T$ in $P(Y+T)^q$ to see this. Each resulting raw derivative is still a scalar modulo $\mathfrak m^{d+1}$ after substitution, so pruning and the nonuniform ordinary-gate bounds still apply to such oracle gates. Their scalars can depend on formal derivative data. General coefficient gates can instead act on ordinary intermediate polynomials such as the marked matrix entry above.


[Finite nested-query and Hasse-derivative checks](oracle_transfer.py)
