# Two limits on using formal degree to extract a Boolean layer

Let $\mathcal M(P)$ be the canonical multilinear polynomial of a formal polynomial $P$ on Boolean inputs. It replaces every positive exponent by one and combines coefficients. Write $[\mathcal M(P)]_d$ for its homogeneous component of total degree $d$. These two results concern different promises.

## The Hamiltonian-existence decision function has degree at least $\lfloor n^2/4\rfloor$

The input is a loopless directed graph on $n\ge2$ labelled vertices, with one Boolean variable per possible arc. Over any field, every polynomial $P$ agreeing on **all** graphs with the indicator that the graph contains a directed Hamiltonian cycle satisfies
$$
\deg P\ \ge\ \deg\mathcal M(P)\ \ge\ \lfloor n^2/4\rfloor .
$$
The first inequality holds because reducing exponents and combining terms never increases total degree.

**Proof.** Partition the vertices into nonempty sets $A,B$ of sizes $\lfloor n/2\rfloor,\lceil n/2\rceil$. Fix all within-part arcs and all $B\to A$ arcs present. Leave every $A\to B$ arc free. Every Hamiltonian cycle must use a free arc. Conversely, any one present arc $a\to b$ suffices. Starting at $b$, visit all vertices of $B$, take a present backward arc to start a path through $A$ ending at $a$, and close via $a\to b$. The path construction permits singleton parts.

The restriction is OR on $L=|A||B|=\lfloor n^2/4\rfloor$ bits. Its multilinear representative is $1-\prod_{e=1}^L(1-z_e)$. The coefficient of the full monomial is $(-1)^{L+1}$, nonzero in every field, including characteristic two. Restricting $\mathcal M(P)$ at constants preserves multilinearity and cannot raise degree. Uniqueness on the cube therefore gives the inequality. [Verified multilinear uniqueness](BooleanIdeal.lean)

Consequently the promise $\deg P\le n+r$ already forces $r\ge\lfloor n^2/4\rfloor-n$ for this decision task. For $r=o(n^2)$ the promise is eventually impossible, independent of circuit size. This argument uses the full input domain, including dense graphs. A restriction on repeated coordinates within individual monomials is a different promise. Multilinear polynomials can have arbitrary total degree.

A literature-based sharpening gives a lower bound within a linear number of arcs of the full adjacency length, and a corresponding bound on the number of multiplication gates. [Sparse saturated graphs and multiplicative complexity](degree-literature.md)

## A polynomial-size homogeneous circuit with a hard canonical top layer

There is no polynomial-size general extraction of $[\mathcal M(P)]_d$ from polynomial-size arithmetic circuits under the promise $\deg P=d$, by the pinned formal Hamiltonian-cycle polynomial lower bound. The following reduction works over any field and preserves formal coefficients.

For $n\ge2$, use one marker $Z_i$ per vertex and one arc variable $X_{ij}$ for every $i\ne j$. Fix vertex 0 as root. The polynomial $W_n$ sums over all length-$n$ closed directed walks from 0, with immediate self-loops disallowed. At each step $i\to j$ multiply by $Z_iX_{ij}$. Its formal degree is $d=2n$. Indeed every term has that degree, and each Hamiltonian cycle gives a surviving coefficient one.

For a straight-line circuit form $M_{ij}=Z_iX_{ij}$. Initialize $D_{0,0}=1$ and $D_{0,j}=0$ for $j\ne0$. Compute
$$
D_{t+1,j}=\sum_{i\ne j}D_{t,i}M_{ij},\qquad W_n=D_{n,0}.
$$
Path extension proves the recurrence over the formal polynomial ring. In the upstream convention a variable, field constant, binary addition or binary multiplication each costs one gate and any prior gate may be shared. There are $n^2$ occurring variables, two constants and $n(n-1)$ shared marker–arc products. Each of $n^2$ updates needs $n-1$ multiplications and $n-2$ additions. The displayed implementation therefore uses at most $2n^3-n^2-n+2$ gates. It can be emitted in $O(n^3\log(n+1))$ bit operations by indexing the tables and writing the constant number of $O(\log(n+1))$-bit gate indices per instruction.

A length-$n$ walk contributes to the canonical degree-$2n$ layer only when all $n$ source markers are distinct. This follows by counting supports: there are $n$ occurrences of markers and $n$ occurrences of edge variables, drawn from disjoint sets. Distinct source vertices force distinct arcs and give exactly a directed Hamiltonian cycle. Conversely each such cycle occurs exactly once because its traversal starts at the fixed root. Different cycles give different formal arc monomials. Coefficients in this layer are exactly one in every characteristic, even though other walk contributions can cancel. It follows that
$$
[\mathcal M(W_n)]_{2n}=\left(\prod_{i=0}^{n-1}Z_i\right)\operatorname{hc}_n(X).
$$
Substituting $Z_i=1$ at the input gates of a circuit for the left side yields a circuit of no larger size for the upstream formal $\operatorname{hc}_n$. Diagonal arc variables in the upstream definition are unused for $n\ge2$. Its exact arithmetic-circuit theorem supplies an absolute $c>0$ such that, for each fixed characteristic and all sufficiently large $n$, the layer requires more than $n^{c(\log_2 n)^{1/3}}$ gates. In particular even an unbounded-time search cannot always produce a polynomial-size circuit for this layer. Here the promised difference $\deg W_n-d$ is zero. [Formal polynomial and size bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L34-L46) · [Pinned proof](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Solution.lean#L26-L33)

This reduction is about the size of a formal output of a general extraction operation. For example, on four vertices with all markers one and just $0\to1,1\to0$ present, there is one length-four root-closed walk and no Hamiltonian cycle. Thus the original walk circuit fails the full Boolean-existence promise. The walk can use the same coordinate repeatedly. Bounding the number of such coordinates gives a different result.

## Every small representative of one language in P needs repeated coordinates

Let the binary language have input length $N=n^2+n$, with $n\ge2$. Parse the first $n$ bits as vertex markers, followed by the $n\times n$ adjacency matrix in row-major order. Ignore its diagonal. Reject every other input length. Accept exactly when $W_n$ evaluates to one in $\mathbb F_2$. The recurrence decides the language uniformly. It uses $O(n^3)$ indexed bit operations on well-formed inputs, and simulating array access by scans still gives polynomial time on a Turing machine. Thus the language lies in P.

Let $P_n$ be **any** family of formal polynomials computed by polynomial-size arithmetic circuits over $\mathbb F_2$ that recognize this language on the Boolean cube. For each $n$, define $r_n$ as the maximum number of distinct variables with exponent at least two in a nonzero monomial of $P_n$ whose support has size at most $2n$, taking zero for an empty maximum. Then, for all sufficiently large $n$,
$$
r_n=\Omega\big((\log n)^{1/3}\big).
$$
The statement concerns monomials in the formal **output** after cancellations. The fact that the algorithm deciding the language runs in polynomial time is compatible with this lower bound on multiplicities.

**Proof.** Cube agreement and uniqueness give $\mathcal M(P_n)=\mathcal M(W_n)$. For a variable $x_i$ write $M_iP=(1-x_i)P|_{x_i=0}+x_iP|_{x_i=1}$, and put $D_i=M_i-I$. These operators commute across coordinates. On a monomial, $D_i$ gives zero unless the exponent of $x_i$ is at least two, in which case both resulting terms have the original support. In the expansion $\mathcal M=\prod_i(I+D_i)$, each term indexed by a set of size greater than $r_n$ therefore annihilates every input monomial of support size at most $2n$. Every input monomial of larger support contributes only to degrees greater than $2n$, including after any partial application of these differences. Hence keeping only subsets of size at most $r_n$ still computes the correct homogeneous degree-$2n$ output.

If the original circuit has size $S_n$, a difference in one coordinate uses three copies of the preceding circuit and a constant number of arithmetic gates. The sum over subsets therefore costs $O((S_n+1)\sum_{a=0}^{r_n}\binom{N}{a}3^a)$ gates. Extract ordinary homogeneous degree $2n$ by retaining degrees zero through $2n$ at every gate and multiplying those vectors by truncated convolution. This costs a further $O((n+1)^2)$ multiplicative factor in circuit size and works in characteristic two. The resulting size is at most $\operatorname{poly}(n,S_n)(3N)^{r_n}$. Setting markers to one gives a circuit for the formal $\operatorname{hc}_n$ by the walk identity. Comparing with its pinned size lower bound and taking logarithms base $n$ gives $c(\log_2 n)^{1/3}\le O(1)+r_n\log_n(3N)$, where $S_n$ is polynomial in $n$ and $\log_n(3N)=O(1)$. This proves the claim. The construction needs only the numerical bound $r_n$ for the size comparison. [Lean clipping lemmas](SparseRepeat.lean) · [Executable circuit transformation](sparse_repeats.py)

Hrubeš proved that, assuming VP differs from VNP over the field in question, the canonical polynomial of a polynomial-time computable Boolean function can require superpolynomial arithmetic circuits, including in characteristic two. His examples include monotone 2-CNF. [Hrubeš, 2015](https://users.math.cas.cz/~hrubes/PDFs/Mult.pdf)

Forbes, Shpilka, Tzameret and Wigderson give a related permanent example. They multilinearize a small product and take its top marker-degree component to recover the permanent times a marker monomial. The rooted-walk construction here recovers the Hamiltonian-cycle polynomial in characteristic two and turns its formal lower bound into a statement about every small representative of one language in P. [Multilinearization precedent, §4.2](https://toc.cs.uchicago.edu/articles/v017a010/v017a010.pdf#page=30)

## Reproduction

Run the following command with Python 3 from the companion directory.

~~~sh
python3 degree_checks.py
~~~

The verifier exhausts the free arcs of the complete-bipartition restrictions for $n=2,\dots,6$ (598 graphs), checking Hamiltonian existence by rooted permutation enumeration. It computes the Boolean Möbius coefficients to check the full OR monomial over $\mathbb F_2$. For $n=2,\dots,5$ it independently compares the dynamic programme with enumeration of all walk sequences over integer coefficients and modulo 2 and 3. It canonicalizes the output monomials, extracts the layer and compares it coefficient by coefficient with permutation enumeration. At $n=5$ the formal walk sum has 156 surviving monomials over the integers and 108 modulo 2. In both cases the extracted layer has all 24 rooted Hamiltonian cycles, each once. The verifier also tests the marked Boolean input encoding at every assignment for $n=2,3$ and checks rejection on malformed lengths. These finite checks accompany the mathematical reductions above.
