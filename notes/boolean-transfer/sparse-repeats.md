# A Hamiltonian-cycle lower bound from repeats in one monomial

Suppose an $S$-gate arithmetic DAG over $\mathbb F_2$ correctly decides directed Hamiltonian-cycle existence on the Boolean cube of $m$-vertex adjacency matrices. For each monomial of its **formal output after cancellation**, count the distinct variables with exponent at least two. Let $r$ be the largest such count among the monomials involving at most $m$ distinct edges. For polynomial $S$ and all sufficiently large $m$ we prove
$$
r\ \ge\ \tfrac c2(\log_2 m)^{1/3}-O(1),
$$
where $c>0$ is the source theorem's constant. The previous result counted the union of the repeated coordinates across all these monomials. The new result puts repeats **in a single monomial**, even if different monomials repeat different edges. Exponents and reuse inside the DAG are unrestricted. [Source lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L34-L46) · [Previous result](boolean_jet.md#formal-output-tradeoff-for-an-np-decision-problem)

## The identity

For $N$ variables and cutoff $d$, define $R_i p=(1-x_i)p|_{x_i=0}+x_i p|_{x_i=1}$. This linear operator changes each positive exponent of $x_i$ to one. The $R_i$ commute. Write $\Delta_i=R_i-I$, $R_B=\prod_{i\in B}R_i$, and $\Delta_J=\prod_{i\in J}\Delta_i$. Empty products act as the identity. Define
$$
T_r p=\sum_{J\subseteq[N],\, |J|\le r}\Delta_J p .
$$

On a monomial with repeat set $D$, every term with $J\not\subseteq D$ vanishes. When $|D|\le r$, all surviving terms are present, so their sum equals $\prod_i(I+\Delta_i)$ on that monomial. This is full Boolean multilinear reduction. Every partial clip preserves the set of variables occurring in a monomial, so terms of support larger than $d$ cannot contribute to formal degree $d$. By linearity,
$$
\operatorname{hom}_d(T_r p)=\operatorname{hom}_d(\operatorname{ML}p)
$$
whenever **each output monomial of support size at most $d$ repeats at most $r$ distinct coordinates**. This holds over any commutative ring. Every $T_r p$ also agrees with $p$ on the cube without a repeat promise, since every nonempty mixed difference evaluates to zero there.

In characteristic two, for Hamiltonian-cycle **existence** and $d=m$, the right-hand side is exactly the prescribed formal tour polynomial. Lean proves this identity directly for the signed sum of actual partial reductions of any cube-correct decision polynomial. [Signed reduction and tour theorem](SparseRepeat.lean) · [Formal graph identification](TourLayer.lean)

## Number of arithmetic gates

Expanding gives $\Delta_J=\sum_{B\subseteq J}(-1)^{|J|-|B|}R_B$. One $R_B$ suffices for the entire input DAG. In characteristic two its coefficient is the parity of $\sum_{j=k}^r \binom{N-k}{j-k}$ for $k=|B|$ and $0\le r\le N$. For $r<N$ this is $\binom{N-k-1}{r-k}\bmod2$, by Pascal's identity. For $r=N$ only $R_{[N]}$ survives.

To obtain $R_B$ for $k=|B|>0$, share the $k$ input variables, their complements and a constant one. For each of $2^k$ assignments, copy the original DAG with those inputs fixed and multiply its output by its $k$ selector literals. Sum the selected outputs. Counting input and constant gates gives $I(k)=2^k(S+k+1)+2k$. Set $I(0)=S$. For an upstream DAG designating an earlier output, take its prefix through that gate. If $K$ is the set of sizes with odd coefficient, the implemented length before extracting the degree layer is
$$
L=\sum_{k\in K}\binom Nk\bigl(I(k)+1\bigr)-1.
$$

Keeping degrees zero through $d$ at every gate costs at most $1+(d+1)^2L$ gates. At a multiplication, degree $j$ takes $j+1$ multiplications and $j$ additions. Earlier results remain available by index. The compiler takes $r$ as input and operates directly on the DAG. Computing the binomial parities, listing the subsets and writing binary gate indices takes polynomial time in $N,S,d$ and the stated gate bound, including the intermediate DAG of length $L$. Each field constant occupies one bit. [Compiler and checks](sparse_repeats.py)

A simpler upper bound for the output size is
$$
1+(d+1)^2(S+3r+2)\sum_{k=0}^r2^k\binom Nk
\ \le\ 1+(d+1)^2(S+3r+2)(1+2N)^r .
$$
Substitute $d=m,\ N=m^2$. The derived circuit computes the formal $\mathrm{hc}_m$, so it exceeds $m^{c(\log_2m)^{1/3}}$ gates. Taking logarithms gives the claimed lower bound on $r$ for every fixed polynomial bound on $S$. Using the $m(m-1)$ off-diagonal variables gives the same asymptotic conclusion. For fixed $r$ the compiler is polynomial. Its exponent grows with $r$.

## Counterexamples and limits of the compiler

Take $x_A=\prod_{i\in A}x_i$, $|A|=d$, and $D\subseteq A$ of size $r+1$. The monomial $x_A\prod_{i\in D}x_i$ has $r+1$ repeats. No clip of at most $r$ coordinates produces $x_A$, so the degree-$d$ part of the truncated output is zero. Full clipping gives $x_A$. Also, a promise concerning only supports of size **exactly** $d$ misses spurious terms. For $p=x_1^2x_2^2$, $r=1$, the truncated degree-three layer over $\mathbb F_2$ is $x_1^2x_2+x_1x_2^2$, while full clipping has degree two. Conversely cancellations can make the method succeed outside the promise. Adding $x_A^2+x_A^3$ to a canonical representative, for $d>0$, changes neither its cube values nor its degree-$d$ component.

Consider a fixed XOR of operators $R_B$ that succeeds on all promised inputs. For every $r$-set $D$, choose $A\supseteq D$ of size $d$, where $r\le d\le N$. On the test monomial above with this $D$, the coefficient of $x_A$ in $R_B$ is one precisely when $D\subseteq B$. At least one nonzero sample must contain each $r$-set. If all samples are of size at most $r$, every $r$-set is forced. More generally, counting incidences gives
$$
\binom Nr\le\sum_B \binom{|B|}{r}\le\sum_B 2^{|B|}.
$$
The last sum counts assignments when each sampled interpolation is implemented separately. The bound concerns this sampling strategy. It does not exclude sharing between samples or a different type of arithmetic circuit. [Lean coefficient and covering proof](CoverCost.lean)

## An easy decision problem with the same lower bound

Consider the language “the selected edges **are exactly** one directed spanning cycle.” Check that each vertex has one incoming and one outgoing edge, then follow successors from a fixed vertex and check that the first return occurs at step $m$. A constant number of vertex indices and counters suffice on read-only adjacency input. This is a deterministic logspace algorithm.

The indicator of an exact tour edge set $A$ is $x_A\prod_{e\notin A}(1-x_e)$. Summing over tours counts each accepted input once. Its degree-$m$ homogeneous component is $\mathrm{hc}_m$, since a degree-$m$ term must choose the constant from every complementary factor. The same per-monomial repeat lower bound therefore holds for every polynomial-size arithmetic representation of this logspace language. This measure alone cannot distinguish Hamiltonian-cycle existence from a problem solvable in polynomial time. [Lean proof for the easy language](EasyTourLayer.lean) · [Earlier work on tour incidence](https://github.com/Ma1achy/pequalnp-proofs/tree/30709949f9116bd1200223a54751e0d600e6d4e0/notes/affine-elimination/cycle2)

The comparison extends to the entire prefix through logarithmically many additional degrees. Matching polynomially many additional degrees in uniform polynomial time is equivalent to P = NP. [Degree-prefix equivalence](degree-prefix.md)

A separate restriction realizes OR on $\lfloor m^2/4\rfloor$ independent edges. Thus an assumption of total degree $m+O(1)$ would already exclude every cube-correct polynomial for Hamiltonian-cycle existence at large $m$. A published sparse saturated-graph construction improves this to within $O(m)$ of the full loopless adjacency length. [Elementary restriction and marked walks](degree-obstructions.md) · [Published construction and multiplication bound](degree-literature.md)

## Verification boundary

Lean checks the signed clipping identity and its degree-$m$ consequence for both graph languages. It also checks the monomial tests and the covering bound for fixed sampling strategies. The arithmetic gate counts, the resulting asymptotic lower bounds, and the logspace recognition algorithm have written proofs. The Python compiler passed 1,498 monomial/degree/cutoff cases and 384 seeded DAG cases. For a three-vertex decision circuit with repeats distributed over all six edges, the compiler recovered exactly the two formal tour monomials in 179 gates. Its central hypothesis and cost estimates concern the formal output of a circuit, so unrestricted Boolean circuit size remains open. [Reproduce the checks](verify.sh)

## Relation to earlier results

Expansions of commuting coordinate projections are classical. Kuo, Sloan, Wasilkowski and Woźniakowski give an inclusion–exclusion decomposition for projections that eliminate coordinates. Here each operator keeps affine dependence in its coordinate, and the number of repeated coordinates in a monomial controls where the expansion terminates. [Kuo et al., §2](https://web.maths.unsw.edu.au/~fkuo/pubs/ksww09-decomp.pdf)

Hrubeš's Theorem 1 and Corollary 2 give monotone 2-CNF families whose multilinearizations are VNP-hard in the paper's circuit-size comparison sense. In particular VP ≠ VNP implies that full multilinearization can take a family out of VP. Our compiler targets one degree layer under a restriction on individual output monomials. [Hrubeš, pp. 3–4](https://users.math.cas.cz/~hrubes/PDFs/Mult.pdf)
