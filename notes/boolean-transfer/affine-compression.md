# Grouping arc coordinates in a space of affine directions

Let $E=\{(a,b):a,b\in[N],\ a\ne b\}$ be the loopless directed arcs. Let $K\subseteq\mathbb F_2^E$ be a linear subspace of dimension $d$, and let $v_{ab}\in K^*$ evaluate coordinate $(a,b)$. Put $v_{bb}=0$. The following argument finds independent sums of coordinates on rectangles whose tails and heads lie on disjoint vertices.

**Grouping lemma.** Put $k=\lfloor d/(2N)\rfloor$. For any integer $m\ge 1$ satisfying
$$
                  k-2m \ge 2m\ln(4m^2),
$$
there are $m$ distinct heads $b_1,\ldots,b_m$, another $m$ distinct vertices reserved as anchors, and disjoint nonempty sets $O_1,\ldots,O_m$ avoiding all these vertices, such that the $m^2$ functionals
$$
                    w_{ij}=\sum_{a\in O_i}v_{a b_j}
                    \quad(1\le i,j\le m)
$$
are linearly independent in $K^*$. Thus their joint evaluation maps $K$ onto $\mathbb F_2^{m\times m}$.

**Proof.** Order all heads arbitrarily. For each head $b$, let $U_b$ be the span of all coordinate functionals at earlier heads, and let $t_b$ be the dimension gained by adjoining all coordinates at $b$. The coordinate functionals span $K^*$, so $\sum_b t_b=d$, with each $t_b\le N-1$. At least $k$ heads have $t_b\ge k$. Otherwise at most $k-1$ heads can contribute as much as $N-1$ each, and the others contribute at most $k-1$ each, giving $d<2Nk$. Select $m$ such heads in their original order and reserve $m$ further distinct vertices as anchors. This is possible since $2m\le k\le (N-1)/2$.

At a selected head $b$, discarding the $2m$ reserved vertices as possible tails costs at most $2m$ dimensions modulo $U_b$. Select $k-2m$ remaining tails $T_b$ whose coordinate functionals are independent modulo $U_b$. These sets may overlap across heads.

Assign each unreserved vertex independently to $O_i$ with probability $1/(2m)$ for each $i$, leaving it unused with probability $1/2$. Fix a selected head $b_j$ and a nonempty set $J\subseteq[m]$ of size $h$. We bound the probability that $\sum_{i\in J}w_{ij}$ belongs to $U_{b_j}$. Condition on the assignments outside $T_{b_j}$. For its remaining tails, inclusion in the union of the bins in $J$ gives independent Bernoulli bits of parameter $p=h/(2m)\le 1/2$. Independence of their vectors modulo $U_{b_j}$ permits at most one bit pattern that makes the sum vanish in the quotient. Its probability is at most $(1-p)^{k-2m}$.

Writing $z=\exp(-(k-2m)/(2m))$, a union bound over the selected heads and all nonempty bin sets gives failure probability at most
$$
           m\sum_{h=1}^m \binom mh z^h
           =m((1+z)^m-1)
           \le m(\exp(mz)-1)<1 .
$$
Indeed the hypothesis gives $z\le 1/(4m^2)$, and $e^x-1\le 2x$ for $0\le x\le1/4$. Fix a successful assignment. Each selected head then has $m$ independent sums modulo its earlier heads, which also forces each bin to be nonempty. In a nonzero relation among all the sums, take the last participating head. Its nonempty sum cannot belong to the span of earlier heads. This proves the lemma.

## Application to Hamiltonian cycles

Let $R\subseteq(\mathbb F_2^E)^*$ be the span of the linear parts of allowed affine forms $L$, and take $K=R^\perp$. For $m\ge3$ as in the lemma, make $O_i$ the outgoing ring of city $i$, make $b_i$ its singleton incoming port, and use its reserved anchor. A singleton ring has no internal arc. Set a Boolean baseline $c$ equal to one on the directed outgoing ring arcs, the anchor-to-outgoing-port arcs and the incoming-port-to-anchor arcs. Insert unused vertices into a forced path replacing one anchor, with all its former entering arcs at the start and all leaving arcs at the end. Set the remaining coordinates of $c$ to zero.

Choose a linear right inverse for the surjection in the lemma. Applied to the matrix with independent entries $Y_{ij}$ off the diagonal and zero diagonal, it gives a vector of linear forms $Z(Y)$ in $K$, meaning each coefficient vector belongs to $K$. Under $X\mapsto c+Z(Y)$, every allowed form specializes to the Boolean constant $L(c)$, so all generators $L^2-L$ vanish.

Every spanning tour must leave each outgoing ring and enter each incoming port. Both kinds of arcs have zero baseline. A degree-$m$ term must therefore choose exactly $m$ linear factors, each a crossing from an outgoing ring to an incoming port, one per ring and one per port. The other arcs take their baseline constants. Once the crossings are fixed, each outgoing ring has just one possible full traversal ending at its specified exit. Contracting the cities gives one base tour, and each choice of crossings realizing a base tour extends uniquely. Summing the choices for each step $i\to j$ produces exactly $\sum_{a\in O_i}Z_{a b_j}=Y_{ij}$. Thus the degree-$m$ homogeneous component of the specialized tour polynomial is $\operatorname{hc}_m(Y)$, and lower components vanish.

For the squarefree union of two distinct tours, the same degree count would force both tours to use exactly the same $m$ crossing arcs and only baseline arcs besides. Unique extension for those crossings excludes this possibility. Each such union consequently has zero components through degree $m$; multiplying by any ordinary polynomial preserves this vanishing.

It follows that a polynomial-size circuit congruent to $\operatorname{hc}_N$ modulo the allowed affine Boolean identities and all two-tour union monomials yields a polynomial-in-$N$ circuit for $\operatorname{hc}_m$. Computing the affine substitutions costs $O(N^2 m^2)$ operations and retaining components through degree $m$ increases size by an $O((m+1)^2)$ factor. The pinned formal lower bound gives $m\le\exp(O((\log N)^{3/4}))$. For large $k$, taking $m=\lfloor\sqrt{k}/4\rfloor$ satisfies the explicit grouping condition. Therefore the codimension of the span of the allowed linear parts must satisfy
$$
        d=N(N-1)-\dim R
          \le N\exp(O((\log N)^{3/4})).
$$
This necessary condition allows arbitrarily dense affine forms. It still permits the full Boolean ideal, for which $d=0$. [Pinned formal lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L33-L46)

## Verification

The grouping and router arguments above are written proofs. The compression checker computed right inverses in the original arc coordinates, checked 810 partitions of a small example exhaustively, and exercised examples up to 96 vertices. A separate calculation enumerated tours with nontrivial crossing weights and tested cancellation in characteristic two. Lean checks that the two error ideals can be discarded given the stated scalar and order conditions. [Compression checks](compression_checks.py) · [Crossing weights](affine_guard_projection.py) · [Formal transfer](AffineGuard.lean) · [Nonlinear identities](smooth-guards.md)
