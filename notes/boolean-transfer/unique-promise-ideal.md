# The exact polynomial quotient for the zero-versus-one tour promise

Work over $\mathbb F_2$ with one variable $X_e$ for each of the $m=n(n-1)$ loopless directed arcs. Write $X_S=\prod_{e\in S}X_e$, and let $h_n=\sum_T X_T$ sum over distinct spanning directed tours rooted at vertex zero. For $n\ge3$ define the two ideals in the ordinary polynomial ring by
$$
 B=\langle X_e^2-X_e:e\text{ an arc}\rangle,\qquad
 D=\langle X_{T\cup U}:T,U\text{ distinct tours}\rangle .
$$
The generators of $D$ use the **squarefree union** of the two tours. In the Boolean quotient $X_TX_U=X_{T\cup U}$. In the ordinary polynomial ring those two monomials can be different.

**Exact Boolean target.** General directed Hamiltonicity has polynomial-size Boolean circuits if and only if there is a family of polynomial-size ordinary arithmetic circuits over $\mathbb F_2$ with outputs $P_n$ satisfying
$$
                         P_n-h_n\in B+D .
$$
No coefficient extractor or ideal-membership test is supplied to those circuits. The displayed condition is imposed on the final output. It is an existence criterion and does not require a small certificate of ideal membership. Establishing a superpolynomial bound for this congruence would rule out polynomial-size Boolean circuits for Hamiltonicity and imply $\mathrm P\ne\mathrm{NP}$. [Isolation and nonuniform equivalence](unique-promise.md)

## Why this is exactly the right ideal

Let $\mathcal K$ be the family of arc sets containing at most one tour. It is downward closed. Every generator displayed above vanishes on every Boolean point $1_E$ with $E\in\mathcal K$. For the converse, reduce any polynomial $F$ to its unique multilinear representative $\bar F$ modulo $B$ by replacing each positive exponent by one. Write $a_S$ for the coefficient of $X_S$ in $\bar F$. On the Boolean cube,
$$
 \bar F(1_E)=\sum_{S\subseteq E}a_S,\qquad
 a_S=\sum_{E\subseteq S}\bar F(1_E).
$$
The second formula is Boolean Möbius inversion in characteristic two. If $F$ vanishes on $\mathcal K$, then $a_S=0$ for every $S\in\mathcal K$, since all its subsets belong to the same family. Each remaining $S$ contains two distinct tours $T,U$, so $X_{T\cup U}$ divides $X_S$ in the ordinary ring. Therefore $\bar F\in D$ and $F\in B+D$. This proves the entire vanishing-ideal assertion.

On $\mathcal K$, $h_n$ equals the required answer, since it counts the contained tours modulo two. Hence agreement with the promise is equivalent to the displayed congruence. A fan-in-two Boolean circuit is translated gate by gate using $xy$ for AND, $1+x$ for NOT, and $x+y+xy$ for OR. Conversely an $\mathbb F_2$ arithmetic circuit can be evaluated on Boolean bits using XOR and AND with constant overhead in the usual Boolean basis. Combining these translations with isolation gives the circuit-family equivalence. Circuits with inputs and constants counted separately still have polynomial size in either model. An arithmetic circuit evaluating this congruence is allowed arbitrary output on a graph with several tours.

## How much of the formal lower bound survives

Every squarefree generator of $D$ has degree at least $n+3$. Two distinct cyclic successor permutations cannot differ at one vertex, and exchanging just two images changes the sign of the permutation. All $n$-cycles have the same sign. Thus if **only $D$ is allowed**, any formal output $P_n$ congruent to $h_n$ has degree-$n$ component exactly $h_n$ and has no terms below degree $n$. This holds even with arbitrary cancellations, since the monomials of $D$ are multiples of its generators.

From a size-$s$ formal circuit for any such $P_n$, retain components through $n$ at each gate and convolve at multiplication gates. This gives a size-$O((n+1)^2(s+m+1))$ circuit for $h_n$. The pinned formal lower bound for $h_n$ is superpolynomial. Therefore **arbitrary errors from $D$ alone preserve superpolynomial formal circuit size**. This proof uses the formal arithmetic lower bound for the degree-$n$ tour polynomial. It requires no lower bound for the positive-surplus layers. [Pinned formal theorem](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean) · [Gate-wise component extraction](boolean_jet.md)

One can also apply the pinned approximate lower bound with only linear gate overhead. Over the Laurent series field, substitute $\epsilon X_e$ for each input and multiply the output by $\epsilon^{-n}$. This gives $h_n+O(\epsilon^3)$ coefficientwise, since every formal error term has degree at least $n+3$. Scaling each input used by the original circuit takes one multiplication, and the two shared constants and final scaling cost three more slots. With variables counted as input slots this uses at most $2s+3$ slots. [Definition and approximate lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L48-L61)

In particular, **every circuit with formally multilinear output that answers the zero-versus-one promise has superpolynomial size**, with no multilinearity restriction on the internal gates. Its output is already its own Boolean normal form, so its difference from $h_n$ belongs to $D$.

In the presence of $B$, the same degree argument no longer applies. For example, $h_n^2$ agrees with $h_n$ modulo $B$ and its ordinary degree-$n$ component is zero. This example identifies a failure of the extraction argument and supplies no small circuit for $h_n^2$. The question is whether polynomial-size circuits can exploit Boolean idempotence while being allowed *all* off-promise errors from $D$. The earlier oracle result shows why querying a chosen representative at low formal orders does not suffice in its black-box model. [Adaptive oracle obstruction](oracle-transfer.md)

## A quantitative lower bound with some Boolean identities allowed

For a set of arcs $A$, let $B_A=\langle X_e^2-X_e:e\in A\rangle$. Suppose a size-$s$ arithmetic circuit satisfies $P-h_n\in D+B_A$, with no restriction on its internal gates. Partially interpolate its output on the Boolean bits in $A$. This operation $R_A$ replaces every positive exponent of an $A$-variable by one and leaves every other exponent unchanged. It kills $B_A$, fixes $h_n$, and maps $D$ into $D$ because it preserves monomial support. Consequently $R_A(P)-h_n\in D$.

Using one copy of the circuit per assignment to $A$, multiply each restricted output by its assignment indicator and sum. This computes $R_A(P)$ with $O(2^{|A|}(s+m+|A|+1))$ gates. Applying the preceding formal or approximate lower bound gives, for any polynomial-size family satisfying these congruences and all sufficiently large $n$,
$$
                 |A|\ \ge\ c(\log_2 n)^{4/3}-O(\log n)
$$
for a constant $c>0$. Thus even **allowing arbitrary errors on supports containing two tours**, the identities on fewer arc bits cannot supply a polynomial-size solution to this congruence. Here $|A|$ measures the number of distinct identities sufficient for membership, independent of how many times the circuit uses a wire. The unrestricted Boolean model allows all $n(n-1)$ identities. [Partial interpolation and its circuit](boolean_jet.md) · [Lean exponent-clipping lemma](PartialLayer.lean)

## Verification

Lean proves recovery of coefficients on a downward-closed Boolean domain, the ideal membership criterion for arbitrary polynomial terms, and the equivalence for formally multilinear promise-correct outputs. It also proves that the degree-$n$ layer of any ordinary polynomial congruent to the tour polynomial modulo $D$ equals the tour polynomial. The $n+3$ threshold, circuit-size deductions, and bounded-set interpolation consequence above are written arguments. On all 4,096 four-vertex graphs the executable tests found 270 supports containing two or more tours. Independently choosing coefficients on those supports preserved all 3,826 promised answers. In the other direction, arbitrary sampled completions changed canonical coefficients only on those 270 supports. [Formal ideal and extraction](PromiseIdeal.lean) [Finite interpolation tests](promise_isolation.py) · [Boolean normal form](BooleanIdeal.lean)
