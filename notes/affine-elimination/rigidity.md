# Equality forces affine witness labels in the block-local encoding

Take $B\ge2$ disjoint visible blocks. Block $i$ has $2b_i$ bits $(x_i,y_i)$, where $b_i\ge1$, and parity $q_i=x_i\cdot y_i$. The target accepts exactly the assignments with $\bigoplus_i q_i=0$. An encoding has $h$ existential Boolean helper variables $w$ and is an explicit conjunction of affine clauses. Each individual forbidden flat may involve all helpers and **at most one visible block**. More precisely, its set of points is a cylinder in all other visible blocks. There is no restriction on its codimension or on the rank of its helper coefficients. Helper-only flats can be counted separately. These hypotheses concern a specified partition of the visible variables.

**Theorem.** Every such encoding needs $h\ge B-1$. At $h=B-1$ the minimum number of clauses is $\sum_i2^{b_i}$. If this minimum is attained, the bijection from helpers to attainable block-parity vectors is affine. In each block, exactly one forbidden flat has a helper projection equal to half the helper cube. The other $2^{b_i}-1$ flats in that block project onto the full helper cube.

### From rectangles to the clause bound

For a fixed helper assignment, the allowed visible set is either empty or a Cartesian product $\prod_i D_i(w)$ of nonempty local sets. If a factor contained points with different block parities, changing just that coordinate block would change the parity of the whole assignment while both points remain allowed. Every nonempty rectangle thus has one even parity vector. Every even vector occurs because each local parity has both levels nonempty. This proves $2^h\ge2^{B-1}$.

At equality of the witness counts, all helper assignments are used, with exactly one $w$ per even pattern. Write $p_i(w)$ for its $i$th bit. The rectangle at $w$ must equal the **entire** product of the levels $q_i=p_i(w)$. Any missing point in that product could only be represented by a second witness of the same pattern. In particular the block-$i$ clauses by themselves describe the relation $q_i=p_i(w)$ on all $(x_i,y_i,w)$, since the other factors are nonempty at each $w$. Every helper-only constraint is true at every $w$. Each label $p_i$ is balanced on helper assignments, because exactly $2^{B-2}$ even patterns have bit $i$ set.

Fix a block of size $b=b_i$ and choose any $w_0,w_1$ with $p_i(w_t)=t$. Substitute $w=w_0+t(w_0+w_1)$. The block must represent $q=t$ using its original number of clauses, and each restricted forbidden set is again an affine flat or empty. The bad graph $t=1+q$ has $2^{2b}$ points. Each flat in this graph has size at most $2^b$. Indeed its projection to the visible coordinates is injective and the lifted $t$ is affine on the projected flat. Therefore the polar form $x\cdot y'+x'\cdot y$ vanishes on the flat's direction, which has dimension at most $b$ by nondegeneracy. This gives the per-block lower bound $m_i\ge2^b$.

For attainment label the first $B-1$ blocks by separate helper bits, and the last by their sum. In block $i$, for each $s\in\mathbb F_2^{b_i}$ forbid the flat $x_i=s,\;s\cdot y_i+p_i(w)=1$. These flats exactly describe a mismatch in that block and give a unique satisfying witness whenever the target is true. Summing over independent blocks attains the claimed count.

### Proof of rigidity at equality

With exactly the stated total number of clauses, each block has exactly $2^b$, and no clause is spent on a helper-only or empty flat. On the line of **any** opposite-label pair, the $2^b$ restricted bad flats cover $2^{2b}$ points with at most $2^b$ points each. They are all disjoint and each has exactly $2^b$ points there.

Fix one original bad flat $F$ of this block. Its helper image $P$ is affine, and every nonempty visible fiber of $F$ has the same cardinality $d$, since each fiber is a translate of the kernel of the linear projection on the direction space. For every opposite-label pair,
$$
 d\big(\mathbf1_P(w_0)+\mathbf1_P(w_1)\big)=2^b .
$$
There are just two possibilities. With $d=2^{b-1}$ both endpoints of every pair belong to $P$, so $P$ is all of helper space. With $d=2^b$, one endpoint of every pair belongs to $P$. Holding an endpoint fixed shows that membership in $P$ is constant on each label class, with opposite values on the two classes. Thus $P$ equals one label class.

The odd level $q=1$ contains no flat larger than $2^{b-1}$. A direct proof uses the nondegenerate polar form to bound dimensions by $b$. If an odd flat had dimension exactly $b$, every other coset of its direction would be balanced, making odd points a majority. Counting over fixed nonzero $x$ gives only $(2^b-1)2^{b-1}$ odd points. Details of the coset argument and its literature attribution are in the companion proof. [Inner-product flat-cover theorem](obstruction.md)

Consequently a size-$2^b$ fiber can occur only when the *bad* level is $q=0$, i.e., $p_i(w)=1$. Disjointness on opposite-label lines implies disjointness at every helper assignment. The two levels differ in cardinality by exactly $2^b$. Every full-helper-support flat contributes the same number of points to either label. Each size-$2^b$-fiber flat contributes exactly $2^b$ points to the larger level and none to the smaller one. The level difference therefore forces exactly one of these flats. Its image $P=\{w:p_i(w)=1\}$ is an affine flat containing half the helper assignments. Hence it is a hyperplane, and $p_i$ is a nonconstant affine Boolean function. This applies to each block and proves the asserted affine bijection. Conversely, every affine bijection to the even patterns attains the minimum by the same fixed-$x_i$ construction.

### Exact cost of a prescribed quadratic labeling

Still assume $h=B-1$, and prescribe a bijection to even parity patterns. If each label $p_i$ has multilinear degree at most two and its polar form has rank $2r_i$, the minimum for this particular labeling is exactly
$$
 \sum_i 2^{b_i+r_i}.
$$
This result permits arbitrary coefficient ranks in individual block-local clauses.

To see this, split the alternating polar form of a balanced label into $r$ symplectic pairs and a radical. One can construct the basis by taking vectors with pairing 1, adding their multiples to the other basis vectors to clear the pairings, and repeating on their orthogonal complement. In these coordinates the label equals a sum of $r$ pair-products plus a linear form and a constant, since its difference with the pair-products has zero polar form. Translations absorb the pair-variable linear terms by $(u+\beta)(v+\alpha)=uv+\alpha u+\beta v+\alpha\beta$. The remaining linear form on the radical must be nonzero. If it vanished, the difference between the counts of zeros and ones would have magnitude $2^{h-r}$, obtained by multiplying the bias sum of each product pair ($3-1=2$) and each unused bit ($2$). Balancedness excludes this. Take the radical linear form (and constant offset) as one helper coordinate $z$. The label now reads $z+\sum_{j=1}^r u_jv_j$.

Together with the $b$ visible products, the violating graph on the active coordinates is therefore $z=1+q_{b+r}$. Fix all unused coordinates to zero to obtain the graph lower bound $2^{b+r}$. For the matching upper bound, fix the vector of first operands in the $b+r$ pairs and impose the resulting single affine equation on $z$ and the second operands. Lifting these flats back through the block-specific helper change of basis gives a cover in the original variables. Different blocks can use different changes of basis to derive their clauses, since the lifted outputs refer to the same original helpers.

Given dense quadratic coefficients, basis construction, coefficient substitution, and recovery of the inverse transformation use polynomial bit time. For instance one can do $O((h+1)^2)$ elementary basis changes, rescanning $O((h+1)^2)$ coefficient bits after each operation. Even allowing an extra scan factor for addressing gives $O((h+1)^6)$ bit operations for preprocessing one block. Each emitted flat uses at most $b+r+1$ original-coordinate rows of at most $2b+h+1$ bits. Explicit substitution by dense matrix-vector multiplication, writing the rows, and incrementing the operand-pattern counter take at most $O((2b+h+1)^4)$ bit operations per flat. This compilation cost assumes the quadratic helper labeling is given. The proof uses no minimization oracle.

### Four blocks and three helpers

Let $B=4$, $b_i=1$ and $h=3$. Labeling by $w_1,w_2,w_3,w_1+w_2+w_3$ takes exactly eight clauses. For a second bijection put $p_1=w_1+w_2w_3$, $p_2=w_2$, $p_3=w_3$ and $p_4=p_1+p_2+p_3$. The first three labels recover the helpers uniquely. The first and fourth each have polar rank two, and the others have rank zero. The four exact local counts are $4,2,2,4$, totaling **12** for this prescribed labeling.

Run the independent verifier with the following command from this directory.

~~~sh
python3 rigidity_checks.py
~~~

For each local relation the verifier scans all 2,451 distinct nonempty affine flats of the five-bit space $(x,y,w_1,w_2,w_3)$ and tests containment in the sixteen violating assignments. It also constructs the proposed cover, checks every member against the flat inventory, and verifies disjointness, coverage and the volume lower bound. For the linear labels the largest contained flats each have eight points. For the nonlinear labeling their sizes are $4,8,8,4$, respectively. The finite check uses eight inventories of containment tests over the same list. Each test compares at most 32 five-bit points. The proof above gives the counts for arbitrary block sizes under its stated hypotheses.

The equality and rigidity results concern this block-local model at its minimum witness count. Their priority in the literature is unverified. Sharing a clause across visible blocks or adding extra helpers changes the rectangle argument.
