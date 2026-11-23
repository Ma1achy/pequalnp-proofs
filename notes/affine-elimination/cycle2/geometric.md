# Direction and domain obstructions for two existential bits

Write $v=(x,y)\in\mathbb F_2^{2k}$, $q(v)=x\cdot y$, $R=2^k-1$, and $O=\{q=1\}$. The relation to represent is $q=0$. A conjunction of affine clauses on $(v,w)$, where $w$ is a helper word, forbids a union of affine flats. Its existential projection must reject exactly $O$. All results below concern the whole visible relation. The unrestricted two-helper exponent remains between $k/4$ and $k/3$ on this evidence.

## How many directions can cover the odd set?

A direction is a linear subspace $U$ shared by parallel translates $v+U$. If $M$ nonempty affine flats in $T$ distinct directions cover exactly $O$, then
$$
 M\ge R,\qquad 2M\ge R+R^2/T .
$$
The second inequality detects a cost invisible in the flat count alone. In particular, a minimum cover with $M=R$ needs $R$ different directions.

**Proof.** Let $B(v,u)=q(v+u)+q(v)+q(u)$ be the nondegenerate polar form. If a translate of $U$ is monochromatic, its second differences vanish, so $U$ is isotropic and $d=\dim U\le k$. On such a $U$, $q(u)$ is linear in $u$, and a translate $v+U$ is monochromatic exactly if $B(v,u)=q(u)$ for all $u\in U$. The map $v\mapsto B(v,\cdot)|_U$ is onto $U^*$ by nondegeneracy. Hence the eligible translates occupy one coset of $U^\perp$, of size $2^{2k-d}$. There are $2^{2(k-d)}$ monochromatic cosets. All other cosets are balanced. The global difference $\#\{q=0\}-\#O$ is $2^k$ by counting for fixed $x$. Thus the number of monochromatic even cosets minus the number of monochromatic odd cosets equals $2^{k-d}$. Setting $t=2^{k-d}$ shows that exactly $t(t-1)/2$ translates of $U$ are all odd. In particular an odd flat has dimension at most $k-1$ and a direction of dimension $k-1$ has just **one** odd translate.

Let a used direction contribute $m_U$ distinct or repeated listed flats; write $a_U$ for the number of points covered by that group's union divided by $2^k$. A group covers at most $m_U 2^d$ points and at most the capacity of the odd cosets of $U$. Consequently $a_U\le m_U/t$ and $a_U\le(t-1)/2$, so
$$
 m_U\ge a_U(2a_U+1).
$$
The covered volumes satisfy $\sum_U a_U\ge |O|/2^k=R/2$. Sum the last bound and apply Cauchy–Schwarz over $T$ directions. The first inequality $M\ge R$ follows from the maximum odd flat size $2^{k-1}$.

More generally, if a subfamily of $M$ flats in $T>0$ directions covers at least $2^{k-1}D$ odd points and contains only odd points, then $2M\ge D+D^2/T$ by the same proof. No disjointness between directions is assumed.

**Construction within a factor of two.** For $0\le d<k$, fix a $(d+1)$-dimensional coordinate subspace $A$ of the $y$ bits. For each $x\ne0$, use a direction $U_x\subset A$ of dimension $d$ annihilated by $x$. When $x|_A$ is nonzero, use its kernel in $A$. Otherwise take any one of the kernels already used. Partition the odd $y$ of that $x$ into cosets of $U_x$. All nonzero functionals on $A$ occur, and different nonzero functionals have different kernels over $\mathbb F_2$. This gives
$$
 T=2^{d+1}-1,\qquad M=R\,2^{k-d-1},\qquad M(T+1)=R(R+1).
$$
Comparison with $(R+R^2/T)/2$ gives a factor of less than two, with equality to the lower bound at the two endpoints $d=0,k-1$. A direct compiler can enumerate the $x$'s, solve for one $y$ with $x\cdot y=1$, extend a basis of $U_x$ to $\ker x$, and enumerate the cosets via the added basis vectors. It needs polynomial-in-$k$ setup per $x$ and output term. For example scanning dense matrices and row coordinates gives $O((M+2^k)(k+1)^5)$ bit operations and $O((k+1)^3)$ bits besides streamed output.

## Consequence for singleton certificates in the helper square

A consistent source flat $F_j$ of helper rank two is the graph $w=f_j(v)$ on an affine visible domain $D_j$, with $f_j$ affine there. Choose an affine extension to all visible points by elimination. Let $K_j$ be the direction of each nonempty visible section $\{v:(v,c)\in F_j\}$ for fixed $c$. This is the kernel of the extended flat's projection to $w$, identified with a visible space. It is independent of the helper value, including when some sections are empty.

Let $c,\ell,p$ denote the source counts of cylinders, rank-one leaves, and rank-two leaves, and put $m=c+\ell+p$. Let
$$
 L=c+2{\ell\choose2}+4\left[{\ell\choose3}+p{\ell\choose2}+\ell{p\choose2}\right].
$$
This counts an upper bound on all nonquartet output flats from minimal pointwise certificates. A minimal square cover containing a rank-one line needs at most two other members, one for each point outside the line. Classifying square offsets gives the coefficients above. The remaining case has four singleton graphs simultaneously producing different points. [Square certificate classification](../rank_certificates.md)

Let $s$ be the number of distinct $K_j$ among the $p$ singleton graph leaves. Slicing the four graphs of a quartet at four assigned distinct helper values gives one visible flat, if consistent. Its direction is exactly the intersection of their four $K_j$. Therefore this part has a cover with
$$
 M_4\le24{p\choose4},\qquad
 T_4\le \sum_{j=1}^{\min(s,4)}{s\choose j}.
$$
Repeated directions count only once. One may substitute the actual number of distinct fourfold intersections of available direction spaces in the second bound. The $L$ other flats each cover at most $2^{k-1}$ points. If $D=R-L>0$, quartet flats must cover at least $2^{k-1}D$ odd points. Thus $T_4>0$ and
$$
 2M_4\ge D+D^2/T_4 .
$$
In particular $R=O((m+1)^3+(p+1)^2(s+1)^2)$ with absolute constants. If $m=o(2^{k/3})$, then $ps=\Omega(2^{k/2})$. Since $p\le m$, this requires $s=\omega(2^{k/6})$. If $s=O(2^{k/6})$, every encoding has $m=\Omega(2^{k/3})$, even if it uses arbitrarily many rank-two source clauses. The rank-one upper construction matches that exponent with zero rank-two leaves. This restriction concerns the directions of the fixed-helper **visible sections**, which may vary despite identical helper graph maps.

## A quartet uses three affine flats and five extra equations

On the joint visible domain $D=\bigcap_{j=1}^4D_j$, let $a=f_2+f_1$, $b=f_3+f_1$, and $c=f_1+f_2+f_3+f_4$, each with values in $\mathbb F_2^2$. The four helper labels are distinct precisely when $c=0$ and the two column vectors $a,b$ are independent. Indeed a pair of distinct nonzero vectors exhausts the nonzero helper values with its sum. For each $u\in\{(1,0),(0,1),(1,1)\}$ emit
$$
 D\cap\{c=0,\quad a=u,\quad u_1 b_2+u_2 b_1=1\}.
$$
These three flats partition the quartet's coverage. Each output needs only five scalar equations beyond $D$. The untrimmed 24-section enumeration above has a different benefit: its direction is read off immediately from four input section kernels. The three-flat projector uses fewer terms. Its output directions may differ from those 24 intersections. The two bounds can be used separately.

Since every consistent output flat lies in $O$, its codimension is at least $k+1$. Every quartet which witnesses a rejection therefore satisfies
$$
 \operatorname{codim}(D)\ge k-4.
$$
If the normalized visible domain codimensions of every four rank-two leaves sum to less than $k-4$, or if the span of all rank-two domain normals has rank less than $k-4$, no quartet can witness a rejection. In this case $R\le L$ forces $m=\Omega(2^{k/3})$. Testing the common span requires a single Gaussian elimination. A list of domain widths can also be sorted and its four largest added. Neither procedure needs an optimal-direction search.

**Sharpness.** For $k\ge4$, distribute the equations $x_5=\cdots=x_k=0$ as evenly as possible among the four domains; their intersection has codimension $k-4$. Take $f_1=0$, $f_2=(x_1,x_2)=a$, $f_3=(y_2,y_1)=b$, and $f_4=a+b+(x_3,x_4)$. Their joint coverage is exactly
$$
 x_3=\cdots=x_k=0,\qquad x_1y_1+x_2y_2=1 .
$$
It consists of three disjoint maximum-size odd flats. Each one has codimension $k+1$. The combined set has $3\cdot2^{k-1}$ points, which forces at least three odd flats even with arbitrary normalization. If an exact encoding on all visible inputs is wanted, add one helper-independent singleton for every odd point outside this region. Then inside the region the quartet is the unique minimal certificate and outside it all odd assignments are rejected. The singleton completion establishes sharpness of the local obstruction; its size is exponential.

**Rigidity at the sharp threshold.** Let $k\ge4$ and $\operatorname{codim}(D)=k-4$. If a quartet covers even one visible point, put $D_0=D\cap\{c=0\}$ and let $U$ be its direction space. Then $D_0$ has codimension $k-2$, the affine map $H=(a,b):D_0\to\mathbb F_2^4$ is surjective, and its directional kernel is $U^\perp\subset U$. On all of $D_0$ one has $q(v)=\det H(v)$. The quartet consequently covers **every odd point of $D_0$**, exactly $3\cdot2^{k-1}$ points.

Indeed $\operatorname{codim}(D_0)\le k-2$. If the affine image of $H$ has dimension at most two, the preimage of an attained invertible matrix has codimension at most $k$ in the ambient visible space, contradicting the maximum odd-flat size. If the image has dimension three it is an affine hyperplane. The six invertible binary $2\times2$ matrices affinely span the four-dimensional matrix space, as can be seen by varying each column at a fixed nonzero value of the other column. Their sum as matrices is zero: each column takes each of its three possible nonzero values twice. Hence each affine hyperplane contains an even number of the six and both sides meet the six. Any two invertible points in such a hyperplane form an affine line entirely consisting of invertibles. Its full preimage would again have codimension at most $(k-2)+(3-1)=k$. Thus $H$ is onto. A line between two distinct invertible matrices now has preimage of codimension $\operatorname{codim}(D_0)+3$. This forces $\operatorname{codim}(D_0)=k-2$.

Write $K$ for the directional kernel of $H$ on $U$. It has dimension $k-2$. On the preimage of every invertible matrix, $q=1$. For each $z\in K$, the affine derivative $q(v+z)+q(v)=q(z)+B(v,z)$ vanishes throughout these preimages. They affinely span $D_0$ because the six invertible matrices affinely span the image and every nonempty fiber is an entire $K$-coset. Thus the derivative vanishes on $D_0$. In particular $K\subset U^\perp$, and equality follows by their identical dimensions. Every $K$-coset inside $D_0$ is monochromatic, and $D_0$ is the entire affine coset of $K^\perp$ in which such cosets can occur. Applying the direction-capacity count to $K$ gives exactly $4(4-1)/2=6$ odd $K$-cosets there. The six invertible fibers are all odd and exhaust them. This proves the identity on all of $D_0$.

For an arbitrary input with $n$ visible bits and normalized domains, one quartet needs at most $4n+5$ affine rows for each of three Gaussian reductions. With dense rows, even scanning the pivot list and tracking indices gives $O((n+1)^6)$ bit operations per quartet and $O((n+1)^3)$ transient bits besides output. Constant helper maps and empty domains are included. For input already separated into domain-plus-map form, scanning all quartets costs $O((1+{p\choose4})(n+1)^6)$ bit operations. This result does not bound the original $p$ by a polynomial in $k$.

## Few visible directions across all source leaves

In this paragraph allow any $h$ and let $s\ge1$ count the distinct visible section directions $K_j$ across **all** nonempty source flats, including cylinders. If an encoding is exact, it must satisfy
$$
 m\ge 2^{\lceil 2k/s\rceil-h-2}.
$$
Set $d=\lceil 2k/s\rceil$. The sum of the codimensions of the distinct directions with codimension below $d$ is at most $s(d-1)<2k$. Their common intersection therefore contains some nonzero $u$. Delete every leaf with section codimension at least $d$. The remaining encoding and its visible projection are invariant under $v\mapsto v+u$, because every section of every retained leaf is invariant. But $q(v)+q(v+u)=q(u)+B(v,u)$ is balanced on all visible inputs by nondegeneracy. Pairing each $v$ with $v+u$ shows that every invariant predicate differs from the target on at least a quarter of the cube. Deleting a leaf can affect a visible point only in that leaf's visible projection, a union of at most $2^h$ cosets of its fixed section direction. Each deleted leaf therefore influences at most a $2^{h-d}$ fraction of the visible cube. The union bound proves the claim.

For **fixed** $s,h$ with $1\le s\le h+1$, this bound has the correct exponent. For $k\ge s$ split the product pairs into $s$ nonempty blocks of sizes differing by at most one. Use $s-1$ helper bits to require the first $s-1$ local parities to equal the corresponding bit and the last to equal their sum. Ignore any excess helpers. For each full visible assignment on a block, forbid that assignment together with a mismatching helper parity (discard the empty flat if that mismatch is impossible). Each block gives only one direction for nonempty visible sections: all changes outside the block and no changes inside. There are at most $s\,2^{2\lceil k/s\rceil}$ clauses. Enumerating block values and writing each dense affine system uses $O(s\,2^{2\lceil k/s\rceil}(k+h+1)^3)$ bit operations. For two helpers the sharp rates under limits $s=1,2,3$ are respectively $\Theta(2^{2k}),\Theta(2^k),\Theta(2^{2k/3})$. The unrestricted two-helper construction uses many directions.

**Maps alone.** A bound of four distinct helper maps or one common linear derivative is insufficient as a restriction. Split *any* two-helper source flat into its four sections $D_c\times\{c\}$, keeping only nonempty sections. This preserves its full extended forbidden set and costs a factor of at most four in clauses. After splitting, only four constant maps occur, all with zero derivative. Equivalently, the accepted visible set is an OR of four conjunctions of affine clauses, one per helper value; a list of clauses for a branch can be lifted back by coupling each with that branch's helper value. With at most three globally distinct singleton graph maps, a four-point certificate is impossible, but already four constant maps suffice to express every two-helper encoding within a constant factor. The slice transformation uses only substitution and Gaussian reduction, in polynomial bit time and output size.

## Reproduction and uncertainty

From this directory run the following command.

~~~sh
python3 geometric.py
~~~

The checker exhausts every affine flat for $1\le k\le3$ and groups them by direction. For $k=3$ there are 2,825 linear direction spaces. Exactly 1 direction of dimension 0, 63 of dimension 1 and 315 of dimension 2 have odd translates; the script verifies the predicted number of translates separately for every direction. The constructive tradeoff is checked for every permitted $d$ at $k\le6$. For $k=6$, the (flat count, direction count) pairs are $(2016,1),(1008,3),(504,7),(252,15),(126,31),(63,63)$.

The explicit three-flat quartet construction passes all 256 constant helper-label profiles and 384 seeded affine-map/domain tests up to seven visible bits (seed 77233), using direct helper-square coverage as oracle. The sharpness family gives exactly 24, 48, 96, 192 and 384 odd points for $k=4$ through 8, and all nonempty resulting flats have codimension $k+1$. Small saturated low-direction encodings are checked by existential enumeration for every $1\le s\le\min(k,3)$ and $k\le4$.

The starting extremal cover-size theorem for inner product is due to Cohen and Shinkar. The direction-capacity count follows from the same quadratic geometry with parallel classes kept separate. The restricted bounds here do not establish publication priority. [Cohen and Shinkar, The complexity of DNF of parities](https://eccc.weizmann.ac.il/report/2014/099/)
