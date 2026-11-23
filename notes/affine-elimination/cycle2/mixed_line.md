# Five affine clauses suffice for three product pairs and two helpers

The exact minimum is **five** for a conjunction of explicit affine clauses with two existential helper bits which projects pointwise to $x_1y_1+x_2y_2+x_3y_3=0$. The four-clause lower bound follows from the independent helper-square certificate classification: four input flats produce at most six projected flats, while the exact odd-inner-product cover number is seven. The construction below attains five. One unrestricted helper requires six, by the separate incidence argument. [Finite lower bounds](synthesis.md) · [Unassisted bound of Cohen and Shinkar](https://eccc.weizmann.ac.il/report/2014/099/download/)

Write $w=(h,t)$, $A=(x_1,x_2)$, $B=(y_2,y_1)$ and $\tau=x_3$. Forbid the following five affine flats. Each one is the falsifying set of a clause containing just two affine literals.

| Flat | Simultaneous equations defining the forbidden set |
|---|---|
| 1 | $w=(0,0)$ |
| 2 | $w=A$ |
| 3 | $w=B$ |
| 4 | $w=A+B+(0,\tau)$ |
| 5 | $\tau=1,\quad h=A_1+B_1+y_3$ |

The first four clauses have helper rank two, each forbidding one word at every visible input. The fifth has helper rank one and forbids an entire vertical line when active. Put $d=\det(A,B)=A_1B_2+A_2B_1$.

If $\tau=0$, the forbidden words are precisely the span of $A,B$. There is no surviving helper if and only if they span the square, or $d=1$.

If $\tau=1$, consider the multiset $M=(0,A,B,A+B+(0,1))$. Its four entries sum to $(0,1)$. Exactly two labels have odd multiplicity. Indeed an even number have odd multiplicity, and both the empty label set and all four labels sum to zero. The two odd labels differ by $(0,1)$, so they fill a vertical line. The other parallel line is incomplete, since filling the whole square with four terms uses each exactly once and yields sum zero. Let $\lambda$ be the first coordinate of the complete line. It equals the parity of the number of occurrences of $(1,1)$ in $M$, so
$$
\lambda=A_1 A_2+B_1 B_2+(A_1+B_1)(A_2+B_2+1)=d+A_1+B_1.
$$
Adding a forbidden vertical line with first coordinate $h_*=A_1+B_1+y_3$ covers the whole square exactly when it is the opposite line, namely when $h_*+\lambda=d+y_3=1$. Combining the cases, absence of a surviving witness is exactly $d+\tau y_3=1$. This proves pointwise correctness.

The point labels and the active line exchange information through their actual coordinates. For example, on the visible all-zero assignment the three nonzero helper words work, but the all-zero witness never works. The construction need not provide a unique extension. The number of helpers and the explicit-conjunction representation are fixed in this result.

## Checks and arithmetic costs

The coordinates in increasing bit order are $x_1,x_2,x_3,y_1,y_2,y_3,h,t$, and each packed row stores its right side in bit zero. The five raw row pairs are $(128,256),(130,260),(160,272),(162,284),(9,226)$. Input size in the shared dense codec is 117 bits. Each coefficient is one bit. To reproduce the direct check and both projection traces, run from the research directory:

~~~sh
python3 cycle2/mixed_line.py > cycle2/mixed_line.json
~~~

The direct verifier compares the flattened equations with an independent four-word multiset calculation on all 256 lifted assignments. The counts of visible inputs with 0, 1, 2, 3 surviving words are respectively 28, 12, 22, 2. For each input clause it records an odd visible point and word on which only that clause fails, so deleting the clause would change the existential projection.

The general pairwise flat projector was also checked at both intermediate stages in both helper orders against explicit extension enumeration, for 1,024 comparisons. The order $h,t$ produces 5, 10, 15 normalized flats; $t,h$ produces 5, 7, 9. The same final predicate has a minimum unassisted description of seven clauses, showing residual redundancy after these implemented local simplifications. The JSON retains row sizes and operation counts at each stage. This construction is fixed-dimensional. Its correctness by itself supplies no asymptotic upper bound beyond the previously known balanced-block construction.
