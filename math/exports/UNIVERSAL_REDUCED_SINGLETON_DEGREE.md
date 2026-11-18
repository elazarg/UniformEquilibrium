# A four-player singleton reduction with degree minus one

Let $G$ be a real hollow four-by-four matrix. For any square matrix $A$ use the coordinatewise minimum map $m\mapsto\min(m,Am)$. Say $A$ is $R_0$ if its only homogeneous complementary solution is zero, equivalently if that map has no other zero. Write $\deg A$ for its local Brouwer degree at zero in that case. Write $i\to j$ when $G_{ji}>0>G_{ij}$.

**Selection theorem.** Assume the following numerical conditions.

* $G$ is $R_0$ of degree one, $\det G>0$, and $G^{-1}$ has a strictly positive column.
* Some pair has both entries negative. There is no directed Hamiltonian cycle with a mutually negative opposite chord and a positive entry on the other chord.
* All off-diagonals and all principal triple determinants are nonzero. At every core choice described below the two-by-two matrix $M$ is invertible.

Then one can select a row $Y$ with exactly one positive off-diagonal entry, in column $X$, such that the reduced three-by-three matrix $D$ below is $R_0$ **of degree exactly $-1$**. The choice uses just the twelve off-diagonal numbers. Testing a specified choice can give zero even when all the matrix hypotheses hold. The construction also gives an explicit formula for the degree at every eligible choice.

In a four-player quitting game the table input is $G_{ij}=r_i(\{j\})-r_i(\{i\})$ for $i\ne j$. Eliminating the continuation indifference of $Y$ and exchanging the two core roles produces this reduced matrix. Its degree is the starting index for the three-date construction. Previously a separate weighted inequality supplied the starting index as well as a later, nonlinear boundary comparison. The selection theorem discharges the index requirement on the whole generic matrix domain above, without restrictions on higher coalition rewards. The finite-amplitude boundary comparison is still required to produce an equilibrium.

## The reduced matrix

An $R_0$ matrix of nonzero degree solves every complementary target by degree invariance along the target homotopy. The all-ones target therefore requires a positive entry in each row; $R_0$ requires a negative in each column. Some $Y$ has exactly one positive supplier $X$. Otherwise every row and column has exactly one negative. A permutation consisting of a four-cycle would lack a mutually negative pair. Two negative transpositions make every principal triple determinant negative, precluding a positive inverse diagonal entry. Assume generic singleton entries from now on. Normalize row $Y$ to $G_{YX}=1$, and write $G_{Y,\{U,V\}}=-d^\top<0$ for the remaining two players. Put $a=G_{XY}$, $g^\top=G_{X,\{U,V\}}$, $e=G_{\{U,V\},X}$, $f=G_{\{U,V\},Y}$, and $H=G_{\{U,V\},\{U,V\}}$ with off-diagonals $h_U=G_{UV},h_V=G_{VU}$. Define
\[
 M=H+e d^\top,\qquad D(y,m)=(ay+g^\top m,\ fy+Mm).
\]
Here $y$ is scalar and $m$ has two coordinates. Positive scaling of a row preserves the complementary zeros and the degree by a positive-scaling homotopy. The generic assumptions used below are nonzero off-diagonals, nonzero principal triple determinants, and $\det M\ne0$ at every eligible labeling. These remove zero sets of finitely many nonzero polynomials after clearing the normalization denominators. For example $\det M$ has a nonzero $-h_U h_V$ term. Thus the exclusions in the last numerical condition have empty interior. Where the reduction is used for the quitting conjecture, positive terminal exploitability gaps persist under small reward perturbations, since any fixed player gain changes by at most twice their sup norm.

## Index at a specified core

The two diagonal entries of $M$ are $e_i d_i\ne0$ and its determinant is nonzero, so $M$ is $R_0$ by checking the three possible nonempty active supports. A homogeneous complementary solution for $D$ with $y=0$ therefore vanishes. If $y>0$ then $m=0$ is impossible since $a\ne0$. Taking $x=d^\top m>0$ lifts any remaining solution to a nonzero solution for $G$. Hence $D$ is $R_0$ as well.

Set $z=-H^{-1}e$. The reduced degree is
\[
 \deg D=
 \begin{cases}
 -1-\operatorname{sgn}(h_U h_V),& z>0,\ d^\top z<1,\ g^\top z>0,\\
 -1,&\text{otherwise}.
 \end{cases}
\]
To compute it, a complementary problem at offset $b$ asks for $m\ge0, Am-b\ge0, m_i(Am-b)_i=0$. At a regular solution its index is the sign of the determinant of its active principal submatrix: the remaining rows are identity rows in the minimum map. For an $R_0$ matrix, solutions stay bounded along bounded offset homotopies by normalization, so the sum of the indices at any regular offset is its homogeneous degree. Generic offsets avoid ties and singular active solutions: for each finite support either its active target is in a proper linear subspace, or the candidate solution is linear in the target and a tie imposes a further equality.

Take positive generic $v,t_U,t_V$ with $t+ev>0$, and a sufficiently large regular $u>0$. Use offsets $(u,v,t+ev)$ for $G$ and $(u,t)$ for $D$. The two offset families admit simultaneously regular choices since the first is an invertible linear parametrization and the second a projection. For generic fixed $t,v$, all sufficiently large $u$ avoid the finite exceptional hyperplanes. For $G$, $x\ge v+d^\top m>0$. If $y>0$ then $x=v+d^\top m$, and the solutions with $y>0$ for the two problems are in bijection. Interchanging the $X,Y$ equation rows and eliminating the unit $x$ pivot in the $Y$ row gives the active submatrix of $D$; the signs of their indices are opposite.

For $D$ any $y=0$ solution would require $g^\top m\ge u$ with $m$ solving the fixed $M,t$ problem. These $m$ are bounded, ruling this out. For $G$ with $y=0$, the $X$ equation gives $g^\top m=u$ and therefore $x\to\infty$ along any sequence of these solutions as $u\to\infty$. With a single active twin $i$, the equation $e_i x=t_i+e_i v$ would bound $x$. No active twin is impossible since $u>0$. With both active,
\[
 m=z(x-v)+H^{-1}t,\qquad g^\top m=u,\qquad x\ge v+d^\top m .
\]
The two components of $z$ are nonzero. Also $\det M=\det H(1-d^\top z)$ and $\det G_{XUV}=\det H\,(g^\top z)$, so both threshold equalities are excluded. These equations now give one solution for all sufficiently large $u$ precisely under the three strict inequalities in the displayed degree formula. Its index is $\operatorname{sgn}(\det G_{XUV})=-\operatorname{sgn}(h_Uh_V)$. Subtracting the contribution of the positive-$y$ solutions from the degree-one count proves the formula.

## Why at least one core has degree exactly minus one

Suppose every eligible choice is exceptional in the index formula. For each, the twins must satisfy $e_i h_i<0$ and at least one component of $g$ must be positive. These are necessary sign conditions for $z>0$ and $g^\top z>0$, even in the index $-2$ case. Only five sign patterns up to simultaneous relabeling satisfy them for every eligible choice and avoid the specified sign exits.

The following is an exhaustive reproducible count. Encode a positive in column $j$ by bit $2^j$ of its row mask. Use every off-diagonal assignment and identify patterns by simultaneous permutations of the four labels. The representatives need not be the least elements of their orbits.
```
for each of the 4096 assignments of twelve signs:
    discard if any row has no positive or any column has no negative
    discard if no pair is negative in both directions
    for each ordering (i,j,k,l) of the four labels:
        if i→j→k→l→i and the chord ik is negative in both
            directions and the chord jl has a positive entry: discard
    form all (X,Y) with X the only positive supplier in row Y
    discard if this list is empty
    for each listed (X,Y), with other labels U,V:
        discard if either G_UX G_UV or G_VX G_VU is positive
        discard if both G_XU and G_XV are negative
    retain the assignment
```

| Positive column masks in rows 0 through 3 | Number of labeled assignments |
|---|---:|
| $(8,8,3,6)$ | 24 |
| $(8,8,3,3)$ | 12 |
| $(8,8,3,7)$ | 12 |
| $(8,4,9,3)$ | 24 |
| $(8,4,3,3)$ | 12 |

The table can be verified by generating the 24 relabelings of each displayed representative, removing repetitions, and comparing the union with the retained assignments. The empty-list case was disposed of by the negative-permutation argument above.

In the first three patterns rows 0 and 1 have sole positive supplier 3. Both see 2 negatively. With $Y=0$, the label-2 term of $d^\top z$ is $|G_{02}|G_{13}/(G_{03}|G_{12}|)$. With $Y=1$ the label-2 term is its reciprocal. If both cores were exceptional, these terms would both be strictly less than one.

In either remaining pattern write
\[
 G=\begin{pmatrix}0&-a&-b&c\\-d&0&e&-f\\g&\sigma h&0&-\sigma i\\j&k&-l&0\end{pmatrix}
\]
with twelve strictly positive scalar magnitudes and $\sigma=\pm1$. The two cores have $(X,Y)=(3,0),(2,1)$. If both were exceptional, put $E=ce-bf$. For the first core $z=(i/h,f/e)$, so $d^\top z<1$ and $g^\top z>0$ in the core notation give $E>aei/h$ and $eik>fhl$. For the second $z=(l/j,b/c)$, giving $E>cdl/j$ and, when $\sigma=1$, $cgl>bij$. This computation uses normalization of each recipient row by its own positive supplier.

Let $A=\operatorname{adj}(G)$. Since $E>aei/h>afl/k$, in either pattern $A_{02}=afl-kE<0$. For $\sigma=1$, three more negative entries are
\[
 A_{00}=-eik+fhl,\qquad A_{11}=bij-cgl,\qquad A_{13}=bdi-gE .
\]
For the last use $gE>gcdl/j>bdi$. For $\sigma=-1$ the other three are
\[
 A_{30}=dhl-egk-ehj,\qquad A_{11}=-bij-cgl,\qquad A_{13}=-bdi-gE .
\]
Here $ce>E>cdl/j$ gives $ej>dl$. Thus every adjugate column has a strictly negative entry. Since $\det G>0$, this contradicts the assumed positive inverse column. In all five patterns at least one core is nonexceptional, proving the stated selection.

## A boundary check

A particular eligible choice really can have zero degree. Take the matrix with rows $(0,-10,9,-1),(-2,0,-11,12),(-13,8,0,2),(7,5,-9,0)$. Its determinant is $727$ and inverse column 1 is $(18,9,19,81)/727$. All nonempty principal blocks of size at least two are invertible and each column has a negative entry. At target $(101,203,307,411)$ solving each active principal system and checking the outside slacks leaves only support $023$, with solution $(1331,8906/9,8805)$ and active determinant $9$, so $G$ has degree one. For $Y=1,X=3$ the formula gives $z=(2/13,1/9)$, $d^\top z=179/1404$, $g^\top z=1/13$ and $h_Uh_V<0$. The reduced degree is zero. For $Y=0,X=2$ instead $d^\top z=227/108>1$, giving degree $-1$. This is an example about the choice of core.

In applications each twin may have two scheduled variables, one for each of two dates. Duplicate its row and column so they act on the sum of its two variables. A homogeneous zero then gives one in the reduced problem by summing the nonnegative duplicate variables, hence the duplication preserves $R_0$. At a regular target give the second copy of each twin a strictly smaller target. The lower-target copy can never be active, and the remaining solutions have unchanged active principal determinants. The five-variable starting index is therefore also $-1$. No strategic witness is an input or output of this linear selection.

The checked declaration `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean` supplies the original degree-one condition from a hypothetical equilibrium failure. For formalization the selection result takes the remaining numerical filters as explicit hypotheses, independently of their game-semantic proofs. The two small exact computations are the five sign orbits and the regular-support census for the example. The proof gives a global initial index for a continuation construction, not a global absence of zeros on the boundary of that construction or a proof of arbitrary four-player uniform-equilibrium existence.
