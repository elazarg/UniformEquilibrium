# The fourth order test for the reciprocal pair with two distinct dependents

Let a four-player quitting table have native singleton comparisons $G_{ij}=r_i(\{j\})-r_i(\{i\})$. Suppose each row has one positive foreign comparison. Two players name one another as their positive donor, and each of the other players names a different member of this pair. Then the native all-four-finite order test passes at rank four, for all twelve singleton magnitudes and every choice of the 44 nonsingleton rewards. It also passes if any subset of the strict comparisons is replaced by zero. The signed test follows with arbitrary own-singleton levels. This is one entire strict orbit among the 21 in the singleton census. Its closure contains two of the 46 surviving one-tie orbits, three of the 39 two-tie orbits and one of the ten three-tie orbits. The theorem concerns the fourth order test. The conjecture requires unbounded ranks. [Order tests](../notes/CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md) · [Sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)

## Two full positive columns and two negative defaults

Label the reciprocal pair $1,3$ and the two dependents $0,2$, so the strictly signed matrix is
$$
G=\begin{pmatrix}
0&-a&-b&c\\
-d&0&-e&f\\
-g&h&0&-i\\
-j&k&-l&0
\end{pmatrix},\qquad a,b,c,d,e,f,g,h,i,j,k,l>0.
$$
In the census convention, minimizing over simultaneous permutations of rows and columns gives row masks $(2,1,1,2)$. In the displayed labels the six surviving weak orbits in this closure can be represented by zeroing the following sets of entries: $\{10\},\{02\},\{02,10\},\{02,32\},\{02,20\},\{02,10,20\}$, where $ij$ denotes the entry in row $i$ and column $j$. These follow by setting entries to zero and retaining the faces in the published census up to simultaneous relabeling.

At fixed rank the all-finite obedience constraints are weak inequalities on a compact finite-order simplex, continuous in the rewards. Thus failure is open in the matrix with the higher rewards fixed. We may assume every principal triple is nonsingular by a strictly signed perturbation. If the native absorbing infimum were zero, the negative singleton comparison supplies four-finite approximations and passage at every rank. Otherwise the strict inverse-column theorem gives $\det G>0$ and a positive column of $G^{-1}$, and the singleton complementarity map has degree one. [Four-finite completion](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md) · [Positive inverse column](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md) · [Degree test at positive axes](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md#degree-at-a-positive-inverse-column)

Eliminate the core variables on rows 1,3. On a target supported on 0,2 their equations are $x_3=(dx_0+ex_2)/f$ and $x_1=(jx_0+lx_2)/k$. The resulting matrix on 0,2 is
$$
M=\begin{pmatrix}A&B\\C&D\end{pmatrix}
=\begin{pmatrix}
cd/f-aj/k&ce/f-al/k-b\\
hj/k-g-id/f&hl/k-ie/f
\end{pmatrix}.
$$
Its determinant is $\det G/(-fk)<0$, and the principal $0,2$ block of $G^{-1}$ is $M^{-1}$. We show that **both** dependent columns of $G^{-1}$ are positive.

If the given positive column has index 0, its two dependent coordinates give $D<0$ and $C>0$. For target $e_0$ the degree test on the reciprocal pair $1,3$ forces $\det G_{013,013}>0$ since $G_{13},G_{31}>0$ and $G_{10},G_{30}<0$. Thus $(G^{-1})_{22}>0$, giving $A<0$. The negative determinant of $M$ gives $B>0$.

If instead the positive column has index 1, the degree test on $2,3$ gives $\det G_{123,123}>0$ since $G_{23},G_{32}<0$ and $G_{21},G_{31}>0$. Hence $D<0$. The two positive dependent coordinates of this column solve $M(x_0,x_2)^T=(-c/f,i/f)^T$. The first solution coordinate has sign equal to $Dc+Bi$, hence $B>0$. The first equation now gives $A<0$ and $\det M<0$ gives $C>0$. The simultaneous relabeling $(0\;2)(1\;3)$ treats positive columns at 2 or 3. In every case $M^{-1}$ is strictly positive, and reconstructing the two core coordinates makes both claimed full columns positive.

The determinant of $M^{-1}$ is negative. Hence $((G^{-1})_{20}/(G^{-1})_{00})((G^{-1})_{02}/(G^{-1})_{22})>1$. For at least one dependent axis the other dependent has more weight than the axis owner. Relabel by the same swap if necessary. Normalize $y=G^{-1}e_0/\sum_i(G^{-1})_{i0}$ so $y_2\ge y_0$.

On the triple $0,1,3$ the probability vector proportional to $(1,j/k,d/f)$ has native payoff $w_0=A/(1+j/k+d/f)<0$, $w_1=w_3=0$ and $w_2=C/(1+j/k+d/f)>0$. On $2,1,3$ take masses proportional to $(1,l/k,e/f)$. Now $w_2=D/(1+l/k+e/f)<0$, $w_1=w_3=0$ and $w_0>0$. These defaults and their coordinatewise positive-part reply caps are realized in the limit by diffuse independent races on the indicated triples. In each case every occupied neutral owner has zero payoff from quitting and from waiting, the negatively paid owner's best cap is zero, and the positive outsider attains its passive payoff by waiting. The all-finite completion uses the occupied rivals for late embedding of the unused clock. [Diffuse defaults and the hidden continuation](EVERY_FOUR_PLAYER_QUITTING_GAME_PASSES_THE_THIRD_ORDER_TEST.md)

For the two respective charged owners the helper comparisons are $-a$ at 1 and $-i$ at 3. The ratios of their magnitudes to the absolute charged default are
$$
R_0=\frac{a(1+j/k+d/f)}{aj/k-cd/f}>1+k/j>1+y_0/y_1,\qquad
R_2=\frac{i(1+l/k+e/f)}{ie/f-hl/k}>1+f/e>1+y_2/y_3.
$$
The last inequalities follow from the two core equations for $y$. The rank-four hidden continuation theorem passes the all-finite test if either ratio is at least four. Therefore a failed game would have
$$
 y_0\le y_2,\qquad y_0\le3y_1,\qquad y_2\le3y_3.
$$
These inequalities and $y\ge0$, $\sum y_i=1$ define a tetrahedron. The four nonnegative parameters $y_0,y_2-y_0,y_1-y_0/3,y_3-y_2/3$ give directly its rays in homogeneous coordinates $(3,1,3,1),(0,0,3,1),(0,1,0,0),(0,0,0,1)$.

## Order priors throughout the tetrahedron

Fix an observation of the training dates. An order word inserts all sixteen validation labels at distinct finite dates disjoint from these training dates, with unit count discrepancy at every cut. For each monitored date $t$ and tested recipient $i$ let $F_{ij}(t)$ be the prescribed probability that $j$ exits first minus the probability that $j$ exits before $t$ when $i$ is removed. The same definition at $t=\infty$ gives both Never and Late. The assigned-minus-offered payoff for $i$ is $\sum_{j\ne i}G_{ij}F_{ij}(t)$ since quitting without an earlier rival earns the native own payoff zero.

Let $p$ be the sole positive donor of recipient $i$. The three nonaxis rows satisfy $\sum_j G_{ij} y_j=0$ and row 0 has a strictly positive weighted sum. The balanced portion of each row is a nonnegative sum, indexed by its two negative donors $n$, of $y_n e_p-y_p e_n$: the coefficient of the $n$th vector is $-G_{in}/y_p$. The surplus in row 0 is a positive multiple of $e_3$. Consequently a prior suffices whenever its mean differences obey
$$
 y_n F_{ip}(t)-y_p F_{in}(t)\ge0\quad\text{for all }i,n,t,\qquad F_{03}(t)\ge0\quad\text{for all }t .
$$

The attached checker verifies a covering of the displayed tetrahedron by smaller tetrahedra. For each small tetrahedron it finds four priors with a common training observation, one per vertex $z_u$. At a parameter $y=\sum_u\lambda_u z_u$ it uses the prior $\sum_u\lambda_u\pi_u$. For each balanced row generator and deadline, write $H(\pi,z)$ for its expected difference. Bilinearity gives the gain at $y$ as
$$
 \sum_{u,v}\lambda_u\lambda_v\{H(\pi_u,z_v)+H(\pi_v,z_u)\}/2 .
$$
Every coefficient is nonnegative. Every word used separately has $F_{03}(t)\ge0$. These bounds prove every required conditional obedience inequality at the actual parameter, including the surplus of row zero.

The certificate lists rational vertices, schedules and tetrahedra. Exact determinant comparisons verify containment, pairwise disjoint interiors and equality of summed volumes, so the cover includes every boundary point. A numerical unit-flow program proposes a finite mixture of complete order paths at each vertex. Verification rounds its weights to integers, checks the count discrepancy at every cut, and enumerates all $4^4=256$ independent validation-label choices on each complete word. It then compares the symmetric vertex coefficients by integer products. The 23 tetrahedra use 1,191 weighted words across their vertex priors and 16,880 exact Bernstein inequalities. Only the exact checks enter the proof. With four finite clocks every unilateral replacement still faces a finite exit, so row translation preserves all inequalities. Closedness in the original rewards proves the weak-sign assertion. [Exact tetrahedron cover and order verification](../experiments/RANK_FOUR_RECIPROCAL_CORE.py)
