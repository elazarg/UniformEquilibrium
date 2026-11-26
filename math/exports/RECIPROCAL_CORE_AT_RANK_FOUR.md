# The fourth order test for sign classes with a reciprocal pair

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

## A chain into a reciprocal pair

Suppose each of four recipients has a unique positive foreign singleton comparison. Two recipients name one another, a third names one of that pair, and the fourth names the third. At every choice of the twelve strict singleton magnitudes, all 44 higher rewards and all signed own levels, the all-four-finite order test passes at rank four. Passing is closed in the table, so arbitrary subsets of these strict comparisons can be replaced by ties. In the sign census the strict orbit is $(2,1,1,4)$. Its closure contains four of the surviving one-tie orbits, six two-tie orbits, and three three-tie orbits. A uniform equilibrium requires unbounded ranks.

Label the positive donors $(3,3,1,0)$ in row order, so the singleton comparison matrix is
$$
G=\begin{pmatrix}
0&-a&-b&c\\
-d&0&-e&f\\
-g&h&0&-i\\
j&-k&-l&0
\end{pmatrix},\qquad a,b,c,d,e,f,g,h,i,j,k,l>0.
$$
A failure of the all-finite test persists in an open neighborhood, by compactness of the finite order simplex. We can assume all principal triples nonsingular. A failed game has positive native absorbing infimum, since the negative comparisons furnish four-finite completion. Thus $\det G>0$, some column of $G^{-1}$ is positive, and the singleton minimum map has degree one. We use the positive-axis degree test and the private hidden continuation at a charged triple default from the [positive columns and negative defaults](#two-full-positive-columns-and-two-negative-defaults).

For targets supported on $1,2$, eliminating rows $0,3$ gives $x_0=(kx_1+lx_2)/j$, $x_3=(ax_1+bx_2)/c$ and the two-by-two matrix on coordinates $1,2$
$$
M=\begin{pmatrix}A&B\\C&D\end{pmatrix}=
\begin{pmatrix}
fa/c-dk/j&fb/c-dl/j-e\\
h-gk/j-ia/c&-gl/j-ib/c
\end{pmatrix}.
$$
Here $D<0$, $\det M=-\det G/(cj)<0$, and $(G^{-1})_{\{1,2\},\{1,2\}}=M^{-1}$. Axis 0 cannot be a positive column, since its diagonal cofactor is $-eik-fhl<0$. If axis 1 is positive, $C>0$ and the degree test on the positive reciprocal pair $0,3$ forces $\det G_{013,013}=-cjA>0$. Hence $A<0$, and $B>0$ by the determinant. If axis 2 is positive, the second column of $M^{-1}$ gives $B>0$ and $A<0$, then $C>0$. If axis 3 is positive, the degree test on the negative reciprocal pair $0,1$ again forces $\det G_{013,013}>0$, since both see 3 positively. Now the two positive leaf coordinates satisfy $M(x_1,x_2)^T=(d/j,g/j)^T$. Its two negative diagonal entries imply $B,C>0$. Thus $M^{-1}>0$ entrywise in every case. The two core equations make both full columns 1 and 2 strictly positive. Their principal inverse determinant is negative. Consequently, on at least one of these axes $m$, the normalized vector $y=G^{-1}e_m/\sum_r(G^{-1})_{rm}$ has $y_m\le y_{3-m}$.

The triple default on $1,0,3$ with masses proportional to $(1,k/j,a/c)$ gives negative payoff $A/(1+k/j+a/c)$ in row 1, zero on the two helpers, and positive payoff $C/(1+k/j+a/c)$ at the outsider 2. On $2,0,3$ use masses proportional to $(1,l/j,b/c)$ to give the corresponding values $D/(1+l/j+b/c)$ at 2 and $B/(1+l/j+b/c)$ at 1. Both defaults are implementable by diffuse races. With the helper 0 at the first default and the more negative of helpers 0,3 at the second, the two ratios of helper loss to charged default loss satisfy
$$
R_1=\frac{d(1+k/j+a/c)}{dk/j-fa/c}>1+j/k>1+y_1/y_0,\qquad
R_2=\frac{\max(g,i)(1+l/j+b/c)}{gl/j+ib/c}\ge1+\frac1{l/j+b/c}>1+\frac{y_2}{y_0+y_3}.
$$
Either ratio at least four already passes the rank-four hidden continuation test. A failure therefore satisfies $y_1\le 3y_0$, $y_2\le3(y_0+y_3)$.

For each axis $m$ use the order-word score differences $F_{ip}(t)$ of the reciprocal-pair construction. Every word is restricted to have $F_{m,p(m)}(t)\ge0$. With the sole positive donor $p(i)$ in each row, the only further inequalities are $y_n F_{i,p(i)}-y_{p(i)}F_{in}\ge0$ for both negative donors $n$ and all observed dates, Late and Never. Nonaxis rows are balanced at $y$, and the axis surplus has the same sign as its positive donor. [Order-word construction](#order-priors-throughout-the-tetrahedron)

The [finite certificate](../experiments/RANK_FOUR_CHAIN.py) checks these inequalities by affine vertex priors with the same training observation and nonnegative bilinear Bernstein coefficients. It relabels each selected axis to 0 and its positive donor to 3, so the flow proposal, independent label enumeration, exact cover check and rational rescoring are shared with the reciprocal-pair verifier. To obtain the joint volume of the two axis domains set $t=y_1$, $z=y_2$. The available interval in $y_0$ has length $1-t-z-t/3$. The base on $t\le z$ is the triangle with vertices $(0,0),(0,3/4),(3/7,3/7)$, with respective heights $1,1/4,0$. On $z\le t$ the triangle is its reflection, with heights $1,0,0$. Each triangle has area $9/56$. Six times the total volume is $45/112+9/28=81/112$. All certificate tetrahedra lie on their stated axis side and have pairwise disjoint interiors. Equality of summed and domain volumes gives the closed cover including each tie face, by limits within the appropriate side. The 50 tetrahedra use 2,885 weighted words across their vertex priors, giving 40,080 exact Bernstein inequalities. Every tested exit uses only a singleton reward. Four finite clocks protect all original signed row translations.

## A reciprocal-core owner with an additional positive donor

Keep the displayed reciprocal-core matrix but change $G_{32}$ to $+l$. In these labels the positive donors in the four rows are respectively $\{3\},\{3\},\{1\},\{1,2\}$. This is witness 3, with canonical masks $(2,4,3,4)$. Every such matrix, with arbitrary strictly signed magnitudes, passes the fourth order test for every completion of its 44 higher rewards. All weak specializations and arbitrary own-singleton levels are included.

The negative pair $01$ satisfies $G_{03},G_{13},G_{32}>0>G_{23}$ and $G_{02}<0$. Thus failure of the fourth order test would imply $\det G>0$ and $G^{-1}e_2>0$, by the positive-axis theorem and the weak-blocker completion. For a leaf target supported on $0,2$, the core equations now read $x_1=(jx_0-lx_2)/k$, $x_3=(dx_0+ex_2)/f$. The reduced leaf matrix is
$$
M=\begin{pmatrix}cd/f-aj/k&al/k+ce/f-b\\hj/k-g-id/f&-hl/k-ie/f\end{pmatrix}
=\begin{pmatrix}A&B\\ C&D\end{pmatrix},\qquad \det M=-\det G/(fk)<0.
$$
The two leaf entries of column 2 of $G^{-1}$ are $(-B,A)/\det M>0$, so $A<0<B$. Since $D<0$ and $BC>AD>0$, also $C>0$. The two leaf entries of column 0 are $(D,-C)/\det M>0$. Its core entry $x_3$ is positive by the reconstruction, and its zero row-2 target gives $hx_1=gx_0+ix_3>0$. Both inverse columns are therefore strictly positive. The determinant of their $0,2$ block equals $1/\det M<0$. Writing $y^{(h)}$ for column $h$ normalized to total one gives
$$
\frac{y^{(0)}_0}{y^{(0)}_2}<\frac{y^{(2)}_0}{y^{(2)}_2}.
$$
The ratio $y_3/y_2=(d/f)(y_0/y_2)+e/f$ increases strictly from column 0 to column 2 as well. Hence $\max(y_0,y_3)/y_2$ increases. Column 2 can be selected when $\max(y_0,y_3)\ge y_2$ at that column; otherwise column 0 satisfies $\max(y_0,y_3)\le y_2$. [Positive axis for the negative pair](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md#a-positive-axis-throughout-all-six-entry-sign-chambers) · [Four-finite completion](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md)

Partition each of the two domains by the weak ordering of the four coordinates. If $p$ lists them in descending order, the vertices are the indicator vectors of its first $k$ owners, normalized by $k$, for $1\le k\le4$. Indeed the barycentric coefficients of a probability vector $y$ in that order are $k(y_{p_k}-y_{p_{k+1}})$, with the next value after the fourth taken as zero. This accounts for every point of both domains including their common boundary. On each cell the checker uses the same complete-word scoring and affine interpolation as the reciprocal-core certificate. The marked row has a single positive donor, respectively 1 or 3. Every other balanced row uses all its positive-negative donor pairs, including both positive donors of row 3. This yields the order inequality for the entire singleton cone at each point of the cell. All validation symbols are solo, so every higher entry is unrestricted. Closedness of fixed-rank passing gives the weak signs, and the negative singleton in the strict chamber provides the signed completion as above. [Exact fourth-rank order check](../experiments/RANK_FOUR_ADDITIONAL_DONOR.py)

This adds one strict, three one-tie and two two-tie orbits to the six-chamber count. Its closure alone meets $1,5,7,3$ surviving orbits with zero through three ties. The seven closures together meet $7/21$, $22/46$, $29/39$ and $10/10$, respectively. [Sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)

## A dependent with a second positive comparison

In the reciprocal-core matrix displayed above, change $G_{20}$ to $+g$ and keep $G_{02}=-b$. The positive donors are $3,3,\{0,1\},1$ in physical row order. The canonical mask is $(2,1,1,6)$, witness 7 of the singleton census. The all-four-finite fourth order test passes on this class for every choice of the 44 nonsingleton rewards. The same conclusion holds at all weak specializations and with arbitrary own-singleton levels.

Put $J=j/k$, $L=l/k$, $D=d/f$, $E=e/f$. The reciprocal-core exterior theorem already treats both dependent-to-dependent comparisons with either sign. On the hard branch its reduced matrix has positive inverse and negative diagonals:
$$
 M=\begin{pmatrix}cD-aJ&G_{02}+cE-aL\\G_{20}+hJ-iD&hL-iE\end{pmatrix}
   =\begin{pmatrix}A&B\\ C&H\end{pmatrix},\qquad A,H<0<B,C.
$$
The core equations $x_1=Jx_0+Lx_2$ and $x_3=Dx_0+Ex_2$ then reconstruct two strictly positive full leaf columns. The fixed-rank openness and four-finite reduction used above supply the same singleton hypotheses at a putative rank-four failure. [Seven reciprocal-core exteriors](TWO_FREE_ROWS_FROM_A_RECIPROCAL_PAIR.md#seven-strict-singleton-chambers-for-the-exterior)

Return to $G_{02}=-b$, $G_{20}=+g$ and take $y$ to be the positive column 0 normalized to sum one. The old $013$ default still has just one negative value $A/(1+J+D)$, and the omitted row has positive value $C/(1+J+D)$. Likewise the $213$ default has one negative value $H/(1+L+E)$ and the omitted row is positive. Reusing their rank-four hidden tests yields $y_0\le3y_1$, $y_2\le3y_3$. The first test also gives
$$
 D(1+4c/a)<3J-1.
$$
Since $c y_3>a y_1+b y_2$ at this column, and $y_1\ge J y_0$, one obtains $D y_0<y_3(3y_1-y_0)/(y_3+4y_1)$. Using $E y_2=y_3-Dy_0$ gives the additional price bound
$$
 \frac{d}{e}<\frac{y_2}{y_0}\;\frac{3y_1-y_0}{y_3+y_1+y_0}.
$$

The half of this domain with $y_0\le y_2$ is exactly the tetrahedron in the first reciprocal-core certificate. Reflecting it by $(0\,2)(1\,3)$ gives the half with $y_2\le y_0$. The order checker covers both halves at column 0, using the full sign generators where possible. On each restricted cell of the reflected half, write the numerator $N(y)=y_2(3y_1-y_0)$ and denominator $P(y)=y_0(y_3+y_1+y_0)$ of the displayed bound. Take $u$ to be the largest of the ratios of their symmetrized bilinear coefficients on vertex pairs with positive denominator. A coefficient with zero denominator also has zero numerator, since $y_2\le y_0$ throughout that half. Expanding in nonnegative barycentric coefficients gives $N(y)\le uP(y)$ on the whole cell. Thus the physical fraction $d/(d+e)$ lies in $[0,u/(1+u)]$.

For a deadline let $F_{ij}$ denote the complete-word assigned count at foreign singleton $j$ minus the corresponding deadline count. Row 1 is balanced at $y$, with $f y_3=d y_0+e y_2$. Its gain multiplied by $y_3/(d+e)$ is the convex combination of $y_0 F_{13}-y_3 F_{10}$ and $y_2 F_{13}-y_3 F_{12}$ with first weight $d/(d+e)$. Checking the two endpoints of the stated interval proves every physical row-1 comparison. Each endpoint remains linear in $y$, so the usual quadratic Bernstein verification with affine priors applies without a change of degree. The other rows are fully priced and the surplus at row 0 has the single donor 3. [Rank-four word checker](../experiments/RANK_FOUR_DEPENDENT_COMPARISON.py)

Among the surviving strict, one-tie, two-tie and three-tie orbits the closure meets $1,5,8,3$, respectively. Combined with the seven previously covered chambers it adds $1,3,2,0$, bringing the totals to $8/21$, $25/46$, $31/39$ and $10/10$. [Singleton sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)
