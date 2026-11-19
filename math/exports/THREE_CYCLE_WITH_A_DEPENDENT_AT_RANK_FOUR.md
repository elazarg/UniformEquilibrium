# The fourth order test for a three-cycle with a dependent

Suppose each of four players has a unique positive foreign singleton comparison, three of those positive comparisons form a directed cycle, and the fourth points into it. The all-four-finite fourth order test passes for all twelve singleton magnitudes, all 44 nonsingleton rewards and arbitrary signed own-singleton levels. Any subset of the strict comparisons can also be replaced by zero. Together with the two reciprocal-core results and the two-pair matching result, this covers every remaining strict sign chamber with just one positive comparison per row. On the full sign census the four closures together pass rank four on 4 of 21 strict chambers, 13 of 46 one-tie chambers, 22 of 39 two-tie chambers and all 10 three-tie chambers. The unbounded-rank criterion for uniform equilibrium remains open. [Order criterion](../notes/CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md) · [Reciprocal-core results](RECIPROCAL_CORE_AT_RANK_FOUR.md) · [Two-pair matching](MATCHED_SINGLETON_ORDER_TESTS_AT_RANKS_FOUR_TO_SIX.md) · [Sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)

## Two positive inverse columns

Use the native comparison $G_{ij}=r_i(\{j\})-r_i(\{i\})$. Relabel the unique positive donors as $(3,3,1,2)$, so the sign chamber has canonical mask $(2,4,1,1)$ and
$$
 G=\begin{pmatrix}0&-a&-b&c\\-d&0&-e&f\\-g&h&0&-i\\-j&-k&l&0\end{pmatrix},\qquad a,b,c,d,e,f,g,h,i,j,k,l>0.
$$
If the native absorbing regret infimum is zero, the weak-blocker completion gives four-finite approximations and passage at every rank. Otherwise $\det G>0$ and $G^{-1}$ has a strictly positive column. Put $C=G_{123,123}$, $r=(-a,-b,c)$ and $m=(d,g,j)^T$. For a positive inverse-column vector $x$, the core rows give $C x_{123}\ge m x_0>0$. Multiplying their three strict successor inequalities gives $D=fhl-eik>0$. Consequently
$$
 M=C^{-1}=D^{-1}\begin{pmatrix}il&fl&ei\\ik&fk&fh\\hl&ek&eh\end{pmatrix}>0.
$$
The Schur complement at 0 is $s=rMm=\det G/D>0$. Thus $G^{-1}e_0=(1,Mm)/s$ is positive. For $n\in\{1,2,3\}$ the leaf coordinate of $G^{-1}e_n$ is $-(rM)_n/s$, and its core part is $M e_n$ plus $Mm$ times the leaf coordinate. Such a column is strictly positive precisely when $(rM)_n<0$. [Prescribed-clock completion](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md) · [Positive inverse column](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)

Write $A=l/k$, $B=e/f$, $S=A+1+B$, $\rho=iB/(hA)<1$ and $L=aA+b-cB$. Use the cyclic singleton path on owners $1,2,3$ in that order, putting unconditional first-tour phase masses $(1-\rho)(A,1,B)/S$ and scaling successive tours by $\rho$. Its three active neutrality equations hold since $fB=e$, $l=kA$ and $\rho hA=iB$. The three core rows have nonnegative remaining tail on every phase. For each owner its tail starts at zero on its own phase and stays zero while its own mass is removed. In the cyclic order, the next phase removes a negative entry and the one after that removes a positive entry, returning the tail to zero. These are the complete core deadline inequalities. The outsider's unnormalized tail starts at $-L$, increases through the first two phases and declines to $-\rho L$ on the third, with the common denominator $S$ suppressed. If $L\le0$, all four tail inequalities hold and the established singleton-path discretization gives uniform equilibrium. Otherwise $(rM)_2=-fkL/D<0$, so $G^{-1}e_2$ is strictly positive. The explicit column for $n=3$ shows that $G^{-1}e_3$ is strictly positive precisely when $cB<a\rho A+b$. [Continuous singleton-path criterion](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

If column 3 is positive, the principal $2,3$ minor of $G^{-1}$ equals $-ad/\det G<0$ by the complementary-minor identity. Thus $(G^{-1})_{32}/(G^{-1})_{22}>(G^{-1})_{33}/(G^{-1})_{23}$. For a column normalized to total mass one, we can use column 2 with $2y_3\ge y_2$ or column 3 with $2y_3<y_2$.

## A shifted cyclic default when column 3 is not positive

Here $cB\ge a\rho A+b$, so $0<L\le(1-\rho)aA$. Start the same cyclic path partway through its first phase, after removing mass $(1-\rho)L/(aS)$. This is strictly inside the phase because $L<aA$. The outsider's remaining unnormalized tail is now $-\rho L$, and every later tail is at least this value. The later tour minima are $-\rho^nL$, $n\ge1$. Write $S'=S-(1-\rho)L/a$. Starting at the new cut, the passive outsider receives $w_0=-\rho L/S'$. Its complete cap is zero since any deadline removes a remaining tail no smaller than the initial one, and an initial solo quit pays zero. Owner 1 remains active with prescribed payoff and cap zero. The other core owners retain their nonnegative obedient continuation payoffs.

This gives a four-finite limit of native payoffs and caps $(w,w^+)$, where $w^+$ is the coordinatewise positive part. Subdividing the single-owner phases into small hazards gives the physical independent clocks of the singleton-path discretization. The effects of ties against a pure deadline vanish uniformly. Each core owner faces a strictly positive conditional quitting probability on its phase in every complete tour, so its private survival tends to zero geometrically. One can clip the core clocks at increasing finite bounds and append the outsider beyond them without changing any prescription or complete cap in the limit. Thus the hidden two-owner continuation theorem at rank $N\ge3$ applies whenever
$$
 R=\frac{aS'}{\rho L}=\frac{aS/L-(1-\rho)}{\rho}\ \ge\ (N-2)^2.
$$
For example the published integer witness with $(a,b,c,d,e,f,g,h,i,j,k,l)=(1,1,3,1,1,2,1,2,1,1,1,2)$ has $R=35/3$ and therefore also passes rank five for every completion of its higher rewards. [Hidden continuation and finite tail embedding](EVERY_FOUR_PLAYER_QUITTING_GAME_PASSES_THE_THIRD_ORDER_TEST.md)

A failure at rank four would imply $aS/L<1+3\rho$. Since $L\le(1-\rho)aA$, this gives
$$
 1+B<\rho(2-3\rho)A<2(i/h)B.
$$
Now take the normalized core vector $y$ proportional to $(0,(i/h)B,1,B)$. Direct substitution gives $(Gy)_1=(Gy)_2=0$, $(Gy)_3>0$ and $(Gy)_0\ge0$, the last inequality using $cB\ge a\rho A+b$. This gives the parameter for the order inequalities on the triangle $y_0=0$, $2y_1\ge y_2+y_3$.

## Exact order priors on three domains

For a word inserting sixteen distinct validation dates between fixed training ranks, let $F_{ij}(t)$ be the prescribed probability of first exit by $j$ minus its probability of exiting before tested date $t$ after deleting $i$. The final date gives Never and Late. As the own singleton is zero and the draws avoid training dates, the prescribed-minus-tested payoff of $i$ is $\sum_{j\ne i}G_{ij}F_{ij}(t)$. If $p_i$ is its positive donor, $y_{p_i}>0$ and $Gy\ge0$, its row decomposes into a nonnegative combination of the balanced generators $y_n e_{p_i}-y_{p_i}e_n$ (coefficient $-G_{in}/y_{p_i}$ for each negative $n$) and the surplus $(Gy)_i e_{p_i}/y_{p_i}$. This remains valid at $y_0=0$ on the selected proper-core vectors, since 0 is nobody's positive donor.

On the two full-axis domains each word separately has $F_{h,p_h}(t)\ge0$ for its axis $h$. On the proper face use axis $3$ for this comparison and place all validation labels of owner 0 strictly after those of its three rivals. Its prescription is then always passive and $F_{03}(t)\ge0$ at every rank. These two comparisons handle both possible surplus rows on the face.

The checker covers the column-2 half-space $2y_3\ge y_2$ by 38 tetrahedra and the column-3 half-space $2y_3\le y_2$ by 26 tetrahedra inside the normalized simplex. The first has normalized volume $2/3$, the second $1/3$. It checks containment, pairwise disjoint interiors and the total determinant volumes. The proper triangle has vertices proportional to $(0,1,0,0),(0,1,2,0),(0,1,0,2)$; six longest-edge bisection leaves cover it. On each piece a common training observation and a prior per vertex give all balanced-generator inequalities throughout the piece by checking every symmetrized mixed vertex coefficient. The face verifier repeats one vertex to reuse the four-vertex calculation. Independent enumeration of all $4^4$ validation selections per complete word checks interlacing, every tested date and each surplus condition. The respective word and integer-inequality counts are 1,903 and 31,840 on column 2, 1,017 and 22,720 on column 3, and 243 and 7,360 on the face. [Exact checker and sign counts](../experiments/RANK_FOUR_THREE_CYCLE_TAIL.py)

All rival clocks are finite, so the inequalities survive every signed row translation. The order simplex is compact and its inequalities are continuous in the table, giving the weak-sign closure. The new chamber's closure contains six surviving one-tie orbits, ten two-tie orbits and five three-tie orbits, disjoint from those covered by the three earlier unique-donor chambers. This leaves 17 strict, 33 one-tie and 17 two-tie orbits outside these four rank-four closures.

## A positive comparison back to the dependent

In the three-cycle theorem change the core owner's comparison $G_{30}$ back to the dependent from negative to positive. **The fourth order test still passes for the entire strict chamber, all 44 nonsingleton rewards, every signed own-singleton level, and every specialization of foreign comparisons to zero.** This is census chamber $(2,4,9,4)$, witness 5. It adds one strict, four one-tie and three two-tie orbits to the preceding four full-chamber results. Their union now passes rank four on 5 of 21 strict, 17 of 46 one-tie, 25 of 39 two-tie and all 10 three-tie orbits.

Use physical labels
$$G=\begin{pmatrix}
0&-a&-b&c\\-d&0&-e&f\\-g&h&0&-i\\ j&-k&l&0
\end{pmatrix},\qquad a,b,c,d,e,f,g,h,i,j,k,l>0.$$
As in the preceding three-cycle result, it suffices to treat the hard matrix branch. The positive-axis theorem for a mutually negative pair $01$ applies directly to these signs, giving $\det G>0$ and $G^{-1}e_2>0$. Its matrix hypotheses require $G_{03},G_{13},G_{32}>0>G_{23}$ and $\min(G_{02},G_{12})<0$, and therefore hold here regardless of the higher rewards. [Positive axis from a mutually negative pair](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md#a-positive-axis-throughout-all-six-entry-sign-chambers)

Eliminate rows and columns $1,3$, leaving $0,2$. The Schur matrix is
$$
 M=\begin{pmatrix}A&B\\ C&D\end{pmatrix}
 =\begin{pmatrix}cd/f-aj/k&ce/f-al/k-b\\hj/k-g-id/f&hl/k-ie/f\end{pmatrix},
 \qquad \det M=\det G/(fk)>0.
$$
The leaf coordinates of $G^{-1}e_2$ are $(-B,A)/\det M$, so $A>0>B$. For $x=G^{-1}e_3$ the two leaf equations have right side $(-a/k,h/k)$; thus $x_0=(-aD-hB)/(k\det M)$. If $x_0>0$ the first equation gives $x_2>0$. Rows 1 and 2 then give $x_3=(d x_0+e x_2)/f>0$, $x_1=(g x_0+i x_3)/h>0$. Otherwise $D>0$ and $c(e/f)\ge b+a i(e/f)/h$. Set $U=l/k$, $V=e/f$, $\rho=iV/(hU)<1$. This is exactly $cV\ge a\rho U+b$, the sufficient condition for the shifted three-cycle continuation and proper-face certificate above. The changed entry $G_{30}$ plays no role there: 0 waits beyond all three core clocks, including after a core clock is deleted, and affects no payoff or offer to owner 3.

It remains to price the two full positive axes. Write $y^{(h)}$ for the positive inverse column $h$ normalized to total mass one. The $2,3$ principal minor of $G^{-1}$ equals $-ad/\det G$, while the minor with rows $0,2$ and columns $2,3$ equals $af/\det G$. The complementary-minor identity therefore gives
$$
 \frac{y^{(2)}_3}{y^{(2)}_2}>\frac{y^{(3)}_3}{y^{(3)}_2},
 \qquad
 \frac{y^{(2)}_0}{y^{(2)}_2}>\frac{y^{(3)}_0}{y^{(3)}_2}.
$$
Use axis 2 on $2y_3\ge y_2$ or $y_0\ge y_2$. If both inequalities fail at this column, axis 3 lies in $2y_3\le y_2$ and $y_0\le y_2$.

The checker reuses the original two half-space partitions. In the region $2y_3\le y_2$ five base tetrahedra lie in $y_0\ge y_2$. They have total normalized volume $1/10$ and move to axis 2. The resulting axis domains have volumes $23/30$ and $7/30$. Subdivision addresses and thirty explicitly listed training schedules certify them with affine vertex priors. For a row with several positive donors, split each negative singleton's weighted deficit among its positive donors using their available masses $G_{ip}y_p$. The unspent mass is the axis surplus. It therefore suffices to price each balanced generator $y_n e_p-y_p e_n$ and, on the nonzero axis, every positive-donor surplus separately. Row 3 now has positive donors 0 and 2; the verifier explicitly counts both assigned-minus-tested surpluses when this row is the axis. Its integer checks enumerate every validation draw and all observed dates, Never and Late. The two full-axis domains require respectively 55 and 33 tetrahedra, with 63,520 and 42,480 balanced-generator inequalities. All rival clocks are finite. Compactness of the finite order simplex gives the stated weak-sign specializations. The five-chamber union is still a fixed-rank result. [Exact schedules and sign-count checker](../experiments/RANK_FOUR_MIXED_THREE_CYCLE.py)

## Two owners with the same positive donor

There is a second mixed-sign extension of the three-cycle result. Let rows 0 and 1 have 3 as their sole positive foreign singleton, row 2 have positive foreign singletons at both 0 and 1, and row 3 have 2 as its sole positive foreign singleton. **Every higher-reward completion passes the fourth order test**, including every weak-sign specialization and arbitrary original own-singleton levels. This is census chamber $(2,4,9,2)$, witness 6. Together with the preceding five whole-chamber tests, the cumulative strict, one-tie, two-tie and three-tie counts are $6/21$, $19/46$, $27/39$, $10/10$.

In the preceding display for $G$ replace $G_{20}$ by $+g$ and $G_{30}$ by $-j$. The mutually negative pair lemma again provides a strictly positive inverse column 2 on the hard branch. The Schur matrix using core $1,3$ still has $\det M=\det G/(fk)>0$ and $A>0>B$ from that column. Its entries $B=ce/f-al/k-b$ and $D=hl/k-ie/f$ are unchanged. At $x=G^{-1}e_3$ the reduced right side is still $(-a/k,h/k)$, so $x_0\le0$ again gives $D>0$ and $c(e/f)\ge b+ai(e/f)/h$. The shifted cycle and proper-face test on $123$ apply, since only the core comparisons towards the absent owner 0 have changed. The sign pattern is invariant on switching 0 and 1. If $x_1\le0$, the same reasoning after that switch applies to the core $023$. If both $x_0,x_1>0$, the first leaf equation $Ax_0+Bx_2=-a/k$ yields $x_2>0$ and row 1 gives $x_3>0$. Thus columns 2 and 3 are both positive in the only other case.

Their principal minor $-ad/\det G<0$ permits the original choice of column 2 on $2y_3\ge y_2$ or column 3 on $2y_3\le y_2$. Once the column has been selected, switch 0 and 1 if needed to take $y_0\ge y_1$. This halves each of the two original domains. Their normalized volumes are $1/3$ and $1/6$ before reflection. The exact checker reuses the original tetrahedra on this side of the symmetry plane. At axis 2 both 0 and 1 are protected positive donors; at axis 3 only donor 2 is required. It verifies the complementary balanced generators, all surplus tests and the finite boundary specializations just as above. [Exact schedules and cumulative census](../experiments/RANK_FOUR_MIXED_THREE_CYCLE.py)
