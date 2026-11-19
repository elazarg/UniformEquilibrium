# Equilibria with large withdrawal rewards on the six-entry frontier

Use the six-position template for four independent quitting players. In native units the pair $01$ is mutually negative. Player $a=3$ receives $K>0$ on $013$, and the two mates and player $b=2$ receive positive grand rewards. The two other changes give an advantage $L>0$ to player 3 for withdrawing from the grand coalition, and an advantage $N>0$ to one mate $u$ for withdrawing from $012$. Each advantage can be implemented by lowering the participating reward or raising the passive reward after withdrawal. Other higher entries are zero except where explicitly allowed below. All four original own singleton levels are arbitrary. The general three-player return, the sure-owner tests and the 21 numbered integer singleton examples are given in the main six-entry paper. [Template, first-date tests and accumulating return](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)

Most of the results below use witness 18, whose singleton rows are $(0,-1,-1,2),(-2,0,1,2),(1,1,0,-2),(-1,-1,2,0)$. On this matrix the small-$R$ return and the large-$R$ stationary branch overlap even when the positive triple price and a mate's grand reward are unbounded. A different construction permits a fourth player to mix on the dates where the three-player return would give it a profitable deviation. For a large negative participating withdrawal the affected mate can have a negative continuation. The two-dimensional return carries that continuation through the large-withdrawal dates near witnesses 6 and 18. At witness 6 a four-date solution also works with two independently large rewards and explicit bounds uniform in the triple reward.

## Three unrestricted prices at witness 18


At the singleton matrix of witness 18, use the opposite entrant assignment $a=3,b=2$. Write $R=Z_2(I)$ and $A=Z_0(I)$, $B=Z_1(I)$ for the three positive grand rewards. Fix $N=4,L=B=1$. **All three prices $K,A,R$ may vary independently throughout $(0,\infty)$.** This holds for either withdrawal owner and both implementations of each edge, and for all original own levels. The conclusion persists throughout an open neighborhood of the singleton data and three fixed prices within the six-position template.

With withdrawal owner $u=1$, the preceding sure-$v$ criterion for $v=0$ applies at $R\ge2L$, while the accumulating return already covers every $K>0$ at smaller $R$. It suffices to establish the claim for $u=0$. In the general return specialized here, write $s=2z=4S/(2+3S)$. The first joint step uses odds $p_0=s/2+t$, $p_1=2t$, $p_3=t$, with $3t+K(st+2t^2)=s/2$. Every later joint prepend uses $p_0=p_3=t$ and $p_1=2t$. In the recurrence for witness 18, $y+x/3$ decreases under each subsequent prepend: its new numerator over $(1+t)^2(1+2t)$ is $y+(1+t)x/3-t^2$. Its value at the first prepend is at most $2s/[3(1+s/2)]$, since the corresponding numerator is $2s/3+st/6-t^2$ and denominator $(1+s/2+t)(1+2t)(1+t)$. Thus $F(S)\le8S/(6+15S)$, using $s=4S/(2+3S)$. Choose $S=1/7$, where $F(S)<S$; every seed up to this value has $s\le4/17$ and first and subsequent $t\le s/6\le2/51$. The row-2 guard $2Rt^2\le1$ holds with strict margin for $R\le300$. We now give stationary equilibria whenever $R\ge250$.

Let the positive stopping odds be $(x,y,s,w)$ and $h_i=1-\prod_{j\ne i}(1+p_j)^{-1}$. Set $n,l\in\{0,1\}$ equal to one for a positive passive implementation of the respective withdrawals $N,L$ and zero for a negative participating implementation. The nonpivot equations are
$$
\begin{aligned}
 f_0&=2w-s-y+sy[N(n+(1-n)h_0)-A h_0 w],\\
 f_1&=2w+s-2x-sx B h_1 w,\\
 f_3&=2s-x-y+xy[sL(l+(1-l)h_3)-Kh_3].
\end{aligned}
$$
In $s/2\le w\le2s$ and $0<s\le1/5$, the first two equations have unique nonnegative continuous roots in $y,x$, respectively. They decrease strictly in their own variable, with derivatives at most $-1+sN<0$ and $-2$, since $h_i+p_j\partial_jh_i<1$. They tend to minus infinity at large own variable. The root $x$ lies in $[(2w+s)/(2+sBw),w+s/2]$, and $y>0$ except at the left edge. At that edge $f_3=2s-x>0$. On the right edge $x\ge5s/(2+2s^2B)>2s$ and $sLx<1$, so $f_3<0$. These signs are uniform in $K,A$.

The remaining row is $f_2=x+y-2w-R h_2xyw$. At the top edge $s=1/5$ we have $w\ge1/10$, $x\ge (2/5)/(2+2/25)>19/100$ and $h_2\ge1-1/[(1+19/100)(1+1/10)]>23/100$. Because $x\le w+s/2\le2w$, the top has $f_2<0$ for $R\ge250$ (also at $y=0$, since $x<2w$). On every sufficiently small bottom edge at every zero of $f_3$, one has $f_2>0$. In fact, for any fixed finite prices, divide the three nonpivot equations by $s$ and take $s\downarrow0$ along such zeros. Since $y\le(2w-s)/(1-sN)$ and $x\le w+s/2$, compactness and the nonsingular leading equations give $(x,y,w)/s\to(4/3,2/3,5/6)$ and $f_2/s\to1/3$.

The rectangle in $(w/s,s)$ has opposite strict $f_3$ signs on its vertical sides and opposite strict $f_2$ signs at the $f_3$ zeros on its two horizontal sides. Its two-component field has nonzero degree: homotope $f_2$ to the affine function that is positive at the bottom and negative at the top, then $f_3$ to the affine function positive on the left and negative on the right. No boundary zero occurs. The interior zero has strictly positive odds and gives an exact absorbing stationary equilibrium, valid also after the row translations.

For perturbations of $G,N,L,B$, replace the left edge by $w/s=-G_{02}/G_{03}$ so that $y=0$ there. The monotone inverses and bounds on the sides persist with strict relative margins after division by $s$, uniformly in $K,A$: the contribution of $A$ to $f_0$ and of $K$ to $f_3$ on the right is nonpositive. For the top, $x$ depends only on $G_{10},G_{12},G_{13},B,s,w$, and the baseline $G_{20}x+G_{23}w=x-2w$ is strictly negative throughout that compact edge even at its left end, since $B>0$. The positive lower bounds on $h_2,x,w$ absorb the nearby $G_{21}y$ term. The positive leading $f_2/s$ at the lower $f_3$ zeros persists by nonsingularity for each fixed finite price.

For the lower interval use the general return notation and $\alpha=H/E>0$. The subsequent-step identity gives
$$
 y'+\alpha x'=\frac{y+\alpha(1+t)x-\alpha E t^2}{(1+Dt)(1+Ct)(1+t)}\le y+\alpha x.
$$
At the first step its numerator is $(hV+\alpha W)z+\alpha Wzt-\alpha Et^2$ and its denominator is $(1+Vz+Dt)(1+Ct)(1+t)$. Consequently $F(S)\le (hV+\alpha W)z/(1+Vz)$. The upper bound at $S=1/7$ is strictly smaller than that seed and depends only on singleton data. Every prepend has $t\le Wz/E$, where $z$ is at most its endpoint value, and the quiet guard follows from $R C t^2\le\min(h,H/D)$. The strict margin up to $R=300$ persists for nearby singleton data, independently of $K,A$. This proves openness of the entire orthant.

### One bounded price at witness 18, in either orientation

Let $G$ be the displayed witness 18 matrix, $a=3,b=2$. If $0<N\le1$, **all five other prices $K,L,R_0,R_1,R_2$ are independently arbitrary and positive**. Either mate may own the withdrawal and either implementation of each edge is permitted. The conclusion holds uniformly on a neighborhood of the singleton matrix for all these choices. For $u=1$, the preceding sure-$v$ and accumulating comparison already proves the result, since on the only remaining branch $KN>2L$ one has $2L<KN\le K$. We give a different argument for $u=0$, where that sure-$v$ sign comparison fails. Write $A=R_0,B=R_1,R=R_2$ and $m=-G_{01}$. On a sufficiently small neighborhood we may suppose $m>9/10$. The earlier square and return let us assume
$$
 L<KN/m,\qquad R>300,\qquad K<R .
$$
Indeed the return covers every $R\le300$ with a strict uniform guard on the seed interval ending at $1/7$ and also $R\le K$, since its center linear cutoff is $(5/2)K$.

Write the odds as $p=(x,y,s,w)$ and $h_i=1-\prod_{j\ne i}(1+p_j)^{-1}$. Set $z=Ns[n+(1-n)h_0]$, $M=(G+z e_0 e_1^\top)^{-1}$, and write stationary indifference as $p=M q$, where
$$
 q=\big(A s y w h_0,\ B s x w h_1,\ R x y w h_2,\ xy[Kh_3-sL(l+(1-l)h_3)]\big).
$$
Use $0<s\le1/4$, so $0\le z\le1/4$. In the cone defined below $x\ge3s/5$, hence $h_3/s\ge(8/5+3s/5)/[(1+s)(1+3s/5)]>10/9$. Therefore $sN/m<h_3$ and $q$ is nonnegative.

We record explicit matrix inequalities uniform in this interval of $z$. At the stated witness,
$$
 G^{-1}=\begin{pmatrix}3&1&4&1\\1&1&2&0\\2&1&3&1\\2&1&5/2&1/2\end{pmatrix},\qquad
 M=G^{-1}-\frac{z}{1+z}G^{-1}e_0e_1^\top G^{-1}.
$$
Every $M_{2j}>0$, and the ratios $M_{0j}/M_{2j}$ lie strictly between $3/5$ and $4$, while $M_{3j}/M_{2j}$ lie strictly between $9/20$ and $4$. The ratios $M_{1j}/M_{2j}$ are strictly below $4$. Moreover $M_{10},M_{11}>0$, $M_{12}>3/2$ and $M_{13}>-1/1000$. These follow directly from $0\le z/(1+z)\le1/5$, including $M_{13}=0$ at the center, and persist throughout one singleton neighborhood by compactness.

Use angular variables $(x/s,y/s,w/s)\in[3/5,4]\times[0,4]\times[9/20,4]$. Form $T=Mq$ and send these ratios to $(T_0,\max(0,T_1),T_3)/T_2$. This is a continuous self-map of the angular box for each $s>0$, since $q_1>0$. At any angular fixed point $y>0$: if $y=0$, the only nonzero coordinate of $q$ is $q_1$ and $M_{11}>0$. Thus $T_1/y=T_2/s$ there. For every fixed finite choice of the six prices the maximum of $T_2/s$ over the angular box tends to zero as $s\downarrow0$. In contrast, at $s=1/4$ and at every angular fixed point, $x\ge3/20$, $w\ge9/80$ and $h_2\ge1-[(1+3/20)(1+9/80)]^{-1}>1/5$. Therefore
$$
 \frac{T_2}{s}=\frac{T_1}{y}
 \ge x\left(\tfrac32 R w h_2- K/1000\right)
 > \frac{3R}{20}\left(\frac{27}{800}-\frac1{1000}\right)>1 .
$$
The bound includes the potentially negative $M_{13}q_3$, since $q_3\le Kxy$. Choose a small bottom radius $s_*>0$ where all angular ratios have $T_2<s_*$. Adjoin to the angular map the scalar update $s\mapsto\operatorname{proj}_{[s_*,1/4]}(2s-T_2)$. Brouwer gives a fixed point; the two strict radial inequalities exclude both endpoint radii. At the interior fixed point $s=T_2$ and all four odds are positive, so $p=Mq$. This gives an original absorbing stationary equilibrium throughout the remaining region, uniformly over the five unrestricted prices. Together with the square and return this proves the full statement.


The stationary sector from this argument allows simultaneous perturbations of all 38 other native higher payoffs, with 29 independent favorable half-lines. More precisely, there is a single $\delta>0$ such that for $u=0$, $0<N\le1$, $L<KN/m$, $R>300$, $K<R$ and the singleton matrix in a fixed neighborhood, all nine remaining native entries in row 3 may vary in $[-\delta,\delta]$. Each of the 29 remaining entries in rows 0,1,2 may vary throughout $[-\delta,+\infty)$ when its recipient participates, and throughout $(-\infty,\delta]$ otherwise. Every such table admits an original absorbing stationary equilibrium. The five displayed positive prices may range without additional bounds. This statement concerns the stated sector; the low-return part of the whole-price theorem uses the six-position table.

To prove this, work on the same angular box and annulus $s_*\le s\le1/4$ in unscaled odds coordinates. First add the favorable parts of all 29 changes to $q$: a larger joining reward adds a nonnegative odds monomial times $h_i$, while a smaller passive reward adds a nonnegative odds monomial. These increments enlarge $q_0,q_1,q_2$. All bounded remainders change the reduced stationary field $p-Mq$ by a vector error with every component bounded by $C\delta s^2$, uniformly on that box. Indeed all extra native passive payoffs have at least two active opponents, and extra joining payoffs have at least one active opponent and an additional multiplier $h_i=O(s)$ after division by opponent survival. The inverse matrices are uniformly bounded. Take the singleton neighborhood with compact closure inside all strict matrix bounds above. A single small $\delta$ will work throughout it.

There are no zeros on the boundary at any time in the linear homotopy adding these errors. At a hypothetical root $s=(Mq)_2+O(\delta s^2)$, the sum of the nonnegative $q_j$ is bounded above and below by positive multiples of $s$, using uniform bounds on $M_{2j}$. The uniform strict column-ratio bounds exclude each angular face for $x,w$ and the upper face for $y$. On $y=0$ the component $q_3$ vanishes, and each of $M_{10},M_{11},M_{12}$ is uniformly positive, excluding this face. At the bottom radius choose $s_*$ small for the fixed endpoint table, including its favorable increments, so $|(Mq)_2|<s_*/2$ on that face. At the top $s=1/4$, the inequality in the preceding proof implies $y\ge c R y - C\delta$ with $300c>1$, so $R y=O(\delta)$. Then $q_3=O(\delta)$, using $K<R$. Since $M_{10},M_{11},M_{12}$ are uniformly positive, the equation for $y$ also gives $q_0,q_1,q_2=O(\delta)$. This contradicts the lower bound on $\sum_jq_j$ at $s=1/4$.

Finally the unperturbed full stationary map has nonzero degree on this region. In normalized angular and radial coordinates the clamped Brouwer map just used maps the closed convex box into itself with no boundary fixed point. Its residual therefore has degree one by homotopy to a constant interior map. Near all its fixed points the clamps are inactive: $y>0$, and at an interior radial fixed point $2s-T_2=s$. Its angular residuals are $(p_i/s-T_i/T_2)_{i=0,1,3}$ and its radial residual is $T_2-s$. Multiplying angular rows by $s>0$ and subtracting suitable multiples of the radial row gives the three residuals $p_i-T_i$; reversing the radial row gives $s-T_2$. These row operations and the change to odds coordinates affect degree by one common sign. Thus the nonzero degree belongs to the true unperturbed field. Boundary exclusion preserves it while interpolating both the favorable increments and the bounded remainders. For each fixed endpoint table the same small bottom radius works throughout this interpolation.


On the nearby open subset where $(G^{-1})_{13}>0$, all 38 extra coordinates admit these favorable half-lines on compact subsets. Indeed $M_{13}=(G^{-1})_{13}/[1+z(G^{-1})_{10}]$ by the same rank-one formula. On each such compact subset the entire first-index row $M_{1j}$ is uniformly strictly positive. Add the otherwise unbounded favorable row-3 increments to $q_3$ as well. The hypothetical root still has $\sum_j q_j$ comparable to $s$, so $y$ is uniformly bounded below by a positive multiple of $s$ on all boundaries when the adverse errors are small. At the top the positive $M_{13}q_3$ only improves the radial inequality, yielding $R y=O(\delta)$ and hence $\sum_jq_j=O(\delta)$ from the $y$ equation, a contradiction. Every such compact subset has its own common adverse bound. This open subset is nonempty: decreasing the witness entry $G_{02}$ by $\eta>0$ small changes $(G^{-1})_{13}$ from zero to $\eta/(1-2\eta)>0$. The normalized radial fixed point method for positive inverses already appears in [the coalition jackpot theorem](POSITIVE_INVERSE_COALITION_JACKPOTS_UNIFORM_EQUILIBRIUM.md). The present calculation uses it at a zero entry of the inverse, with a rank-one correction and signed, independently varying higher payoffs.

### Simultaneously unbounded withdrawals at witness 18

Use the same $u=0$, $a=3$, $b=2$ assignment and let $A,B,R>0$ be the grand rewards of $0,1,2$. Let $d_N=1$ for a passive pair withdrawal edit and $d_N=2$ for a participating triple edit. Let $d_L=2$ for a passive triple withdrawal edit and $d_L=3$ for a participating grand edit. Put
$$
 W=1+N^{1/d_N}+L^{1/d_L},\qquad H=\max(A,B,R).
$$
There is a constant $D$ such that $H\ge DW^3$ gives an exact full-support stationary equilibrium for **every** $K>0$. This holds for the displayed witness and throughout one fixed neighborhood intersected with $(G^{-1})_{13}\ge0$. Each of the 38 remaining higher entries can simultaneously vary without bound in its favorable half-line (nonnegative for a participant, nonpositive for a passive recipient). The constants are independent of all these prices. Signed original own payoffs are arbitrary.

Use the preceding odds $p=(x,y,s,w)$ and set $\kappa_0=n+(1-n)h_0$, $\kappa_3=l+(1-l)h_3$, where $n,l$ equal one for a passive edit. Absorb both withdrawals on the left of the indifference equations:
$$ M=(G+z e_0e_1^\top+d e_3 e_0^\top)^{-1},\qquad z=Ns\kappa_0,\qquad d=s y L\kappa_3. $$
Then $p=Mq$, with the four source terms $q=(Asyw h_0,Bsxw h_1,Rxyw h_2,Kxyh_3)$ before adding the nonnegative increments from the other higher entries. These increments are the odds monomials for passive rewards with sign reversed, and the odds monomials times $h_i$ for participating rewards. At the witness, all entries of $G^{-1}$ except $(1,3)$ are positive and that entry vanishes. For $M_z=(G+z e_0e_1^\top)^{-1}$ the rank-one formula gives
$$ (M_z)_{13}=\frac{(G^{-1})_{13}}{1+z(G^{-1})_{10}},\qquad M_{13}=\frac{(M_z)_{13}}{1+d(M_z)_{03}}. $$
Hence on the specified side all entries of $M$ are nonnegative for $0\le z,d\le\epsilon$, with all entries other than $M_{13}$ uniformly positive after choosing $\epsilon>0$ and the singleton neighborhood small. In particular $M_{1j}>1/2$ for $j=0,1,2$. By the displayed inverse the ratios $M_{ij}/M_{2j}$ lie strictly between $1/3$ and $4$ for $i=0,3$ and are strictly below $4$ for $i=1$ throughout.

Use the angular box $1/3\le x/s,w/s\le4$, $0\le y/s\le4$. For $s\le1$, one has $s/4\le h_i\le12s$ there, since each owner has a rival with odds at least $s/3$. Choose a fixed $0<c<1$ small. Up to the top radius $s_0=c/W$, the bounds on $z$ are $Ns$ or $12Ns^2$ and those on $d$ are $4Ls^2$ or $48Ls^3$, respectively. They are below $\epsilon$ simultaneously. The angular map given by $T=Mq$ in the three ratios $T_i/T_2$ is a continuous self-map even at $y=0$, since $B>0$ supplies $q_1>0$. At any angular fixed point $y>0$ since $M_{11}q_1>0$. There $T_2/s=T_1/y$. At the top, the three source ratios $q_0/y,q_1/y,q_2/y$ are bounded below by $As_0^3/12,Bs_0^3/144,Rs_0^3/36$, respectively. The nonnegative fourth column allows $K$ and all further favorable terms to be arbitrarily large. Thus $T_1/y\ge Hs_0^3/288>1$ upon taking $D=576/c^3$. At small $s$ one has $T_2/s\to0$ uniformly over the angular box for each fixed endpoint table, because all extra terms are $O(s^2)$ there. The same projected radial Brouwer map now gives an interior radius and strictly positive odds with $p=Mq$. Every unilateral replacement faces geometric rival absorption, so the stationary indifferences give exact terminal and uniform equilibrium after all signed row translations.

For a separation at the exact witness, take the passive implementations, $A=B=1$, $N=k^{1/4}$, $L=k^{1/2}$, $K=k$, $R=k^{5/4}$ and all other higher entries zero. Then $R/W^3\to\infty$. In the earlier weighted collision test the $K$ entry is adverse on every support. At full support inverse column 3 has a zero entry. On $013$ the first two singleton equations force $y=2w$, $x=w$ and the third gives $-3w=1$, excluding a positive direction for this joining reward. All other proper supports omit some member of $013$. Thus the adverse scale is at least $k^{1/2}$, while the largest possible favorable scale is $O(k^{5/12})$. The two-sure opening fails since $KN>L$. The only candidate sole sure quitter is $v=1$, since $G_{ab}=2>0$ excludes $b$. Its final inequality, in $z'=RY>0$, reads
$$2/z'-2z'/R+(1/R-1)(K+z')/L\ge0,\qquad N=L/(K+z')+z'/R.$$
Here $z'/R\ge N-L/K\to\infty$, so the inequality fails. Every proper full-support forced quit offer is strictly positive since all participating higher entries are nonnegative and each player has a positive one. This family therefore has exact proper stationary equilibria across a region beyond the earlier weighted, sure-opening and product-lowness tests.

## A four-player date extends the return to large passive withdrawal rewards

At witness 6 take $u=0,v=1,b=2,a=3$, with singleton rows $(0,-1,-1,2),(-1,0,-1,2),(1,1,0,-1),(-1,-1,2,0)$. The two mates can be exchanged. Implement the withdrawal of $u$ by the **positive passive** entry $N=Z_u(vb)$. Allow either implementation of the other withdrawal, of size $L$. Write $K=Z_a(uva)$, $R=Z_b(I)$, $A_u=Z_u(I)$ and $A_v=Z_v(I)$. For every $K,R>0$ there are $N_0<\infty$ and $d>0$ such that the original game has a uniform-equilibrium payoff whenever
$$N\ge N_0,\qquad 0<L,A_u,A_v\le dN.$$
The constants can be taken uniformly on compact subsets of $K,R\in(0,\infty)$ and on a sufficiently small singleton neighborhood for each such compact set. In particular, with the other five prices fixed at arbitrary positive values, the entire positive tail of the passive reward $N$ is covered. Increasing $N$ does not help the sure-pair inequality $KN\le mL$.

Start the preceding backward return at $S e_b$, $0<S\le1$. The same two solo dates produce the continuation $(U,V,B,A)=(0,0,0,4S/(1+3S))$ in order $u,v,b,a$. The letters $U,V,B,A$ below denote native continuation values. Write $(x,y,s,w)$ for the four odds in the same player order. At a joint date a proper mover's two offers agree when its continuation equals the sum of joining-minus-passive rewards times the corresponding nonempty rival-set odds products. For all four owners these required continuations are
$$
 \begin{split}
 U&=y+s-2w+sy(A_u w-N),\
 V&=x+s-2w+A_v xsw,\
 B&=-x-y+w+Rxyw,\
 A&=x+y-2s+xy(K-Ls).
 \end{split}                                                    \tag{1}
$$
The two implementations of $L$ have the same difference here. If $b$ waits with certainty, its requirement in (1) is $B\ge-x-y+w+Rxyw$. Each mover receives its forced-quit offer.

**The limiting return.** Put $s=z/N$ and first take $1/N,L/N,A_u/N,A_v/N=0$ in the equations and payoffs, keeping the term $z y$. The outputs $U,V$ of each joint date vanish. From a child $(0,0,B,A)$ with $A>0,B\ge0$ the old three-mover step uses $x=y=2w_0$, $A=4w_0+4K w_0^2$. If $B\ge4Rw_0^3-3w_0$, this step works with $b$ quiet. Otherwise set
$$
 x=2w,\qquad y=\frac{A-2w}{1+2Kw},\qquad z=1-2w/y,
$$
and choose $0<w<w_0$ so $f_A(w)=(2Rw^2-1)y-w=B$. Its endpoint values are $-A$ and $4Rw_0^3-3w_0$. On this interval $y\ge2w$, $y'=-2(1+Ky)/(1+2Kw)$, so $2y+w y'>0$ and $-y'-1>0$. Therefore $f'_A>0$. The selected odds and $z\in[0,1)$ depend continuously on the child, including the switch where $z=0$.

In either case the new values are
$$ A'=\frac{Kxy}{(1+x)(1+y)},\qquad B'=\frac{B+x+y-w}{(1+x)(1+y)(1+w)}. $$
The second equality is the quit offer on the repaired step by (1). One has $0<A'\le A-x-y$ and $0\le B'\le1$ if $B\le1$, by the on-path payoff formula, which has only the three singleton terms $1,1,-1$ and zero higher payoffs in row $b$. Since $A\le1$ initially, $A'/A\le K/(1+K)$, using $A=x+y+Kxy$ and $xy\le x+y$. Also $|B'-B|\le C(x+y)$ for bounded odds and $w=x/2$. Thus the iterations converge uniformly to $F(S)e_b$ with $F$ continuous. The product of the blank probabilities on the entire joint prefix is at least $\exp[-\sum(x+y+w)]\ge e^{-3/2}$. Its terminal continuation had $B=0$, hence $F(1)\le1-e^{-3/2}<1$. For small $S$ no repair occurs: every $4Rw_0^3-3w_0$ is negative. This is precisely the original return, so $F(S)=3S+O_K(S^2)>S$. Fix $S_0>0$ giving that strict inequality.

**Finite tables.** On $S\in[S_0,1]$, after a common finite number of prepends the limiting $A$ is so small that the three-mover guard is strict at that step and all subsequent steps. We justify stability through the preceding finite sequence, allowing small $U,V$ in the actual children. Fix its compact set of limiting child states. All have $A>0$. For $s=0$ the first, second and fourth equations of (1) select the unique quiet candidate near the limiting one: $x=V+2w$, $y=U+2w$ and $A=x+y+Kxy$. Use it when the third inequality holds. At limiting points where the guard fails or binds, solve the proper equations instead. Define $s=z/N$, and for given $(w,z)$ solve
$$x=(V+2w-s)/(1+A_vsw),\qquad y=(A-x+2s)/(1+x(K-Ls)).$$
The first equation then becomes $z=1+A_u s w-(U+2w-s)/y$. At the parameter limit its derivative in $z$ on moving all terms to the left is one. After eliminating $z$, the derivative of the remaining equation in $w$ is $f'_A(w)>0$. These two nonsingular scalar equations and the positive limiting $x,y,w$ give the nearby proper branch by the implicit function theorem in the parameters $(1/N,L/N,A_u/N,A_v/N,U,V,B,A)$. The scaled equations are smooth in these parameters even at zero. At a switch the sign of $z$ on this branch is the sign of the quiet candidate's surplus $-x-y+w+Rxyw-B$: in the limiting constrained family $z=1-2w/y$ strictly decreases in $w$ while $f_A$ strictly increases. The strict derivatives persist, and at $z=0$ the two branches coincide. Thus choosing the proper branch only on a failed guard gives positive $s$ and a continuous selection. Finite covers of the limiting graph at each step make these continuations uniform. The root selections agree on overlapping neighborhoods after shrinking them, by local uniqueness along the compact single-valued limiting graph.

At selected dates the forced quit offers of $u,v$ are $A_u s y w/[(1+y)(1+s)(1+w)]$ and $A_v s x w/[(1+x)(1+s)(1+w)]$. These vanish uniformly in the parameter limit, using the passive implementation of $N$. The other two outputs converge uniformly to $A',B'$ as well. Thus the finite composition on $[S_0,1]$ converges uniformly to the limiting one. Take one further strictly quiet step when the limiting $A$ is sufficiently small. It sets $U,V$ exactly to zero, and thereafter all the original three-mover steps are exact. Their $A$ decreases geometrically and $B$ remains nonnegative; strict quiet feasibility follows from the small $w_0$. This tail has uniformly summable changes in $B$, so the actual continuous return map has opposite strict signs relative to the identity at $S_0$ and $1$. It has a positive fixed point.

For singleton perturbations the same finite systems (1) vary smoothly in the singleton entries. The two initial solo steps can use the mate that first reaches zero as in the eight-calibration construction, giving the same limiting state at the symmetric center. For the small-$A$ quiet tail, the perturbed $U=V=0$ equations still give $x=Dw,y=Cw$ for positive $D,C$ close to two. The passive $b$ numerator is $B+H w$ with $H$ close to three. Its positive linear term gives the uniform small-odds guard against its cubic grand offer. The positive own output contracts as in the preceding general return. These strict estimates and the two fixed-point signs persist. Compactness gives uniform constants for $K,R$ in fixed compact subsets. Finally truncate the backward word at the fixed point and repeat it. The two original solo dates give uniform contraction per word against every unilateral replacement; the joint dates have exact prescribed and optimal offers at their annotated continuation. The contracting seam argument used above gives vanishing terminal regret and an original fixed uniform payoff for all signed singleton levels.

### The same large passive withdrawal at witness 18

The large-$N$ actual-equilibrium theorem just proved for witness 6 also holds at witness 18 and on its singleton neighborhood for **either** mate $u$ owning the positive passive entry $N=Z_u(vb)$. As there, $a=3$, $b=2$, $K,R$ range on any fixed positive compact set, both implementations of $L$ work, and $0<L,A_u,A_v\le dN$ with $N\ge N_0$. The proof needs the first limiting continuation's asymmetric mate values.

Let $m=-G_{uv}$, $n=-G_{vu}$ and $D=2/n$. Write $(U,V,B,A)$ for a child in order $u,v,b,a$ and $(x,y,s,w)$ for the odds. The original two solo steps from $S e_b$, $0<S\le1$, give $B=0$ and $A=4S/(2+3S)$. For $u=0$ one has $U=0,V=A,m=1,D=1$; for $u=1$ one has $U=A,V=0,m=2,D=2$. All later limiting children have $U=V=0$.

Set $s=z/N$ as before. In the limiting four-mover equations, $x=V/n+Dw$ and $y=(A-x)/(1+Kx)$. The quiet endpoint $w_0>0$ solves $my=U+2w$. At zero $x<A$ and $my>U$ in both first children and all subsequent ones. On $[0,w_0]$ use
$$z=m-(U+2w)/y,\qquad g(w)=-x-y+2w+Rxyw.$$
The passive guard is $B\ge g(w_0)$. On failure one has $g(0)<0\le B<g(w_0)$ and can solve $g(w)=B$ with $0<w<w_0$ and $z>0$. Indeed $y'=-D(1+Ky)/(1+Kx)<0$ and the sign of $(xyw)'$ is the sign of
$$(x+Dw)y-Dxw+Kx^2y.$$
For $u=0$ one has $y\ge2w$, $D=1$; for $u=1$ one has $x=2w$ and $y\ge w$. Both imply $(xyw)'\ge0$, so $g'\ge2-D-y'>0$. The function $z$ strictly decreases, including at the switching endpoint. These are precisely the two transversalities in the finite-step stability proof.

The mover's output is $A'=Kxy/[(1+x)(1+y)]\le A-x-y$ and $w\le x$. The passive numerator for $b$ is $B+x+y-2w$; it is nonnegative for both orientations since $x\ge w$, $y\ge2w$ for $u=0$ and $x=2w$ for $u=1$. Thus $0\le B'\le1$. The blank product of the limiting prefix is at least $\exp[-2A_{\rm initial}]\ge e^{-8/5}$, hence $F(1)<1$. As $S$ decreases to zero, the initial quiet numerator before subtracting the cubic grand offer is at least $w$ in both orientations, as it is on the subsequent quiet steps. The original quiet return therefore gives $F(S)=4S/3+O_K(S^2)>S$. The same contraction $A'/A\le K/(1+K)$, summable changes of $B$, and finite-chart perturbation now apply. In particular, the finite scaled equations are smooth: their mate rows read $U=my-G_{ub}s-2w+sy(A_uw-N)$ and $V=nx-G_{vb}s-2w+A_vxsw$. The remaining rows are the preceding $B,A$ equations with $+2w$ in the required $B$. A strictly quiet final chart resets both mate values to zero and leaves the uniformly positive linear quiet guard for the exact tail. The two solo dates and contraction at the seam give the same signed uniform-payoff conclusion.

### Removing the bound on the other withdrawal

In the witness-6 theorem, when the grand withdrawal is implemented by $Z_a(I)=-L$, the entire range $0<L<\infty$ is allowed: only $A_u,A_v\le dN$ is needed at large passive $N$. For $0<K\le1$ the same holds for the positive passive implementation of $L$. All constants are locally uniform for the indicated $K,R>0$ and on singleton neighborhoods. Thus in these cases both withdrawal prices can grow independently without imposing any upper ratio between them.

The sure pair handles $mL\ge KN$. Otherwise put $\ell=mL/(KN)\in(0,1)$, allowing its closed interval in taking limits. At the center $m=1$, so the limit equations of the previous proof now use $\lambda=L/N=K\ell$ and the terms $U=y(1-z)-2w$, $A=x+y+xy(K-\lambda z)$. For each seed and each joint date keep the same quiet endpoint $w_0$ and take $w=\theta w_0$, $\theta\in[\epsilon,1]$, where a small fixed $\epsilon>0$ is specified below. The other variables are
$$
 x=2w,\qquad y=\frac{A-x-\lambda x^2}{1+(K-\lambda)x},\qquad z=1-x/y .
$$
Indeed $y\ge x>0$ follows from $A\ge2x+Kx^2$, giving $0\le z<1$. Use $B'=(B+x+y-w)/[(1+x)(1+y)(1+w)]$ for the output of the quiet player for *every* trial $\theta$. Write $g=-x-y+w+Rxyw$. At a feasible choice this waiting payoff agrees with the appropriate prescribed payoff, since we shall enforce $B=g$ for $\theta<1$ and $B\ge g$ for $\theta=1$.

For the negative-grand implementation $A'=(K-\lambda z)xy/[(1+x)(1+y)]\le A-x-y$, and $A'/A\le K/(1+K)$ as before. For the positive passive implementation with $K\le1$, $A'\le Kxy\le (x+y)^2/4\le A^2/4$. Both bounds apply to all trial paths and keep $A\le1$. They give $\sum(x+y)<\infty$ uniformly: the former telescopes, and in the latter case $x+y\le A$ decreases in its geometric upper bound. The limiting $F(1)<1$ uniformly over the trial parameters because $0\le B'\le1$ and the total joint blank product stays bounded away from zero. The trial $A$ remains strictly positive at every fixed finite step. Choose $J$ so after $J$ steps the quiet guard is strictly satisfied forever, uniformly in all $J$ trial parameters, at the center. Indeed the quiet tail has $g(w_0)=4Rw_0^3-3w_0<0$ when $A$ is small. Now impose joint compatibility on the first $J$ choices without needing a unique inverse for $g$. Take $\epsilon$ small enough that $Rxw<1/2$ at $w=\epsilon w_0$ for all $A\le1$. Then $g<0\le B$ at that endpoint. At any fixed point of the update
$$
 \theta_j\ \longmapsto\ \operatorname{proj}_{[\epsilon,1]}(\theta_j+B_j-g_j)
$$
the lower endpoint is impossible and the other two cases are exactly the required comparisons.

These trial maps exist for all sufficiently close finite tables by uniform perturbation of a *finite* sequence. More explicitly, at fixed $w$, the scaled $U$ and $A$ equations select $z,y$ transversely at each limiting trial: eliminate $z=1-x/y$; the remaining derivative in $y$ is $1+(K-\lambda)x\ge1$. The $V$ equation selects $x=2w$. The quiet endpoint $w_0$ is selected by the three usual equations at $z=0$, now allowing the nearby actual $U,V$. Its switch sign is preserved: $y$ decreases strictly as $x$ increases, by implicit differentiation of $A=x+y+(K-\lambda)xy+\lambda x^2$. Thus $z$ strictly decreases up to its simple zero at $w=w_0$, and remains nonnegative throughout the perturbed trial interval. These statements persist on the compact parameter and trial graphs at each of the $J$ steps with $S\in[S_0,1]$. The error parameters here are $1/N,A_u/N,A_v/N$ and the singleton perturbation, with $\ell$ retained as a free parameter. The finite trial outputs use the actual forced offers for $u,v,a$ and $b$'s actual *waiting* offer. For fixed points these are correct even at a proper $b$ date. As above, force one more strictly quiet date to reset $U,V$ to zero, then attach the continuous uniformly convergent exact quiet tail. This defines $F(S,\theta)$ for the finite tables. Strict signs at the lower $\theta$ faces and the upper seed persist. At a sufficiently small fixed $S_0>0$ all trial $g$ are strictly negative, by $x=2w$, $y\ge x$ and the uniform small bound on $A$. Thus a fixed point of the $\theta$ updates at $S_0$ must choose $\theta_j=1$ at each step; the original quiet return there has $F(S_0)>S_0$, also after perturbation.

Adjoin the update $S\mapsto\operatorname{proj}_{[S_0,1]}F(S,\theta)$ and apply Brouwer to the resulting continuous map of the compact box. Both seed endpoints have been excluded, and each $\theta$ comparison therefore gives an actual Nash prepend at $F(S,\theta)=S$. The truncation and repetition argument of the preceding theorem completes the proof.

### Three more passive-withdrawal tails with opposite singleton signs in the entrant row

The same large-passive-$N$ statement holds at witnesses $8,19$ for $u=1$ and at $21$ for $u=0$, on neighborhoods, with both implementations of $L$. Here $a=3,b=2$. The following sufficient conditions give the common proof. For the chosen withdrawal owner $u$ and the other mate $v$ put
$$m=-G_{uv},\quad n=-G_{vu},\quad C=G_{ua}/m,\quad D=G_{va}/n,\quad d=-G_{ba},\quad h=G_{bu},\quad i=G_{bv},\quad l=-G_{au},\quad k=-G_{av}.$$
The original two solo steps and quiet return apply with its positive initial slope (their choice of the first mate may differ from the withdrawal owner). In addition require $m,n,C,D,d,h,i,k>0$, $l<0$, $E=lD+kC>0$ and $H=hD+iC-d>0$. All three named assignments satisfy these conditions. In their order $(C,D,l,k,h,i,d)$ equals $(2,2,-1,2,1,2,1)$, $(2/3,3/2,-1,3,1,1,1)$ and $(2,1,-1,2,1,1,2)$.

For a limiting child $(U,V,B,A)$ in owner order $u,v,b,a$, write $X=V/n$, $Y=U/m$. Put $x=X+Dw$, $y=(A-lx)/(k+Kx)$. For $s=z/N$ the limiting mate and entrant equalities give $z=m[1-(Y+Cw)/y]$. The quiet endpoint $w_0>0$ solves $y=Y+Cw$. Its existence follows from the preceding quiet return at the first child and from $E>0$ subsequently. Indeed the numerator of $y-(Y+Cw)$ over $k+Kx$ is the strictly decreasing quadratic
$$A-lX-kY-KXY-[E+K(XC+YD)]w-KDCw^2.$$
Thus $z>0$ earlier and $z'(w_0)<0$. For $B\ge0$ on $0<w\le w_0$ set
$$ P_B(w)=\frac{B+hx+iy-dw}{xyw}.$$
If the quiet guard fails, $R>P_B(w_0)$, and we instead require $R=P_B(w)$. This function decreases strictly from infinity. Indeed $xw,xy,yw$ increase strictly and $w/y$ also increases. For $xy$ use $d(xy)/dx=(ky-lx)/(k+Kx)>0$. For $yw$ and $w/y$ use, respectively, the positive quantities $(k+KX)y-Dlw$ and $A-lX+DKwy$ after differentiating. If $hD\ge d$, write $P_B=(B+hX)/(xyw)+(hD-d)/(xy)+i/(xw)$. If $hD<d$, write its last two terms as $[i+(hD-d)w/y]/(xw)$. The bracket decreases and is positive since $y\ge Cw$ and $H>0$. These formulas also prove $P'_B(w)<0$ throughout. The proper comparison and the quiet/proper switching surface therefore have exactly the nonsingular derivatives used above.

The passive output of $b$ has nonnegative numerator $B+hx+iy-dw\ge H w$ and stays below $\max(h,i)$ whenever its child does. The active output $A'=Kxy/[(1+x)(1+y)]$ obeys $A-A'\ge lx+ky$. After the first step $X=Y=0$. Since $x=Dw$ and $y/w\ge C$, the last expression is at least $\min(k,E/(D+C+1))(x+y+w)$. The first step has bounded odds on the compact seed interval. Later $A$ is decreasing, so $x,y,w$ are uniformly bounded and $A=lx+ky+Kxy\le c_K(x+y+w)$. Thus $A$ contracts geometrically and the sum of all these odds is uniformly bounded. The blank product stays strictly positive, giving the strict upper fixed-point sign from the terminal $B=0$ at the two solo steps. At small seed the quiet numerator is at least $Hw$ against the cubic grand term, so the original positive-slope return gives the opposite sign. The finite stable charts, quiet resetting step and signed seam argument now follow as in the four-player-date theorem. This proves existence for $N\ge N_0$ and $0<L,A_u,A_v\le\delta N$ uniformly over positive compact sets of $K,R$.

### The large negative participating withdrawal at witness 6

Take singleton witness 6 with $u=0,v=1,b=2,a=3$ as in the passive-withdrawal theorem. Instead implement $N$ by the negative participating entry $Z_u(uvb)=-N$. For every $K,R>0$ there are $d>0,N_0<\infty$ such that all tables
$$N\ge N_0,\qquad 0<L,A_u,A_v\le dN$$
have a uniform-equilibrium payoff. Both implementations of $L$ and either mate as withdrawal owner are allowed. The constants are uniform on compact subsets of the positive $(K,R)$ quadrant. This uses a new two-coordinate return. The large negative payoff remains present in the mover's continuation at a repaired date.

**Limiting dates.** Use child order $(U,V,B,A)$ and odds $(x,y,s,w)$, retaining $z=Ns$ as $1/N,L/N,A_u/N,A_v/N$ tend to zero. At an all-proper date the four required child values are
$$U=y-2w-zy,\quad V=x-2w,\quad B=-x-y+w+Rxyw,\quad A=x+y+Kxy.$$
The forced quit value of $u$ now converges to $-zy/[(1+y)(1+w)]$. A return starts at $(0,v,b,0)$ with $0<b\le1$ and $0\le v\le4b$. Prepend the two solo dates $a,b$ as before. Their output is
$$ (0,V,0,A),\qquad V=\frac{v}{1+3b},\qquad A=\frac{4b}{1+3b}.$$
Thus $V\le A\le1$. The solo owners tie at zero and waiting players get nonnegative payoffs.

For $U\le0,V\ge0,A\ge0$ define a nonnegative upper endpoint $w_0$. If $A>V-U$ it is the unique $w_0>-U/2$ for which $x=V+2w_0$, $y=U+2w_0$, $A=x+y+Kxy$. Otherwise set $w_0=-U/2$. These prescriptions agree at $A=V-U$. For a trial $w=\theta w_0$, $0<\theta\le1$, set
$$
 x=\min(A,V+2w),\quad y=(A-x)/(1+Kx),\quad t=y-U-2w,\quad
 g=-x-y+w+Rxyw,\qquad D=(1+x)(1+y)(1+w).
$$
One has $t\ge0$. When $y>0$, $x=V+2w$ and $y\ge U+2w$. When $y=0$, $x=A$, $w\le -U/2$ and $V+2w\ge x$. Use the following outputs for all trials:
$$
 U'=-\frac{t}{(1+y)(1+w)},\quad V'=\frac{V+2w-x}{(1+x)(1+w)},\quad
 B'=\frac{B+x+y-w}{D},\quad A'=\frac{Kxy}{(1+x)(1+y)} .
$$
For $\theta=1$ these are an actual three-mover stage with $b$ waiting when $y>0$, and a stage on $u,a$ when $y=0$, provided $B\ge g$. In the latter case $x=A,w=-U/2$, both $U',A'$ vanish, and the passive $v$ numerator is $V-A-U\ge0$. This also covers a zero hazard for one or both movers. For an interior trial with $B=g$ and $x,y,w>0$, the equations give a repaired date with $z=t/y$.

**Bounds for arbitrary trials.** One always has $0\le A'\le A-x-y$, and $A'/A\le K/(1+K)$ for $0<A\le1$ since $xy\le x+y$. The first trial has $B=U=0$, $V\le A$. Unless $V=A$ and $w=0,y=0$, its $x=V+2w$ and $y>0$, with $V'=0$. Here $B'\ge0$, $-1\le U'\le0$, and
$$D(4B'+3U')=4x+2w+y(1-3x)+6xw\ge0.$$
At the exceptional $x=A=V,y=w=0$ the same conclusions hold. After this first trial all states satisfy
$$
 -1\le U\le0,\quad V\ge0,\quad 0\le B\le1,\quad 4B\ge V-3U .
$$
Indeed writing $a_0=-U\le1$, the bound $t\le y+a_0$ propagates $-U'\le1$. When $y>0$, $V'=0$ and
$$D(4B'+3U')=(4B-3a_0)+(4-3a_0)x+y(1-3x)+2w+6xw\ge0.$$
For $x\le1/3$ all terms are nonnegative; otherwise $x+y\le1$ bounds the middle terms below by $1-3x+3x^2>0$. Here $w\le x/2$ gives $B'\ge0$. When $y=0$,
$$D(4B'-V'+3U')=(4B-V-3a_0)+x(5-3a_0)+6xw\ge0,$$
and $w\le a_0/2\le 2B/3$ implies $B'\ge0$. In all cases $B'\le1$ since this is the waiting value under odds $x,y,w$, with singleton rewards $1,1,-1$, zero higher rewards and child $B\le1$. In fact $B'>0$ at every step from a seed with $b>0$: on the first trial $x+y>0$, and every subsequent positive $B$ remains positive.

Consider $J$ trials followed by one forced upper endpoint and then only quiet stages. The $A$ values decrease geometrically uniformly in the trials. Once $A$ is small the upper endpoint's $b$ guard is strict: for $y>0$ it has $w\le x/2$ and $Rxw<1/2$, and for $y=0$ one has $g\le w-A\le2B/3-A<B$. At that endpoint either a $u,a$ stage resets $U=A=0$ and leaves the new $(0,V',B',0)$, or a quiet three-mover stage resets $U=V=0$. In the latter case the exact small-$A$ quiet tail from the previous theorem gives $(0,0,F_b,0)$. At the transition $y=0,V+2w=x$ these two outputs agree, since $A',V'$ vanish and the tail changes $B'$ by $O(A')$. Denote the resulting output by $(0,F_v,F_b,0)$; it is continuous in the seed and trials, and $F_b>0$, $0\le F_v\le4F_b$.

The upper seed has $F_b<1$ uniformly in all trials. Indeed $\sum(x+y)\le A_{\rm initial}\le1$. Up to the first date with $y=0$ one has $w\le x/2$. At this first $y=0$ date $w\le1/2$, and thereafter $A=x=y=0$ and $-U$ drops by at least $w$ at every off-solution trial. This gives a uniform bound on the sum of all $w$, including the tail. The blank product of the joint prefix is uniformly bounded below, and its child immediately after the two solos had $B=0$. On the lower seed choose $b_*>0$ small. For any choices satisfying the $b$ comparisons, all stages there are quiet since $x,y\le A\le4b_*$ and the $y=0$ bound just proved excludes an interior $b$ choice. At the first quiet date, uniformly in $0\le v\le4b$,
$$
 F_b=3b+v/4+O_K(b^2)>b
$$
for all sufficiently small $b>0$. Indeed $w=(A-V)/4+O_K(b^2)$, the first passive value is $V+3w+O_K(b^2)$, the new $A'$ is $O_K(b^2)$ and later changes are $O_K(b^2)$. At $v=4b$ the first quiet date instead has $x=A=V$, $y=w=0$, gives $F_v=0$, and all trials are identical because $w_0=0$.

**Finite tables and simultaneous choice.** Work on $b\in[b_*,1]$, $\tau=v/b\in[0,4]$, and $J$ controls $\theta_j\in[\epsilon,1]$. Take $J$ large to reach the strict final quiet region just proved. Choose $\epsilon>0$ small so $Rxw<1/2$ at $w=\epsilon w_0$ on the whole bounded domain. On this face $g<B$ uniformly at each of the finitely many limiting trials: if $y>0$, $w\le x/2$, and if $y=0$, $w\le2B/3$ except at the first date where the only such trial has $w=0,x=A>0$. The same inequalities hold for a sufficiently large $J$ regardless of the value of $\epsilon$. All constants can be chosen for a fixed compact set of $K,R$.

Here are details for replacing the finite trial graphs by continuous maps at actual finite prices. They avoid dividing by a disappearing trial $y$. On each compact limiting graph $g-B$ is strictly negative wherever $x y w=0$. For $w=0$ this follows from $g=-x-y$ and $A+B>0$; $x=0$ or $y=0$ was handled above. Choose $\eta>0$ so that $g-B\ge-3\eta$ requires all three odds bounded strictly above zero. Use a continuous cutoff $\chi$ equal to one on $g-B\ge-\eta$ and zero on $g-B\le-2\eta$.

On the support of the cutoff, keep the trial's $w$ fixed and continue its other variables using the exact equations
$$
 x=(V+2w-s)/(1+A_vsw),\quad
 y=(A-x+2s)/(1+x(K-Ls)),\quad
 z=1+A_usw-(U+2w-s)/y,\qquad s=z/N.
$$
These are smooth in $(1/N,A_v/N,A_u/N,L/N)$. At the zero parameters, the first two equations select $x,y$ successively, independently of $z$, and the third selects $z=t/y$. The Jacobian is triangular with diagonal ones. Compactness and local uniqueness give uniformly close continuous solutions in neighborhoods of these compact graphs. Where $\theta=1$ on this support the endpoint is the quiet three-mover endpoint and $z=0$ exactly; where $\theta<1$, $z>0$ at close finite parameters. For the latter assertion, away from the endpoint use strict positivity at the limit. At a quiet endpoint $y=U+2w>0$, its $z$ derivative with respect to $w$ is strictly negative, since $y=(A-V-2w)/(1+K(V+2w))$ strictly decreases. This sign and the simple endpoint zero persist uniformly near the switching set.

Use the actual forced offers for $u,v,a$ and the passive value for $b$ on this chart, and the actual comparison $g=-x-y+w+Rxyw$ with these continued odds. Interpolate the four outputs and this comparison with the limiting formulas using $\chi$. Thus the maps are continuous and uniformly close to the limiting ones. At $\theta=1$ both formulas agree exactly on a genuine quiet ($b$ waiting) stage for the given child, including the $u,a$ switch; this uses $s=0$. If an interior control satisfies the interpolated equality $g=B$, it lies in $\chi=1$ for a sufficiently small perturbation and gives a genuine four-proper stage. For evaluating fake intermediate inputs one may truncate $U$ above at zero and $V,B,A$ below at zero. All true-stage outputs already have these signs: on the proper chart $U'=s y(A_u w-N)/[(1+y)(1+s)(1+w)]\le0$ and $V'\ge0$, while $A'\ge0$ for small $L/N$ by the positive lower odds on that graph. On a true upper endpoint $V'$ is either zero or the nonnegative passive value. All $B$ outputs after the first date keep a positive margin by compactness. Induction over the finite steps keeps all trial states uniformly close to the limiting graphs.

The last forced quiet endpoint and its exact tail are continuous on a neighborhood of these last states and use only the six-position entries already specified. The strict $b$ guard at that endpoint persists by compactness, and by geometric decay the later $U=V=0$ quiet tail is uniformly valid when $A$ is small. Its seam varies continuously, also at the switch to the $u,a$ stage. Hence the actual trial output and its comparison maps converge uniformly to the limiting ones over the whole box.

Apply Brouwer using updates $\theta_j\mapsto\operatorname{proj}_{[\epsilon,1]}(\theta_j+B_j-g_j)$, $b\mapsto\operatorname{proj}_{[b_*,1]}F_b$ and $\tau\mapsto\operatorname{proj}_{[0,4]}(F_v/F_b)$. The strict lower control bounds exclude $\theta_j=\epsilon$. All chosen stages therefore meet their actual $b$ comparison. Uniform convergence excludes $b=1$. At $b=b_*$ every fixed limiting control is quiet and $F_b>b_*$. At $\tau=4$ the limiting first trial has $w_0=0$, then returns $F_v=0$. Compactness excludes these two fixed-point faces at sufficiently close finite parameters, by passing any contrary sequence to a limiting fixed point. At $\tau=0$ the true output $F_v$ is nonnegative, so clipping does not change a fixed equality. Thus the actual seam is exactly $(0,v,b,0)$. Truncate any infinite quiet tail and repeat the resulting finite word. The fixed solo dates for $a,b$ bound the block Lipschitz factors of both the prescribed and unrestricted best-reply values strictly below one, uniformly in the truncation. As in the previous theorem this gives a signed uniform-equilibrium payoff.

The conclusion also persists on a singleton neighborhood of witness 6, common to each fixed positive compact set of $K,R$. To verify this at the upper endpoints as well as inside the proper charts, write
$$
m=-G_{uv},\ n=-G_{vu},\ c=G_{ua},\ c'=G_{va},\ h=G_{bu},\ i=G_{bv},\ d_0=-G_{ba},\ f=G_{ab},\ \ell=-G_{au},\ k=-G_{av}.
$$
These constants are positive near this matrix. The first solo odds are $b/d_0$. After that stage $B=0$; prepend the solo $b$ at the smaller of the mates' two nonnegative zero-value thresholds, their current payoffs divided by $-G_{ub},-G_{vb}$ respectively. One mate reaches zero and the other stays nonnegative. The first child varies continuously, including the choice boundary. The waiting guards there persist as the entrants have positive singleton gains on the other's solo date, and the active owners tie at zero.

For later children $U\le0$ use $w_0=-U/c$ when $A\le(\ell/n)(V-c'U/c)$. Otherwise solve $A=\ell x+k y+Kxy$ with $x=(V+c'w_0)/n$, $y=(U+c w_0)/m$. At the boundary these prescriptions agree. In the initial child it is also possible that $U>0$ and $V=0$. This can happen only close to the limiting initial mate tie $v=0$ by compactness, so $A$ stays bounded below and $U$ tends to zero uniformly as the singleton perturbation shrinks. Then the strictly positive quiet endpoint exists by the same scalar equation. Use trials $w=\theta w_0$ with
$$x=\min(A/\ell,(V+c'w)/n),\qquad y=(A-\ell x)/(k+Kx),\qquad t=my-U-cw.$$
Their outputs replace $V+2w-x$ by $V+c'w-nx$ and $B+x+y-w$ by $B+hx+iy-d_0w$, and use $g=-hx-iy+d_0w+Rxyw$. On the proper cutoff chart the three exact finite equations become
$$
x=(V+c'w+G_{vb}s)/(n+A_vsw),\quad
y=(A-\ell x+fs)/(k+x(K-Ls)),\quad
z=m+A_usw-(U+cw+G_{ub}s)/y .
$$
Their transverse limit at fixed $w$ persists, and their $z=0$ endpoint is exactly the perturbed quiet endpoint. Consequently all finite trial maps, their cutoff margins and their strict fixed-point boundary exclusions persist by uniform convergence to the center graphs. The exact tail after a resetting quiet date uses $x=c'w/n$, $y=cw/m$ when $U=V=0$; its passive numerator $B+(hc'/n+ic/m-d_0)w$ has a uniformly positive linear coefficient, and $A=\ell x+k y+Kxy$ still gives a uniformly geometrically decreasing positive sequence. The finite construction, its exact pair/triple switch, and the signed seam argument therefore work for all singleton matrices in the stated neighborhood.

### A negative participating withdrawal at witness 18

The large-$N$ participant-withdrawal conclusion also holds near witness 18 when $u=0,v=1$, $a=3,b=2$. Thus $N$ is the magnitude of the negative participating reward $Z_0(012)$; the other withdrawal may have either implementation. For every compact positive set of $K,R$ there are $d>0,N_0<\infty$ and a neighborhood of this singleton matrix giving original uniform equilibrium whenever $N\ge N_0$ and $0<L,A_u,A_v\le dN$.

Start instead from the rectangular seed $(0,v,b,0)$, $0\le v\le3$, $b_*\le b\le1$. The solo $a$ odds are $b/2$; the solo $b$ then makes row $u$ zero. Both stages have their proper comparisons and give
$$ U=B=0,\qquad V=(2v+4b)/(2+3b),\qquad A=4b/(2+3b)\le4/5.$$
The same endpoint and trial formulas as in the variable-singleton version apply with $m=1,n=2,c=c'=2,h=i=1,d_0=2,f=2,\ell=k=1$. Thus $x=\min(A,V/2+w)$, $y=(A-x)/(1+Kx)$, $t=y-U-2w$, and the passive numerators in $V',B'$ are $V+2w-2x$ and $B+x+y-2w$, respectively. At the upper endpoint when $y=0$ the pair $u,a$ resets $U,A$ and leaves $V'\ge0$. On the initial trial that ends this way $w=0$ because $U=0$. All earlier notation for $D$ and $g$ uses the actual coefficients; in particular $g=-x-y+2w+Rxyw$.

Write $a_0=-U$. The uniform invariant is
$$0\le a_0+A\le4/5,\qquad 0\le B\le1,\qquad B\ge a_0.$$
Indeed $a_0'\le(y+a_0)/(1+y)$ and $A'\le(A-x-y)/(1+y)$, giving the first bound. At every trial
$$D(B'-a_0')=(B-a_0)+x(1-a_0-y+2w)\ge (B-a_0)+x/5.$$
These inequalities include $y=0$ and the initial $U=B=0$. At that first trial $x>0$ since $A>0$ and $V\ge A$, so $B>a_0$ persists thereafter. Also $B'\le1$ by the waiting formula. The trial $V'$ is bounded by $\max(V,2)$: its numerator is $V+2w-2x$ against $u,a$ odds, and it vanishes if $y>0$. At the top face $v=3$ the initial solo stages give $V<3$ uniformly for $b\ge b_*$, hence all outputs have $F_v<3$. No coupling of the two seed coordinates is needed.

At a small-$A$ upper endpoint with $y>0$, $x\ge w$ and $y=U+2w$. The previously produced mate deficit $U$ can be substantial. Nevertheless $B>a_0$ gives
$$B-g=B+x+y-2w-Rxyw=B-a_0+x-Rxyw>0$$
as soon as $Ryw<1$. If $y=0$ at the endpoint, $B-g=B+A-a_0>0$. The reset and exact quiet tail therefore work as before. For an arbitrary limiting trial with $xyw=0$, either $w=0$ and $g=-x-y<B$, or $y=0$ and $2w\le a_0$, so $B-g\ge B-a_0+x>0$. The analogous strict inequality at the initial trial follows from $V\ge A>0$. At the lower control face choose $\epsilon>0$ small. More explicitly the formulas extend to $\theta=0$, where $w=0$ and $x+y+B>0$ on every finite trial graph, including earlier choices in $[0,1]$. The first positive $x$ bound and the displayed invariant persist at $\theta=0$, giving strict lower-face comparisons uniformly by compactness. This supplies the proper cutoff, finite charts and control endpoint guards for the Brouwer argument.

The sum of $x+y$ over the entire prefix is bounded by the initial $A$. Before the first zero $y$ one has $w\le x$. At the zero and later trials the same decrease of $a_0$ bounds their extra $w$'s. The blank product is uniformly positive and $F_b(1,v)<1$. For sufficiently small $b>0$, every true trial on the first date is quiet. If $V\ge2A$ its upper endpoint is the solo $u$ at $x=A$, $w=0$, giving $F_b=A/(1+A)=2b+O(b^2)$. Otherwise $V<2A=O(b)$; the first quiet odds satisfy $w=(A-V/2)/3+O_K(b^2)$, $y=2w$, $x=V/2+w$. Its passive output is $x+O_K(b^2)$, and later changes are $O_K(b^2)$, hence $F_b=(A+V)/3+O_K(b^2)\ge4b/3+O_K(b^2)$. To exclude interior controls on this lower seed, for $y>0$ one has $x\ge w$, and $t\ge0$ gives $y\ge2w-a_0$. Thus $B-g\ge B-a_0+x(1-Ryw)>0$ for all trials with $A$ small and $y>0$, as $w\le x\le A$. For $y=0$ use the strict guard above. This establishes the strict lower fixed-point boundary.

Use the previous product Brouwer proof with the updates for $b$ and the controls unchanged and $v\mapsto\operatorname{proj}_{[0,3]}F_v$. Nonnegativity at the pair end and the strict upper face exclude spurious clipping. The finite proper chart and the continuous exact quiet tail are those in the variable-singleton formulas. The same limiting fixed-point boundary signs and finite graph cutoff comparisons persist in a singleton neighborhood. The initial $b$ solo continues to zero row $u$ there, since only that mate sees a negative $b$ singleton. This gives the claimed signed uniform equilibrium.

### The other negative participating withdrawal at witness 18

Take $u=1,v=0,b=2,a=3$ at witness 18 with $Z_u(uvb)=-N$. Fix any compact subset of the positive $(K,R,A_v)$ octant, where $R=Z_b(I)$ and $A_v=Z_v(I)$. In a singleton neighborhood, all sufficiently large $N$ give original uniform equilibrium whenever $0<L,A_u\le dN$ for a sufficiently small common $d>0$, with either implementation of $L$. Two different four-mover stages are used. On one the small odds belong to $b$, on the other to $v$.

Write $(U,V,B,A)$ for the child values, $(x,y,s,w)$ for the four odds in the same order, and $a_0=-U$. From the seed $(0,v,b,0)$ use coordinates $T=b+v/4\in[\rho,2]$, $\tau=v/(4T)\in[0,1]$. Prepend solo dates $a,b$ with odds $b/2$ and $(v+b)/(1+b/2)$. Their owners tie at zero and the waiting players get nonnegative values. This gives
$$U=(v+2b)/D_0,\quad V=B=0,\quad A=(2v+2b)/D_0,\qquad D_0=1+v+3b/2.$$
Thus $0<U\le A<2$, $U\ge A/2$ and $A-U<1$.

**The primary trials.** First let $(1/N,L/N,A_u/N)$ tend to zero and use $s=z/N$. If $A>V+a_0$, choose the quiet endpoint $x=V+2w_0,y=w_0-a_0/2,A=x+y+Kxy$. Its unique root has $w_0>a_0/2$ and is strictly positive also at the initial child. Otherwise put $w_0=a_0/2$. For $w=\theta w_0$, $0<\theta\le1$, set $x=\min(A,V+2w)$, $y=(A-x)/(1+Kx)$ and $D=(1+x)(1+y)(1+w)$. On $y>0$ the outputs and the comparison for $b$ are
$$a_0'=(2y+a_0-2w)/[(1+y)(1+w)],\quad V'=0,\quad B'=(B+x+y-2w)/D,\quad A'=Kxy/[(1+x)(1+y)],\quad g=-V-y+Rxyw.$$
At $\theta=1$ this is a true quiet triple if $B\ge g$, and at $B=g$ it is a repaired stage with $z=(2y+a_0-2w)/y\ge0$, strictly positive for $\theta<1$. The zero-$y$ control is defined below.

After the first trial $a_0,A,V\ge0$, $a_0+A\le1$, $0\le B\le1$, $a_0\le3B$. Indeed $a_0'+A'\le (a_0+2y-2w+Kxy)/(1+y)\le(a_0+A+y)/(1+y)\le1$. On later positive-$y$ trials $x=V+2w\le A\le1$ gives
$$D(3B'-a_0')=(3B-a_0)+3x+y-4w+x(2w-a_0-2y)\ge (3B-a_0)+x(1-a_0-y)+y(1-x)\ge0.$$
On the first trial $x=2w$ and $D(2B'-a_0')=U+x(1+x+U-2y)\ge3x/2+3x^2/2+y(1/2-3x/2)>0$. For $x>1/3$ the last expression is at least $1-2x+3x^2$ since $x+y\le2$; for smaller $x$ use $x+y>0$. The passive formula gives $0<B'\le1$ on every positive-$y$ trial. Also $A'\le A-x-y$, with $A'/A\le K/(1+K)$ after the first trial.

**The upper endpoint on the pair face.** When $A\le V+a_0$ try $u,a$ with $x=A,w=a_0/2$. This works if $a_0\le A+B$, and gives $U'=A'=0$, $V'=(V+a_0-A)/[(1+A)(1+a_0/2)]$, $B'=(B+A-a_0)/[(1+A)(1+a_0/2)]$. Otherwise use
$$s_b=(a_0-A-B)/3>0,\qquad x=A+2s_b,\quad w=(B+x)/2.$$
With $y=0$ all three movers $u,b,a$ tie at zero. The guard of the quiet $v$ is $V+B\ge s_b+A_vxs_bw$. On success the output is $(0,(V+B-s_b)/[(1+x)(1+s_b)(1+w)],0,0)$.

On failure use all four movers with $y=z/N$. There is a unique $0<s<s_b$ solving
$$x=A+2s,\quad w=(B+x)/2,\quad s+A_vxsw=V+B.$$
Here $V+B>0$ and the left side increases strictly. Set $z=(a_0-A-B-3s)/s$; the four indifferences give
$$a_0'=(a_0-A-B-3s)/[(1+s)(1+w)],\quad V'=(V+B-s)/[(1+x)(1+s)(1+w)],\qquad A'=B'=0.$$
These outputs agree with the three-mover outputs at $s=s_b$.

In fact $V'>H(a_0')$ where $H(t)=t/3+t^2/9$. We have $V'>4a_0'/9$: in $9(V+B-s)>4(a_0-A-B-3s)(1+A+2s)$ the worst case has $V=0,B=a_0/3,A=0$, since $a_0\le1$ makes the right side decreasing in $A$. For $r=s/a_0\in[0,2/9]$ this follows from $4(2-9r)(1+2r)<9(1-3r)$ or $1-7r+72r^2>0$. Repeat the endpoint procedure on $(U',V',0,0)$. On another repair $s+2A_v s^3=V$, $0<s<a_0/3$, and
$$a_0'=(a_0-3s)/(1+s)^2,\qquad V'=(V-s)/[(1+2s)(1+s)^2].$$
At $V=H(a_0)$ direct subtraction gives
$$V'-H(a_0')=\frac{s^2[(a_0-3s)^2+9(s+1)^2]}{9(1+s)^4(1+2s)}>0.$$
A previous strict excess is added after division by $(1+2s)(1+s)^2$. At sufficiently small $a_0$ one has $H(a_0)\ge a_0/3+2A_v(a_0/3)^3$, so the quiet $u,b,a$ endpoint terminates. Before then every repair reduces $a_0$ by at least $3s$, uniformly positive for $a_0$ bounded below since $V\ge H(a_0)$. Thus only boundedly many secondary repairs occur. The completed endpoint has $a_0'=A'=0$ and is continuous also at a switch to zero $v$ hazard, where the following quiet completion changes $V'$ by $O(a_0')$. Each completion has $0\le B'\le1$, $V'\le\max(V,2)$ by the waiting numerator $V+2w-x-s$. It leaves $V'+B'>0$ when $V+B>0$, using $s_b\le2B/3$ on the first three-mover candidate and the strict $H$ excess on its successors.

**Completing the control maps.** On the primary $y=0$ arc take $g=-V$, agreeing with the other formula at the boundary. At its lower endpoint $w_1=(A-V)_+/2$, use
$$a_0'=(a_0-2w_1)/(1+w_1),\quad V'=(V+2w_1-A)/[(1+A)(1+w_1)],\quad B'=(B+A-2w_1)/[(1+A)(1+w_1)],\quad A'=0.$$
For $w_1\le w\le w_0=a_0/2$ interpolate linearly between this state and the completed upper endpoint. If $w_1=w_0$ the two definitions agree. For $w_1>0$ the lower bounds pass by continuity from $y>0$. When $w_1=0$ one has $V\ge A$, $a'_0=a_0$, $B'=(B+A)/(1+A)\ge B$. The upper endpoint has $a'_0=A'=0$, so the same convex bounds hold throughout. The first trial always has $y>0$. Subsequently $V+B>0$ persists: at the lower endpoint the sum of the two numerators is $B+V$ and at the upper endpoint use the preceding strict conclusion. Thus $g<B$ everywhere on the zero-$y$ face of each finite trial graph.

Use $J$ controls $\theta\in[\epsilon,1]$ followed by a forced upper endpoint and quiet tail. Choose $J$ large by geometric decrease of $A$, which becomes zero after any zero-$y$ trial. On every final positive-$y$ upper endpoint $Rxw<1$, giving $g=-V-(1-Rxw)y<B$, and $U'=V'=0$. The exact subsequent quiet tail has $x=2w,y=w$, a positive linear passive numerator $B+w$ and summable odds. It varies continuously also at the switch to the completed pair face, since $A'\to0$ there. On the lower control face choose $\epsilon>0$ small so $Rxw<1/2$. Then $g<B$ uniformly by the same inequalities and finite compactness. The inequality is strict wherever $xyw=0$. At a positive-$y$ quiet endpoint $z=2+(a_0-2w)/y$ has a simple zero, since $y=(A-V-2w)/(1+K(V+2w))$ strictly decreases. As in the preceding two-coordinate return, continue the three primary proper equations at fixed $w$ via the triangular $(x,y,z)$ chart and use a cutoff supported near $g=B$. Interpolate its outputs and comparison there. At the pair-face upper control use the actual completed endpoint as specified below, keeping the control comparison $-V$. Finite induction gives uniformly close trial graphs; harmless off-solution inputs to the primary stage after the first can be clipped to $U\le0$ and $A,V,B\ge0$. On true primary outcomes these signs hold, even for negative participating $L$, by the uniform positive odds on the primary proper charts and small $L/N$. The subsequent secondary repair uses its own output estimates below instead of this clipping.

The limiting seam has $F_b\le1,F_v\le2$, so $F_b+F_v/4\le3/2<2$. For small $T$ all selected primary trials are quiet, since $Rxw<1$ on the positive-$y$ arc. The first quiet stage has $w=(A-U/2)/3+O_K(T^2)$, $y=U/2+w$, $B'=y+O_K(T^2)$ and $A'=O_K(T^2)$. The rest of the quiet tail changes this by $O_K(T^2)$, hence $F_b=v+4b/3+O_K(T^2)>T$ uniformly at $T=\rho$ sufficiently small. Always $F_v+F_b>0$. Apply Brouwer with projected updates to $F_b+F_v/4$, $F_v/(4F_b+F_v)$ and $\theta+B-g$ for $T,\tau$ and each control respectively. The strict boundary margins persist, with exact limiting chosen controls used at $T=\rho$. Nonnegative true outputs make the proportion equality exact. At a fixed point each upper control takes its genuine quiet or completed endpoint, and each interior control gives its genuine proper row in the cutoff chart. The first primary control always has positive $x,y,w$: even when $b=0$, the first child has $U>0$, $A\ge U$, $V=0$ and the lower control is positive. This fixed finite stage supplies a recurring rival against every one-owner deviation, uniformly under truncation of the final tail. The exact seam and the preceding contraction argument give the original signed uniform payoff.

**The second repair on finite tables.** Write $a=-U$ for the mate's deficit in this patch. Consider first the limiting terminal branch after the primary trial. Its input satisfies $a+A\le1$, $a\le3B$, $A,B\ge0$, and $V+B$ is uniformly positive on each compact incoming trial graph. This last inequality concerns the states on which a terminal patch is actually evaluated. If the $ua$ stage fails its $b$ guard, the quiet-$v$ candidate has
$$s_0=(a-A-B)/3>0,\qquad x_0=A+2s_0,\qquad w_0=(B+x_0)/2.$$
At the boundary where $s_0=0$ it matches the $ua$ stage. On the subset where the quiet-$v$ guard fails or binds,
$$A_v x_0s_0w_0\ \ge\ V+B-s_0\ \ge\ (V+B)/3,$$
since $s_0\le2B/3$. Thus all three physical odds are bounded away from zero there, uniformly for $A_v$ in a positive compact interval. The repaired root $s$ given by $s+A_v(A+2s)s(B+A+2s)/2=V+B$ is also bounded away from zero, as are its $x,w$. At these first repair outputs the limiting excess $V'-H(a')$, $H(a)=a/3+a^2/9$, has a strictly positive uniform minimum. Indeed the proved inequality $V'\ge4a'/9$ is strict above $H(a')$ when $0<a'<1$, and $a'\le a-B\le2/3$. If $a'=0$ the positive $x,s,w$ and $A_v$ give a strictly positive $V'$. Include the contacting $z=0$ outputs in this compactness argument.

During subsequent all-proper limiting repairs the excess at least propagates as $(V-H(a))/[(1+2s)(1+s)^2]$, using the displayed invariant calculation. The sum of the successive $s$ is bounded by $1/3$ since $a-a'\ge3s$. Hence the excess stays uniformly positive, even if the number of steps is provisionally unbounded. The equation $s+2A_v s^3=V$ then bounds $s$ uniformly away from zero on every proper step or contact. The drop $a-a'\ge3s$ consequently bounds their number by a common finite integer. At every true terminal quiet repair, one may pad with empty dates leaving $(0,V',0,0)$.

For finite tables put $y=z/N$ on this second chart, and solve successively at fixed $s,z$
$$
 x=\frac{A-y+2s}{1+Ky-(L/N)zs},\qquad
 w=\frac{B+x+y}{2+Rxy},\qquad
 z=\frac{2y-s-2w-U}{s[1-(A_u/N)w]}.
$$
These are the exact indifferences of $a,b,u$. At zero $(1/N,L/N,A_u/N)$ the first two give $x=A+2s,w=(B+x)/2$ independently of $z$, and the third has unit derivative in $z$ on moving all terms to the left. The remaining exact residual for $v$ is $x+s-2w+A_v xsw-V$. Its derivative after elimination is strictly positive in $s$ at the limit. Also $z=(a-A-B)/s-3$ strictly decreases in $s$ on these positive-odds charts. The implicit function theorem and compactness supply the same nearby proper solution, with positive $z$ precisely on the side where the quiet-$v$ guard fails near a contact. At $z=0$ the two branches coincide exactly. Away from contact both strict signs persist. This continuation uses $A_v$ itself as a compact parameter, with no upper bound independent of that compact set. The other two error parameters are $L/N,A_u/N$.

One must also handle the possibility that the actual $A'$ is slightly negative for the negative-grand implementation of $L$. On every secondary proper date its exact outputs are
$$
 a'=\frac{zs[1-(A_u/N)w]}{(1+y)(1+s)(1+w)},\quad
 B'=\frac{Rxyw}{(1+x)(1+y)(1+w)},\quad
 A'=\frac{xy(K-\mathbf1_{\rm neg} Ls)}{(1+x)(1+y)(1+s)} .
$$
The other mate's output is $V'=A_v xsw/[(1+x)(1+s)(1+w)]$. On the compact active and contacting charts $s$ has the positive lower bound just proved, and all odds have upper bounds. Consequently $a'\ge0$,
$$ |A'|\le C(1/N+L/N)a',\qquad 0\le B'\le (C/N)a' .$$
At $z=0$ all three vanish exactly. After a secondary proper date apply the quiet-$v$ candidate directly, even if the child $A$ is negative. The relative bounds give $s_0=(a-A-B)/3>0$, $x_0=A+2s_0>0$ and $w_0=(B+x_0)/2>0$ whenever $a>0$ and the errors are small. If $a=0$ all three are exactly zero. As $a\downarrow0$ all these odds are $O(a)$, while $V$ still has its positive margin; the quiet-$v$ guard is then strict and the stage resets $U,A,B$ to zero. This gives a continuous endpoint even at $a=0$. The estimates and compact implicit charts now continue the finite number of secondary choices, uniformly over the compact incoming graph. Equivalently, on every still-proper finite step the decrease of $a$ keeps half the uniform positive limiting drop, and the strongly quiet small-$a$ stages terminate the patch. No clipping of a negative intermediate $A$ is necessary on this patch. At a true quiet-$v$ endpoint any passive output has numerator $V+B-s_0$ and bounds the positive grand quit offer by the guard, so the retained $V'$ is nonnegative.

The same proof works on a singleton neighborhood. At a quiet $uab$ stage write $c=G_{ua}>0$, $g=G_{ub}>0$, $h=G_{bu}>0$, $d_0=-G_{ba}>0$, $\ell=-G_{au}>0$ and $f=G_{ab}>0$. The exact positive-odds equations are
$$
 s_0=\frac{a-(c/d_0)(B+hA/\ell)}{g+c h f/(d_0\ell)},\qquad
 x_0=(A+f s_0)/\ell,\qquad w_0=(B+h x_0)/d_0.
$$
Thus $s_0$ changes sign exactly at the $ua$ guard, the relative estimates ensure positivity after a secondary proper date, and the two patches match when $s_0=0$. The true four-row equations have the same nonsingular derivatives at the certified compact limiting charts, with coefficients depending smoothly on the singleton entries. The ratios in the three exact output formulas are determined by the higher rewards and retain their bounds. Hence all strict comparisons and the continuous return persist.

For the primary interpolation at nearby singleton matrices use the variable-singleton formulas of the preceding return. In particular $w_1=[(n A/\ell)-V]_+/c'$ where $n=-G_{vu},\ c'=G_{va}$. On the pair face extend the control comparison by $-G_{bu}V/n+(d_0-G_{bu}c'/n)w_1$. This agrees with the proper formula at a zero-$y$ boundary and converges uniformly to $-V$. The lower endpoint uses the actual passive values there and the upper endpoint uses the continued exact procedure just given. They agree when the interpolation interval collapses. Initial solo odds still reset $V,B$ exactly and the limiting first $U>0$, first positive $x,y,w$, cutoff and boundary margins persist. All finite maps therefore converge uniformly to the controlled center maps as the singleton and price perturbations vanish.

### An exact four-date equilibrium on an unbounded six-price region

At witness 6 use the negative participating withdrawal $Z_u(uvb)=-N$. Use either implementation of the grand withdrawal of size $L$, and write $K=Z_a(uva)>0$ for the entrant's triple price. The three positive grand prices of $u,v,b$ are $A_u,A_v,R$. There are universal $M<\infty$ and $\delta>0$ such that every $K,L>0$ and positive prices satisfying
$$
 N\ge M,\qquad \frac{R}{(1+K)^2}+\frac{A_v}{N(1+K)}\ge M,\qquad A_v\le\delta N R,\qquad A_u\le\delta\left(\frac{NR}{(1+K)^2}+\frac{A_v}{1+K}\right)
$$
admit an exact terminal equilibrium and its original uniform-equilibrium payoff for any signed own levels. The prices $N,R$ have no required ratio. Either mate may own the withdrawal by symmetry. If $L\ge KN$ the sure pair suffices. We construct an exact period of four dates, with supports $ua,uvba,b,a$ in chronological order, throughout $0<L<KN$.

**The four exact dates.** Introduce an auxiliary coefficient $d\in[0,K]$. The required child value of $a$ on the full date will use $d$, and its forced output will use $r$ with $r=K$ for passive $L$ and $r=d$ for participating $L$. We shall enforce $d=K-Ls$, where $(x,y,s,w)$ are the full-date odds in player order $u,v,b,a$. Set
$$
 t=Rw=\frac{x+y}{xy+1/R},\quad
 z=Ns=\min\!\left(1,\frac{1-2w/y}{1-1/(Ny)-(A_u/(NR))t}\right).
$$
Below these odds are strictly positive and the denominator is positive. The required continuations for all four proper actions to tie are
$$U_c=y+s-2w+(A_u/(NR))zyt-zy,\quad V_c=x+s-2w+(A_v/(NR))zxt,\quad B_c=0,\quad A_c=x+y-2s+dxy.$$
The odds $w$ give $B_c=0$ and the cap on $z$ gives $U_c\ge0$, as the first expression decreases in $z$ and vanishes at the uncapped choice. The full-date outputs are
$$
 U'=\frac{(A_u/(NR))zyt-zy}{(1+y)(1+s)(1+w)},\quad V'=\frac{(A_v/(NR))zxt}{(1+x)(1+s)(1+w)},\quad
 B'=\frac{x+y-w}{(1+x)(1+y)(1+w)},\quad A'=\frac{rxy}{(1+x)(1+y)(1+s)}.
$$
Prepend $ua$ with odds $x_2=A'$, $w_2=-U'/2$. Both movers tie at zero. Its passive outputs are
$$
 v=\frac{V'+2w_2-x_2}{(1+x_2)(1+w_2)},\qquad b=\frac{B'+x_2-w_2}{(1+x_2)(1+w_2)}.
$$
Use $(0,v,b,0)$ as the seed. In reverse order the solo $a$ odds $b$ give $V_b=0$ in row $b$. The solo $b$ odds $q=[2b-(1+b)U_c]/[(1+b)(1+U_c)]$ then give row values $U_c$, $U_c+v(1+U_c)/(1+3b)$, $0$ and $(4b-2(1+b)U_c)/(1+3b)$. Therefore it suffices to solve
$$
 J_1=4b(V_c-U_c)-(A_c+2U_c)v=0,\quad
 J_2=b(4-2U_c-3A_c)-(A_c+2U_c)=0,\quad
 J_3=d-K+(L/N)z=0
$$
with $b,V_c-U_c,A_c,-U',x,y,s,w>0$. At such a zero $J_1=0$ implies $v>0$ and the relations recover the two solo continuation values exactly, and $A_c=2q/(1+q)>0$ gives $q>0$ (the denominator $1+q=(1+3b)/[(1+b)(1+U_c)]$ is positive). All waiting players on $ua$ and the solo dates have zero immediate quit offers and nonnegative waiting values. Every deviator faces geometric rival absorption on this four-date word.

**Uniform angular bounds.** Parameterize $d=\theta r$, $0\le\theta\le1$; use $\theta=1$ also when $r=d=0$. At zero errors $z=1$, $s=w=U_c=0$, $V_c=x$, $A_c=x+y+dxy$. Put $e=(1+r)^{-1}$, $T=y/(1+y)$, $E=1+(1-r)x$. From the displayed offers,
$$
 v=\frac{TE}{(1+x+rxT)(1+T/2)},\qquad \frac bv=\frac{x/y+1/2+(r-1/2)x}{E}.
$$
Thus $J_1=(v/E)Q(x)$ with the positive prefactor defined by the first formula, where
$$ Q(x)=Cx^2+[1-y+(r-d)y]x-y,\qquad C=4/y-3+5r+d(r-1)y .$$
For $0<y\le1$ both $C\ge1$ and the linear coefficient is nonnegative. The unique positive root is $x_*=eX_*$, determined by
$$ (e^2 C)X_*^2+[e(1-y)+(1-\theta)(1-e)y]X_*-y=0.$$
The coefficients are polynomial in $e$ for each $y,\theta$. At $e=0$ the unique positive root is one and its scalar derivative in $X_*$ is $(1+\theta)y>0$, including $\theta=0$. Thus on every fixed compact interval of positive $y\le1$ the root extends smoothly on $0\le e\le1$. If $r>1$, evaluation at $x=1/(r-1)$ gives $Q(x)=4x[x/y+1/2+(r-1/2)x]>0$. Therefore $E>0$ at $x_*$ for all $r$.

Write $x=e(X_*+\xi)$. At $\xi=0$ the derivative of the unscaled $J_1$ in $\xi$ is the positive prefactor $v/E$ times
$$2e^2 C X_*+e(1-y)+(1-\theta)(1-e)y,$$
strictly positive also at $e=0$. The formula defining $v/E$ above extends as a positive function when $E=0$. Thus $J_1$ has uniform opposite signs on $\xi=\pm\eta$ around its zero, once a compact $y$ interval is fixed.

On the middle graph $J_2=b(4-3A_c)-A_c$. At $y=1$, $A_c\ge1$, and $b$ is uniformly below one: $B'\le1$, $w_2=T/2=1/4$, and $b=(B'+A'-T/2)/[(1+A')(1+T/2)]\le4/5$. The sign is negative. For $y\downarrow0$, uniformly in $r,\theta$, $x_*\le y/(1-y)$. Also $dx_*$ is bounded: for $d\ge2$ use $C\ge d^2y/2$, and for $d<2$ use the preceding bound. The linear coefficient gives $(r-d)x_*\le1$. Consequently $A_c=O(y)$ and $A'=O(y)$. Since $r\ge d$,
$$ b=\frac{(x+y+rxy)/[(1+x)(1+y)]-T/2}{(1+A')(1+T/2)}\ge(1/2-o(1))A_c .$$
Thus $J_2>0$ at some fixed $y_*>0$. These two signs have strict uniform margins on the compactified graph; $A_c\ge y$ there. Choose small $\eta$ so they hold also for $|\xi|\le\eta$, and obtain the strict signs for $J_1$ on $\xi=\pm\eta$ from its uniform positive derivative.

**Restoring finite prices.** Put $X=X_*+\xi$ and write
$$
 \nu=1/N,\qquad \beta=A_v/(NR),\qquad \alpha=A_u/(NR e),\qquad
 \rho=1/[R e(e+\beta)] .
$$
Since $e\ge(1+K)^{-1}$ the theorem's bounds give $\nu,\rho\le1/M$, $\beta\le\delta$ and $\alpha\le\delta(e+\beta)$. This remains true when the second term of $R/(1+K)^2+A_v/[N(1+K)]$ furnishes the lower bound. In these variables
$$ \tau=e t=\frac{eX+y}{Xy+\rho(e+\beta)},\qquad w=\rho(e+\beta)\tau,\qquad s=\nu z,\qquad z=\min\!\left(1,\frac{1-2w/y}{1-\nu/y-\alpha\tau}\right). $$
On the strip $y_*\le y\le1$, $|\xi|\le\eta$, both $X,\tau$ stay bounded above and below by positive constants. The cap is well-defined with $z$ close to one. In all expressions $rx=(1-e)X$, $dx=\theta(1-e)X$, $(A_u/(NR))zyt=\alpha z y\tau$ and $(A_v/(NR))zxt=\beta z X\tau$. Hence the two unscaled residuals $J_1,J_2$ are continuous through $e=0$ and converge uniformly to their displayed zero-error values. Their four face signs persist. The quantities $b,A_c,-U',z,\tau$ are uniformly positive upon shrinking $\eta$ and the errors. Indeed at the reference center $A_c\ge y$ and $x_*\le1$ from $Q(x_*)=0$; the formula for $b$ then gives strict positivity including $e=0$ and $r=0$.

For actual $e>0$ one still needs $V_c>U_c$, since both can become small at different rates. When the fraction for $z$ is below one, $U_c=0$ and $V_c=eX+\nu z-2\rho(e+\beta)\tau+\beta z X\tau>0$. The positive terms in $e$ and $\beta$ dominate the $\rho$ term uniformly. When the cap is one, the $s$ and $w$ terms cancel exactly, giving $V_c-U_c=eX+\beta X\tau-\alpha y\tau>0$ by $\alpha\le\delta(e+\beta)$. This proof only uses $V_c>U_c$ at the actual prices.

At $d=0$ the third residual is negative since $L<KN$ and $z\le1$, while at $d=K$ it is positive. On the box with coordinates $(\xi,y,d/K)$ use $r=K$, $\theta=d/K$ for passive $L$ and $r=d$, $\theta=1$ for participating $L$. Poincaré–Miranda gives a common zero. It has $r>0$, so the $ua$ odds are strictly positive even arbitrarily close to $L=KN$. This proves the stated single uniform price bound for both implementations.

For the separated subfamily take all four original own singletons equal to one, $K=A_u=A_v=1$, sufficiently large fixed $R$, $L=2R$ and then sufficiently large $N$. The six-entry exclusion gives a positive stationary regret floor and a single date with uniformly positive first-exit probabilities for every one of the fifteen coalitions in each sufficiently accurate profile. Here an exact four-date profile achieves equilibrium on the same tables. [Sharp six-entry exclusion](SHARP_SPARSITY_FOR_COMPULSORY_GRAND_EXITS.md)

### Four unrestricted prices on the high grand-reward tail

At witness 6 with the participating withdrawal of size $N$, there is a constant $C$ such that
$$R\ge C(1+K)^4$$
gives an exact terminal equilibrium and an original uniform-equilibrium payoff for **every** positive $L,N,A_u,A_v$, either implementation of $L$, either choice of withdrawing mate, and all signed own singleton levels.

If $L\ge KN$ the two sure mates work. For $L<KN$ the sole-$v$ test gives positive odds $X,Y,Z$ for $u,a,b$, respectively, at which all three are indifferent. At witness 6 they satisfy
$$X=1/(RY),\qquad 0<Y<N/A_u,\qquad Z=(K+RY)/L=1/(N-A_uY).$$
The sufficient and necessary inequality for $v$ to quit surely is
$$X-2Y+(1+A_v/R)Z\ge0.$$
Indeed $G_{bv}=1$, $G_{av}=-1$, $G_{va}=2$, $G_{vb}=G_{vu}=-1$. The odds and the test use only the difference of the two payoffs across each withdrawal edge, so apply to both choices of $L$. If $R+A_v\ge2L$ then $(1+A_v/R)Z\ge 2Y$. If $A_u\ge N\sqrt{2R}$ then $X>2Y$. [Sure-opening criterion](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)

It remains to consider $N>R/(2K)$, $A_v<2L<2KN$, $A_u<N\sqrt{2R}$. Choose $C$ large enough that $C/2\ge M$, $2/C\le\delta$, and $\sqrt{2/C}\le\delta$, where $M,\delta$ are the constants of the four-date theorem above. Then $N\ge M$ and $R/(1+K)^2\ge M$. Furthermore $A_v/(NR)<2K/R\le 2/C$ and $A_u/[NR/(1+K)^2]<\sqrt{2}(1+K)^2/\sqrt R\le\delta$. The four-date theorem applies.

### The passive withdrawal with four unrestricted prices

At witness 6, with $a=3,b=2$ and **either** implementation of each withdrawal, there is $C<\infty$ such that every
$$R\ge C(1+K)^6$$
has an original uniform-equilibrium payoff, independently of **all** $L,N,A_u,A_v>0$ and the signed own singleton levels. For the participating withdrawal of size $N$ the preceding result gives the fourth power and an exact equilibrium. Here the withdrawal is $Z_u(vb)=N$. The two mates are symmetric. The sure tests above reduce the problem to
$$L<KN,\qquad N>R/(2K),\qquad A_u/N<\sqrt{2R},\qquad A_v/N<2K.$$
All implicit constants below are absolute. Bounds required to be small can be achieved by increasing $C$.

**A full date and its predecessor.** Use $y\in[1/50,3/2]$ and $x\in[x_-,x_+]$, where
$$x_-=8/\sqrt R,\qquad x_+=\begin{cases}y&K\le1,\\1/[200(1+K)]&K>1.\end{cases}$$
In order $u,v,b,a$ use full-date odds $x,y,s,w$ where
$$ w=\frac{x+y}{1+Rxy},\qquad z=Ns=\frac{1-x/y}{1-(A_u/N)w+(A_v/N)(x/y)w}.$$
Here $w\le2/(Rx)$, $2w<x$ and $(A_u/N)w<1/2$. Thus $0\le z\le2$, $(z-1)_+=O(1/(x\sqrt R))$. Put $d=K-(L/N)z$, and use $r=K$ for passive $L$ or $r=d$ for participating $L$. Both mates on this date require the same continuation $h$, and the two outsiders require $0$ and $A$, respectively:
$$h=x+s-2w+A_vsxw,\qquad A=x+y-2s+dxy.$$
Indeed the other mate requires $y+s-2w+A_usyw-Nsy=h$, and $Rxyw=x+y-w$ ties $b$. The outputs $(U,V,B,D)$ at these indifferences are
$$U=\frac{A_usyw}{(1+y)(1+s)(1+w)},\quad V=\frac{A_vsxw}{(1+x)(1+s)(1+w)},\quad B=\frac{x+y-w}{(1+x)(1+y)(1+w)},\quad D=\frac{rxy}{(1+x)(1+y)(1+s)}.$$
In particular $h>0$, $U=O(1/(x\sqrt R))=O(1)$, $V=O(K/R)$. Uniformly $h=x+O((1+K)/\sqrt R)$ and $A\ge x+y-O((1+K)/\sqrt R)$.

Prepend a $uva$ date with odds $P=V+2t$, $Q=U+2t$, $t$ in that order. The mates then tie at zero. The required tie for $a$ is
$$F=D-P-Q-KPQ=0.$$
When it holds the new $a$ value is $D_1=KPQ/[(1+P)(1+Q)]$. The new $b$ value from waiting is $B_1=(B+P+Q-t)/[(1+P)(1+Q)(1+t)]$; its guard is $B+P+Q-t\ge RPQt$. Link the two intervals $(x,t)=(x_-,t)$, $16(1+K)/\sqrt R\ge t\ge0$, and $(x,t)=(x,0)$, $x_-\le x\le x_+$. Their concatenation is one rectangle coordinate. Along with $y$, all offers are continuous. The formulas for $D_1,B_1$ define trial values everywhere.

At the first endpoint $D\le Kx_-$, so $F<0$. At the last endpoint when $K\le1$ we have $x=y$, $z=0$, $U=V=0$ and $D>0$. When $K>1$, there $1-z\ge c x$ with a universal $c>0$: the numerator of $1-z$ is at least $x/y-O(1/(x\sqrt R))$ and the denominator is bounded above and below. Hence $D\ge c'Kx^2$ for either choice of $L$, while $U+V+KUV=O((1+K)/\sqrt R+K/R+K^2(1+K)/R^{3/2})$. With $R\ge C(1+K)^6$ this is strictly below $D$. Thus $F>0$ along the other face.

**Closing the return.** Before this predecessor insert successive $uva$ dates with odds $(2p,2p,p)$, where $4p+4Kp^2=D_j$. The update is
$$D_{j+1}=4Kp^2/(1+2p)^2,\qquad B_{j+1}=(B_j+3p)/[(1+2p)^2(1+p)].$$
The two mate values stay zero and $a$ ties. Over the entire trial rectangle $P=O((1+K)/\sqrt R)$, $Q=O(1)$, hence $D_1=O(K(1+K)/\sqrt R)$ and $KD_1$ is small. The bound $D_{j+1}\le K D_j^2/4$ implies uniform geometric decrease. The $B_j$ are uniformly bounded (each update is an expected waiting payoff using bounded baseline entries), and $|B_{j+1}-B_j|=O(D_j)$. Thus $B_\infty$ exists continuously and $B_\infty=B_1+O(D_1)$.

Starting with the putative seed $(0,0,B_\infty,0)$, prepend solo $a$ with odds $B_\infty$ and solo $b$ with odds $[2B_\infty-(1+B_\infty)h]/[(1+B_\infty)(1+h)]$. Matching the required continuation $(h,h,0,A)$ is equivalent to
$$J=B_\infty(4-2h-3A)-(A+2h)=0.$$
Use the formula for $J$ as a trial residual on the whole rectangle. Uniformly $B_\infty\ge B-o(1)>0$ and $B_\infty\le1+o(1)$, where $o(1)$ tends uniformly to zero as $C$ increases: $B\le1$, $P,t,D_1=o(1)$ and $(B+Q)/(1+Q)\ge B$. At $y=3/2$ we have $A\ge3/2-o(1)$ and $J<0$. At $y=1/50$ we have $x\le y$, $h=x+o(1)$, $A\le x+y+Kxy\le x+1.02y$, and $B\ge(x+y)/(1+y)^2-o(1)$. Thus $4-2h-3A>3.8$ there for large $C$ and $J>0$, since $3.8(x+y)/(1.02)^2>3x+1.02y$. Poincaré–Miranda gives a common zero of $F,J$. At the zero $A,h,B_\infty>0$, so the solo $b$ odds are positive: $2B_\infty-(1+B_\infty)h=A(1+3B_\infty)/2$. Both solo movers tie at zero, and quiet players there receive nonnegative values against zero immediate offers.

On the first predecessor, if $t=0$ then the quiet $b$ guard holds. If $t>0$ then $x=x_-$ and $F=0$ implies $P,Q,t\le D\le8K/\sqrt R$, so $RPQt=O(K^3/\sqrt R)$ is small compared with $B$. At this zero $D_1=O((1+K)^3/R)$: for $t>0$ use these sharper bounds, and for $t=0$ use $P=V=O(K/R)$, $Q=U=O(1)$. All later quiet-$b$ guards follow since the respective offers in waiting-numerator units are $4Rp^3=O(RD_1^3)=O((1+K)^9/R^2)$ while all $B_j$ are bounded below by a positive constant. All four actions on the full date meet their comparisons even at a zero hazard, by the displayed ties. Truncate the quiet prefix and repeat the resulting finite block. Its prescribed and optimal reply payoffs at the seed agree and approach the seed. Each deviator faces at least one of the two fixed positive solo hazards per block, giving a common contraction below one. Actual terminal regret tends to zero and row translations restore the original signed target. [Truncated-return argument](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)
