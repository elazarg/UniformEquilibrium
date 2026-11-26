# Two arbitrary signed triple-quitting rewards and a return with several possible continuations

Let four players choose Continue or Quit independently on each positive date. The first nonempty coalition $T$ to quit pays $r(T)$ at absorption. The live stage and Never pay zero. A player can replace its entire stopping law, including by Never. Give the players any four original own levels $s_i$ and define the matrix of native singleton payoffs by
\[
 G=\begin{pmatrix}0&-8&6&-2\\9&0&2&-10\\-7&15&0&-4\\14&-3&-4&0\end{pmatrix}.
\]
On every nonempty $T$, let $r_i(T)-s_i$ equal $\sum_{j\in T}G_{ij}$ for a passive player and its negative for a participant. Add $L$ to player 0 whenever $T$ contains $013$ and $K$ to player 1 whenever $T$ contains $123$. Strings denote coalitions. Both additions apply on the grand coalition.

**Theorem.** There is an original uniform-equilibrium payoff for every finite pair $(L,K)\in\mathbb R^2$ and every $s\in\mathbb R^4$ in this family. In addition, let $A,B$ be two further awards paid only at the grand coalition, to players 0 and 1 respectively. Every independent choice of four finite nonnegative awards $L,K,A,B$ admits an original uniform-equilibrium payoff. When $L\le39$, all three of $K,A,B$ may be arbitrary finite signed numbers. The proof also supplies the following method of constructing an equilibrium when there may be several compatible next continuations. A compact positive interval of scalar seeds suffices if each seed permits a return to some seed in the same interval, each return can be approximated with arbitrarily small error against every deadline, and the clocks of every player's opponents absorb with uniformly positive probability per return. Arbitrarily long exact blocks that already have uniform rival absorption per date suffice by themselves.

We first prove the signed-plane result at $A=B=0$. The full row equations below can have multiple inverses. On the large-positive-$L$ branch any selected inverse obeys the same invariant inequalities. This permits repeated returns without proving continuity of a selection or equality to the initial seed. The proof covers in particular $K<L$, all negative premiums and mixed signs. It uses only the displayed raw rewards and produces every clock used in the construction.

Write $g=Gq$ for a row of quit probabilities $q$, $H_i=\prod_{j\ne i}(1-q_j)$ and $w$ for the child continuation in native units. Wait pays $g_i+H_iw_i$. Quit pays $-g_i$ plus $Lq_1q_3$ to player 0 or $Kq_2q_3$ to player 1. At every multiactive date in the return, the parent annotation is the Wait offer, the active players tie, and quiet players weakly prefer Wait.

## Starting at a scalar seed

Start at $7x e_2$, with $e_2$ the unit vector at player 2. Prefix a block of solo-0 dates with aggregate exit probability $s'=x/(1+x)$. Its output is $(0,9s',0,14s')$. Then prefix solo-2 with aggregate probability $14s'/(4+14s')$, obtaining $(U,V,0,0)$ with
\[
 U=21x/(1+9x/2),\qquad V=16x/(1+9x/2).
\]
At each solo block the active player is indifferent at native zero, and the other coordinates move monotonically between nonnegative endpoints. Exact aggregate probabilities can be split into arbitrarily fine conditional hazards. At mesh $\eta$ the native immediate-Quit advantage of any quiet player is at most $15\eta$, since the two triple premiums vanish in every unilateral comparison there. The chronological order reverses the prefixing order. Positive aggregate hazards of both solo owners bound the opponents' survival after deleting any single player's clock.

## All second premiums when the first is at most 39

For $L\le-20$ take sure quitters 1 and 3 and leave 0 and 2 quiet. In native units the four Wait-minus-Quit differences divided by two are $-10-L/2,-10,11,-3$. Every comparison absorbs on that first date, so this works for every $K$ and every choice of own levels.

Suppose $-20\le L\le39$, with $K$ still arbitrary. Start at the seed $7x e_2$, $1/1000\le x\le16/7$. The two solo blocks in the construction give $(U,V,0,0)$ with $U=21x/(1+9x/2)\le336/79$, $V=cU$, $c=16/21$. Put $k=3/14$, $b=27/8$, $\alpha=9k/10$. Use one 013 row with $q_0=kp,q_1=p,q_3=y$ and $q_2=0$, solving
\[
 U=\frac{16p+4y+Lpy}{(1-p)(1-y)},\qquad 10y-9kp=(1-kp)(1-y)V/2 .
\]
The right side of the first equation increases strictly in $p,y$ on their proper range. The derivatives have signs $16+(L+4)y>0$ and $4+(L+16)p>0$. The second equation gives the same increasing function $y(p,V)$ as in the triple chart. At $p=0$ the first requirement is $V/5<U$, and it diverges as $p\uparrow1$, giving a unique root. Since the requirement increases in $y$, $p\le U/(16+U)<3/14$. Put $z=y/p$. The tie gives $z\ge\alpha$. If $p\ge1/8$, the second equation yields $z\le\alpha+V/(20p)\le\alpha+(256/79)(2/5)<3/2$. For $p\le1/8$ use both ties to get
\[
 20z-18k=c\frac{1-kp}{1-p}(16+4z+Ly)
 \le c\frac87\big[16+(4+39/8)z\big].
\]
The last bound gives $z<3/2$ again, so $y<bp$. The first 013 outputs are $U'=8p+2y+Lpy>4.5p$, $V'=10y-9kp\le15p$, $D'=4(bp-y)>7.5p$. The silent player 2 can Wait, and the other three tie. Prefix a solo-3 block of aggregate probability $V'/(10+V')$. Its new coordinates are $((10U'-2V')/(10+V'),0,(10D'-4V')/(10+V'),0)$, with both displayed numerators positive. All intermediate annotations are nonnegative. The second premium vanishes on the initial block, on this reset and on all other solo or 013 dates, even in each player's unilateral Quit comparison.

For the rest of the return keep $V=0$ and take the same 013 row with $y=\alpha p$. The same monotone equation solves for $p$, the active players tie and silent 2 still prefers Wait. Here $U'=8p+2y+Lpy>0$ while $U-U'\ge8p$ from the Wait formula. This last inequality also holds on the first 013 date, and the solo-3 reset further lowers U. At fixed $L$, $U\le C_Lp$ on the $V=0$ arm because $p<3/14$ and $y=\alpha p$. This gives uniform geometric decay of U and convergence of the bounded coordinate D with a uniform tail error $O(U)$. Thus the final return to the $e_2$ axis is continuous in $x$.

To verify the lower sign directly, $v=(891,-413,587,559)/587$ has $vG=(0,0,2284/587,0)$. The total $\sum p$ on 013 rows is at most $21x/8$ and their aggregate hazard at most $2.75\sum p$. The solo-3 reset adds at most $V'/10\le1.5p$ to the sum of its subdivided hazards. The total is less than $12x$. During these steps $0\le U\le21x$ and $0\le D\le13.5\sum p<36x$ since the reset reduces D. The 3 coordinate vanishes and the coefficient of the nonnegative 1 coordinate in $v$ is negative. Summing the exact Wait updates therefore gives a terminal $D\ge12103x/[587(1+9x/2)]-850x^2$, larger than $7x$ at $x=1/1000$. At the other endpoint $D\le15<16$. A fixed scalar follows. Truncating the final tail, subdividing every solo block and repeating in physical order yields the uniform payoff by the implementation argument below.

## All second premiums when the first exceeds 39

**A full row or a sure opening.** On the face $D=0$ write $h=q_2$, $y=q_3$ and impose $g_2=g_3=0$. Then
\[
 p=q_1=(8y+4h)/27,\qquad q_0=(4y+20h)/63,\qquad
g_0=(130h-118y)/27,\quad g_1=(34h-66y)/7.
\]
For fixed $0<U\le6$ and $h\in[0,1]$, player 0's tie is equivalent to
\[
 \Phi(y)=(8Ly^2+4Lhy+236y-260h)/27-U(1-p)(1-h)(1-y)=0.
\]
For $L\ge39$, this has a unique continuous solution $y=y(U,h)\in(0,1)$ because the values at zero and one have opposite strict signs and the first summand strictly increases while $H_0$ decreases. The resulting $p,q_0$ are less than one even at $h=1$. At $h=1$ the solution $d$ is independent of $U$, and is the unique positive root of $8Ld^2+(4L+236)d-260=0$. It satisfies $d<17/33$ by substitution at $L=39$ and monotonicity with $L$. Define $K_b=2(34-66d)/(7d)>0$.

For $K>K_b$ define $F(h)=(Khy-2g_1)/H_1$ for $0\le h<1$. It is continuous, $F(0)=V_*(U)$ is the triple-row boundary with $y=(27/8)p$, and $F(h)\to+\infty$ at one, since the limiting numerator is $Kd-2(34-66d)/7>0$. Therefore whenever $V>V_*(U)$ some $0<h<1$ gives $F(h)=V$. Choose any such root. It is an exact full row with next native state $(U',V',0,0)=(g_0+H_0U,g_1+H_1V,0,0)$. The equal Quit and Wait offers give $2U'=H_0U+Lpy>0$ and $2V'=H_1V+Khy>0$. Since $0$'s maximal passive reward is 6 and $1$'s is 11, $U\le6,V\le11$ persist inductively.

For $K\le K_b$ there is a sure equilibrium. If $K\le-16$, take $q_2=q_3=1$, $q_0=q_1=0$. The native Wait-minus-Quit differences divided by two are $4,-8-K/2,-4,-4$, as required. For the remaining cases write $u=4/(8+L/2)<4/15$ and $K_1=2[9(3u+4)/14-8]$. For $-16\le K\le K_1$ take $q_2=q_3=1$, $q_1=u$ and $q_0=(8+K/2)/9\in[0,(3u+4)/14]$. Players 0 and 1 tie. The other two Wait-minus-Quit signs hold because $-7q_0+15u-4<0$ and $14q_0-3u-4\le0$. For $K_1\le K\le K_b$ fix $q_2=1$ and vary
\[
 q_3=y\in[d,1],\quad q_1=(6-2y)/(8+Ly/2),\quad q_0=(3q_1+4)/14 .
\]
Rows 0 and 3 tie. At $d$ these hazards agree with the preceding full formulas at $h=1$, so $g_2=0$ there. Throughout this interval $g_2=(27q_1-4)/2-4y$ decreases, and player 2, who gets no bonus, prefers Quit over Wait evaluated at its own level. The difference $g_1-Ky/2$ is nonnegative at $d$ and nonpositive at 1, so it vanishes at some admissible $y$. If 2 is the sole sure quitter, refusal followed by survival is punished with a single date where $q_0=1$, $q_1=7/15$ and $q_3=0$. Its native payoff from either action there is zero. This proves equilibrium outright at arbitrary signed own levels, with a two-date uniform bound after any deviation.

**Positive progress of every selected full row.** Start at scalar seed $7x e_2$, where $0<x\le15/7$. The two solo blocks give $(U,V,0,0)=x(21,16,0,0)/(1+9x/2)$. Assume $K>K_b$, and put $\lambda=4/3$. The inequalities $0<U\le6$, $0\le V\le\lambda U$ persist for **every choice** of a full root. Indeed write $t=h/p\in[0,27/4]$. Then
\[
 (g_1-\lambda g_0)/p=-1021/84+5t/21<-10.5,
 \qquad H_1-H_0=(p-q_0)(1-h)(1-y)\le(11/14)p .
\]
Thus $V'-\lambda U'\le(-10.5+\lambda 6(11/14))p<0$. Subtracting the two full ties gives
\[
 (Kh-\lambda Lp)y=2(g_1-\lambda g_0)+H_1V-\lambda H_0U<-14p.
\]
Since $K>0$, $y>10/L$ and $p>10/[(27/8)L]$. In particular every full row gives $U'\ge Lpy/2>50/[(27/8)L]$. Any infinite chain of such rows already produces UE. For each player at least one other has hazard at least $(3/14)p$ in every row. Reverse arbitrarily long finite segments, then append AllContinue. All row comparisons and prescribed recursions hold at their annotations, and replacing the bounded terminal annotation by an actual tail costs at most a fixed constant times the geometric deleted survival, uniformly against all deadlines and Never. The tail under a unilateral replacement can also be bounded by the original finite reward bound, so this estimate includes signed own levels and Never. The same works for arbitrarily long finite full segments. Compactness and the terminal-to-uniform theorem give existence. Consequently if this alternative does not occur every choice can be continued until the seam is met after finitely many full rows. Boundaries from $V=V_*(U)$ can always be passed to the $013$ arm.

**Completing and iterating scalar returns.** If $0\le V\le V_*(U)$, the exact $013$ map applies at $D=0$ and completes to $(0,0,D_\infty,0)$ with $0<D_\infty\le15$. Here are details for the enlarged range $U\le6$. Put $k=3/14$, $b=27/8$, $\alpha=9k/10$. The $013$ hazards are $(kp,p,0,y)$ with
\[
 U=(16p+4y+Lpy)/[(1-p)(1-y)],\qquad 10y-9kp=(1-kp)(1-y)V/2.
\]
For $V\le11$ the second equation gives $y$ increasing in $p,V$, and the first equation increases in $p$, starting at $V/5$ and tending to infinity. One has $V_*/U\le(891/14)/(59/2)=891/413<5$, so the unique positive proper choice exists. It stays in $\alpha p\le y\le bp$ by comparing with the seam at $V_*(U)$, where $y=bp$. The seam has $V_*<13<180$, within the monotonicity range. Player 2 can Wait because $g_2=4(bp-y)\ge0$ and its native child is nonnegative. The new $U'=8p+2y+Lpy$ and $V'=10y-9kp$ have $V'/U'<5$, and $U-U'\ge8p$. For the invariant cone put $u=(y/p-\alpha)/(b-\alpha)$, and let $t$ be the critical next $p$ with $y_{\rm next}=bt$ at $V'$. Then $2t/[(1-kt)(1-bt)]=up$ and its required first coordinate is
\[
 U_{\rm crit}=(8+2b)up\,A+ Lbupt A/2,\qquad A=(1-kt)/(1-t).
\]
Since $p\le U/(16+U)\le3/11$, $t\le up/2<1/7$, $A\le7/6$ and $A-1\le(7/12)(1-k)up$. Hence
\[
 U'-U_{\rm crit}\ge(8+2\alpha)(1-u)p+
 p^2[(17/24)Lbu-(8+2b)(7/12)(1-k)u^2]>0
\]
for every $p>0$ here. Already $L\ge3$ suffices for the bracket at $u>0$. The unique next root thus has $y_{\rm next}/p_{\rm next}<b$. The bounds $p\le3/11$, $y\le U/(4+U)\le3/5$ and $y\le bp$ give $U\le C_L p$. Thus $U$ decreases geometrically, $V$ halves and the bounded $D$ has total remaining variation $O(\sum p)$. For fixed $L$ its limiting $D_\infty(U,V)$ is continuous by uniform convergence on the bounded cone. It is strictly positive when $U>0$ because by the second triple step $g_2>0$, and the remaining $\sum p<\infty$ with proper hazards preserves a positive fraction of that value. All its finite approximations have exact multiactive incentive comparisons.

As $x\downarrow0$ at fixed $L$, the initial ratio $V/U=16/21$ lies below $V_*(U)/U\to891/413$. Thus sufficiently small inputs use the $013$ arm alone. Their returned seed $f(x)=D_\infty/7$ exceeds $2x$. Indeed $v=(891,-413,587,559)/587$ satisfies $vG=(0,0,2284/587,0)$. On $013$ the total hazard is $O(U)=O(x)$ by $U-U'\ge8p$. All inputs and outputs are $O(x)$ since player 2 starts at zero and each increment is $O(p)$. The Wait recursions therefore give $D_\infty=v(U,V,0,0)+O(x^2)=12103x/[587(1+9x/2)]+O(x^2)>14x$.

Fix $\delta>0$ small enough that this last fact holds up to $\delta$. For initial $x\in[\delta,15/7]$ every completed full path enters $013$ with $U\ge\min\{U(\delta),50/(bL)\}>0$ and $0\le V\le V_*(U)$. On that compact set $D_\infty$ has a strictly positive minimum. Choose $0<\xi\le\delta$ at most one seventh of this minimum. For every $x\in[\xi,15/7]$ either the unbounded-full-path alternative has decided the game, or there is a selectable return from $7xe_2$ to $7x'e_2$ with $x'\in[\xi,15/7]$. Iterate these returns in the prefixing direction. Each contains a solo-0 and a solo-2 block with aggregate hazards uniformly bounded below by strict positivity of $\xi$. Consequently opponents of each player contract by a common factor $\beta<1$ per return. To realize arbitrarily many returns, truncate each geometric $013$ tail with head error at most $\varepsilon$, subdivide the solo blocks to arbitrarily small mesh, and reverse the concatenation into physical order. Each artificial seam costs at most $\varepsilon$, summing to at most $\varepsilon/(1-\beta)$ for every deviation. The solo immediate-Quit error is incurred at most once by a deadline. Replacing the final child annotation by AllContinue after $n$ returns costs $O(\beta^n)$, including at signed original own levels. Compactness gives a convergent subsequence of the prescribed targets, and terminal-to-uniform payoff selection gives an original UE. At no step of this argument is a continuous choice of full roots, or an exact scalar fixed point of that choice, required.

## Independent awards on the grand coalition

At $L\le39$ the construction uses only the opening with two sure players or a sequence of solo and 013 dates. No unilateral replacement by either grand-award recipient can create the grand coalition on any of these dates. Indeed, on a 013 date player 2 is absent, including when 0 or 1 changes its own decision. Thus the entire proof on that region allows arbitrary signed $A,B$ as claimed.

For $L>39$, take the four awards nonnegative. On a full row the two immediate bonuses are now $(L+Ah)py$ and $(K+Bq_0)hy$. For each fixed $h$, the strictly increasing equation $\Phi(y)=0$ and its endpoint signs remain valid with $L+Ah$ in place of $L$. Its $h=1$ root $d$ is computed with $L+A$. If $(K+Bq_0(d,1))d-2(34-66d)/7>0$, the same function $F(h)$ with $K+Bq_0$ in its numerator tends to infinity as $h\uparrow1$. This gives every required full step. In the opposite case set $q_2=1$ and follow the previous curve $d\le y\le1$ with $L+A$ in the formula for $q_1$. The player-1 comparison $g_1-(K+Bq_0)y/2$ is nonnegative at $d$ and strictly negative at 1, since there $g_1=9q_0-8<0$. The player-2 sign still holds throughout and the same refusal punishment works. Thus this case gives a sure equilibrium.

In the full-row case the two outputs remain positive and the $4/3$ bound still follows from the two passive update equations. Subtraction of the two tie equations now gives
\[
 [(K+Bq_0)h-(4/3)(L+Ah)p]y<-14p.
\]
Nonnegativity yields $y>10/(L+A)$, $p>10/[b(L+A)]$ and $U'\ge(L+Ah)py/2> 21p/4$, where $b=27/8$. This gives the same strictly positive lower bounds needed for the interval of scalar seeds and for absorption on long full segments. Both extra awards disappear throughout the 013 arm and the solo blocks, including all comparison offers there. The scalar return and original-equilibrium implementation therefore apply on the whole four-dimensional nonnegative orthant.

## Implementing the comparisons and formalization

In the scalar fixed-point case, choose the one seed furnished by the sign change. Repeat the truncated word with its solo hazards subdivided to mesh $\eta$. Let $d$ be its endpoint error and $\beta<1$ a bound for each deleted clock's rivals surviving a period. Every crossing of a period boundary costs at most $d$, weighted by successive survival probabilities, and the total is at most $d/(1-\beta)$. A single deadline can incur at most one $15\eta$ immediate-Quit error. Never obeys the same bound by geometric absorption, and privately randomized deadlines average the bounds. In the interval case the same calculation gives the preceding finite-concatenation estimate, with a single end error bounded by the reward range times $\beta^n$. Since all relevant finite-exit rewards are bounded at the fixed table, this handles arbitrary signed own levels even when the very last prescribed tail is AllContinue. Compactness gives one limiting payoff as accuracy tends to zero. The terminal-to-uniform theorem supplies the required uniform large-horizon comparison at that fixed target.

The raw-table adapter checks the additive rules on the fifteen nonempty coalitions and reads $L,K$ from 013 and 123 and any further awards $A,B$ from the grand coalition. The fixed-target quantifiers are those of `quittingUniformEquilibriumPayoffConjecture` in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The finite approximations give the hypotheses of `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. In formalization, the full-row intermediate value argument and its uniform rate bound can be separated from the interval-return construction. The latter uses arbitrary choices of roots and the uniform bound on each rival survival. All other raw payoff entries are specified by the theorem. General Fin4 existence is open.
