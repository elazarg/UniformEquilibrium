# A four-player uniform-equilibrium payoff with five arbitrary signed participant rewards and four unbounded passive adjustments

Four players choose Quit or Continue independently on each live date. The first nonempty quitting coalition pays its reward vector from the next date onward. The live stage and perpetual continuation pay zero. Terminal regret compares with every unilateral behavioral replacement, including Never. A uniform-equilibrium payoff is one target chosen before the accuracy, approached with approximate equilibrium from every sufficiently long finite horizon at that accuracy.

Fix arbitrary original own singleton levels $s_i$. On a nonempty coalition $T$ set the native reward $r_i(T)-s_i$ equal to $\sum_{j\in T}G_{ij}$ for each passive player $i$, and to its negative for each participant $i$, using
\[
G=\begin{pmatrix}0&-8&6&-2\\9&0&2&-10\\-7&15&0&-4\\14&-3&-4&0\end{pmatrix}.
\]
Apply the following increments to the native rewards. Recipient 0 gets $L$ on 013, $S$ on 023 and $D$ on 0123. Recipient 1 gets $K$ on 123 and $E$ on 0123. Strings specify exact coalitions. The two grand increments are totals independent of all triple increments. Increase player 0’s passive rewards on 23 and 123 by $B_0,B_1$, and decrease player 1’s passive rewards on 23 and 023 by $C_0,C_1$, respectively. These four adjustments are independently nonnegative in magnitude.

**Theorem.** Every $(L,S,D,K,E)\in\mathbb R^5$, every $(B_0,B_1,C_0,C_1)\in[0,\infty)^4$, and every $s\in\mathbb R^4$ in this family admit an original uniform-equilibrium payoff. The proof uses a finite one-stage Nash existence theorem to choose a row when a specified three-player continuation is unavailable. Its fully active outputs can have negative native coordinates. Explicit two- and three-player continuations cover all the resulting signs. The choices need not depend continuously on their inputs.

Write a hazard row as $q=(a,p,h,y)$ in player order, $g=Gq$, and $H_i=\prod_{j\ne i}(1-q_j)$. Put $c_0(q)=[(1-p)B_0+pB_1]hy\ge0$, $c_1(q)=-[(1-a)C_0+aC_1]hy\le0$, and $c_2=c_3=0$. Prefixing the row at child annotation $w$ gives native Wait offer $g_i+c_i(q)+H_iw_i$. Native Quit pays $-g_i+b_i$, with
\[
 b_0=[L(1-h)+Dh]py+S(1-p)hy,\qquad
 b_1=[K(1-a)+Ea]hy,\qquad b_2=b_3=0.
\]
All dynamic updates below use Wait, and each prescribed positive hazard on a proper joint row ties the two offers. Original signed levels can be restored because the eventual construction bounds survival after deleting each player's clock.

From a seed $7x e_2$, where $e_2$ is the unit vector, prefix solo 0 with aggregate exit probability $x/(1+x)$ and then solo 2 with aggregate probability $14[x/(1+x)]/(4+14[x/(1+x)])$. The intermediate and final states are $(0,9x/(1+x),0,14x/(1+x))$ and
\[
 (U,V,0,0)=\frac{x}{1+9x/2}(21,16,0,0).
\]
In each solo block the moving player is indifferent at native zero. All other coordinates interpolate monotonically between nonnegative endpoints. Dividing the same aggregate exit probability into individual hazards at most $\eta$ therefore leaves at most $15\eta$ advantage for a quiet player's immediate Quit. None of these reward changes enters such a comparison. Prefixing order is opposite to chronological play.

## The range $L\le39$

For $L\le-20$ take sure quitters 1 and 3 and leave 0 and 2 quiet. In native units the four Wait-minus-Quit differences divided by two are $-10-L/2,-10,11,-3$. Every comparison absorbs on that first date, so this works for every $K$ and every choice of own levels.

Suppose $-20\le L\le39$, with $K$ still arbitrary. Start at the seed $7x e_2$, $1/1000\le x\le16/7$. The two solo blocks in the construction give $(U,V,0,0)$ with $U=21x/(1+9x/2)\le336/79$, $V=cU$, $c=16/21$. Put $k=3/14$, $b=27/8$, $\alpha=9k/10$. Use one 013 row with $q_0=kp,q_1=p,q_3=y$ and $q_2=0$, solving
\[
 U=\frac{16p+4y+Lpy}{(1-p)(1-y)},\qquad 10y-9kp=(1-kp)(1-y)V/2 .
\]
The right side of the first equation increases strictly in $p,y$ on their proper range. The derivatives have signs $16+(L+4)y>0$ and $4+(L+16)p>0$. The second equation gives $y=[18kp+(1-kp)V]/[20+(1-kp)V]$, increasing in $p$ for the stated $V\le256/79$. At $p=0$ the first requirement is $V/5<U$, and it diverges as $p\uparrow1$, giving a unique root. Since the requirement increases in $y$, $p\le U/(16+U)<3/14$. Put $z=y/p$. The tie gives $z\ge\alpha$. If $p\ge1/8$, the second equation yields $z\le\alpha+V/(20p)\le\alpha+(256/79)(2/5)<3/2$. For $p\le1/8$ use both ties to get
\[
 20z-18k=c\frac{1-kp}{1-p}(16+4z+Ly)
 \le c\frac87\big[16+(4+39/8)z\big].
\]
The last bound gives $z<3/2$ again, so $y<bp$. The first 013 outputs are $U'=8p+2y+Lpy>4.5p$, $V'=10y-9kp\le15p$, $D'=4(bp-y)>7.5p$. The silent player 2 can Wait, and the other three tie. Prefix a solo-3 block of aggregate probability $V'/(10+V')$. Its new coordinates are $((10U'-2V')/(10+V'),0,(10D'-4V')/(10+V'),0)$, with both displayed numerators positive. All intermediate annotations are nonnegative. Only the increment on 013 enters the chosen active or quiet comparisons on a 013 date. Every bonus vanishes from all comparisons on each solo date.

For the rest of the return keep $V=0$ and take the same 013 row with $y=\alpha p$. The same monotone equation solves for $p$, the active players tie and silent 2 still prefers Wait. Here $U'=8p+2y+Lpy>0$ while $U-U'\ge8p$ from the Wait formula. This last inequality also holds on the first 013 date, and the solo-3 reset further lowers U. At fixed $L$, $U\le C_Lp$ on the $V=0$ arm because $p<3/14$ and $y=\alpha p$. This gives uniform geometric decay of U and convergence of the bounded coordinate D with a uniform tail error $O(U)$. Thus the final return to the $e_2$ axis is continuous in $x$.

To verify the lower sign directly, $v=(891,-413,587,559)/587$ has $vG=(0,0,2284/587,0)$. The total $\sum p$ on 013 rows is at most $21x/8$ and their aggregate hazard at most $2.75\sum p$. The solo-3 reset adds at most $V'/10\le1.5p$ to the sum of its subdivided hazards. The total is less than $12x$. During these steps $0\le U\le21x$ and $0\le D\le13.5\sum p<36x$ since the reset reduces D. The 3 coordinate vanishes and the coefficient of the nonnegative 1 coordinate in $v$ is negative. Summing the exact Wait updates therefore gives a terminal $D\ge12103x/[587(1+9x/2)]-850x^2$, larger than $7x$ at $x=1/1000$. At the other endpoint $D\le15<16$. A fixed scalar follows. Truncating the final tail, subdividing every solo block and repeating in physical order yields the uniform payoff by the implementation argument below.

## Choosing a row above the three-player boundary

Suppose $L>39$. Put $k=3/14$, $A=15/7$, $b=27/8$, $\alpha=9k/10$. Let $M_0\ge6$ bound player 0’s native passive payoffs above at the fixed table. The positive states have the form $(U,V,0,0)$, $0<U\le M_0$, $0\le V\le\min(11,4U/3)$. On 013 the two ties at $a=kp$, $h=0$ are
\[
 U=(16p+4y+Lpy)/[(1-p)(1-y)],\qquad
 10y-9kp=(1-kp)(1-y)V/2 .
\]
The fourth player in hazard order (player 3) ties since $g_3=0$. Quiet player 2 can Wait at child zero exactly when $y\le bp$. Define $V_*(U)$ by solving the first equation on $y=bp$, $0<p<1/b$, and reading the second. Its unique root varies continuously, and $V_*(U)/U\to891/413$ as $U\downarrow0$. For fixed $U$, solving the first equation makes $p$ decrease continuously in $y$ from $U/(16+U)$ to zero at $y=U/(4+U)$. The endpoints $y=\alpha p$ and $y=bp$ each occur exactly once. The required value
\[
 V(y)=2(10y-9kp)/[(1-kp)(1-y)]
\]
increases throughout the interval up to $y=0.9$: its fixed-$p$ derivative in $y$ is positive, and its fixed-$y$ derivative in $p$ has the sign of $10y-9$. For $y\ge0.9$ it exceeds $2(9-9k)/0.1>11$. Thus for $0\le V\le11$ a proper 013 solution with $\alpha p\le y\le bp$ exists uniquely precisely when $V\le V_*(U)$.

If $V>V_*(U)$, then $U,V>0$. At the stage game with this child, add $\epsilon>0$ to the Quit offers of players 2 and 3 only. Take a Nash equilibrium of this finite game and a convergent subsequence as $\epsilon\downarrow0$. Its limit is Nash at the original child and nonblank. Indeed near the blank row, strict positivity of $U,V$ forces 0 and 1 both to Wait. With $a=p=0$, the Wait-minus-Quit differences of 2 and 3 are then $-8y-\epsilon$ and $-8h-\epsilon$, so both must quit surely.

A limiting row with a sure player gives an original equilibrium. For a sole sure player lower its child continuation from the nonnegative value used here to native zero; this weakly favors its Quit. All other endpoint comparisons are independent of the child, as are all comparisons when two players are sure. To implement native zero after the sole sure player's refusal, arrange one further live date with a sure opponent and one other opponent mixing. Write $(j,l;t)$ for sure $j$ and opponent $l$ using hazard $t$, all remaining opponents quiet. For a refusing player $0,1,2,3$ take respectively
\[
 (2,1;3/4),\quad (0,3;9/10),\quad
 (0,1;7/15),\quad (1,0;3/14).
\]
On each such date the withdrawing player's two native offers are zero, by its displayed $G$ row and the fact that none of its specified bonuses enters. All replacements absorb in at most two dates and the original signed singleton is thus correctly restored.

In the remaining proper nonblank row, $g_2,g_3\ge0$ with equality on their positive hazards. If $h,y>0$ the equalities force
\[
 p=(8y+4h)/27,\qquad a=(4y+20h)/63 ,
\]
so all four mix. If $h>0,y=0$, they require $a=Ap$, $27p\ge4h$, hence $p>0$. But the Quit offer to 1 is $-9a-2h$ and Wait pays $9a+2h+H_1V>0$. If $h=0,y>0$, they require $a=kp$ and $y\le bp$, giving the excluded 013 case. Finally $h=y=0$ precludes $p>0$ by the strict Wait comparison for 1, and then precludes $a>0$ by positivity of $U$. We have obtained a proper full row or a sure disposition.

Write $u=g_0+c_0(q)+H_0 U$, $v=g_1+c_1(q)+H_1V$ for the full output, with its other two coordinates zero. Here
\[
 g_0=(130h-118y)/27,\qquad g_1=(34h-66y)/7.
\]
The passive bounds give $u\le M_0$ and $v\le11$. For $\lambda=4/3$, we have $h/p\le27/4$ and
\[
 (g_1-\lambda g_0)/p=-1021/84+5(h/p)/21<-10.5,\qquad
 H_1-H_0=(p-a)(1-h)(1-y)\le 11p/14 .
\]
Since $V\le\lambda U$, $H_1 V-\lambda H_0 U\le (H_1-H_0)V\le(121/14)p$. The passive adjustments have signs $c_1-\lambda c_0\le0$, giving $v-\lambda u<-1.8p$. Also $g_1-2g_0=-(902h+130y)/189<0$ and $H_1/H_0=(1-a)/(1-p)\le3/2$, since $3p-2a=(48y-12h)/63<1$. Together with $c_1-2c_0\le0$, these imply $v<2u$. In particular if $u\le0$ then $v<0$ and $|u|<-v/2$. Always $u\ge-118/27$ since $U\ge0$. The passive penalties may make $v$ arbitrarily negative as the table varies. Each full selection at this fixed table has $p$ bounded below: $V>V_*(U)$ and $V/U\le4/3$ bound $U$ away from zero by the small-$U$ seam limit. As $p\to0$, the displayed hazard relations force $a,h,y\to0$, and the 0 tie $2g_0+c_0(q)+H_0U=b_0$ would force $U\to0$. Also $a\ge kp$, giving positive hazard from two different players on each such date.

Keep choosing a row while $(u,v)$ is positive and above the boundary. Arbitrarily long chains consisting entirely of full rows already yield a uniform payoff: reverse arbitrarily long finite segments and append AllContinue. The exact row comparisons and the per-date lower bound on two different hazards make the effect of the artificial bounded tail tend to zero geometrically, uniformly under all unilateral deadlines and Never. Subsequence selection and the terminal-to-uniform argument below apply. Otherwise every such chain finishes in a signed correction or the nonnegative 013 region.

## Completing a nonnegative 013 entry

If $0\le V\le V_*(U)$, the exact $013$ map applies at $D=0$ and completes to $(0,0,D_\infty,0)$ with $0<D_\infty\le15$. The following estimates apply up to the finite table-dependent upper bound $M_0$. Put $k=3/14$, $b=27/8$, $\alpha=9k/10$. The $013$ hazards are $(kp,p,0,y)$ with
\[
 U=(16p+4y+Lpy)/[(1-p)(1-y)],\qquad 10y-9kp=(1-kp)(1-y)V/2.
\]
Use the unique solution just established. Player 2 can Wait because $g_2=4(bp-y)\ge0$ and its native child is nonnegative. The new $U'=8p+2y+Lpy$ and $V'=10y-9kp$ have $V'/U'<5$, and $U-U'\ge8p$. For the invariant cone put $u=(y/p-\alpha)/(b-\alpha)$, and let $t$ be the critical next $p$ with $y_{\rm next}=bt$ at $V'$. Then $2t/[(1-kt)(1-bt)]=up$ and its required first coordinate is
\[
 U_{\rm crit}=(8+2b)up\,A_t+ Lbupt A_t/2,\qquad A_t=(1-kt)/(1-t).
\]
Since $up=(y-\alpha p)/(b-\alpha)<1/3$, $t\le up/2<1/6$, $A_t\le6/5$, and $A_t-1\le(3/5)(1-k)up$. Hence
\[
 U'-U_{\rm crit}\ge(8+2\alpha)(1-u)p+
 p^2[(7/10)Lbu-(8+2b)(3/5)(1-k)u^2]>0 .
\]
Here $L>39$, and the first term is positive when $u=0$. The unique next solution has $y_{\rm next}/p_{\rm next}<b$: at fixed $V'\le11$, its tie makes $y$ increase with $p$ and $y/p=\alpha+(1-kp)(1-y)V'/(20p)$ nonincreasing, strictly so for $V'>0$. For $V'=0$ the ratio equals $\alpha$. Equivalently, both seam coordinates are strictly increasing functions of $t$ on $[0,1/b)$, so $U'>U_{\rm crit}(V')$ places the next entry below its seam. The bounds $p\le U/(16+U)$, $y\le U/(4+U)$, $y\le bp$ with $U\le M_0$ give $U\le C p$ at this fixed table. Thus $U$ decreases geometrically, $V$ halves and the bounded $D$ has total remaining variation $O(\sum p)$. For fixed $L$ its limiting $D_\infty(U,V)$ is continuous by uniform convergence on the bounded cone. It is strictly positive when $U>0$ because by the second triple step $g_2>0$, and the remaining $\sum p<\infty$ with proper hazards preserves a positive fraction of that value. All its finite approximations have exact multiactive incentive comparisons.

## Repairing a negative second coordinate

The only remaining type of output has $(u,v,0,0)$ with $v=-W<0$ and finite $W$. The two passive increases may likewise make $u$ large and positive at a fixed full output. If $u\le0$, we have $|u|<W/2$. Each correction below ends on $(0,0,d,e)$, where $d,e\ge0$ and $d+e>0$. In particular the next preparatory blocks need not begin on the $e_2$ axis. Only $L$ can enter a correction, since each other increment or passive penalty vanishes in every relevant payoff or forced comparison: the chosen rows are 01, 012 or 013, with no simultaneous hazard for 2 and 3, and those two players have no modified rewards.

**Pair 01.** For $u>0$ put $\widehat p=u/(16+u)$, $\widehat a=W/(18+W)$. If $k\le\widehat a/\widehat p\le A$, use these as the two 01 hazards. Their tied updates are $u'=8p=H_0u/2$, $W'=9a=H_1W/2$. The quiet increments $g_2=15p-7a$, $g_3=14a-3p$ are nonnegative, and their sum is $12p+7a>0$. Since 2 and 3 have unboosted Quit values $-g_i$ and nonnegative child values, both can Wait. The next hazards for the pair are $p/(2+p)$ and $a/(2+a)$, so the new ratio lies between its old value and one. The pair may be repeated with summable hazards.

**Small negative magnitude, $u>0$.** When $\widehat a<k\widehat p$, use 013 with $a=kp$, $h=0$. Solve its two displayed ties with $V=-W$. The second gives $y$ strictly increasing with $p$ on the admissible range because $W/(18+W)<k$ implies $W<5$. Explicitly,
\[
 y=[18kp-(1-kp)W]/[20-(1-kp)W].
\]
At $y=0$ the needed $p=\widehat a/k<\widehat p$ requires less than $u$ in the first equation. The requirement increases strictly to infinity as $p$ tends to one, yielding a unique root $0\le y\le\alpha p$. Thus $g_2=4(bp-y)>0$ gives the guard for quiet 2, while 3 stays tied at zero. The outputs satisfy $u'=8p+2y+Lpy>0$, $W'=9kp-10y=H_1W/2$. The next pair trial ratio is at most $(9kp/18)(16/u'+1)\le k(1+p/2)<A$, so a change from this branch always enters 01. On this branch $u-u'\ge8p$ and $u\le C_Lp$ since $y\le\alpha p$ and $p\le M_0/(16+M_0)<1$. The remaining $u$ decays geometrically until a switch, and the joint hazards are summable. At the lower pair boundary $y=0$ the formulas agree.

**Large negative magnitude, or $u\le0$.** Use 012 with $a=Ap$, $y=0$; this keeps active 2 tied at zero. The remaining ties require
\[
 W=\frac{18Ap+4h}{(1-Ap)(1-h)},\qquad
 u=\frac{16p-12h}{(1-p)(1-h)} .
\]
At fixed $W>0$ the first gives decreasing $h$ from $W/(4+W)$ to zero as $p$ increases from zero to $p_{\rm end}=W/[A(18+W)]<1/A$. The second displayed quotient strictly increases along that curve: its $p$ partial is positive since $16-12h>0$, and its $h$ partial is negative since $16p-12<0$. The endpoints of its range are $-3W$ and $16p_{\rm end}/(1-p_{\rm end})$. When $u>0$ the upper test is precisely $\widehat a\ge A\widehat p$, and equality gives the 01 row. The lower test for negative $u$ is verified throughout below. One has $u'=8p-6h=H_0u/2$, $W'=9Ap+2h=H_1W/2$.

Quiet 3 can Wait if $h\le27p/4$, since $g_3=27p-4h$ and its child is nonnegative. For $u\ge0$ the 0 tie gives $h\le4p/3$, hence the guard is strict. For $u>0$ the next pair trial ratio is at least $[9Ap/(18+W')][16/(8p)]\ge 18A/(18+11)>k$. Thus any switch enters 01. For negative $u$ write $Z=-u$. The root exists whenever $W>Z/3$. At fixed $Z$ it has $p,h$ strictly increasing with $W$: at fixed $u$ the second tie gives $p=[u+(12-u)h]/[16+u(1-h)]$ with derivative of positive sign $192-4u$, and the first tie then increases with $h$ up to $Ap=1$. At the boundary $h_b=27p_b/4$ one has
\[
 Z=\frac{65p_b}{(1-p_b)(1-27p_b/4)},\qquad
 \frac{W_b}{Z}=\frac{459}{455}\frac{1-p_b}{1-Ap_b}.
\]
The first equation has exactly one solution $0<p_b<4/27$. Since $Z\le118/27$ initially and decreases on every 012 step,
$p_b\le Z/(65+27Z/4)<0.047$ and $W_b/Z<1.09$. The guard holds strictly for $W>W_b$: its sign is negative at the initial endpoint $p=0$, positive as $Ap\uparrow1$ (then $27p>4$), and the equality just displayed is unique.

This threshold persists even when the initial $W$ is arbitrarily large. Put $c=(A-1)/(18A+16/3)$. Since $u<0$ gives $h>4p/3$, the first tie yields
\[
 \log[(1-p)/(1-Ap)]\le (A-1)p/(1-Ap)\le cW.
\]
Here $W'=H_1W/2=9Ap+2h\le11$ and $Z'=H_0Z/2$. Consequently $I=\log(W/Z)-2cW$ never decreases on a 012 update. Initially $W\ge2Z$, so the first guard holds. At a given initial $Z$, increasing $W$ above $2Z$ increases $W'$ and decreases $Z'$. The function $t\exp(-2ct)$ increases on $[0,11]$ since $22c<1$. Thus even for an arbitrarily large initial $W$, the value of $I$ after the first step is at least its value after a step starting at $W=2Z$, hence at least $\log 2-4cZ$. As $2\exp[-4c(118/27)]>1.26$, every subsequent $W/Z$ stays above $1.26$, giving both existence and the strict quiet-3 guard inductively. Both magnitudes halve or faster. The hazards are summable by $18Ap+4h\le W$. They are proper, with the first row finite at every fixed input and all later rows satisfying $W\le11$, which uniformly bounds each of $Ap$ and $h$ away from one.

On the 013 or 012 branch at least one of players 2 and 3 gains a strictly positive passive increment, and that player remains quiet if the branch changes to 01. On 01 both are quiet and at least one gains. The total subsequent hazards are finite and each is proper, hence a positive fraction of the generated coordinate survives in the limit. The other coordinate stays nonnegative. This proves the claimed $d+e>0$. Both active target coordinates tend to zero, and the passive coordinates converge by boundedness of passive rewards and summability of hazards. Each completed correction can therefore be truncated with arbitrarily small endpoint error and exact one-step comparisons.

## Iteration and original uniform payoffs

From $(0,0,d,e)$ with $d,e\ge0$, $d+e>0$, prefix a solo-0 block of aggregate $a_0=d/(d+7)$ and then a solo-2 block of aggregate $a_2=z/(4+z)$, where $z=14a_0+(1-a_0)e>0$. Omit an empty first block. These leave the positive input
\[
 U=6a_2,\qquad V=2a_2+9(1-a_2)a_0,\qquad
 1/3\le V/U=1/3+6a_0/z\le16/21 .
\]
Intermediate annotations are nonnegative; the solo guards again cost at most $15\eta$ for a single deadline at mesh $\eta$.

Iterate as often as desired. If there are infinitely many full dates in this trajectory, each such date contracts every deleted survival by a fixed factor below one. If there are only finitely many, consider the suffix of consecutive no-full returns. Each such return is the positive 013 completion and the two solo preparations, with $e=0$ at its endpoint. On the strip $1/3\le V/U\le16/21$, uniformly as $U\downarrow0$, the final $d$ satisfies
\[
 d=[891U-413V]/587+O(U^2).
\]
Indeed $v_*=(891,-413,587,559)/587$ gives $v_*G=(0,0,2284/587,0)$. On 013 the latter term applied to $q$ vanishes. Since $u-u'\ge8p$, the total hazard is $O(U)$ and every coordinate is $O(U)$ (coordinate 2 starts at zero and gains at most $15p$ per step). Summing Wait recursions therefore gives the displayed bound. The positive preparation sends $d$ to $U_{\rm next}=3d+O(d^2)>2U$ for sufficiently small $U$. For $U$ bounded away from zero on the compact input strip below the seam, continuity and strict positivity of the 013 endpoint give $d$ a positive lower bound. Every no-full return produces such a positive axial seed. It follows that along this suffix the small-$U$ region cannot absorb the trajectory toward zero: after the first return either small sizes double, or a return starting at a larger size has a uniformly positive next size. Thus infinitely many returns have both solo aggregate hazards bounded below by a positive constant, giving contraction under every deletion. This reasoning only asserts infinitely many contractions along a trajectory. It also covers arbitrary choices of finitely many full rows per return; if a single full segment runs forever its per-date contractions already suffice.

For each desired accuracy take a finite initial collection of rows and completed returns in prefixing order containing enough contracting dates or blocks that every deleted survival is tiny. Truncate each of its finitely many infinite correction arms with terminal annotation error as small as needed so that the sum of all these errors is tiny. Truncation retains each full row and each preparatory block; the full-segment case needs no truncation. Split the finitely many preparatory blocks to a sufficiently fine mesh, reverse the list into chronological order and append AllContinue. Each finite-exit reward and annotation is bounded at this fixed table. Following a prescribed or replacement clock, a crossed seam costs at most its annotation error, and replacing the terminal annotation costs at most a fixed bound times the final deleted survival. Each fixed stopping deadline can incur a solo Quit error only at that one deadline; all its preceding Wait comparisons hold exactly up to the seams. Never is controlled by the same endpoint estimate, and private mixtures of deadlines preserve the bounds. For signed original levels, adding $s_i$ at finite exits respects the annotated recursions, and the possible terminal tail discrepancy including Never is covered by the same deleted survival. Thus actual original terminal regrets tend to zero. Compactness provides one convergent payoff subsequence. For completeness, for a finite prefix of $m$ dates followed by AllContinue, with $B$ bounding all absolute original terminal rewards, the terminal-to-$n$-stage discrepancy is at most $Bm/n+2B\max_i D_{-i}(m+1)$, since earlier exits lose at most $m$ paid stages and later exits are charged at most twice their bound. This holds for adherence and every replacement and gives target delivery for every sufficiently long $n$ at the chosen accuracy. In the earlier periodic fixed-point construction, rival survival through each period is below a common factor less than one, so its expected number of live stages is bounded uniformly over replacements and its terminal payoffs have the same finite-horizon approximation. These estimates also give the standard terminal-to-uniform selection implication directly.

## A table at which all fully active choices leave the nonnegative region

Set the original own levels to one. Start with $L=D=2000$, $K=E=10^9$ and every other increment zero. Then subtract $M=10^{13}$ from player 1's reward on **every** exact coalition containing 2 and 3. In the theorem's parameters this changes $K,E$ to $10^9-M$ and $C_0,C_1$ to $M$. At any fixed continuation the subtraction reduces both of player 1's action offers by the same $Mhy$. Hence every comparison at that continuation is unchanged, while its output for player 1 falls by $Mhy$.

There is no sure opening even allowing arbitrary refusal punishments. For players 2 and 3 the constant private hazard $1/2$ guarantees the original own level: averaging their two native absorbing offers cancels $g_i$ and their own clock ensures eventual absorption. In particular, a sure 2 or 3 must weakly prefer Quit at native continuation zero. Every other player facing a sure rival compares the absorbed offers directly. If $y=0$, a sure 0 forces $p=0$ and then $h=1$, when 0 would prefer Wait. A sure 1 forces $a=1$. A sure 2 forces $p=0$, then $a=0$, violating the quiet-3 comparison. If $y>0$, the comparison of 3 gives $a\le(3p+4h)/14\le1/2$. Player 0 can Wait and faces a sure rival, so $6h-8p-2y\ge 1000py$ and $p<3h/4$. Player 1 can also Wait against a sure rival. Its comparison gives $10^9 y\le 4+18a/h<13$. Only 2 can now be sure. With $h=1$ player 3 mixes, hence $a=(3p+4)/14$ also mixes, and the 0 tie gives $p=(6-2y)/(8+1000y)>0.7$. But $g_2=(27p-4)/2-4y>0$, violating the comparison for sure 2.

There is also no stationary terminal equilibrium. A sole active player's negative singleton payment to an outsider is beaten by the outsider quitting immediately. Every singleton column has such an outsider, pair rewards are unchanged, and AllContinue loses to immediate Quit. At a proper stationary row with at least two active players, a mixer's constant payoff equals its Quit offer and its Wait offer with that same continuation. On an unmodified active coordinate this requires $g_i=0$. Each proper pair fails this test. On 012, 023 and 123 take the unmodified active comparisons of 1, 2 and 3 respectively, whose $g_i$ are strictly positive, negative and negative. On 013, player 0 has $g_0<0$ and a positive joining increment, impossible in its stationary tie. At a full stationary row, 2 and 3 give the same linear formulas for $p,a$ as above, while player 1 requires
\[
 (2-H_1)g_1=[(1-H_1)10^9+H_1 M]hy\ge10^9hy .
\]
Thus $y\le34h/66$ from $g_1>0$, and $y\le10/10^9$ from $g_1\le34h/7$. We get $g_0>2h$ and $p<h/3$. The stationary 0 tie would instead require $(2-H_0)g_0=(1-H_0)2000py<h$.

The scalar seed $x=4/3$ produces $(U,V)=(4,64/21)$. At its seam $2000bp^2<4$ gives $p<1/40$ and
$V_*(4)=2(10b-9k)p/[(1-kp)(1-bp)]<2$. Thus the nonblank Nash selections at this input are all full. Before the subtraction, at every such selection the two ties yield
\[
 [10^9 h-(4/3)2000p]y
 =2(g_1-(4/3)g_0)+H_1V-(4/3)H_0U<-12p
\]
by the full-row bounds. Consequently $y>9/2000$. If $h\le10^{-9}$, the 0 tie gives $2000py=2g_0+4H_0\le4+12h$. Since $p\ge8y/27$, this forces $y<0.083$ and $a<0.006$. The 1 tie would then give
\[
 10^9hy=2g_1+(64/21)H_1
 >-132(0.083)/7+(64/21)(0.994)(1-10^{-9})(0.917)>1,
\]
although its left side is at most $0.083$. Thus $Mhy>45$ for every full selection. Its original output at this child, in native units, is below $11-45=-34$ for player 1. The signed correction is needed for every nonblank choice at this prescribed input. Other initial continuations are allowed by the equilibrium question.

## Source correspondence and scope

The fixed-payoff quantifiers are those of `quittingUniformEquilibriumPayoffConjecture` in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The vanishing original terminal regret and the selected target implement `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. This theorem allows arbitrary signed changes on five identified participant rewards, independent unbounded increases on two and decreases on two identified passive rewards, and four arbitrary own-level translations. The remaining native data are specified. Arbitrary Fin4 remains open.
