# A uniform-equilibrium payoff requiring at least three simultaneous quitters

Four players numbered 0 through 3 choose whether to quit independently at every live date. The first nonempty coalition $T$ to quit absorbs at its reward vector $r(T)$. The live state, including the date the quit decisions are taken, pays zero and perpetual continuation pays zero. A player may replace its complete behavioral stopping law, including by Never. Let $e$ be the largest increase in original expected terminal payoff from such a replacement.

Use the hollow matrix
\[
 G=\begin{pmatrix}0&-8&6&-2\\9&0&2&-10\\-7&15&0&-4\\14&-3&-4&0\end{pmatrix}.
\]
Fix any four own singleton levels $s_i$. On each nonempty $T$ the native reward $r_i(T)-s_i$ is $\sum_{j\in T}G_{ij}$ when $i\notin T$, and its negative when $i\in T$, with the following additions. Recipient 0 receives an additional $L$ when $T$ contains $\{0,1,3\}$, and recipient 1 an additional $K$ when $T$ contains $\{1,2,3\}$. Both additions apply to the grand coalition.

**Theorem.** A uniform-equilibrium payoff exists for every fixed finite pair of premiums $0\le L\le K$ and every vector of original own levels $s\in\mathbb R^4$. When $0\le L\le39$, the second addition $K$ may be any real number. In each case the proof constructs one fixed target $s+7x e_2$ with $1/1000\le x\le16/7$, where $e_2$ denotes the unit vector at player 2.

For the following necessity statements take $s_i=1$ for every player. There is a finite $L_0>0$ such that for all $K\ge L\ge L_0$ there is neither a stationary terminal equilibrium nor a Nash opening with a sure quitter at the punishment continuation. For every such fixed table there exist $c,\varepsilon_0>0$ such that every behavioral profile with $e\le\varepsilon_0$ assigns probability at least $c$ to a first exit at one of $013,123,0123$, where strings denote coalitions. Furthermore there are finite constants $L_1,M_1$ such that for $L\ge L_1$ and $K/L\ge M_1$ there is no exact terminal equilibrium, even with arbitrary time dependence. At every fixed finite period bound there is then a strictly positive regret floor.

The raw table determines all rates and continuations below. The construction prefixes two solo blocks to a scalar seed and then solves its return using four active players followed by three, or just the last phase when it suffices. A fixed point supplies the target before the approximation accuracy is specified. The necessity result excludes arbitrarily long calendars with at most two active players at each date even though these tables have uniform-equilibrium payoffs. Stationary profiles, sure openings and exact calendars also fail on the indicated subfamilies. The two premiums change the rewards for joining a coalition while leaving all singleton data fixed. This settles a class requiring higher simultaneous exits on the remaining behavioral construction problem. Arbitrary Fin4 existence is open.

## From a scalar seed to a closed return

Prefixing a hazard row \(q\) to a future native value \(w\) gives Wait value \(g_i+H_iw_i\), with \(g=Gq,\ H_i=\prod_{j\ne i}(1-q_j)\). Quit pays \(-g_i+B_i\), with \(B=(Lq_1q_3,Kq_2q_3,0,0)\). We use Wait for every output and tie the offers for active players.

**Seed.** Starting at \((0,0,7x,0)\), \(10^{-3}\le x\le16/7\), prefix a solo-0 block of cumulative exit probability \(s=x/(1+x)\), then a solo-2 block of cumulative exit probability \(14s/(4+14s)\). With solo-j, each other coordinate mixes its child with \(G_{ij}\), at the cumulative exit probability, and j stays at zero. The block endpoints are \((0,9s,0,14s)\) and \((U,V,0,0)=x(21,16,0,0)/(1+9x/2)\). The solo blocks admit splits of arbitrarily small mesh with nonnegative outputs throughout. Write \(c=16/21,\ U_m=336/79\), so \(V=cU,\ U\le U_m\).

**Four active players.** Put \(k=3/14,\ b=27/8,\ \alpha=9k/10\). For \(0\le r\le1\) use \(q_1=p,\ q_2=rp,\ q_0=(k+2r/7)p,\ q_3=zp,\ z=b-r/2\). This gives \(g_2=g_3=0\). With \(a_0=59/4-7r,\ a_1=(891-268r)/28\), all offers tie at input \((U,V,0,0)\) exactly when
\[
 U=F_0(p,r)=\frac{2p a_0+Lzp^2}{H_0},\qquad
 V=F_1(p,r)=\frac{2p a_1+Krzp^2}{H_1}.
\]
For \(0<U\le U_m\), \(F_0\) increases from zero to infinity in p before a hazard reaches one. Its unique root \(p=p(r)>0\) has \(p<1/6,\ zp<1/2\) because \(U\ge 2a_0p/(1-zp)\), \(2a_0\ge31/2,\ z\ge23/8,\ 2a_0/z\ge(31/2)/b>U_m\). The root increases in r. At fixed p the numerator has negative logarithmic derivative of magnitude at least \(\min\{7/a_0,1/(2z)\}\ge4/27\), while \(-\partial_r\log H_0=p/(1-rp)-p/[2(1-zp)]<7/60\).

Set \(V_*(U)=F_1(p(0),0)\). Use this branch only for \(V>V_*(U)\), assuming \(0<V\le cU\). Here \(Lp(0)>10\), since
\[
 F_1(p(0),0)/U\ge (5/6)(891/14)/(59/2+bLp(0))
\]
exceeds c for \(Lp(0)\le10\). Thus \(L>0,\ Kp(r)>10\) throughout. At fixed p along the curve the numerator of \(F_1\) has r-derivative \(p[-134/7+Kp(b-r)]>0\), and \(\partial_r\log H_1\le-2p/7-p+p/[2(1-zp)]<0\). Moreover \(F_1\) increases in p. At \(r=1\) its ratio to the first field is at least \((5/6)\min\{a_1(1)/a_0(1),K/L\}>c\). There is a unique continuous solution \(0<r<1\), converging to zero at the seam.

The outputs \(U'=H_0U-pa_0,\ V'=H_1V-pa_1\) are positive by their Quit offers. Both decrease, \(V-V'\ge22p\), and \(V'\le cU'\), since \(U-U'\le p[a_0+U(35/8+r/2)]\) and \(a_1\ge c[a_0+U_m(35/8+r/2)]\) at both endpoints of this affine inequality. Since \(p>10/L\), the number of four-active rows is uniformly bounded at each fixed L. They terminate with \(0\le V\le V_*(U),\ U>0\), and this phase may be empty.

**Three active players.** At future \((U,V,D,0)\) take \(q=(kp,p,0,y)\), where the 0,1 ties are
\[
 U=\frac{16p+4y+Lpy}{(1-p)(1-y)},\qquad
 y=\frac{18kp+(1-kp)V}{20+(1-kp)V}.
\]
In the bounded range in use (\(0\le V\le cU_m<4\), as V decreases on either branch), the second expression increases in both p and V. The first along that curve increases from \(V/5\) to infinity, giving a unique continuous root if \(U>V/5\). At \(V=V_*(U)\) this is \(y=bp\) and agrees with the four-player row at \(r=0\). At smaller V, solving at the same U increases p and decreases y by strict monotonicity of the first expression in both. The boundary comparison remains valid if \(V_*(U)>4\), since \(p(0)<1/6\) and \(V_*(U)=2p(0)a_1(0)/[(1-kp(0))(1-bp(0))]<26<180\), throughout which the second expression still increases in p. Thus initially \(\alpha p\le y\le bp\), where the lower bound comes from \(10y-9kp=H_1V/2\). On this cone player 3 ties and player 2 can Wait because \(g_2=4(bp-y)\ge0,\ D\ge0\). The outputs are
\[
 U'=8p+2y+Lpy,\qquad V'=10y-9kp=H_1V/2,\qquad D'=g_2+H_2D.
\]
They are nonnegative, \(U-U'\ge8p\), and \(V'/U'\le10b/(8+2b)<5\), giving a next root. Also \(p\le U/(16+U)<3/14\).

If \(0\le L\le39\) there is no four-player initial step. The argument below uses only the triple chart and applies for every real \(K\), since \(q_2q_3=0\) at every date of that chart and of the two solo blocks. At the seam \(p_*=p(0)<1/10\) by \(U\ge(59/2)p_* /(1-bp_*),\ U\le U_m\). Thus
\[
 V_*(U)/U\ge(9/10)(891/14)/(59/2+39\cdot27/80)>4/3 .
\]
On the three-player cone \(V'/U'\le(V/U)(1-kp)/(1-p)\). Since \(\sum p\le U_m/8=42/79\) and \(p<3/14\), the accumulated factor is at most \(\exp(42/79)<7/4\), by \(\log(7/4)\ge6/11\). Starting with \(V/U=c\), every subsequent ratio stays below \(4/3\). Hence every next root stays on the cone.

For \(L\ge39\) the cone is invariant from any entry. Set \(u=(y/p-\alpha)/(b-\alpha)\in[0,1]\). Let t be the critical p on \(y=bt\) at the next input's value \(V'\). Then \(2t/[(1-kt)(1-bt)]=up\), so \(t\le up/2<1/8\), and its required first coordinate is
\[
 U_{\rm crit}=(8+2b)up\frac{1-kt}{1-t}+Lbupt\frac{1-kt}{2(1-t)} .
\]
Using \((1-kt)/(1-t)\le1+(4/7)(1-k)up\le8/7,\ y/p\ge bu\), gives
\[
 U'-U_{\rm crit}\ge(8+2\alpha)(1-u)p+
 p^2[(5/7)Lbu-(8+2b)(1-k)(4/7)u^2]\ge0.
\]
The last inequality holds already for \(L\ge3\). At fixed \(V'\), increasing U increases p, and \(y(p,V')/p=\alpha+H_1V'/(20p)\) decreases. The next root stays on the cone.

At fixed \(L,K\) we have \(U\le C_Lp\) on this cone by \(y\le bp,\ p<3/14,\ y\le U_m/(4+U_m)<0.52\). Thus U contracts by a factor uniformly smaller than one, V halves, and \(\sum_{j\ge n}p_j\le U_n/8\). The silent player has \(0\le D\le15\) since its Wait output averages its child and passive rewards at most 15. Its increment in magnitude is at most \(Cp\), giving uniform convergence to \((0,0,D(x),0)\). Continuity follows because the two row maps agree at \(V=V_*(U)\), the three-active cone is invariant, and the four-active phase has uniformly bounded length. Each finite composition is continuous by pasting and the tails converge uniformly.

**The sign change.** Denote the completed output by $D(x)e_2$. At every full or triple step in these two phases the prescribed annotation is the Wait offer $w_i'=g_i+H_i w_i$. The test vector
\[
 v=(891,-413,587,559)/587,\qquad vG=(0,0,2284/587,0)
\]
gives a positive lower bound on $D(x)$ near the small endpoint. Indeed, both phases lower $U$ by at least $31p/4$, and $a=\sum_iq_i<6p$. Thus $\sum p\le84x/31$ and $\sum a<17x$ through the complete return after the two solo blocks. Write $U_{\rm in},V_{\rm in}$ for the outputs of the two solo blocks. The coordinates $U,V$ are at most $21x$, player 3's value is zero, and $0\le w_2\le15\sum p<41x$ because it begins at zero and on the triple phase $g_2\le15p$. Since $\|v\|_1<5$ and $1-H_i\le a$, summing the identity for $v(w'-w)$ gives
\[
 D(x)\ \ge\ v(U_{\rm in},V_{\rm in},0,0)^\top-3500x^2
 =\frac{12103x}{587(1+9x/2)}-3500x^2.
\]
The nonnegative summand $(2284/587)q_2$ was discarded. At $x=1/1000$ this bound exceeds $7x$. For every $x$, player 2 starts these phases at zero and its Wait recursion is a mixture of its child value and its native passive rewards, all at most 15. Thus $D(16/7)\le15<16$. Continuity gives $D(x)=7x$ for some $x$ at the fixed $L,K$.

**Implementing the return at fixed rewards.** Choose this seed once. Split the solo blocks into hazards at most $\eta$ while preserving their exact aggregate probabilities. Every quiet player on a solo date has a nonnegative assigned native value and an immediate native Quit offer of magnitude at most $15\eta$ since both bonuses vanish for that comparison. Truncate the triple sequence after $n$ steps. Its head tends to $7x e_2$, with maximum coordinate error $d_n\to0$. Use the finite solo subdivisions above and repeat the whole finite word, playing dates in reverse construction order. Every player faces an opposing solo block of fixed positive total exit probability. Thus after deleting any one player's clock, rival survival through each full period is at most a common $\lambda<1$ independent of $n$ and $\eta$. The actual prescribed head differs from the annotated head by at most $d_n/(1-\lambda)$ by the full-period recursion. A replacement by a fixed quitting deadline uses the exact annotated Wait inequalities until it quits. Each crossing of a period boundary costs at most the seam error, with successive weights bounded by $1,\lambda,\lambda^2,\ldots$. Its possible immediate-Quit error of at most $15\eta$ is charged once. The same bound applies to Never by geometric absorption and then to any stopping law by averaging. Therefore the true prescribed payoffs converge to $s+7x e_2$ and terminal regrets tend to zero as $n\to\infty$ and $\eta\downarrow0$. Adding the original own levels to finite exits is legitimate for every comparison because rival absorption is geometric. For each fixed finite word of length $m$ every replacement has expected number of live stages at most $m/(1-\lambda)$. If original rewards are bounded by $R$, the resulting terminal-to-average difference is at most $Rm/[N(1-\lambda)]$ at horizon $N$. This gives the claimed uniform payoff with one profile for all sufficiently large horizons at each accuracy.


## Why simultaneous exits by three or more players are unavoidable

For the rest of the argument take all own levels to be one, write $M=K/L\ge1$, and take $L>0$.

**Exact stationary exclusion.** Let $q_i$ be the four date hazards, $A_i=1-\prod_{j\ne i}(1-q_j)$, and $g=Gq$. In units relative to 1 on absorption, $P_i=g_i$ is the payoff contribution to waiting, and the Quit offer is $Q_i=-g_i+b_i$ with $b_0=Lq_1q_3$, $b_1=MLq_2q_3$, $b_2=b_3=0$. The formula also holds when a third rival acts because the same bonuses apply on the grand coalition. A half hazard at every date guarantees at least 1, since the two native offers from the current exit add to $b_i\ge0$ and this strategy absorbs almost surely. All-Continue opponents give the reverse punishment bound. Thus $\mu_i=1$.

A proper stationary Nash row with at least two active players requires $B_i=P_i-A_iQ_i=(1+A_i)g_i-A_i b_i\ge0$, with equality on every active coordinate. Indeed Never against its stationary rivals yields $1+P_i/A_i$, and a finite deadline is a convex combination of this payoff and the immediate Quit offer. Necessarily $g\ge0$. At any nonzero $q\ge0$ satisfying $Gq\ge0$, all $q_0,q_1,q_2$ are positive. Setting any one of them to zero forces the others to vanish by rows $(3,1)$, $(2,3)$ and $(0,2)$ respectively. If $q_3=0$ then all $b_i=0$ and the first three active equations contradict $\det G_{012,012}=922$. So all are active. Let $p=q_1$, $\theta=q_2/p$. The two unbonused ties imply $q_0=(3/14+2\theta/7)p$, $q_3=(27/8-\theta/2)p$. Thus $g_0=(7\theta-59/4)p$ and $g_1=(268\theta-891)p/28$. Positivity of $g_1$ gives $\theta>891/268>3$. Direct subtraction yields $g_1<3g_0/2$. However, putting $f(A)=A/(1+A)$, the two boosted ties give
\[
 \frac{g_1}{g_0}=M\theta\frac{f(A_1)}{f(A_0)}
 \ \ge\ \theta\min\left(1,\frac{\theta}{35/8+\theta/2}\right)>\frac32 .
\]
Indeed $A_1\ge q_2$, $A_0\le q_1+q_2+q_3$, and $f(A_1)/f(A_0)\ge\min(1,A_1/A_0)$. The right lower bound at $\theta=3$ is $72/47$. This contradicts the active equations. At a single active owner $j$, an outsider with $G_{ij}<0$ strictly improves from receiving $1+G_{ij}$ to at least 1. AllContinue fails against immediate Quit.

**Sure openings.** At $\mu$ the Wait-minus-Quit differences divided by two are
\[
 D_0=-(8+u)q_1+6q_2-2q_3,\quad D_1=9q_0+(2-Mu)q_2-10q_3,\quad D_2=-7q_0+15q_1-4q_3,\quad D_3=14q_0-3q_1-4q_2,
 \qquad u=Lq_3/2.
\]
At a sure player $D_i\le0$, at a quiet player $D_i\ge0$, and at a mixer $D_i=0$. When $q_3=0$ the bonuses vanish and the baseline has no sure row. Here $D_3\ge0$ gives $14q_0\ge3q_1+4q_2$. If $q_0=1$, then $D_1>0$ forces $q_1=0$, then $D_2<0$ forces $q_2=1$, contradicting $D_0\le0$. If $q_1=1$, $D_0<0$ forces $q_0=1$. If $q_2=1$, $D_1>0$ forces $q_1=0$, $D_0>0$ then forces $q_0=0$, contradicting $D_3\ge0$.

If $q_3>0$, then $D_3\le0$ yields $q_0\le(3q_1+4q_2)/14\le1/2$. Thus $D_0\ge0$, $q_2>0$, $q_1<3q_2/4$, and $D_1\ge0$. Consequently $Mu\le 2+9(3\cdot3/4+4)/14<6.1$. Take $L\ge1220$. Then $u<6.1$ and $q_3=2u/L<0.01$. Only player 2 can be sure, so $q_2=1$. Since 3 mixes, $D_3=0$ gives $q_0=(3q_1+4)/14>0$ and player 0 mixes as well. Thus $q_1=(6-2q_3)/(8+u)>0.42$ and $D_2> -3.5+15(0.42)-0.04>0$, impossible at a sure player. Any stationary equilibrium containing a sure player would give a sure Nash row at its best-response continuation, and hence at $\mu$, since decreasing the continuation weakly favors the sole sure player's Quit, and all other comparisons are independent of continuation. Multiple sure players make every comparison independent of continuation.

**A paid coalition must quit first.** Use the baseline consequence that for some $\delta>0$ every profile of sufficiently small baseline regret has probability at least $\delta$ of two or more first quitters. A self-contained proof for this $G$ is given below. Let $C\ge1$ bound baseline absolute original payoffs and let $h=\delta/24$. On the compact set of $q\in[0,1]^4$ where two hazards are at least $h$ and $q_i[(Gq)_i]_+=0$ for every $i$, there is an $a>0$ with $\max(q_1q_3,q_2q_3)\ge a$. Indeed if $q_3=0$ then no pair of $012$ can be the support, since each has a participant whose comparison with the other is positive. The triple $012$ has $(Gq)_1>0$ and $q_1>0$. If $q_3>0$ and $q_1=q_2=0$, the pair $03$ has $(Gq)_3>0$. These exhaust all supports with vanishing maximum. If the compact set is empty use any $a>0$, as the limiting row below would already contradict emptiness.

Take $L$ so large that $La/2>2C+1$ and fix any $M\ge1$. Suppose profiles had new regret $e\to0$ and $p=\Pr(T\in\{013,123,0123\})\to0$. Every deviator's baseline payoff is bounded above by its modified payoff, while the prescribed payoff gain due to the modification is at most $MLp$ per player. Thus baseline regret $e^0\le e+MLp\to0$. There is a date of survival $S\ge\delta/2$ on which two hazards are at least $h$. Otherwise every date before survival falls below $\delta/2$ has conditional tie probability at most $6h\max q_i$, which is at most $6h$ times the conditional exit probability, and subsequent dates together have total mass at most $\delta/2$. This would give tie mass at most $6h+\delta/2<\delta$. Pass to convergent hazard rows along selected dates. Baseline immediate Quit has native value $-(Gq)_i$ whereas the player's baseline cap is at least 1 in original units. The conditional regret is at least $q_i[(Gq)_i]_+$ because the prescribed mixture assigns $q_i$ to immediate Quit, while the prescribed Wait branch cannot exceed its cap. Since a player can follow the profile to this date before switching, this quantity is at most $e^0/S$. The limiting row therefore lies in the compact set above.

On a subsequence $q_1q_3$ or $q_2q_3$ stays at least $a/2$. In the first case outsider 0 receives a bonus of at least $La/2$ by quitting immediately, in the second outsider 1 receives at least $MLa/2$. In either case the conditional baseline Quit offer is at least $-C$, while the modified conditional prescribed payoff is at most $C+MLp/S$. Thus following the profile to this date and then quitting gives unconditional gain at least $S(La/2-2C)-MLp$, bounded away from zero. This gives a positive lower bound on paid first-exit probability at all sufficiently small regrets for each fixed finite modified table.


**Why the baseline requires a tie.** First check that the unboosted table has no sure row at punishment 1. Set $u=0$ in $D$ above. The $q_3=0$ argument is unchanged. If $q_3>0$, the same $D_3\le0,D_0\ge0$ imply $q_0\le1/2$, $q_1<3q_2/4$ and $D_1\ge0$. Thus $q_3=1$ would give $D_1\le9/2+2-10<0$. Only player 2 can be sure, so $q_2=1$, $q_3$ mixes and $q_0=(3q_1+4)/14>0$ also mixes. From $D_0=0$, $q_1=(6-2q_3)/8>1/2$. But $D_2> -7/2+15/2-4=0$, contradicting its sure status.

Suppose baseline regrets $e$ and tie probabilities $\tau$ both tend to zero. For the live history prior to date $t$ write $S_t$ for survival, $b_t$ for the vector of unrestricted best response caps and $W_t$ for the prescribed payoff. These are original units. Let $F(w,q)$ denote the prescribed one-date expectation using $w$ if nobody quits. The nonnegative one-step loss $\ell_t=b_t-F(b_{t+1},q_t)$ satisfies $\sum_t S_t\ell_t\le e$ componentwise by telescoping the prescribed recursion and using $b_t\ge W_t$. Following the strategy up to $t$ and then optimizing also gives $\|b_t-W_t\|_\infty\le e/S_t$. All caps are at least 1 by the constant half hazard. Joint Never mass is at most $e$ because if the limiting survival is positive then conditional prescribed payoff tends to zero and the conditional cap is at least 1.

Write $\eta=e+\tau+1/n$ along the sequence, $\sigma=\sqrt\eta$, and stop just after survival first falls below $\sigma$. There is such a cut for large $n$. Every hazard up to it is at most $1-\gamma$ for fixed $\gamma>0$ and large $n$. Otherwise compactness at the bounded child caps $b_{t+1}\ge\mathbf1$ and $\ell_t\le e/\sigma$ gives a limiting Nash row with a sure quitter. Lowering its continuation to the punishment levels keeps it Nash as in the sure-opening argument. The final survival is at least $\gamma^4\sigma$. With $a_t=\sum_i q_{it}$ and $H=\sum_t a_t$ through the cut, the log survival bound $-\log(1-q_{it})\le q_{it}/\gamma$ gives $H\to\infty$.

Put mass $a_t/H$ on the marked rows $(w,q,z)=(b_{t+1},q_t,q_t/a_t)$, skipping blank dates. Take a weak limit on the compact marked space. Every limiting $w=\mathbf1+Gx$ for $x$ in the probability simplex with $Gx\ge0$. Indeed, the future conditional probability of a tie or Never is at most $(\tau+e)/(\gamma^4\sigma)$, and the child cap differs from the actual conditional payoff by at most $e/(\gamma^4\sigma)$. Write $a=\sum_i q_i$. The empirical mean of the nonnegative $\ell_t/a_t$ is at most $e/(\sigma H)$ componentwise. Since $b_t$ is the best of the two current actions using the child cap, any positive-rate limiting support row is Nash at $w$. The mean of the normalized tie probability has the same bound with $\tau$ in place of $e$, so any such row has just one active player. On a zero-rate row $z_i>0$ implies $w_i=1$ because a strictly greater continuation would give a strict Wait advantage and positive normalized loss for the positive proportion assigned to Quit. These assertions use compactness locally at points with strict inequalities.

For every polynomial $V$ the mean of $(V(F(w,q))-V(w))/a$ is zero in the limit. The expression extends continuously in $(w,a,z)$ to $a=0$ by $\nabla V(w)\cdot\sum_j z_j(r(\{j\})-w)$, by expanding the product probabilities. Replacing $V(F)$ by $V(b_t)$ before division by $H$ costs at most a fixed Lipschitz constant times $4e/\sigma$. On a blank row the corresponding telescoping difference has the same summed error bound. The remaining sum telescopes to bounded endpoints, proving the identity.

Here is an explicit contradiction to this mean-zero identity. In simplex coordinates put $Y_i=\{x:Gx\ge0,(Gx)_i=0\}$, $D_iU=\nabla U(x)\cdot(e_i-x)$, where $e_i$ is the coordinate vector. At a positive solo row of player $i$ with proper hazard $h$, its indifference gives $w_i=1$. The output is $\mathbf1+Gx'$ with $x'=(1-h)x+he_i$. This output is the limit of pre-date caps (the unnormalized row losses vanish), so $Gx'\ge0$ and $(Gx')_i=0$. Convexity puts the segment from $x$ to $x'$ in $Y_i$. At a zero-rate row $x\in Y_i$ whenever $z_i>0$.

Use $y=(6x_0-2,8x_1-2,5x_2-2)$, and define $U$ by the following coefficients on the monomials $y^\alpha$, $1\le|\alpha|\le3$, in ascending lexicographic order on the triples $\alpha$.

```
145,170,51,27,321,201,-61,47,-23,0,58,22,102,246,-36,-13,-54,71,-7
```

Use six vertices $A,B,C,D,E,F$, in this order, obtained by dividing each of the following vectors by its coordinate sum.
\[
 (388,304,559,461),\ (244,356,587,337),\ (45,21,28,0),\ (25,42,56,0),\ (312,268,891,459),\ (60,28,189,0).
\]
The vertex lists for $Y_0,Y_1,Y_2,Y_3$ are $ABCD,ABE,ACEF,BDEF$. They result by solving $\sum x_j=1,(Gx)_i=0$ and each pair of tight rows from $x\ge0,Gx\ge0$, keeping nonsingular feasible solutions. For $P=D_iU$ evaluate its symmetric affine polarization on triples of these vertices with repetition by
\[
 \frac16\sum_{\varnothing\ne S\subset\{1,2,3\}}(-1)^{3-|S|}|S|^3 P\left(\frac{\sum_{j\in S}v_j}{|S|}\right).
\]
The four maxima are respectively $-20852908491/5017776128$, $-4055857013/1179868608$, $-5487168/21253933$, $-1882523941/1031797300$. Barycentric expansion bounds $D_iU<-1/4$ throughout every $Y_i$.

Take $V(w)=U(G^{-1}(w-\mathbf1))$, which is defined since $\det G=4568$. At a proper positive solo row its normalized increment is $h^{-1}\int_0^h D_iU((1-t)x+te_i)/(1-t)\,dt<-1/4$. At a diffuse row the normalized increment is $\sum_i z_iD_iU(x)<-1/4$. The limiting mean is therefore strictly negative, the required contradiction. Thus $\inf(e+\tau)>0$ on the baseline, which implies the fixed tie bound used above.


## Why even an exact behavioral equilibrium can fail

Keep the own levels equal to one. Assume $L$ and $M=K/L$ are both sufficiently large independently. In an exact profile every reached restart is exact, since a profitable switch there could be made after following the original calendar. The lowering argument at a first sure date would yield a sure Nash row at punishment, so all hazards are proper. Every date is consequently reached with positive probability. Every deleted player's rivals absorb almost surely from every restart. Otherwise their survival would have a positive infinite product and their probability of any attempt from a sufficiently late restart would tend to zero. Every compulsory coalition contains a rival of each deleted player, contradicting the same fixed-table probability floor at each of these exact restarts. Write $W_i$ for the native prescribed payoff, also the native best-response cap. Properness makes Wait optimal, so, setting H_i=∏_{j≠i}(1−q_j), g=Gq, we have

\[ W_i=g_i+H_iW_i^{\prime}\ge-g_i+b_i,\qquad W_i=-g_i+b_i\ (q_i>0),\qquad W_i\ge0.\]

Iterating the first equation shows these values coincide with the literal Never payoff against rivals. Thus W_i and b_i are bounded above by a universal constant independent of the chosen calendar, $L$ and $M$, since the passive rewards and the entries of $G$ are fixed. Constants in O bounds below are universal as L,M→∞.

If W₀=0 at any date, then g₀≤0, −g₀+b₀≤0 imply g₀=b₀=0 and W₀′=0. Thus q₁q₃=0 on the whole tail. This precludes each of the three compulsory coalitions on an exact restart. Hence W₀>0 throughout.

If g₃>0 then q₃=0 since the unbonused player 3 has nonnegative cap. Also q₀>0 because g₃=14q₀−3q₁−4q₂. When q₃=0, co-activity of 1 is impossible since g₁=9q₀+2q₂>0 and b₁=0. Co-activity of 2 then makes the active 0 offer −6q₂<0. A sole 0 would have W₀=0. We conclude g₃≤0 everywhere. Iterating W₃≤H₃W₃′ against certain rival absorption implies W₃=0 and therefore g₃=0 at every date.

Consider a nonblank row with g₀≥0. If q₀=0 then g₃=0 gives q₁=q₂=0 and q₃>0 forces g₀=−2q₃<0. So q₀>0 and b₀=W₀+g₀>0, giving q₁q₃>0. Since 6q₂≥8q₁+2q₃, this is a fully mixed row and b₁/b₀=Mq₂/q₁≥4M/3. The uniform bound on b₁ gives W₀≤C/M at every such row. On every other row W₀≤H₀W₀′. Iterating up to the next nonnegative-g₀ active row, or to infinity and using rival absorption if none exists, shows W₀=O(1/M) on the whole calendar.

It follows that |g₀|=O(1/M), namely q₂=(4/3)q₁+q₃/3+O(1/M). Since b₁≤C implies q₂q₃≤C/(ML), we have q₃=O(1/M+1/√(ML)). Indeed q₂≥q₃/6 whenever q₃ exceeds six times the error in the expression for q₂. When q₂>0 its offer gives g₂≤0. Substituting g₃=0 gives 27q₁≤4q₂+8q₃ and then q₁=O(q₃+1/M). When q₂=0 the equation for g₀ gives that bound directly. The displayed row equations now bound all hazards by O(η), η=1/M+1/√(ML).

At every date with q₂>0, W₂=−g₂=O(η). On an intervening run with q₂=0, W₀′−W₀≥8q₁+2q₃ by g₀=−8q₁−2q₃. Summing gives total q₁ at most C/M across the run. Also g₂≤15q₁ there, so W₂≤W₂′+15q₁. If q₂ vanished forever then g₀≤0 on that tail, so W₀≤H₀W₀′ would give W₀=0 by rival absorption. Thus every date has a subsequent date with q₂>0. Iterating to that date proves W₂=O(η) everywhere.

The total charge A=Σ_{t≤N}a_t of successive prefixes diverges by rival absorption. Along a subsequence the four normalized hazard sums converge to a probability vector v. Summing the Wait identities over the prefix gives

\[ \sum_{t=1}^N g_i(t)=W_i(1)-W_i(N+1)+\sum_{t=1}^N(1-H_i(t))W_i(t+1).\]

Consequently Gv≥0. Rows 0,2,3 of Gv are O(η) since those W values are O(η) and 1−H_i≤a. Were exact profiles available for arbitrarily large L and M jointly, a further compact limit would give a probability vector v* such that Gv* is a nonnegative multiple of e₁. This contradicts det G=4568 and the fact that G⁻¹e₁=(−160,−196,−413,−455)/2284 is strictly negative. This excludes exact profiles above fixed thresholds in both parameters.

If regret tended to zero along periods bounded by $N$, pass to a subsequence with one period and a phasewise limit. A nonblank limit has continuous prescribed terminal payoffs by geometric joint absorption. Every finite deadline passes to the limit. Never is bounded by the limit of late deadlines since any positive rival Never mass contributes the positive own level on those forced late quits. This would yield an exact profile. If the limit is blank, let $A$ be total hazard per period and $x$ the limiting vector of playerwise totals divided by $A$, so $\sum x_i=1$. For the fixed finite table the native prescribed terminal payoffs tend to $Gx$ because period singleton probabilities are $Ax_i+o(A)$ and all multiple-exit probabilities are $O(A^2)$. Immediate Quit implies $Gx\ge0$. For $x_i<1$, literal Never against the other three tends to native $(Gx)_i/(1-x_i)$, so low regret forces $x_i(Gx)_i=0$. When $x_i=1$ the zero diagonal gives the same equality. The matrix is $R_0$. All pair determinants are nonzero, the triple principal determinants in lexicographic order are $922,1174,-392,624$, the full determinant is $4568$, and each column has a negative outsider. Indeed a support of size at least two would yield a nonzero kernel vector of its principal block, while a singleton support violates an outside inequality. Thus each fixed $N$ has the stated positive gap.

## Raw-table adapter and formalization

The degree and positive stationary residual tests use the same singleton field on this family. An exact stationary conclusion cannot apply on the large-premium subfamily by the stationary exclusion above. The compulsory triple first exits also exclude every construction restricted to joint dates with at most two movers. The fixed-target quantifiers are those of `quittingUniformEquilibriumPayoffConjecture` in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The raw-table adapter reads the twelve off-diagonal values, checks the displayed exit rewards on the fifteen coalitions and extracts the two premiums. It needs no strategic input. The finite periods with shrinking terminal error implement the hypotheses of `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. The distinction between a restricted-calendar regret floor and the unrestricted one is made explicit by `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`. A formalization can first establish the exact row equations and invariant cone, then continuity of the scalar return, its sign change, and the independent finite-word implementation. The necessary paid triples use the separate baseline cubic and the reward comparison above. These reward-family and unrestricted-behavior conclusions are ordinary mathematics awaiting formalization.
