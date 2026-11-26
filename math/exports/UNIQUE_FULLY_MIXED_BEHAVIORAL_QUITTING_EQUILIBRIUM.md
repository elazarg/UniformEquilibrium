# A four-player quitting game with a unique fully mixed behavioral equilibrium

There is an open set of four-player reward tables for which every sequence of independent behavioral profiles with terminal exploitability tending to zero converges, at every fixed date, to the same fully mixed stationary calendar. The original uniform-equilibrium payoff and the limiting distribution of first quitters are unique. At the rational center each player's quit probability tends to one half on the **first date** and on each subsequent fixed date. Consequently every nonempty coalition has limiting first-date probability $1/16$ and limiting terminal probability $1/15$. Arbitrary signed additions to the exit payoffs preserve these conclusions when at least one resulting own singleton payoff is positive. For nearby tables the corresponding probabilities are given by their stationary row.

An unrestricted calendar gives each player a private independent hazard $q_i(t)$ on the unique continuing history at date $t$. At the first nonempty quitting coalition $T$ it pays $r(T)$; live play and perpetual continuation pay zero. An arbitrary unilateral replacement includes all stopping laws and literal Never. Terminal exploitability $e$ is the largest player's optimal replacement payoff minus its prescribed payoff, maximized over players. Write $s_i=r_i(\{i\})$, $c=\prod_i(1-q_i)$, $c_{-i}=\prod_{j\ne i}(1-q_j)$, and $F(w,q)=cw+\sum_{T\ne\varnothing}p_T(q)r(T)$, where $p_T$ is the independent probability of exactly $T$. A row is exact at $w$ if neither pure action of any player improves its component of $F$. The vector $\mu$ of punishment levels takes, for each player, the infimum over opponents' profiles of its best-response payoff.

## The rational table

Let indices be cyclic $0,1,2,3$ with predecessor $i-1$ modulo four. For each $i>0$, put $r_i(T)=0$ whenever $T$ omits $i$. Put $r_0(T)=0$ when $T$ omits 0 except $r_0(\{3\})=-3$ and $r_0(\{1,3\})=3$. Set $r_i(\varnothing)=0$ in the next formula. For each $T$ omitting $i$, put
\[
 r_i(T\cup\{i\})=r_i(T)+D_i(T),\qquad
 D_0(T)=2\mathbf1_{3\in T}-1,\qquad
 D_i(T)=1-2\mathbf1_{i-1\in T}\quad (i=1,2,3).
\]
This specifies all sixty rewards. Here $s_0=-1$ and $s_1=s_2=s_3=1$. Facing sure player 3 holds player 0 to at most $-2$. Facing a sure predecessor holds each positive-own player to zero. These singletons also give a strict blocker for each player.

There is no sure Nash row at any continuation. If $i$ is sure, every other player compares its two actions at nonempty opponent coalitions. Its gain from Quit is the expectation of $D_j$, which depends only on its predecessor. A binary predecessor forces a binary best response. Starting with $q_i=1$ and proceeding around the cycle through the other three players makes all four coordinates binary. If at least two are sure, every player has a sure opponent, and the responses give $q_0=q_3$ and $q_j=1-q_{j-1}$ for $j=1,2,3$, an impossibility. If only $i$ is sure, a positive-own nonquitter with predecessor different from $i$ strictly prefers Quit.

The full mask has an exact interior stationary equilibrium at $q=(1/2,1/2,1/2,1/2)$ with $w=0$. Its forced-Continue offers vanish because the two exceptional passive terms for player 0 cancel and all others' passive rewards vanish. The expected gains $D_i$ also vanish. Every unilateral replacement encounters a rival quit with probability bounded below at every date, which validates the stationary one-stage optimality equations for the complete terminal game.

## The unique calendar and its stability under all sixty perturbations

Call a sequence $(w(t),q(t))_{t\ge1}$ an exact trajectory if $w(t)$ lies in $\operatorname{conv}(0,r(T):T\ne\varnothing)$, $q(t)$ is an exact Nash row at $w(t+1)$, and $w(t)=F(w(t+1),q(t))$. Every exact terminal Nash calendar with no sure row yields such a trajectory: positive survival at every finite date and zero initial exploitability imply $W_i(t)=b_i(t)$ and zero one-stage regret at every date. Every sequence of calendars with vanishing exploitability, for a fixed game having no sure root at any bounded continuation, has diagonal subsequences whose limits form such trajectories. Indeed take convergent subsequences of every finite-date hazard, prescribed and optimal value. At a date of positive limiting reach, the bound $S_t(b_i(t)-W_i(t))\le e$ follows by waiting as prescribed to $t$ and then replacing the strategy. The same bound holds with the one-stage regret at $b(t+1)$ in place of $b_i(t)-W_i(t)$ by the two first-action recursions. Thus vanishing initial exploitability forces the first-action regret of the limiting row to vanish; absence of sure roots forces positive next reach. The same argument works with varying rewards converging to such a game. The finite convex hull and the prescribed recursion are closed under these limits.

At the center example, every exact trajectory is constant. No row is sure. For $j=1,2,3$, from optimality of Continue and zero passive payoffs,
\[
 1-2q_{j-1}\le c_{-j} w_j,\qquad w=w(t+1).
\]
All $w_j\le1$ for positive-own players, and $w_1+w_2\le1$ by the exit table, implying $w_1^++w_2^+\le1$. Thus $q_0+q_1\ge1/2$. Also $2q_{j-1}\ge1-c_{-j}\ge\max_{k\ne j}q_k$. Therefore $q_0\ge1/10$, $q_1\ge1/6$, $q_2\ge1/8$ at every date. In particular every deleted player's survival decays geometrically. Optimality of Continue at each date also gives $w_j(t)=c_{-j}(t)w_j(t+1)$ for $j=1,2,3$. Iteration yields $w_j(t)=0$. Players 1 and 2 mix, which now gives $q_0=q_1=1/2$ at every date. The forced-Continue exit term for player 0, $3q_3(1-q_2)(2q_1-1)$, consequently vanishes. Iterating its Continue recursion also gives $w_0(t)=0$. Its mixing forces $q_3=1/2$, and then player 3's mixing forces $q_2=1/2$.

Hence the center calendar has hazards all $1/2$ at every date. For any sequence with terminal exploitability tending to zero, every diagonal limit is this same calendar. The hazards therefore converge to it at every fixed date. Each nonempty coalition then has limiting probability $1/15$ of being the first exit: its prescribed mass on date $t$ tends to $(1/16)^t$, and the probability of surviving any $N$ dates tends to $(1/16)^N$. The first-date grand exit probability tends to $1/16$.

This calendar uniqueness persists on an open neighborhood of all sixty rewards. First, exact trajectories of all nearby games are trapped in any specified neighborhood of $(w,q)=(0,(1/2)^4)$ at **every** date, provided the reward neighborhood is small enough. If not, take games tending to the center and exact trajectories with a bad phase. Restart each trajectory at that phase (or at its edge, using $w(t+1)$ paired with $q(t)$), then take successive compact subsequences of states and hazards. These form a center exact trajectory, contradicting the center rigidity. Absence of sure roots on a common bounded continuation box also holds throughout a neighborhood by compactness, since the center forbids any sure root there.

Near the center root solve the four indifference equations $D_i(w,q)=F_i(w,q_{-i},1)-F_i(w,q_{-i},0)=0$ for $q=g_r(w)$ by the implicit function theorem. The base $q$-Jacobian is a signed cyclic permutation with nonzero entries of magnitude two. Put $T_r(w)=F(w,g_r(w))$; while all probabilities are interior each component equals its forced-Continue offer. At the center, $T_j=c_{-j}w_j$ for $j=1,2,3$, so their derivative rows at zero are $e_j^\top/8$. For player 0,
\[
 T_0=3q_3(1-q_2)(2q_1-1)+c_{-0}w_0,\qquad
 dq_1=-dw_2/16
\]
at the base point, the latter by differentiating $1-2q_1-c_{-2}w_2=0$. It follows that
\[
 DT_0=e_0^\top/8-3e_2^\top/32,\qquad \|DT\|_\infty=7/32.
\]
By continuity the maps $T_r$ contract uniformly on a small convex state ball. The stationary branch exists in that ball by the preceding stationary implicit function theorem (equivalently by invertibility of $I-DT$). By trapping, all phases of every exact trajectory of every sufficiently close game belong to this local branch. If $w^*_r=T_r(w^*_r)$, then
$\|w(t)-w^*_r\|_\infty\le L^n\|w(t+n)-w^*_r\|_\infty$
for some $L<1$ and all $n$. Every trajectory is therefore the unique constant stationary one.

For any such fixed game every vanishing-exploitability sequence accordingly converges at each finite date to its unique interior stationary calendar, and the first-exit probabilities converge to its stationary law. The second assertion follows by continuity on finite prefixes and geometric survival of the limit. All four probabilities at the stationary root can be kept arbitrarily close to $1/2$ by shrinking the open neighborhood. This yields, for example, a uniform positive lower bound on the probability of the grand coalition exiting on the very first date at all sufficiently small exploitability on a smaller neighborhood, by the same compactness argument with varying rewards.

## Arbitrary signed additions to finite exit payoffs

For each base table $r$ in the same sufficiently small open neighborhood and each $\lambda\in\mathbb R^4$, add $\lambda_i$ to player $i$ at every nonempty exit, keeping live play and perpetual Continue at zero. Assume only $\max_i(s_i+\lambda_i)>0$. The translated game has precisely the same calendar limit, and its unique original uniform-equilibrium payoff is $w^*_r+\lambda$.

First, there is no sure row at **any** continuation in these nearby base games or their translations. If $i$ is sure, the next player's gain is an average of participant-minus-passive increments on nonempty rival coalitions. With its predecessor's probability fixed to zero or one each such increment at the center is the same number $+1$ or $-1$. An entry perturbation of size $h<1/2$ changes each difference by at most $2h$ and a translation changes it by zero. Inducting around the cycle forces all hazards binary, then rules them out, just as at the center. This argument is independent of the continuation bound.

Write $s'_i=s_i+\lambda_i$. Each actual translated calendar of exploitability $e$ has total probability of perpetual Continue at most $e/\max_i s'_i$ by the positive-own-level bound. In detail, if perpetual survival is positive then the conditional future exit probability tends to zero and each prescribed tail payoff tends to zero, while immediately quitting asymptotically guarantees $s'_i$. The initial exploitability is at least the probability of reaching any fixed tail times its exploitable difference; pass to the limit along the tails. At any fixed date with positive limiting reach $S_t$ in a vanishing-regret sequence, the conditional perpetual survival is thus at most $e/(S_t\max_i s'_i)$ using the actual reach for each sequence member. Its limit is zero. The finite-date compactness argument and the absence of sure roots again give an exact limiting trajectory, now with all its states in $H_{r+\lambda}$ itself. Subtracting $\lambda$ gives an exact feasible trajectory of the base game since
\[
 F_{r+\lambda}(w+\lambda,q)=F_r(w,q)+\lambda
\]
also holds when either action of one player is forced. Rigidity now identifies the whole sequence of limiting hazards and the one payoff target. Conversely the same interior stationary calendar absorbs geometrically even after one player deviates, so its payoff and its full deviation offers all translate by $\lambda$. It yields that target as an original uniform-equilibrium payoff.

Finally any original uniform-equilibrium payoff is a limit of terminal approximate Nash payoffs. At each accuracy take its one uniform witnessing profile; as the averaging horizon tends to infinity, prescribed and deviating average payoffs converge to their terminal expectations for each fixed replacement, by bounded convergence. The uniform inequality holds for every horizon beyond a common threshold, hence it holds in the limit for every replacement. Letting accuracy tend to zero gives the required vanishing-regret sequence and rules out every other target. Dates have positive conditional reach under the unique stationary profile, so its behavioral calendar is specified at every live history.

## One quadratic determines the payoff, the calendar and the terminal law

The rigidity can also be tested on single rows, without first solving for a trajectory. Write $H=\operatorname{conv}(\{0\}\cup\{r(T):T\ne\varnothing\})$, $a=\sum q_i$, and $Q(w)=w_0^2+1024^2\sum_{j=1}^3 w_j^2$. On every exact row with continuation in $H$ the preceding hazard inequalities hold: they used only that one row and the hull constraints. They exclude $q=0$ and any diffuse source $w\ge s$ since $w_1+w_2\le1$. All three of $q_0,q_1,q_2$ are positive, $a\ge1/2$, and for every $i$, $a_{-i}=\sum_{j\ne i}q_j\ge3q_i/4$. For $i=0$ use $q_1,q_2\ge q_0/2$; for $i=1$ use $q_2\ge q_1/2$ and $q_0\ge q_2/2$; for $i=2$ use $q_0\ge q_2/2$ and $q_1\ge q_0/2$; for $i=3$ use $q_0,q_1\ge q_3/2$. Thus $c_{-i}\le\exp(-3a/7)$. Since player 2 mixes, $2q_1-1=-c_{-2}w_2$. The exact row therefore satisfies
\[
 F_j=c_{-j}w_j\ (1\le j\le3),\qquad
 F_0=c_{-0}w_0-3q_3(1-q_2)c_{-2}w_2 .
\]
In the norm $|w|_Q=\sqrt{Q(w)}$ the off-diagonal operator has norm at most $3/1024$. There is a single $k<1$ such that throughout the whole feasible row set,
\[
 \sqrt{1+a}\,|F(w,q)|_Q\le k |w|_Q .
\]
Indeed $\sqrt{1+a}\exp(-3a/7)$ decreases for $a\ge1/2$. At the left endpoint it is $\sqrt{3/2}\exp(-3/14)$, which remains less than one after adding $3\sqrt5/1024$. For instance use $\sqrt{3/2}<49/40$ and $\exp(3/14)>1+3/14+9/392$.

The centered inequality persists for all exact rows in the corresponding feasible hull on a neighborhood of the center, with $w$ and $F$ measured relative to the perturbed stationary payoff $x_r$. Indeed, away from $w=0$ failure would contradict the strict center bound by taking a compact subsequence. Near $w=0$ all exact rows approach the unique row at zero by compactness, so all lie on the indifference chart. Its derivative has norm at the center at most $1/8+3/(32\cdot1024)$ in the weighted norm. Multiplication by $\sqrt{1+a}$, which tends to $\sqrt3$, still leaves a strict contraction on a small convex ball containing $x_r$. Apply the mean-value inequality between $w$ and $x_r$. Diffuse sources remain absent by compactness of the hull and $w\ge s$. For signed additions to rewards use the translated hull of nonempty exits and translate $x_r$ as above.

In particular let $T_P=P(F)+(P(F)-P(w))/a$ on these rows. A degree-two probability witness for a specified payoff $x$ must satisfy $\int T_P=P(x)$ for polynomials of degree at most two. With $P=Q(\cdot-x_r)$ the integrand is strictly negative except at $w=x_r$, where it vanishes. The right side is nonnegative. Thus $x=x_r$, and the only possible monetary row is the interior stationary one, which indeed gives a point-mass witness. Homogeneous degree-two balance $\int(P(F)-P(w))/a=0$ also forces exactly this row. When the state includes the conditional terminal law $y$ (fifteen nonempty coalitions plus Never), its update on this stationary row is $F_y-\lambda_r=c(y-\lambda_r)$, where $c=\prod_i(1-q_i^*)$ and $\lambda_r$ is the stationary exit law. The coefficient $(1+a)c^2$ is strictly below one at the center and on a smaller neighborhood. Testing $P(y)=\|y-\lambda_r\|_2^2$ in the same equation shows that $\lambda_r$ is the only possible law target and $y=\lambda_r$ almost surely. This gives a degree-two cutoff for both targets on this class.


## Scope and semantic endpoint

The exact equilibrium here is stationary. The substantive restrictions are on every behavioral replacement and every sequence of approximate equilibria, allowing arbitrary delays, periods and date-dependent hazards. An earlier four-player bound forced four simultaneous movers within period two and excluded tails with only two movers in a further exact case. It does not force an unrestricted approximate calendar's first date, its whole limiting law, or its unique original payoff. No degree bound for other games follows from the displayed contraction.

The checked declarations `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` give the two semantic directions. The raw table produces its equilibrium by interior indifference, and all limiting continuations and caps above are derived from original play. For formalization, the bounded continuation recursion, explicit row inequalities and weighted quadratic contraction can be handled before the perturbation argument. The latter uses ordinary finite-dimensional implicit differentiation and compactness. This proof is ordinary mathematics.
