# All four first quitters, interior payoffs and the minimum period for a uniform target

Number the players 0 through 3. Set
\[
 G=\begin{pmatrix}0&-8&6&-2\\9&0&2&-10\\-7&15&0&-4\\14&-3&-4&0\end{pmatrix}.
\]
For every nonempty coalition $T$, let the native reward $Z_i(T)$ be $\sum_{j\in T}G_{ij}$ if $i\notin T$, and its negative if $i\in T$. Original rewards are $1+Z_i(T)$. Live play and perpetual continuation pay zero. On the unique live history each player uses independent private randomization. The first nonempty quitting coalition is observed and absorbs. A unilateral deviation may replace a player's entire stopping law on the finite dates and Never. Write $e$ for the largest unilateral gain in expected terminal payoff.

**Theorem.** This rational table and a nonempty open family of tables arbitrarily close to it have a uniform-equilibrium payoff. Throughout the family all sixty original reward coordinates vary independently. For each such table there are constants $d>0$ and $e_0>0$ such that every behavioral profile with $e\le e_0$ satisfies all three conclusions.

1. Each of the four players has probability at least $d$ of quitting **alone** at the first exit.
2. The probability of a simultaneous first exit is at least $d$.
3. The prescribed original payoff is inside the four-dimensional convex hull of the fifteen exit rewards, at distance at least $d$ from its boundary.

There is no exact terminal Nash profile. For each fixed $N$, every calendar periodic from the first date with period at most $N$ has terminal regret bounded below by a positive number depending on the table and $N$. Yet a fixed target can be attained by a sequence whose first-exit law puts positive mass on precisely the four singletons and one pair. On the strict open family even the minimum number of dates per period allowing simultaneous quits is $\Theta(\log(1/\varepsilon))$. The lower bound holds when the target is left free and arbitrarily many solo dates may be inserted. At the specified target, including at the rational center, the least finite-horizon threshold over all behavioral profiles is $\Theta(\log(1/\varepsilon)/\varepsilon)$. Here a uniform-equilibrium payoff means one target chosen before the accuracy, with a corresponding strategy profile that is approximately optimal against all unilateral replacements throughout sufficiently long finite horizons.

These assertions address the proposed reduction of the four-player problem to the union of bounded periods, laws that can omit a player or a simultaneous exit, and targets on proper faces of the payoff hull. The given examples force all these restrictions to fail together. There are two general reductions. The deletion test below constrains the identities that can quit first. On any strictly protected table with a positive own level for each player, no sure opening and a compulsory simultaneous exit at low regret, a limit obtained with at most $K$ dates per period that allow simultaneous quitting is realized by an exact periodic equilibrium of at most $K$ dates. This preserves the entire first-exit law and the target even if the intervening solo stretches have unbounded lengths. The precise protection condition and quantitative statement are given below. The finite-hazard construction uses only the stated reward formulas and yields every rate, continuation and first-exit mass used below. The theorem gives no universal existence result.

## Stage comparisons and sure openings

Subtract the own level 1 when a finite exit occurs. At a date with hazards $q$, put $g=Gq$ and $H_i=\prod_{j\ne i}(1-q_j)$. The native forced-Quit offer equals $-g_i$, and the native contribution from waiting and absorbing at the current date equals $g_i$. A constant own hazard $1/2$ gives zero expected native contribution on each reached date and absorbs almost surely. Thus each player can guarantee original payoff 1; all-Never opponents give the reverse bound on the punishment level.

At a sure opening at punishment, the signs required of $g_i$ at quiet, mixed and sure players are respectively nonnegative, zero, and nonpositive. At a stationary equilibrium with two or more active players and no sure player the same signs follow since a player's payoff from waiting forever is $g_i/(1-H_i)$ in native units. If there is one active player, a negative outsider gains by quitting. AllContinue fails against a positive own singleton. To check the box signs, write $S,A,Q$ for sure, mixed and quiet players. Homogeneity allows any nonzero solution to be rescaled until $S$ is nonempty. For each status set $q_Q=0,q_S=1$, solve $G_{AA}q_A=-G_{AS}\mathbf1$, and check $0<q_A<1$, $g_S\le0$, $g_Q\ge0$. For one mixer the right side is never zero. The counts for zero, one, two and three mixers are

| Check | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
| Statuses | 15 | 28 | 18 | 4 |
| Mixed equations and open probability bounds | 15 | 0 | 2 | 1 |
| Remaining signs also satisfied | 0 | 0 | 0 | 0 |

The principal triple determinants in lexical order are $922,1174,-392,624$, all principal pairs are nonsingular, and $\det G=4568$. Write $G$ with convention $p\ge0$, $Gp\ge0$, $p_i(Gp)_i=0$ for homogeneous complementarity. Its homogeneous complementarity problem has only the zero solution: a solution on two or more positive coordinates contradicts principal nonsingularity, and a singleton column has a negative outsider. At target $(101,203,307,411)$ the active-principal-system test leaves only the full-support solution $(58352,55379,208055/2,61731)/571$ of positive index.

## A necessary test on the identities that can quit first

Here is the high-survival argument used in this test. It also applies to arbitrary bounded tables with a positive own level, no sure opening at punishment and
\[
 \Delta=\min_{j,0\le h\le1}\max_{i\ne j}(hJ_{ij}-\Gamma_{ij})>0,
\]
where $\Gamma_{ij}=r_i(\{j\})-s_i$, $J_{ij}=r_i(\{i,j\})-s_i$ and $s_i=r_i(\{i\})$. In our table $J=-G$, $\Gamma=G$ and $\Delta=4$. Write $S_t$ for joint survival to date $t$, $W(t)$ for the prescribed payoff from there and $b(t)$ for the vector of best-response payoffs. The conditional regret is at most $e/S_t$, since the player can follow the original profile to $t$ and then switch. If $S_\infty>0$, conditional prescribed payoff tends to zero and the immediate Quit offer tends to the player's own level. Consequently $S_\infty\max_i s_i\le e$.

On any sequence of first dates with conditional regret tending to zero, hazards stay bounded away from one. Otherwise take a subsequence with a sure limit and bounded child caps converging to $b'\ge\mu$, the punishment vector. The nonnegative loss of the current stage action mixture evaluated at child caps is at most conditional regret by the Bellman equation. Thus the limiting row is Nash at $b'$. Lowering its continuation to $\mu$ weakly favors a sole sure quitter and does not change anyone else's comparison. This contradicts the absence of a sure opening. In particular all hazards are at most $1-\gamma$ on dates of sufficiently small conditional regret, with one fixed $\gamma>0$.

Let $M\ge1$ bound original absolute payoffs. Choose $0<\theta\le\min(1/4,\Delta/(16M))$. On a sufficiently low-regret calendar, stop immediately after joint survival first falls below $\theta$. The cut exists by the Never bound. The block has full survival at least $b_0=\theta\gamma^4>0$. If opponents of some $j$ survive the whole block with probability above $1-\theta$, the physical outcome is $\{j\}$ with probability at least $1-2\theta$. A blocker $i$ attaining the displayed margin at the first hazard $q_j$ receives prescribed payoff within $4M\theta$ of $r_i(\{j\})$, while its first-date Quit gives at least $s_i+q_jJ_{ij}-2M\theta$. Its gain contradicts small regret. Thus every player's opponents have block survival at most $1-\theta$. For each fixed $K$ and $e\to0$ we can take $K$ consecutive blocks, using the restart bound. The prefix retains full survival at least $b_0^K$, and survival after deleting any one clock is at most $(1-\theta)^K$.

Let $F_i(b',q)$ evaluate the prescribed row with the cap vector as the continuation, and write $\ell_i(t)=b_i(t)-F_i(b(t+1),q(t))\ge0$. Telescoping the prescribed payoff recursion gives $\sum_t S_t\ell_i(t)\le e$. On our prefix the loss from continuing instead of optimizing at a single date is at most $\ell_i(t)/\gamma$, since Continue has prescribed weight at least $\gamma$. The strategy that always waits therefore has total loss from $b_i(1)$ at most $e/(\gamma b_0^K)+2M(1-\theta)^K$. First let $e\to0$, then $K\to\infty$. For every player the prescribed and literal Never payoffs have the same limit. Moreover, if a player has limiting first-exit participation zero, the sum of that player's hazards on the prefix tends to zero, since the sum weighted by $S_t$ is its total first-exit participation there. Hence its probability of appearing after a different player's unilateral deletion is also negligible there. The geometric tail bound handles the rest. A participant of positive limiting incidence also has positive limiting singleton mass: cut at fixed small survival, use $q\le1-\gamma$ up to the cut, and condition on that player's quit, when its three rivals all wait with probability at least $\gamma^3$.

For a limiting distribution of first quitters, let $B$ be the participants with positive incidence. $B$ cannot be empty by the Never bound. It cannot be a singleton, since deleting that sole owner must still give absorption from the remaining identities with probability tending to one. For any $i\in B$, couple prescribed and deleted play by using the same independently sampled stopping times. If someone else stops before $i$, the payoff to $i$ agrees. On a simultaneous first exit $T$ containing $i$, deleting its clock gives $r_i(T\setminus\{i\})$; on a singleton $i$ first, it yields a later nonempty rival coalition. In the limit those rivals belong to $B\setminus\{i\}$, as just shown. In particular let $P_i(D)=r_i(D)-s_i$, $Q_i(D)=r_i(D\cup\{i\})-s_i$ for nonempty rival sets $D$. If all $P_i(D)>0$ and $P_i(D)\ge Q_i(D)$ on those rival sets, deletion gives a strict limiting gain on $i$'s singleton first exits and never a limiting loss. If instead all $P_i(D)<0$ and $P_i(D)\le Q_i(D)$ there, it gives a strict limiting loss and never a limiting gain. Both contradict equality with the Never payoff. These are raw exclusions of $B$ for general tables under the displayed residual hypotheses.

On the stated additive table a row whose singleton comparisons on the rivals of $B$ have the same strict sign satisfies one of these exclusions. This always applies to a pair. For $B=012,013,023,123$, take respectively row $1,0,2,3$ with signs $+,-,-,-$. Hence only $B=0123$ survives. Compactness upgrades positivity at each limiting law to constants $d,\varepsilon>0$ such that $e\le\varepsilon$ implies every singleton has first-exit probability at least $d$.

In native coordinates $L=(965,-612,762,856)/1142$ has $L G=\mathbf1^\top$. The four affinely independent singleton vectors lie on $Lw=1$. The values of $1142(LZ-1)$ at $02$ and $03$ are $230$ and $-18966$, respectively. Thus no supporting hyperplane of the exit hull contains all four singletons. Every limiting payoff is an interior point because it assigns positive mass to all four. Compactness also gives positive distance from the boundary at sufficiently small regret.

## A finite test excluding every exact profile

Suppose an exact original profile existed. Positive own levels give certain absorption, and a first sure date would give a sure opening at punishment. Every finite date is therefore reached with positive probability, its conditional profile is exact, and every player uses Continue with positive probability. In native coordinates $w(t)=W(t)-\mathbf1\ge0$ by security. The forced-Quit and Wait equations are
\[
 w_i(t)=g_i(t)+H_i(t)w_i(t+1)\ge -g_i(t),
 \qquad q_i(t)>0\ \Longrightarrow\ w_i(t)=-g_i(t).
\]
If $w_i(t)=0$, then $g_i(t)=w_i(t+1)=0$ by these equations and $H_i>0$. Thus the set $Z$ of zero coordinates grows monotonically and is eventually constant.

Fix its final value $Z$. For any nonblank date let $S$ be its support and normalize $q$ to sum one. Then $G_Zq=0$ and $(Gq)_i<0$ for $i\in S\setminus Z$. The following table gives weights $v_Z\ge0$ such that $v_ZGq\le-1$ at every such normalized date. A dash means there is no nonblank date on that stratum. The middle column counts the distinct vertices in the union of the closures of its feasible support cells.

| Zero set | Vertices | Weights |
| --- | ---: | --- |
| empty | 12 | (1,1,0,3) |
| 0 | 5 | (0,1,2,0) |
| 1 | 4 | (1,0,0,2) |
| 2 | 6 | (0,1,0,1) |
| 3 | 5 | (1,1,0,0) |
| 01 | 0 | — |
| 02, 03, 23 | 2 each | (0,1,0,0) |
| 12 | 1 | (0,0,0,1) |
| 13 | 1 | (1,0,0,0) |
| 012, 013, 123, 0123 | 0 | — |
| 023 | 1 | (0,1,0,0) |

To reproduce the entire finite certificate, for each nonempty $S$ use the equalities $\sum_{i\in S}q_i=1$, $G_{Z,S}q_S=0$ and the inequalities $q_S\ge0$, $-G_{S\setminus Z,S}q_S\ge0$. Enumerate vertices by adding enough independent tight inequalities to give a full-rank linear system on $q_S$, retaining its unique solution exactly when all weak constraints hold. Discard a support unless every inequality is strictly positive at some retained vertex; the average of the vertices then satisfies all strict inequalities at once. Pad remaining vertices by zeros off $S$ and remove duplicates. Dotting each with the indicated $v_ZG$ gives at most $-1$. This recipe uses only integer matrices of at most four columns. The polytope is a slice of the compact simplex, so checking its vertices suffices.

Along the final stratum, $w(t+1)-w(t)=-Gq(t)+(1-H(t))\odot w(t+1)$. Multiplying by its nonnegative weights gives an increase of at least $\sum_i q_i(t)$ on every date, including blanks. Bounded payoffs imply finite total hazard. If the stratum has no nonblank date the same conclusion is immediate. All hazards are proper, so finite total hazard leaves positive probability of perpetual continuation. This contradicts certain absorption and excludes arbitrary exact behavioral equilibria.

For a fixed period bound $N$, if regrets tended to zero take a subsequence of the same period converging phase by phase. If the limiting calendar is nonblank its payoff is continuous by geometric absorption over a period. All finite deadline inequalities pass to the limit. They also bound Never since truncating a Never response at date $n$ tends to its payoff plus the nonnegative own level times its rival Never probability. This gives a forbidden exact profile. Otherwise put $a$ equal to total hazard per period and pass to a limit $p$ of the four normalized individual totals. The limiting native prescribed payoff is $Gp$ by expanding the period probabilities to first order. Immediate Quit gives $Gp\ge0$. For $0<p_i<1$ deleting $i$ instead gives $(Gp)_i/(1-p_i)$, which cannot exceed its prescribed value, so $(Gp)_i=0$. At $p_i=1$ the zero diagonal gives the same equality. This contradicts homogeneous complementarity. Thus the fixed-period floor is positive for each $N$ individually.

## A direct cubic obstruction to vanishing simultaneous exits

Use the displayed rational matrix $G$ and native rewards. Suppose terminal exploitability $e$ and the probability $\tau$ of a tied first exit both tend to zero. Let $S_t$ denote joint survival to date $t$, $q_t$ the hazard row, $b_t$ the four original best-response caps and $W_t$ the prescribed continuation. With $F$ the one-step prescribed payoff map, $\ell_t=b_t-F(b_{t+1},q_t)\ge0$ satisfies $\sum S_t\ell_t\le e$ componentwise and $\|b_t-W_t\|_\infty\le e/S_t$. These follow by Bellman recursion, telescoping, and deviating after the indicated live history. Joint Never has probability at most $e$ since the original own singleton levels are one.

Stop after survival first falls below $\delta=\sqrt{\eta}$ for $\eta\ge e+\tau$ tending to zero. Every included hazard stays below $1-\gamma$ uniformly, or compactness at the bounded future caps $b_{t+1}\ge\mu=\mathbf1$ and $\ell_t\le e/\delta$ would give a sure Nash row, which is still Nash after lowering its continuation to $\mu$. Thus the final survival is at least $\gamma^4\delta$ and $H=\sum_t a_t\to\infty$ for $a_t=\sum_i q_{it}$, since $-\log\prod_i(1-q_{it})\le a_t/\gamma$.

Give positive-rate dates mass $a_t/H$ and record $(w,q,z)=(b_{t+1},q_t,q_t/a_t)$. Take a weak limit on the compact marked space. The conditional probabilities of a tied exit or Never on the selected tails are bounded by $(\tau+e)/(\gamma^4\delta)$, so every limiting $w=\mathbf1+Gx$ has $x$ in the probability simplex and $Gx\ge0$. Normalized one-step regret has mean $\sum_t\ell_t/H\le e/(\delta H)$. The normalized tie probability has mean at most $\tau/(\delta H)$. Hence every positive-rate support row is solo and exact. At zero rate, positive $z_i$ requires $w_i=1$: a strict Wait advantage would make $\ell_{it}/a_t$ bounded below by $z_i$ times a positive constant. Here $w\ge\mathbf1$ is already known. For every polynomial $V$, the normalized increments $(V(F)-V(w))/a$ have mean zero in the limit. Their zero-rate extension is $\nabla V(w)\cdot\sum_i z_i(r^i-w)$ by product expansion. Telescoping $V(b_t)-V(b_{t+1})$ and replacing $b_t$ by $F$ costs only $O(e/\delta)$ before division by $H$, including the omitted zero-hazard dates.

Set $Y_i=\{x\ge0:\sum x_j=1,\ Gx\ge0,\ (Gx)_i=0\}$ and $D_iU=\nabla U\cdot(e_i-x)$. A proper positive solo $i$ of hazard $h$ is indifferent, so $x\in Y_i$. Its output is $x'=(1-h)x+he_i\in Y_i$. For $G_{ki}<0$, equilibrium Wait gives $(Gx')_k\ge-hG_{ki}>0$. For $G_{ki}\ge0$ use its convex-combination formula. Thus each $x_t=(1-t)x+te_i$ for $0\le t\le h$ belongs to $Y_i$.

There is an explicit cubic satisfying $D_iU<-1/4$ everywhere on every $Y_i$. Put $y=(6x_0-2,8x_1-2,5x_2-2)$. The coefficients of $U$ on monomials $y^\alpha$, with $1\le|\alpha|\le3$ in ascending lexicographic order, are

    145,170,51,27,321,201,-61,47,-23,0,58,22,102,246,-36,-13,-54,71,-7.

Normalize each of the following six vectors by its sum:

    A (388,304,559,461)   B (244,356,587,337)   C (45,21,28,0)
    D (25,42,56,0)       E (312,268,891,459)   F (60,28,189,0).

The vertex sets of $Y_0,Y_1,Y_2,Y_3$ are respectively ABCD, ABE, ACEF, BDEF. To verify, solve $\sum x_j=1,(Gx)_i=0$ with each pair of additional active inequalities from $x\ge0,Gx\ge0$, discarding singular and infeasible solutions. For $B_i=D_iU$, enumerate triples $v_1,v_2,v_3$ of face vertices with repetitions and evaluate their symmetric three-affine polarization
\[
 \tfrac16\sum_{\emptyset\ne S\subset\{1,2,3\}}
 (-1)^{3-|S|}|S|^3 B_i\Big(\sum_{j\in S}v_j/|S|\Big).
\]
The four maxima are $-20852908491/5017776128$, $-4055857013/1179868608$, $-5487168/21253933$, $-1882523941/1031797300$. Barycentric expansion proves the strict bound throughout each face.

Take $V(w)=U(G^{-1}(w-\mathbf1))$. At a positive solo its normalized increment is $h^{-1}\int_0^hD_iU(x_t)/(1-t)\,dt<-1/4$. A zero-rate row gives $\sum_i z_iD_iU(x)<-1/4$ since $x\in Y_i$ for every active proportion. This contradicts the zero-mean identity and proves $\inf(e+\tau)>0$.

## Stability of the exclusions in the original reward table

Use own singleton levels s_i>0 and comparison coordinates Z_i(T)=r_i(T)−s_i. Write P_i(T)=Z_i(T), Q_i(T)=Z_i(T+i) for nonempty rival masks T. Extend these data by zero at the empty set, and write $P_i(q),Q_i(q)$ for their expectations over the product of the rival hazards. Use the rational center

    G = [0,−8,6,−2; 9,0,2,−10; −7,15,0,−4; 14,−3,−4,0],
    P_i^0(T)=Σ_{j∈T}G_ij,  Q_i^0(T)=−P_i^0(T).

Consider every table within 1/100 in the 56 native coordinates P,Q satisfying Q_i(T)+P_i(T)>0 in all 28 nonempty rival cells. This is open in the sixty original rewards and nonempty arbitrarily close to the center by raising every participant entry of a nonsingleton coalition equally. The center itself, where these inequalities are equalities, is handled separately by the zero-set argument. The strict open set has **no exact terminal Nash profile**. The equilibrium construction below gives an open subfamily of this set.

Independent constant hazard 1/2 guarantees original payoff ≥s_i against every opponent profile, since the two native absorbing contributions sum nonnegatively; eventual absorption is certain. All-Never opponents give μ_i≤s_i, so μ=s. No reachable row in an exact profile can contain a sure mover: lowering the continuation to μ preserves sure optimality when there is only one sure mover; when there are more, all comparisons are independent of the continuation. The following finite linear check excludes such rows at μ throughout the stated radius. For each of 65 statuses with nonempty sure set S, quiet set N and remaining mixers A, set q_S=1, q_N=0, 0≤q_A≤1. The two native offers at μ differ from +Gq and −Gq by at most 1/100 each. Impose (Gq)_i≤1/100 on S, (Gq)_i≥−1/100 on N and |(Gq)_i|≤1/100 on A. All polytopes are empty. To reproduce, list these halfspaces and the 2|A| cube inequalities in q_A. Solve each subset of |A| linearly independent tight equalities and retain feasible solutions. Counts by |A|=0,1,2,3 are 15,28,18,4 statuses and zero retained vertices throughout. Also Δ>0 since every column j has an i with G_ij<0, and its perturbed Γ_ij stays negative while J_ij stays positive.

All dates of an exact terminal profile would now be reached. Joint Never has zero probability: truncating a player's privately prescribed deadline at a deterministic late date gives limiting gain s_i times the joint Never probability by bounded convergence. In particular Σ_t a_t=∞ for a_t=Σ_iq_i(t), since every q_i(t)<1. From every date the prescribed values are optimal, so their native translates W_i≥0. Properness gives

    W_i=P_i(q)+H_i W_i′ ≥ Q_i(q),       H_i=∏_{j≠i}(1−q_j)>0,

with equality to Q_i(q) on participating coordinates. If W_i=0 then P_i(q)≤0 and Q_i(q)≤0. The strict protection implies P_i(q)=Q_i(q)=0, W_i′=0 and every rival hazard zero: if some rival acts, the expected sum on that nonempty event is strictly positive. Iterating leaves only i forever. All future exits would then be its singleton, contrary to a negative outsider Γ_ji and W_j≥0. Thus W_i>0 on every date. No solo can then occur, as its participant's native offer is zero.

For a nonempty simultaneous support S discard any S admitting k∈S with G_kj>0 for every other j∈S. Its actual Q_k is strictly negative for every nonempty rival subset, hence incompatible with its positive prescribed value. The survivors are 13,23,013,023,123,0123. At each such row x=q/a belongs to the simplex on S and (Gx)_i≤1/100 for i∈S, since Q_i(q)>0 and |Q_i(q)+(Gq)_i|≤(1/100)Pr[some rival quits]≤a/100. For λ=(1,1,0,3) the respective maxima of λGx on these six closed polytopes are

    −12, −4, −29139/4925, −17587/3000, −799/150, −109169/61200.

For reproduction fix Σx=1 and choose |S|−1 tight rows of x≥0 and (Gx)_S≤1/100, retaining the feasible nonsingular vertices. Because |P_i(q)−(Gq)_i|≤a/100 and ||λ||₁=5, the table implies λP(q)<−a. The waiting recursion and W′≥0 yield λ(W′−W)≥−λP(q)>a on every active date, with equality zero on a blank. Bounded native values contradict Σa=∞.

At the center the bounds on the four singleton masses, the total simultaneous-exit mass and the distance of the payoff from the hull boundary hold jointly at some positive regret threshold. These bounds persist in a neighborhood. Indeed, changing the original table by at most $h$ in sup norm changes any prescribed or deviating payoff by at most $h$ and its regret by at most $2h$. Exit probabilities depend only on the calendar. The supporting function of the exit hull in every unit direction and the prescribed payoff in that direction each change by at most $2h$ in four dimensions. Shrinking the neighborhood gives the three asserted positive lower bounds. The fixed-period proof also applies at each nearby table with the strict protection and no exact equilibrium just proved. In its all-small-hazards case replace $G$ by that table's native singleton matrix. Its homogeneous complementarity still has only the zero solution by the strict principal determinant and outsider tests above.

## An explicit equilibrium payoff, with stability in the raw rewards

Use the player order $(1,3,2,0)$ from the original table, writing $0,1,2,3$ for the new labels within this construction. Subtract each recipient's own singleton payment on every nonempty exit. Write $P_i(D)$ for its native passive reward at nonempty rival coalition $D$, and $Q_i(D)$ for its native joining reward there. Both take value zero at the empty rival set. The singleton matrix has the form
\[
\begin{pmatrix}0&-a&-c&A\\-b&0&-d&B\\g_2&j_2&0&-k\\g_3&j_3&H&0\end{pmatrix}
=\begin{pmatrix}0&-10&2&9\\-3&0&-4&14\\15&-4&0&-7\\-8&-2&6&0\end{pmatrix}.
\]
Use the variable entries on the left also for nearby tables. Set $u=Q_0(\{1\})/a$, $v=Q_1(\{0\})/b$ and $K_i=(g_i v+j_i u+P_i(\{0,1\}))/(1+u+v)$ for $i=2,3$. At the displayed table $u=v=1$, $K_2=22/3$, $K_3=-20/3$.

For $49/20\le t\le5/2$ put
\[
 x=(A-ct)/a,\quad y=(B-dt)/b,\quad L=-\frac{Ht+g_3 y+j_3x}{K_3xy},\quad X=Lx,\quad Y=Ly,
 \quad s=tL,\quad p=L/(1-s),\quad T=kp/(1-p).
\]
Define $R=(g_2Y+j_2X+K_2XY)/((1+X)(1+Y))$. At the center $x=(9+2t)/10$, $y=(14-4t)/3$ and $L=3(244t-587)/(20(7-2t)(2t+9))$. It increases to $69/560$ since its positive numerator increases and its positive denominator decreases. Thus $p,s\in(0,1)$ on the whole interval. The two endpoint values of $R-T$ are $656541504/2221428391$ and $-64124/993811$, respectively. The formulas retain positive $x,y,L$, proper $p,s$ and these strict endpoint signs under sufficiently small perturbations of every native entry. Choose a root $R=T$ by continuity. At the center its $T$ is approximately $1.40930117$.

Construct a finite period by prefixing dates. Start with native continuation $T e_2$. A solo block of owner 3 with total quit probability $p$ gives $(Ap,Bp,0,0)$. Prefix a solo block of owner 2 with total probability $s$, giving $(aX,bY,0,Hs)$ since $p(1-s)=L$. Each mover always has zero prescribed value and zero Quit and Continue offers. Each quiet owner's value interpolates monotonically between its nonnegative block endpoints.

Fix $\rho=2/3$ and a positive integer $m$. During solo 3 the join offers of observers 0 and 1 are nonpositive, since their joining entries at $\{3\}$ are strictly negative. For observer 2 let $W$ be its current value, initially $T$, and $J=Q_2(\{3\})$. At the center $k=J=7$. Shrink the reward neighborhood so $0<J$ and $J/(k+J)<\rho$. For $m$ steps set the hazard equal to $(1-\rho)W/(k+W)$. The new Wait value is $\rho W$, and the Quit offer is at most $\rho W$ because $J(1-\rho)\le\rho k$. At the next step use hazard $W/(k+W)$ to reach zero exactly. The only possible regret on the block is at this final step, bounded by $(J/k)T\rho^m$. The total hazard probability is exactly $p$ because the cumulative probability $p'$ solves $(1-p')T-kp'=0$. On solo 2 only observer 1 has a positive joining entry at $\{2\}$; those of 0 and 3 are strictly negative. Observer 1's Wait value remains at least $bY$ because it decreases from $Bp$ to $bY$. This has a positive uniform lower bound over the parameter interval and a sufficiently small reward neighborhood. A fixed number $n_0$ of equal subhazards $1-(1-s)^{1/n_0}$ therefore gives $Q_1(\{2\})(1-(1-s)^{1/n_0})\le bY$ throughout. All prescribed and Continue recursions are exact on both blocks.

Next prefix a pair date. At current pair coordinates $(aX_n,bY_n)$ set
\[
 q_1=X_n/(1+u+X_n),\quad q_0=Y_n/(1+v+Y_n),\qquad X_{n+1}=u q_1,\quad Y_{n+1}=v q_0,
\]
starting at $(X_0,Y_0)=(X,Y)$. Both movers are exactly indifferent. For instance player 0 gets $auq_1$ by quitting and $-a q_1+(1-q_1)aX_n$ by continuing. Both equal $aX_{n+1}$. For observer $i=2,3$, with current annotation $z$, the invariant is
\[
 V_i=\frac{z+g_iY_n+j_iX_n+K_iX_nY_n}{(1+X_n)(1+Y_n)}.
\]
Indeed the new annotation equals $(1-q_0)(1-q_1)z+g_iq_0+j_iq_1+(P_i(\{0,1\})-g_i-j_i)q_0q_1$. Inserting this and the new $X_{n+1},Y_{n+1}$ leaves the fraction unchanged. The choices of $L,t$ give $V_3=0$, $V_2=T$. Both $X_n,Y_n$ tend geometrically to zero, so the head of a word with $N$ pair dates tends to $T e_2$.

The new observer annotation, writing $(X',Y')=(uq_1,vq_0)$, is $V_i(1+X')(1+Y')-g_iY'-j_iX'-K_iX'Y'$. At the additive center its excess over the immediate Quit offer equals $V_i(1+X')(1+Y')-K_iX'Y'$. For observer 3 this is nonnegative. For observer 2 it is strictly positive, uniformly over the entire parameter interval and all $0\le X'\le X,0\le Y'\le Y$ using $V_2=R$. Indeed $15y-4x=(332-104t)/5\ge72/5$, so $R-K_2XY/((1+X)(1+Y))$ has a strictly positive minimum. The ratio $X'Y'/((1+X')(1+Y'))$ increases in each variable. This compact-box strict inequality persists in the general annotation-minus-joining-offer formula for nearby rewards, by writing $X'=\alpha X,Y'=\beta Y$ for $\alpha,\beta\in[0,1]$ and evaluating the multilinear joining polynomial at $q_1=X'/u,q_0=Y'/v$.

For observer 3 it suffices to require
\[
 Q_3(\{0\})\le-g_3v,\qquad Q_3(\{1\})\le-j_3u,\qquad Q_3(\{0,1\})\le-g_3v-j_3u-K_3uv.
\]
These are the three nonzero corner tests on the full $(q_0,q_1)$ square for the multilinear difference between the annotation at $V_3=0$ and the forced-Quit offer. Its fourth corner is zero. The center passes all three.

Take $m$ pair dates and play the whole word repeatedly in physical reverse construction order. Its length is $2m+1+n_0$. The pair recursions give $X_m\le X(u/(1+u))^m$ and $Y_m\le Y(v/(1+v))^m$. Both rates are below $\rho$ on a smaller neighborhood since they equal $1/2$ at the center. The invariant expresses the observer annotations as polynomials in $X_m,Y_m$ with constant terms $T,0$; hence the sup distance $\delta_m$ from the annotated head to $T e_2$ is at most $C\rho^m$. Compact parameter bounds make $C$ uniform on a sufficiently small neighborhood.

Every unilateral replacement faces opponent survival at most $\lambda=\max(1-p,1-s)<1$ per period, uniformly bounded away from one, because the two solo owners are distinct. The true prescribed head differs from $T e_2$ by at most $\delta_m/(1-\lambda)$, by contraction of the full-period recursion. A pure deadline pays at most the annotated head coordinate plus $\delta_m/(1-\lambda)+(J/k)T\rho^m$: telescope the exact Continue recursions and charge the Quit error once on its actual stopping date. A seam after $j$ complete periods carries weight at most $\lambda^j$. Literal Never satisfies the same bound by geometric decay, and arbitrary behavioral replacements are mixtures of these deadlines and Never. All profiles under comparison absorb almost surely, so adding the original own levels restores the same constants to every payoff. For a fixed word of length $b'$, truncating at $jb'$ dates bounds the terminal-to-horizon-$n$ error by $2M'((jb'+1)/n+\lambda^j)$ uniformly over replacements for an original reward bound $M'$. Thus the original own-level vector plus $T e_2$ is a uniform-equilibrium payoff. A period of length $O(1+\log(1/\varepsilon))$ suffices for terminal regret and target error at most $\varepsilon$, uniformly on the stated smaller family.

The construction identifies its limiting first-exit law. Set $C_*=XY/(1+u+v)$ and $D_*=(1+X)(1+Y)-(1-s)(1-p)$. In the construction labels the probabilities of the four singletons $0,1,2,3$ and the pair $\{0,1\}$ are respectively
\[
 (Y+v C_*,\ X+u C_*,\ s,\ (1-s)p,\ C_*)/D_*.
\]
To check them, initialize an event indicator's continuation at zero and propagate the indicator through one physical period. At the pair-block entrance in construction order its value is $s$ for singleton 2, $(1-s)p$ for singleton 3, and zero for the other three indicators. The same passive invariant applies to the indicator with $(g,j,P(\{0,1\}))$ equal to $(1,0,0),(0,1,0),(0,0,0),(0,0,0),(0,0,1)$ in the listed order. The limiting one-period masses are the five displayed numerators divided by $(1+X)(1+Y)$. They sum to one minus the limiting full-period survival $(1-s)(1-p)/((1+X)(1+Y))$. The infinite repeated period normalizes its one-period masses by its absorption probability, bounded away from zero. This proves the formula. All five entries are positive, and the only possible simultaneous exit is the pair of original players $1,3$.

The construction intersects the strict conditions $P_i(D)+Q_i(D)>0$ for every nonempty rival set in a full-dimensional open set arbitrarily near the center. Fix all passive data and own levels there. Increase $Q_0(\{1\})$ by $10\xi$, $Q_1(\{0\})$ by $3\xi$, $Q_3(\{0\})$ by $4\xi$ and every other nonempty joining entry by $\xi$, for sufficiently small $\xi>0$. Now $u=v=1+\xi$, so the first two observer-3 tests are strict since $8+4\xi<8v$ and $2+\xi<2u$. The third test already had strict slack $20/3$ at the center. Every $P_i(D)+Q_i(D)$ is strictly positive. All the other required bounds, including the endpoint signs and observer-2 margin, were strict uniformly. They therefore persist in an open ball of all sixty original rewards about the perturbed point; own levels and native data are independent affine coordinates.

## What boundedly many simultaneous dates imply

In this section a joint date means a date at which at least two hazards are strictly positive. The number of solo or blank dates between two joint dates is arbitrary. There are four players, bounded original rewards and zero live and Never payoffs. Translate every nonempty exit by the recipient's own singleton level s_i. On nonempty rival sets let P_i and Q_i be its native passive and joining rewards, and put P_i(empty)=Q_i(empty)=0. Use the same letters for their multilinear expectations at a hazard row. Assume the own levels are positive, there is no one-stage Nash row with a sure quitter at punishment, and there exist u_i>0 and kappa>0 such that

    Q_i(T)+u_i P_i(T) >= kappa      for every nonempty rival set T.

Assume further that terminal exploitability e and actual tied first-exit probability C satisfy inf(e+C)>0. There are game-dependent constants c>0, 0<r<1 as follows. If a periodic calendar with K joint dates in its period has e<=c r^K, every phase is uniformly proper, its native caps are at least a positive number B_K>=c r^K, and its total solo hazard is at most e times an exponential in K. In particular, for fixed K every limiting first-exit law of vanishing-regret periodic profiles with at most K joint dates is exactly the first-exit law of a proper exact periodic equilibrium of at most K dates, every one of which is joint. The initial payoff is preserved. Conversely each such exact word clearly realizes its law. This is an arbitrary-game implication under the preceding hypotheses.

**Bounds independent of the number of solo dates.** The constant own hazard 1/(1+u_i) guarantees at least s_i, since the expected native exit contribution is nonnegative at every date and the player ensures eventual absorption. All-Never opponents give the reverse punishment bound, so mu=s. Write b_i(t) for its native cap, W_i(t) for its native prescribed payoff (original minus s_i), q(t) for the row and S_t for full survival. Put a_t=sum q_i(t), H_i(t)=prod_{j other than i}(1-q_j(t)). The Bellman cap is the maximum of Q_i and P_i+H_i b_i(t+1). The prescribed one-stage mixture of these two alternatives with child caps is F_i(b(t+1),q(t)). Hence l_i(t)=b_i(t)-F_i(b(t+1),q(t))>=0, l_i(t)>=q_i(t)(b_i(t)-Q_i(q(t))) and sum S_t l_i(t)<=e by telescoping against the prescribed values. Each conditional regret is at most e/S_t. All these payoffs and caps are uniformly bounded, b_i(t)>=0, and periodicity makes the caps periodic.

Choose e0>0 and k in (0,1) such that every profile of regret <=e0 has C>=k. One date in any such profile has at least two hazards >=d=k/12. Otherwise at each date sum_{i<j} q_i q_j <=6d max_i q_i <=(k/2)(1-prod_i(1-q_i)); summing against survival contradicts C>=k. Uniformly on all profiles, l_i(t)<=tau for every i implies q_i(t)<=1-gamma for some gamma>0 and tau>0. Otherwise compactness of the row and bounded child caps >=0 gives a sure limit row Nash at a nonnegative continuation. Lowering that continuation to punishment preserves optimality for the sure player and leaves all other comparisons unaffected; with more than one sure player all comparisons are unaffected.

Put theta=k/2, beta=theta gamma^4, and choose a constant e1>0 no greater than e0 or theta tau and less than theta max_i s_i. A tail with regret <=e1 has Never probability <=e1/max_i s_i<theta (late immediate Quit when Never has positive mass). Stop it just after its full survival first falls below theta. Until that date conditional regret is <=e1/theta<=tau, hence all hazards are proper by the last bound. The cut leaves survival at least beta. The block contains a joint date since it contains all but at most theta of the tail's first-exit mass and C>=k. If e<=e1 beta^{K+1}, start K+1 consecutive such blocks at the initial date; the restart regret bound at each cut permits this iteration. They cannot all lie in one period with at most K joint dates. Full survival through the first period is thus at least beta^{K+1}. In particular every phase is proper and

    E=sum_{one period} d_t <= 4e beta^{-(K+1)},      d_t=max_i l_i(t).

If K=0 there are no low-regret profiles by the collision assumption.

Weighted averaging of the two cap alternatives gives

    (1+u_i)b_i(t) >= kappa(1-H_i(t))+u_i H_i(t)b_i(t+1).

At the date with two hazards >=d, the minimum native cap is at least b0=kappa d/(1+max u_i). Across any joint date, the minimum cap moving backward in physical time loses at most a factor alpha=min_i u_i gamma^3/(1+u_i)>0. We next cross an arbitrarily long block of solo dates. At a sole j with hazard h we have Q_j=0 and b_j(t)>=b_j(t+1), so h b_j(t+1)<=l_j(t). For every i the cap is at least its Wait alternative, hence b_i(t)>=b_i(t+1)-M h for some finite M>=1 bounding all absolute caps plus all absolute native singleton rewards. Suppose the child at the end of this block has minimum at least y>0. If E<=y^2/(8M), every earlier date of the block has minimum >=y/2. Indeed, through and including any first alleged crossing below half, each traversed child has minimum >=y/2 and the sum of its solo hazards is at most 2E/y. The total possible drop is <=2ME/y<y/2. Blank dates have zero charge and do not decrease caps. Taking

    B=b0 (alpha/2)^{K+2}

and imposing E<=B^2/(8M), we may cross the full period backwards from the indicated collision phase, losing at most the factor alpha per joint date and 1/2 per solo block. The minimum native cap across every phase is at least B. By periodicity there are at most K intervening solo blocks in the circuit from a joint date; an extra empty block does not affect the bound. The total hazard on solo dates is now at most E/B, independently of their number. The two imposed smallness conditions are implied by e<=c r^K with fixed c>0 and sufficiently small fixed r in (0,1).

**Preservation of the complete law.** Fix K and suppose e tends to zero. After taking a subsequence there are a fixed number m<=K of marked joint dates, ordered in chronology starting at the first such date at or after the initial date. Their rows and caps converge. The initial and final solo pieces form parts of the same cyclic gap. The cap difference between adjacent dates in any such piece is at most d_t+M' a_t for a uniform M', by the prescribed mixture identity. Hence all these gaps have vanishing cap change as well as vanishing exit probability per period. At every marked limit row the Bellman losses are zero by E tending to zero. A nonblank limiting row cannot have only one positive hazard, because that mover would mix properly between its singleton native zero and a continuation at least B. Empty limiting rows may be deleted. At least one remaining row has two hazards >=d, passing to a subsequence in the finite list of positions. All players therefore face geometric rival absorption under any unilateral replacement in the limiting period. Its exact cap identities and support comparisons are the actual full terminal equilibrium conditions. It has at most K genuine joint dates and no other dates.

For a direct check of the initial law, the probability of any event on a deleted solo date in one period is at most E/B. The actual terminal law is the vector of first-period coalition probabilities divided by the probability of some first-period exit, which is bounded below by d. Removing the solo gaps and taking limits of the marked rows therefore preserves all coalition masses, including the initial phase convention. The target is their mean original reward.

**A logarithmic lower bound for joint dates on the displayed strict open family.** Here u_i=1, and the preceding positive-offer drift certificate gives a fixed vector lambda>=0 such that

    lambda P(q) <= -sum q_i whenever Q_i(q)>0 for each positive q_i,

also holding at zero. This is the raw support certificate proved by the six finite polytopes; it assumes no quiet-player inequalities. Let L>=1 be a uniform supremum-norm Lipschitz bound for each Q_i and for lambda P. At each phase set to zero every hazard below 2 d_t/B and retain the others that are positive, giving q*. Each retained i has Q_i(q)>=B/2 by the first-action loss inequality. If E<B^2/(8L), then Q_i(q*)>0 for every retained i, including at d_t=0 where all positive hazards are retained. Thus

    lambda P(q) <= -a_t + (8+2L)d_t/B.

The cap loss of Wait is at most d_t/(1-q_i)<=d_t/gamma, so

    lambda(b(t+1)-b(t)) >= -lambda P(q) - (sum lambda_i)d_t/gamma.

Sum over a period. The telescoping left side is zero and the large collision contributes at least d in total hazard, so

    d <= [(8+2L)/B+(sum lambda_i)/gamma] E.

Since E<=4e beta^{-(K+1)} and B=b0(alpha/2)^{K+2}, either a preceding smallness condition fails or this inequality yields e>=c' (r')^K for table-dependent c'>0 and 0<r'<1. Constants can be uniform on a sufficiently small closed ball in the strict open family by uniform strict protection, the uniformly preserved no-sure and collision gaps, and the established support drift. The explicit production uses N geometrically contracting pair dates and two subdivided solo blocks per period; N=O(log(1/epsilon)) suffices and refining either solo block adds no joint dates. Hence the least joint-date count at the specified target is Theta(log(1/epsilon)); the lower bound also allows the target to vary. This excludes every method producing approximate equilibria on this strict family with a bounded number of joint dates per period, including those allowing arbitrarily many independent solo subdivisions. It makes no claim that a fixed hazard threshold must be exceeded logarithmically often.

## The logarithmic period is necessary, including at the rational center

Return to the original labels, so the constructed target has own singleton values on $F=\{0,1,3\}$. The following proof is uniform up to the rational center on a sufficiently small neighborhood restricted to $P_i(T)+Q_i(T)\ge0$. Let a periodic calendar have terminal exploitability and target error each at most $\varepsilon$. For small $\varepsilon$, its probability of a simultaneous first exit is at least a fixed $c>0$, uniformly by reward sensitivity. Put $h=c/12$. A row with maximum hazard below $h$ has conditional tie probability at most $6h$ times its exit probability, since each pair product $q_iq_j$ is bounded by $h\Pr(\text{exit})$. Consequently the first date $t$ with $\max_i q_i(t)\ge h$ exists, is in the first period, and its incoming survival satisfies $S_t\ge c-6h=c/2$.

Write $q=q(t)$ and let $\Delta$ bound the native reward distance to the center. For any $i\in F$, deviate using hazard $1/2$ except for the better pure action at $t$. Every earlier date's unconditional native contribution is nonnegative by protection. Conditional on reaching $t$ the two offers are at least $P_i(q),Q_i(q)$ since resumed half hazard guarantees the singleton level and absorbs almost surely. Their maximum is at least $|(Gq)_i|-\Delta$. The deviation reaches $t$ with probability $2^{-(t-1)}D_{-i}(t)$, where rival survival $D_{-i}(t)\ge S_t$. Its gain above the singleton level is at most $2\varepsilon$ by the target and regret bounds. Thus $|(Gq)_i|\le \Delta+2^{t+1}\varepsilon/c$. Also the active share of player 2's conditional regret is at least $q_2[(Gq)_2-\Delta]_+$, since its cap is at least its own level and its Quit offer differs by at most $\Delta$ from $-(Gq)_2$. This is at most $\varepsilon/S_t$. Hence $q_2[(Gq)_2]_+\le\Delta+2\varepsilon/c$.

The maximum of $\max_{i\in F}|(Gq)_i|$ and $q_2[(Gq)_2]_+$ has a strictly positive minimum $\kappa$ on $\{q\in[0,1]^4:\max_i q_i\ge h\}$. Indeed $G_Fq=0$ would give $q=(Gq)_2G^{-1}e_2$, where $G^{-1}e_2=(244,356,587,337)/2284$ is strictly positive. Such a nonzero $q$ has both $q_2>0$ and $(Gq)_2>0$. For $\Delta<\kappa/2$ the preceding bounds imply $t\ge\log_2(\kappa c/(4\varepsilon))$. The period length is at least $t$. Together with the explicit upper construction this proves that the least period for regret and target error at most $\varepsilon$ is $\Theta(\log(1/\varepsilon))$. The first-significant-date lower bound also holds without periodicity; deleting wholly blank dates preserves terminal payoffs and only removes possible deviations.

## The optimal uniform horizon over all behavioral profiles

Fix the constructed target. Its least threshold for uniform $\varepsilon$-equilibrium delivery is $\Theta((1+\log(1/\varepsilon))/\varepsilon)$ as $\varepsilon\downarrow0$. These constants can be chosen uniformly on the same small protected family, including the original rational center.

For the upper bound choose the constructed word with terminal regret and target error $\le\varepsilon/4$. Its period length $b$ is $O(1+\log(1/\varepsilon))$. Against every unilateral replacement the probability of staying live through one whole period is at most $\lambda<1$. The expected number of live stages is at most $b/(1-\lambda)$, uniformly for all the stated tables. With $M$ bounding absolute original rewards, the difference between expected terminal and finite-average rewards is at most $Mb/[n(1-\lambda)]$ at horizon $n$, by summing the probabilities of being live at each stage. Taking $n\ge4Mb/[(1-\lambda)\varepsilon]$ controls each deviation and the prescribed payoff at every greater horizon.

For the lower bound take any profile witnessing uniform terminal target delivery to accuracy $\varepsilon$ at all horizons $n\ge n_0$. Bounded convergence for each prescribed or replacement payoff gives terminal exploitability and terminal target error at most $\varepsilon$. The first-significant-date argument yields some $t\ge\log_2(C/\varepsilon)$ with incoming joint survival $S_t\ge c/2$. This conclusion applies even to aperiodic profiles. At every live history the constant half-hazard response guarantees the original singleton level $s_i$. Therefore the prescribed conditional terminal continuation $W_i(k)$ satisfies $S_kW_i(k)\ge s_i S_k-\varepsilon$, by a deviation after reaching date $k$. If $S_k=0$ the inequality holds trivially. In the game's original convention the live stage pays zero and the terminal reward starts on the following stage. Conditioning on being live at each date gives the exact identity
\[
 U_i-u_{i,n}=\frac1n\sum_{k=1}^n S_k W_i(k)
 \ \ge\ \frac{s_i c}{2n}\min(t,n)-\varepsilon ,
\]
where $U_i$ denotes the terminal payoff and $u_{i,n}$ the prescribed $n$-stage average. Both are within $\varepsilon$ of the target once $n\ge n_0$. For small $\varepsilon$ this forces $n_0\ge s_i c\,t/(6\varepsilon)$. No sign condition on the absorbing rewards enters this identity; the original own levels stay uniformly positive.

## Correspondence and formalization

The four-player conjecture is the specialization of `quittingUniformEquilibriumPayoffConjecture` in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The starting degree check is relevant to `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`. Any nonzero-degree inference used to screen an alleged counterexample still has to allow the examples above. The periodic words at successive errors give the convergent payoffs and terminal Nash estimates required by `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. The stage reward in the model is zero at the live state, including the date the quit actions are taken, as defined in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`. In the reverse direction, `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff` in the same file transfers the interior conclusion to every uniform-equilibrium payoff. The unrestricted terminal gap in `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` quantifies over all profiles at once. The separately positive fixed-period lower bounds tend to zero along the constructed words.

The raw participant deletion bound, the finite support and polynomial certificates, the bounded-joint-date reduction and the time estimates are ordinary mathematics. Narrow independent formalization steps are the equality with the deleted-clock payoff at vanishing regret, the rational support certificates, and the periodic construction with its geometric stopping-law response estimate. The proof permits all independent behavioral stopping laws and assumes no public random signal.
