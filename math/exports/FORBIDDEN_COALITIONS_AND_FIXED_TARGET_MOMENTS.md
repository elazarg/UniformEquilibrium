# Which first-exit laws can approximate equilibria attain?

On the following residual branch, an explicit sequence of finite convex tests characterizes each prescribed uniform-equilibrium payoff and each prescribed limiting distribution of first quitters. One may forbid any list of coalitions and require the remaining calendar to respect that restriction even following a refusal. The tests use independently randomized play and the original full unilateral deviation payoffs.

Let $G$ be a four-player quitting game with bounded terminal rewards $r(S)$ for the fifteen nonempty coalitions, and zero live and perpetual-Continue payoffs. All four players randomize independently. Write $r^i=r(\{i\})$, $s_i=r^i_i$, and for $j\ne i$ let $\Gamma_{ji}=r^i_j-s_j$ and $J_{ji}=r_j(\{i,j\})-s_j$. Let $\mu_i$ be the infimum over opponent profiles of player $i$'s optimal unilateral payoff. Assume some $s_i>0$, there is no one-stage Nash root with a sure quitter at $\mu$, and
\[
 \Delta=\min_{i,\,0\le t\le1}\max_{j\ne i}(tJ_{ji}-\Gamma_{ji})>0.
\]

Let $\mathcal A$ be a downward-closed family of subsets of the four players containing at least one singleton, and $I=\{i:\{i\}\in\mathcal A\}$. An allowed calendar has $\operatorname{supp}q(t)\in\mathcal A$ at every date, where $q_i(t)$ is player $i$'s hazard conditional on continued play. This also specifies play following a refusal.

For a row $q$ put $p_T(q)=\prod_{i\in T}q_i\prod_{j\notin T}(1-q_j)$, $c=p_\varnothing$, $A=1-c$, $a=\sum_iq_i$, and
\[
 F(w,q)=cw+\sum_{T\ne\varnothing}p_T(q)r(T),\qquad
 d_i(w,q)=\max_{b\in\{0,1\}} F_i(w,q_{-i},b)-F_i(w,q).
\]
Terminal exploitability $e$ is the largest, over players, of the supremum payoff from replacing their entire strategy minus their prescribed terminal payoff. A sure Nash row at $w$ has some $q_i=1$ and all $d_j(w,q)=0$. Here $b$ replaces coordinate $i$ of $q$. We have $a/4\le A\le a$. Fix $M=\max(1,\max_{T,i}|r_i(T)|)$ and $K=[-M-2,M+2]^4$. Define $E_{\mathcal A}$ to consist of triples $(w,a,z)$ with $w\in K$, $0\le a\le4$, $z$ a probability vector, and $az\in[0,1]^4$, satisfying the following conditions.

* For $a>0$, the row $q=az$ has allowed support and $d_i(w,q)=0$ for all $i$.
* For $a=0$, we have $w\ge s$, $\operatorname{supp}z\subset I$, and $z_i(w_i-s_i)=0$ for every $i$.

For a polynomial $P$, put $L_P=(P(F(w,az))-P(w))/a$ at positive rate and $L_P=\nabla P(w)\cdot\sum_i z_i(r^i-w)$ at zero rate. The two formulas give one continuous polynomial on triples by removing the factor $a$. For a family allowing only the empty mask, the test set is empty and AllContinue has regret at least $\max_i s_i>0$. Otherwise the zero-rate formula permits mixtures of allowed singletons from different masks because the flux is linear in $z$ there.

**Restricted-calendar moment theorem.** The following are equivalent.

1. Some sequence of allowed calendars has original terminal exploitability tending to zero against all unilateral behavioral replacements.
2. A Borel probability on $E_{\mathcal A}$ balances $L_P$ for every polynomial $P$.
3. At every finite degree $d$, the convex hull of the vectors $(L_{w^\alpha})_{1\le|\alpha|\le d}$ on $E_{\mathcal A}$ contains zero.

The same equivalence holds after restricting the state in assertions 2 and 3 to
\[
 w\in H_{\mathcal A}=\operatorname{conv}\{r(T):\varnothing\ne T\in\mathcal A\},\qquad w\ge\mu.
\]
Any convergent payoff subsequence in assertion 1 supplies a fixed original uniform-equilibrium payoff. This homogeneous criterion characterizes nonemptiness. The inhomogeneous equation below retains the initial target.

## From an actual calendar to occupation

Let $e$ denote terminal exploitability. At date $t$, let $W_i(t)$ be the prescribed continuation payoff, $b_i(t)$ the supremum over all replacements against the remaining opponents, and $S_t$ the probability of reaching the date. Optimal first-action recursion gives
\[
 \ell_i(t)=b_i(t)-F_i(b(t+1),q(t))=d_i(b(t+1),q(t))\ge0.
\]
Subtract the prescribed recursion and iterate. For every $N$,
\[
 \sum_{t=1}^N S_t\ell_i(t)+S_{N+1}(b_i(N+1)-W_i(N+1))\le e.
\]
If $S_\infty>0$, the probability of subsequent absorption conditional on reaching $t$ tends to zero, so $W_i(t)\to0$. Quitting immediately gives $b_i(t)\ge s_i-o(1)$. In either case $S_\infty\le e/\max_i s_i$.

Take errors $e_n\le\eta_n\to0$, with $\eta_n>0$. Stop just after survival first falls below $\delta_n=\sqrt{\eta_n}$, which occurs for sufficiently large $n$. Through this date, $\sum_t\ell_i(t)\le\eta_n/\delta_n$. All these rows have every $q_i\le1-\gamma$ for some fixed $\gamma>0$ and large $n$. Otherwise compactness would produce an exact sure row at a state $b\ge\mu$. If two or more players quit surely then no unilateral comparison uses $b$. If there is just one sure quitter, lowering its continuation to $\mu_i$ preserves the Quit inequality and all other comparisons are independent of the continuation. Both give a sure root at $\mu$. Since $-\log c\le\gamma^{-1}\sum_i q_i$ on the prefix, its total $H_n=\sum_ta_t$ satisfies $H_n\ge\gamma\log(1/\delta_n)\to\infty$.

Place weight $a_t/H_n$ on $(b(t+1),a_t,q(t)/a_t)$ on this prefix, omitting zero rates. The identity defining $\ell$ shows that replacing $P(F)$ by $P(b(t))$ in the unnormalized increment sum costs at most $\operatorname{Lip}(P)\sum_t\|\ell(t)\|$, including the error of zero-rate dates. The resulting sum telescopes, with bounded endpoints, so the normalized integrals of $L_P$ tend to zero. The integrals of $d_i/a$ are at most $\eta_n/(\delta_nH_n)$. For any subsequence of allowed rows with relative regret tending to zero and a limit at positive rate, its limit is an exact allowed row. At zero rate, a limiting $w_i<s_i$ gives positive limiting regret. If $w_i>s_i$ then Continue is strictly optimal eventually and $d_i/a$ is $z_i$ times a gap bounded away from zero, so the limiting $z_i=0$. Allowed labels persist. This proves compactness of $E_{\mathcal A}$ and shows by concentration that weak limits of the empirical probabilities are supported on it. They balance all polynomials. Their states satisfy $w\ge\mu$ since each $b_i(t)\ge\mu_i$.

For a supporting affine inequality $h\le0$ of $H_{\mathcal A}$, one has $h(F)\le c h(w)$ at every finite-rate row. With $g(v)=(v_+)^2$, the normalized increment of $g\circ h$ is at most $-g(h(w))/4$. At a diffuse row the derivative satisfies the same inequality, since $h(r^i)\le0$ for each allowed label. Every $C^1$ function on a neighborhood of the box can be approximated there by polynomials uniformly in function and first derivative. This extends balance to $g\circ h$ since $\|F-w\|_\infty\le(2M+2)a$. Thus $h(w)\le0$ almost surely. Finitely many such inequalities, including affine-span equations in both directions, give the hull restriction.

## From moment balance to long paths with allowed labels

Fix $0<\varepsilon<1$. Work in the enlarged box $K'=[-M-3,M+3]^4$. Permit an edge $w\to u$ with allowed row $q$ if $d_i(w,q)\le\varepsilon a$ for every $i$ and $\|u-F(w,q)\|_\infty\le\varepsilon a$. Suppose total charge $\sum a$ on finite paths in this relation were bounded. Let $V(w)$ be the supremum of path charge starting at $w$. For each $n$, the possible paths of lengths at most $n$ form a finite union of compact sets, including the empty paths at every state. Maximizing their continuous charge over paths with prescribed initial point gives an upper semicontinuous capacity. Their countable supremum $V$ is bounded and Borel. Extend it by zero beyond $K'$ and convolve by averaging $V(w+h)$ against a smooth probability density supported in $(0,\varepsilon/2)^4$. Write $S$ for the result.

At an exact row, $w+h\to F(w,q)+h$ is an allowed edge with the same $q$ whenever both translated states are in $K'$. In fact $F(w+h,q)=F(w,q)+ch$. The forced-Continue increase is $\prod_{j\ne i}(1-q_j)h_i$ and the forced-Quit increase is zero, so the regret increase is at most $q_i h_i$. The endpoint error is $Ah$. The defining capacity inequality implies $S(F)-S(w)\le-a$ for each positive exact inner row.

At a diffuse pure-$i$ face approximate by $q=t e_i$, setting $w_i(t)=s_i$ and, for $j\ne i$,
\[
 w_j(t)=\max\{w_j,\ s_j+[t/(1-t)](r_j(\{i,j\})-r^i_j)\}.
\]
These states yield exact rows and converge to $w$ as $t\downarrow0$. The translated states still belong to $K'$ for all sufficiently small $t$, including at the inner box boundary. Dividing the same inequality by $t$ and taking the limit gives $\nabla S(w)\cdot(r^i-w)\le-1$. Averaging gives the diffuse inequality. The Lipschitz increment bound $\|F-w\|_\infty\le(2M+2)a$ allows $C^1$ polynomial approximation of $S$ preserving strictly negative flux throughout $E_{\mathcal A}$. This contradicts assertion 2. Thus arbitrarily great finite charge is achievable at every tolerance.

## From long paths to actual calendars

For each $i$ put $\Phi_i(w)=\|w-r^i\|_2^2$. Its normalized increment on a pure-$i$ exact positive row is $-(2-a)\|w-r^i\|_2^2$ and on a pure-$i$ diffuse row it is $-2\|w-r^i\|_2^2$. Equality forces $w=r^i$. This cannot occur, since a passive $j$ then has positive forced-Quit advantage $aJ_{ji}-\Gamma_{ji}$ at positive rate, or $s_j-w_j=-\Gamma_{ji}>0$ at zero rate, by $\Delta>0$.

Consequently there are $k,\beta,\varepsilon_0>0$ such that every permitted edge in $K'$ with $\varepsilon\le\varepsilon_0$, $a>0$ and $a_{-i}/a\le\beta$, where $a_{-i}=\sum_{j\ne i}q_j$, satisfies $\Phi_i(u)-\Phi_i(w)\le-ka$. Otherwise take tolerances and ratios tending to zero together and use compactness. The relative-regret argument gives an exact or diffuse limit with $z=e_i$; the normalized endpoint perturbation of the quadratic is $O(\varepsilon)$. This contradicts strict negativity on the compact set of limiting pure-$i$ rows. On remaining edges the absolute increment is at most $Ca$, by the fixed-box Lipschitz and displacement bounds. Telescoping on **any** contiguous subinterval $J$ gives
\[
 \sum_J a\le K_0+K_1\sum_J a_{-i}.
\]
One can take $K_0=\operatorname{osc}_{K'}(\Phi_i)/k$, $K_1=(C+k)/(k\beta)$, and then enlarge constants to work for all players.

Reverse a finite path to get the physical date order and append AllContinue. For a deviation by $i$, let $D_i(t)=\prod_{v<t,\,j\ne i}(1-q_j(v))$. The interval inequality applies to physical prefixes. Summation by parts, using decreasing $D_i$ and $\sum_{t\le N}D_i(t)a_{-i}(t)\le3$ by the rival absorption bound $1-\prod_{j\ne i}(1-q_j)\ge a_{-i}/3$, gives
\[
 \sum_{t\le N}D_i(t)a_t\le K_0+3K_1,\qquad
 D_i(N+1)\le\exp((K_0-\sum_{t\le N}a_t)/K_1).
\]
Prescribed continuation gives the trial pre-date value to within $\varepsilon a$. Each unilateral action with the trial continuation gives at most that value plus $2\varepsilon a$. At each date under any replacement the probability of reaching it is at most $D_i(t)$. Iterating the upper bound costs at most $2\varepsilon(K_0+3K_1)$, plus $(2M+3)D_i(N+1)$ for replacing the terminal trial state by any actual tail payoff. Iterating the prescribed lower bound costs at most $\varepsilon(K_0+3K_1)$ plus the same tail term. Thus the actual allowed calendar has terminal exploitability at most
\[
 3\varepsilon(K_0+3K_1)+2(2M+3)\exp((K_0-\sum a_t)/K_1).
\]
This covers arbitrary behavioral replacements, including literal Never. Taking tolerances tending to zero and total charge tending to infinity proves assertion 1. Compactness of payoffs gives a convergent subsequence. The checked theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean supplies the claimed original uniform payoff and uses profiles from the chosen sequence.

Weak compactness of probabilities on $E_{\mathcal A}$ and nested finite-degree balance establish equivalence with assertion 3, also on the restricted state set. Each degree over algebraic data is a finite semialgebraic feasibility problem when the state box is used.


## The test for an individual target payoff or exit law

Fix a payoff $x$ in the reward box. There are allowed calendars with $e\to0$ and prescribed payoffs tending to $x$ if and only if a probability $\sigma$ on $E_{\mathcal A}$ satisfies, for every polynomial $P$,
\[
 \int T_P\,d\sigma=P(x),\qquad T_P=P(F)+L_P ,
\]
where $F=w$ on the zero-rate face. Equivalently, at each finite degree the vector of monomials evaluated at $x$ belongs to the convex hull of their $T$ vectors. The constant equation says the measure has mass one. This inhomogeneous equation keeps the initial condition. Its weights use a mathematical discount according to the row's total hazard, independent of the calendar dates and of the actual game's payoffs.

For necessity, on the prefix used in the occupation proof put $d_t=1/(1+a_t)$, $U_t=\prod_{v<t}d_v$. Give date $t$ mass $U_t(1-d_t)$. Total mass tends to one because $\log(1+a)\ge a/5$ on $[0,4]$. At positive rate $(1-d_t)T_P=P(F)-d_tP(w)$. Replacing $F$ by $b(t)$ and summing with weights $U_t$ telescopes to $P(b(1))-U_{N+1}P(b(N+1))$, with error bounded by $\operatorname{Lip}(P)\sum\|\ell(t)\|$, including zero-rate dates. Also $b(1)\to x$ and the weighted relative regrets tend to zero since $(1-d_t)/a_t\le1$. The same compactness argument supplies $\sigma$. In fact for this construction all its monetary states belong to $H_{\mathcal A}$ above $\mu$. Before the prefix ends, incoming survival is at least $\sqrt\eta$, and right after its last date it is at least $\gamma^4\sqrt\eta$. At these dates $\|b-W\|_\infty\le e/S_t$ and conditional Never probability is at most $e/(S_t\max_i s_i)$. The other conditional rewards are in $H_{\mathcal A}$. This proves the claimed restriction for the limit. A designated payoff outside the feasible hull or below $\mu$ is thereby excluded.

For sufficiency, the long-path comparison above bounds the distance between the trial physical starting value and the actual prescribed payoff by $O(\varepsilon)+O(\exp(-\sum a/K_1))$. It suffices to find paths of unbounded charge starting in each neighborhood of $x$ at each tolerance. Suppose that for some $\varepsilon,r>0$ all robust paths in physical order starting within $r$ of $x$ have charge at most $H$. At every point $v$ in the enlarged box let $V(v)$ be the infimum of $\prod_t(1+a_t)^{-1}$ over such robust paths starting at $v$ with arbitrary finite length, including the empty path, without restricting their future states to the neighborhood. This is Borel by taking compact minima over paths of length at most $n$ and then the countable infimum. It lies in $[0,1]$, and $V\ge e^{-H}$ within $r$ of $x$, since $\log(1+a)\le a$. For a positive exact row the translated physical edge $F+h\to w+h$ gives $V(F+h)\le V(w+h)/(1+a)$. Average the same positive translations with support also within distance $r$ of zero. The smooth average $S$ satisfies $S(x)>0$ and $T_S\le0$ on exact positive rows. The exact solo approximants and linearity in $z$ give this inequality on zero-rate rows. Uniform $C^1$ polynomial approximation controls both terms of $T_S$, so integration implies $S(x)\le0$, a contradiction. The nested finite-degree equivalence again follows by compactness.

For a specified distribution $\lambda$ of first-exit coalitions and Never, augment the trial state with sixteen coordinates $y$ in $[-2,3]^{16}$, using a box enlarged by one for the robust paths. Give each nonempty coalition $T$ the auxiliary reward vector $e_T$, and give Never $e_{\rm Never}$. The monetary Nash conditions still involve only the four players. The additional update is $F_y=c y+\sum_{T\ne\varnothing}p_T e_T$, with zero-rate drift $\sum_j z_j e_{\{j\}}-y$. Use all polynomials in the augmented state and target $(\sum_{T\ne\varnothing}\lambda_T r(T),\lambda)$. In necessity the true conditional law obeys its prescribed recursion exactly, so the same weighted telescope applies. For sufficiency translating the law coordinates gives extra endpoint errors at most $A\|h\|_\infty$, and the pure-solo approximants leave these coordinates fixed. The four monetary quadratics still bound the total hazard weighted by survival. Iterating the prescribed law recursion on a path therefore gives each component of the terminal law within $O(\varepsilon)+O(\exp(-\sum a/K_1))$ of its trial starting component, including Never. This proves the claimed convex test for each individual law. Using only the monetary variables gives the lower-dimensional test for each individual payoff.

## Preserving the entire distribution of first quitters

Let $\mathcal F$ be any collection of nonempty coalitions. Put $C_{\mathcal F}=\Pr(\text{the first quitting coalition belongs to }\mathcal F)$. The empty coalition in a terminal distribution denotes perpetual continuation. Define $\mathcal A$ to consist of sets containing no member of $\mathcal F$. For **each** limiting distribution of terminal coalitions, including perpetual continuation, the following conditions are equivalent.

1. Some original profiles converge to that distribution with $e+C_{\mathcal F}\to0$.
2. Some calendars respecting $\mathcal A$ at every date converge to that distribution with $e\to0$.

Consequently the same statement holds for each limiting payoff target. If condition 1 only prescribes payoffs, extract a convergent subsequence of the fifteen exit probabilities and the Never probability. The augmented moment test above characterizes membership of each specified law in this set. In particular an arbitrary forbidden list can be replaced by its upward closure. The support of every limiting exit distribution from profiles with vanishing exploitability is downward closed among nonempty coalitions.

Here is the approximation, including deviations after the edited dates. Use the preceding survival stopping argument for unrestricted profiles, with $e\le\eta\to0$. On the prefix with incoming survival at least $\sqrt\eta$, every hazard is at most $1-\gamma$ and the total hazard tends to infinity. Fix $L>0$ and stop at the first date taking the cumulative hazard to at least $L$. Write $N$ for its endpoint. For small enough $\eta$ this occurs on that prefix; its total charge is at most $L+4$. At every included date and just after its end the joint survival is at least $b=\exp(-(L+4)/\gamma)$. The regret identity gives $\sum_{t\le N}\|\ell(t)\|_\infty\le4e/b$.

The quadratic interval bound proved above applies with an additive $o(1)$ to this actual prefix with labels in the full family. To see this, on the dates with $\|\ell(t)\|_\infty\le\varepsilon_0 a_t$ use its per-edge bound for $w=b(t+1),u=b(t)$ (here $b(t)$ is the vector of optimal replacement payoffs). At an exceptional date the absolute change of $\Phi_i$ is at most $C'(a_t+\|\ell(t)\|_\infty)$ by boundedness, and the exceptional charges sum to at most $\sum\|\ell\|_\infty/\varepsilon_0$. This also handles dates with $a_t=0$. Telescoping gives $\sum a_t\le K_0+K_1\sum a_{-i}(t)+O(e/b)$ with constants independent of $L$. Hence the survival at the end under deletion of any one player is at most $\exp((K_0-L+O(e/b))/K_1)$. This tail estimate controls a deviator who refuses to follow the prescribed hazards.

For $B\in\mathcal F$ write $p_B$ for the conditional probability that exactly $B$ quits on a date. During this prefix $\prod_{j\in B}q_j\le\gamma^{-4}p_B$. Thus the probability that some forbidden set is contained in the quitters on the prefix is at most $\gamma^{-4} C_{\mathcal F}$. In particular, the sum over prefix dates of the hazards of players with forbidden singleton is at most $\gamma^{-4} C_{\mathcal F}/b$, using their disjoint exact-singleton probabilities at each date. Delete these players' hazards throughout the prefix.

Fix two positive thresholds $\tau<d<1$. On an original date with maximum hazard greater than $d$, keep the remaining hazards at least $\tau$ and discard the others. There are at most $(L+4)/d$ such dates. If the retained support contains $B\in\mathcal F$, then $C_{\mathcal F}\ge b\gamma^4\tau^4$. For a sequence with $C_{\mathcal F}\to0$, every retained support is therefore allowed. On other dates schedule the remaining players' individual hazards on four consecutive subdates in fixed order. All these subdates are allowed. Append perpetual continuation to the edited prefix.

Couple by sharing all original Bernoulli trials. Across the prefix, the probability of any discarded success, or of two successes on any split original date, is at most
\[
 E=\gamma^{-4}C_{\mathcal F}/b+4\tau(L+4)/d+2d(L+4).
\]
For the last bound, sum pair products on each small date, using $q_j\le d$. The same upper bound applies when any player's own trials are deleted. Off these events completed original dates and edited groups give identical first-exit coalitions through the prefix. For prescribed play the terminal laws therefore differ in total variation by at most $E+\max_i D_i(N+1)$, charging all cases reaching the original tail. A replacement is a mixture of deterministic quit dates and Never, since there is a unique continuing history. A new deadline inside a split group compares with the corresponding old date, at additional exceptional probability at most $3d$ for any rival success in that group. On a retained single date the ordinary coupling suffices. A deadline beyond the prefix, including Never, compares with old Never through the prefix and incurs at most the original deleted survival thereafter, in addition to the prefix exceptions. Thus every new cap is at most its old cap plus $2M(E+3d+\max_i D_i(N+1))$. This comparison uses the actual collective first-exit law; the date numbering may change under subdivision. Take $L$ large, then $d$ small, then $\tau$ small, and finally choose the original profiles sufficiently far along their sequence. Diagonal selection gives both assertions. Their converse is immediate from allowed support. The downward-support conclusion also follows directly from $p_B\ge\gamma^4p_T$ for nonempty $B\subseteq T$ on the high-survival prefix, whose omitted tail has probability at most $\sqrt\eta$.

Only the rewards $r_i(T)$ with $T\in\mathcal A$ or with $i\in T$ and $T\setminus\{i\}\in\mathcal A$ can enter prescribed play or a unilateral replacement on an allowed calendar. This gives, for example, 28 entries for at most one mover and 52 for at most two (sixteen singleton entries, twenty-four pair entries and twelve participant entries at triples). A test using $H_{\mathcal A}$ alone avoids computing a punishment value from the other entries. The moment criterion remains equivalent there by the two implications already proved. The restricted calendars give the same laws, payoffs and caps across completions agreeing on these entries. Transfer to unrestricted profiles avoiding the specified exits uses the stated residual hypotheses in each game.

## A lower bound on one physical date

Suppose every coalition in a forbidden list has at least $r\ge2$ members. Let $m_t=S_t\sum_{T\in\mathcal F}p_T(q(t))$ be its unconditional probability on date $t$. For every profile,
\[
 \sup_t m_t\ \ge\ (C_{\mathcal F}/r)^{r/(r-1)} .
\]
Indeed for independent trials in one row the probability of at least $r$ successes is at most $A^r$. Order the trials: after the first success, the remaining independent trials have probability at most $A$ of any success. Induction in $r$ gives the bound on every suffix and then on the row. Consequently
\[
 \sum_t m_t^{1/r}\le \sum_t S_t^{1/r} A_t
 \le r\sum_t (S_t^{1/r}-S_{t+1}^{1/r})\le r .
\]
Bounding $m_t^{1-1/r}$ by its supremum proves the inequality. A positive supremum is attained, since $\sum m_t\le1$. When every allowed-calendar sequence has exploitability bounded away from zero, the preceding theorem gives $\inf(e+C_{\mathcal F})>0$. Thus every sufficiently accurate original profile has a uniformly positive forbidden exit probability on one date. The size assumption matters because many small hazards can spread singleton exits over arbitrarily many dates.

## Boundary, sources and formalization

For a positive and a negative check on the same table, take the four players cyclically ordered. For each coalition omitting $i$ let its payoff to $i$ be zero, except that player 0 gets $-2$ at $\{1\}$ and $2$ at $\{2\}$. Set $r_i(\varnothing)=0$ in this construction only. For a coalition $T$ omitting $i$, define $r_i(T\cup\{i\})-r_i(T)$ to be $2\mathbf1_{3\in T}-1$ for $i=0$, and $1-2\mathbf1_{i-1\in T}$ for $i>0$. Any sure player forces every successor in cyclic order to respond purely because it sees that sure rival and its predecessor is already pure. At least two sure players would impose $q_0=q_3$ and $q_j=1-q_{j-1}$ for $j=1,2,3$, which is impossible. If only $i$ is sure, some $j>0$ distinct from $i$ and with $j-1\ne i$ strictly prefers to join. The same choice of $j$ gives $tJ_{ji}-\Gamma_{ji}=1$ for every $t$. The three positive own levels are one. At $q=(1/2)^4$, $w=0$, the forced offers all vanish, including player 0's cancelling passive contributions. Constant play is an exact equilibrium since each deviator encounters a rival with geometric survival. The law giving each nonempty coalition mass $1/15$ and Never zero passes the individual-law test directly: the augmented row fixes its target, so its point mass satisfies every equation. In contrast, for any solo calendar at its first date at least two positive-own players whose predecessor is inactive can quit for one. Each remaining positive-own player guarantees zero by Never, and the sum of the three prescribed payoffs is at most one at each singleton or at Never. The exploitability is therefore at least $1/3$ for all solo calendars. The intrinsic law or payoff test excludes every target under this restriction.

The declaration `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean` characterizes unrestricted nonexistence on its normal positive-singleton branch. Earlier unrestricted moment conditions test existence; the solo-calendar reduction preserves targets when all collisions vanish. Here the initial target appears as the right-hand side of the polynomial equations. The allowed supports and the individual-law constraint are both supplied by the original reward data and the specified question. The measure is a mathematical witness; the constructed strategies use private independent hazards and require no signal. Conversely for each uniform-payoff witness one may pass to infinite horizon for the prescribed play and each fixed unilateral replacement: bounded finite averages converge to their terminal payoff, including on Never. Thus the fixed-target test with unrestricted supports covers both directions of the original uniform-payoff definition.

For algebraic data each fixed-degree test uses finitely many atoms by Carathéodory and polynomial constraints. The optional monetary cutoff $w\ge\mu$ uses `quittingPunishmentValue_eq_stationaryPunishmentValue` in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`; using the feasible hull alone suffices. For formalization, first define the permitted rows, finite and diffuse flux and the terminal-law recursion, then prove the deletion bound and the discounted starting-value test. The terminal-Nash family theorem cited above is the semantic consumer. A uniform finite cutoff in the degree and the existence of some target for every residual game remain open.
