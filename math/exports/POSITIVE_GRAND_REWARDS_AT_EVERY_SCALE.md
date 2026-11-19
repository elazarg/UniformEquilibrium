# Positive grand rewards at every scale

Fix an invertible four-player centered singleton matrix $G$. Let $J$ be any nonempty set of indices such that every column $G^{-1}e_j$, $j\in J$, is strictly positive. For $j\in J$ give player $j$ a grand reward $R_j\ge0$, independently, with $M=\max_j R_j>0$. Set $R_i=0$ for $i\notin J$ as the *reference* grand reward. There is a constant $\delta>0$ depending only on $G,J$ with the following property. Take the unique $t>0$ satisfying $Mt^3/(1+t)=1$ and put $h_*=1-(1+t)^{-3}$. Use actual native payoffs $Z$ on every coalition. On a rival set $T$ of size $k=2,3$ write
$$
 A_i(T)=Z_i(T),\qquad B_i(T)=Z_i(T+i)-R_i\mathbf1_{k=3}.
$$
Thus for $i\in J$ we take $B_i(I-i)=0$. It suffices that
$$
 \begin{split}
 |Z_i(\{i,j\})|&\le\delta(1+t)/t\quad(i\ne j),\\
 |A_i(T)-h_*B_i(T)|&\le\delta t^{1-k},\qquad
 |B_i(T)|\le\delta(1+t)^4/t^k\quad (k=2,3).
 \end{split}
$$
Every such table has a full-support proper stationary equilibrium. All four stopping odds lie between $ct$ and $Ct$ for fixed $c,C>0$ depending only on $G,J$. The original own singleton levels may have any signs. The same constants work for $G$ in a small neighborhood of the given matrix. A possible counterexample always has some positive inverse column, so for each such column these inequalities give a test on the entire positive grand-reward line and its nearby completions. With several eligible columns the test allows the positive grand rewards in all of them to vary in arbitrary proportions, including zero coordinates.

In particular, as the selected positive grand rewards tend to zero, each of the twelve participating triple rewards can independently be as large as a fixed positive multiple of $t^2$ in either sign, with its corresponding passive pair payoff close to $h_*$ times that value. The $4-|J|$ unselected grand rewards allow analogous magnitudes of order $t$, with their corresponding passive triple payoffs. The pair joining rewards may vary in a fixed interval. For large $M$, $t$ is of order $M^{-1/3}$; for small $M$, $t$ is of order $M^{-1/2}$. These are restrictions on finite original tables and need no assumption that the other prices are zero or of fixed sign.

## An all-scale test with several coalition sizes and both signs

More generally fix any collection of strictly sign-definite inverse columns, with $\sigma_i G^{-1}e_i>0$ on each selected row and $\sigma_i\in\{-1,1\}$. For any rival set $T$ of size $k=2,3$, allow independent reference magnitudes $U_{iT},V_{iT}\ge0$ for the passive and participating entries in each selected row. Set them to zero in every other row. Assume at least one is positive. Choose $t>0$ by
$$
   \sum_{i,T}t^{k-1}[U_{iT}+h_* V_{iT}]=1,\qquad h_*=1-(1+t)^{-3}.
$$
The left side is strictly increasing from zero to infinity. Equally one may use any $t$ for which that sum lies in $[1/4,12]$. In the displayed error bounds of the grand-reward theorem replace $A_i(T),B_i(T)$ by the remainders
$$
 A_i(T)=Z_i(T)+\sigma_i U_{iT},\qquad
 B_i(T)=Z_i(T+i)-\sigma_i V_{iT}.
$$
For unselected rows these are simply the two native payoffs. Keep the same singleton-rival joining bounds. The full-support proper stationary conclusion and the two-sided odds bounds still hold, uniformly over all reference sizes and proportions. Thus one may combine exit sets with two and three opponents present, including negative reference passive rewards on a positive inverse column. The case of several positive grand rewards above uses $U=0$, $V_{i,I-i}=R_i$: since $h_*(1+t)/t$ lies between one and three and $\sum R_i/M\in[1,4]$, its prescribed scale satisfies the stated interval.

For the proof write $p=tx$, where $p$ are the positive stopping odds, and $h_i(p)=1-\prod_{j\ne i}(1+p_j)^{-1}$. The stationary field divided by opponent survival sums the passive terms $Z_i(T)\prod_{j\in T}p_j$ and subtracts $h_i(p)$ times the corresponding joining terms. After division by $t$, the reference fixed point map for its zero is
$$
 T_0(x)=\sum_{i,T}(\sigma_i G^{-1}e_i)\,t^{k-1}
          [U_{iT}+h_i(tx)V_{iT}]\prod_{j\in T}x_j .
$$
Take $D$ to be the part of the probability simplex where every coordinate is at least $d>0$, with $2d$ less than the smallest coordinate of the normalized selected columns $\sigma_i G^{-1}e_i$. At $x=\rho y$, $y\in D$, the normalized $T_0$ is in the convex hull of these columns. For $0<\rho\le1$ one has $h_i(t\rho y)\le h_*$, hence $\|T_0\|_1\le C_1\rho^2$. For $\rho\ge1$ a single rival gives $h_i(t\rho y)\ge td/(1+td)\ge c_2 h_*$, using $h_*\le\min(1,3t)$. Since the total normalized weight is at least $1/4$, $\|T_0\|_1\ge c_1\rho^2$. Fix $r<1<D_0$ so that the reference norm is below $r/2$ on the inner boundary and above $2D_0$ on the outer boundary. On the entire intervening shell the reference norm is bounded below uniformly in $t$ and the proportions: use $rd$ instead of $d$ in the single-rival estimate and the positive minimum of $(rd)^k$.

Let $T_G(x)$ be the actual fixed point map obtained by multiplying the higher terms by $G^{-1}$ with the same sign convention. On this shell $h_i(tx)=O(t/(1+t))$ and $|h_i(tx)-h_*|=O(t/(1+t)^4)$ uniformly. The latter follows by differentiating $\prod_{j\ne i}(1+t x_j)^{-1}$ along the segment from $x$ to the all-ones vector; all three coordinates stay bounded above zero. Each nonreference term on a rival set of size $k=2,3$ therefore has absolute value bounded by
$$
 t^{k-1}\bigl(|A_i(T)-h_*B_i(T)|+|h_i(tx)-h_*|\,|B_i(T)|\bigr)\prod_{j\in T}x_j=O(\delta).
$$
The singleton-rival joining term is bounded by $h_i(tx)|Z_i(ij)|x_j=O(\delta)$. Thus with sufficiently small $\delta$ the normalized actual map still lies in $D$, and its boundary sizes are still strictly below $r$ and above $D_0$. On $D\times[r,D_0]$ apply Brouwer to
$$
 (y,\rho)\longmapsto \left(
 \frac{T_G(\rho y)}{\|T_G(\rho y)\|_1},
 \operatorname{proj}_{[r,D_0]}(2\rho-\|T_G(\rho y)\|_1)
 \right).
$$
The strict radial signs exclude both endpoints. At its fixed point $x=T_G(x)$, with $rd\le x_j\le D_0$. The minimum across $G$ in a sufficiently small closed neighborhood of the original normalized columns and the uniform bounds on $G^{-1}$ preserve all constants. Each player then faces geometric rival absorption. Its stationary immediate offer and perpetual-wait offer are equal, so every deterministic deadline and every private mixture has the same value. This gives exact terminal equilibrium and the signed fixed uniform target. The normalized inverse-column Brouwer map was previously used for an alternating-pair construction with an everywhere positive inverse. Here the stationary polynomial has a whole positive orthant of grand prices, and the estimates control both ends of the odds scale. [Earlier positive inverse construction](POSITIVE_INVERSE_AND_ASYMMETRIC_PAIR_UNIFORM_EQUILIBRIUM.md)

For a separation, use the singleton matrix with rows $(0,-2,-1,3),(-3,0,1,2),(1,1,0,-1),(-3,1,2,0)$. Its inverse column at player 2 is the all-ones vector, and the inverse also has a negative entry. Take $J=\{2\}$, $R_2=(1+t)/t^3$, $Z_2(012)=\alpha t^2$, $Z_2(01)=h_*\alpha t^2$ for a sufficiently small fixed $\alpha>0$, and set $Z_0(I)=Z_1(I)=Z_3(I)=Z_3(12)=t^{-4}$ and $Z_0(123)=2t^{-4}$. All other higher entries are zero. These five smaller entries respect the bounds for all sufficiently large $t$. No pure first-date coalition gives equilibrium. Every singleton has a negative outsider; every pair except $01$ has a member who prefers its partner’s singleton; and at $01$ player 2 strictly prefers joining. At every triple except $123$ the missing player strictly prefers its grand payoff, while player 3 prefers withdrawing from $123$ to $12$. Player 0 withdraws from the grand coalition. All four forced quit offers are positive near the all-quit hazards, so full-support product lowness fails. The two-row endpoint test also fails for every choice: only row 0 has two nonpositive foreign singletons, forcing its mate to be 3, but $G_{30}<Z_3(30)=0$. For $t\to\infty$ the positive passive reward on $01$ in row 2 cannot be a favorable source in the earlier weighted collision test. A supporting set must contain $012$. The triple has row 0 negative on both other members, excluding the required negative orientation in row 2's direction (row 0 must be balanced). On the full set the positive inverse column excludes that negative orientation. The adverse passive scale is of order $t^2$, whereas every favorable scale is $O(t)$; the earlier dominance ratio fails for every support. The earlier two-signed-reward construction needs the same unavailable opposite ray. The single-column jackpot theorem assumes its priced reward is large compared with bounded other rewards, and the earlier positive-inverse coalition theorem assumes every inverse column is positive. [Weighted collision test](WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md) · [Opposite-ray criterion](TWO_SIGNED_REWARDS_FROM_A_SINGLETON_MATRIX.md) · [Single-column theorem](SIGNED_SINGLE_COLUMN_JACKPOT_UNIFORM_EQUILIBRIUM.md) · [Positive-inverse coalition theorem](POSITIVE_INVERSE_COALITION_JACKPOTS_UNIFORM_EQUILIBRIUM.md)
