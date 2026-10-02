**Exact zero-boundary Nash construction can stall at every horizon, with no freedom in equilibrium selection.** I found an explicit rational four-player game proving this.

The example rules out two proposed unconditional selection steps: choosing exact finite-menu Nash equilibria with vanishing unrestricted late defect, and choosing such equilibria with vanishing joint Never mass. It also shows that **zero-boundary provenance alone does not eliminate phantom Nash–Bellman spines**.

This is not a counterexample to Fin4 equilibrium existence. The game has an explicit absorbing, exactly row-perfect stationary equilibrium, constructed below. The unresolved general producer is still unresolved; what this settles is a false exact-source route to it.

## 1. The obstruction theorem

Let the finite timing menu be

$$
F_N=\{0,\ldots,N-1,\mathrm{Never}\},
$$

and let \(\mathcal N_N\) be the set of exact Nash equilibria of the corresponding finite normal-form game. These equilibria are tested only against replacements in \(F_N\).

There is a rational four-player quitting game with zero Never payoff and own-singleton vector

$$
(1,0,0,0)
$$

such that, for every \(N\ge1\):

* \(\mathcal N_N\) consists of **one product of stopping laws**.
* Its unrestricted terminal exploitability is

  $$
  \boxed{\beta=\frac{21}{2}-7\sqrt2
  \approx0.6005050634>\frac12.}
  \tag{1}
  $$
* Its joint Never probability is

  $$
  \boxed{\rho_*=35\sqrt2-49
  \approx0.4974746831.}
  \tag{2}
  $$

Moreover, all prescribed quitting occurs at the last displayed date \(N-1\). Thus, as \(N\to\infty\), the unique exact finite-menu equilibria converge at every fixed date to **all Continue**, not to an absorbing source.

All four players are punishment-normal. In fact, their punishment values equal their own-singleton rewards.

### The complete payoff table

Use players \(I=\{0,1,2,3\}\), with core players \(J=\{0,1,2\}\). Define the three-coordinate table \(g\) by

| \(R\subseteq J\) | \(g(R)\)    |
| ---------------- | ----------- |
| \(\{0\}\)        | \((1,3,3)\) |
| \(\{1\}\)        | \((3,0,3)\) |
| \(\{2\}\)        | \((3,3,0)\) |
| \(\{0,1\}\)      | \((4,1,3)\) |
| \(\{0,2\}\)      | \((1,3,4)\) |
| \(\{1,2\}\)      | \((3,4,1)\) |
| \(\{0,1,2\}\)    | \((2,2,2)\) |

The four-player rewards, specifying all fifteen nonempty coalitions, are

$$
r(S)=
\begin{cases}
(g(S),1),&3\notin S,\\[1mm]
(g(S\setminus\{3\}),0),&3\in S,\ S\ne\{3\},\\[1mm]
(0,0,0,0),&S=\{3\}.
\end{cases}
\tag{3}
$$

Set \(z=(0,0,0,0)\).

Player \(3\) therefore receives one when some core player quits without her, and zero whenever she quits. Her presence in a coalition does not change the core players’ rewards.

Every reward lies in \([0,4]\).

### Punishment normality

Player \(0\) guarantees at least one by quitting at date zero: every coalition containing \(0\) gives her at least one. Against opponents who always Continue, her best-response payoff is exactly one. Hence \(P_0=1\).

For each other player, all rewards are nonnegative, while opponents who always Continue make the best-response payoff zero. Thus

$$
P=(1,0,0,0)=\bigl(r_i(\{i\})\bigr)_{i\in I}.
\tag{4}
$$

The obstruction does not use an abnormal added player.

## 2. The one-stage equations

Write

$$
s=(1,0,0)
$$

for the core own-singleton vector. Index core players cyclically modulo three.

For a core root \(q=(q_0,q_1,q_2)\) and continuation \(v\in\mathbb R^3\), let

$$
D_i(v,q):=Q_i-C_i.
$$

Directly from the table,

$$
\boxed{
D_i(v,q)
=
(s_i-v_i)(1-q_{i+1})(1-q_{i-1})
+q_{i+1}-2q_{i-1}.
}
\tag{5}
$$

Indeed, whenever at least one opponent quits, the difference between joining and not joining is one for the next cyclic player’s participation, minus two for the preceding player’s participation. When neither opponent quits, the difference is \(s_i-v_i\).

The exact Nash conditions are

$$
q_i>0\Longrightarrow D_i\ge0,
\qquad
q_i<1\Longrightarrow D_i\le0.
\tag{6}
$$

If player \(3\) quits with probability \(h\), the core players face precisely the same three-player root game with effective continuation

$$
(1-h)v.
\tag{7}
$$

This follows because player \(3\)’s solitary quit pays the core players zero, whereas adding her to a nonempty core coalition does not alter their rewards.

For player \(3\), let

$$
H(q)=1-\prod_{i\in J}(1-q_i)
$$

be the probability of a core quit. Her pure-action values are

$$
Q_3=0,\qquad
C_3=H(q)+(1-H(q))v_3.
\tag{8}
$$

Three elementary consequences determine every finite-menu equilibrium.

### No core player quits surely in an exact root equilibrium

This holds for **every** core continuation \(v\).

Suppose \(q_i=1\). Equation (5) gives

$$
D_{i+1}=q_{i-1}-2<0,
$$

so \(q_{i+1}=0\). It then gives

$$
D_{i-1}=1>0,
$$

so \(q_{i-1}=1\). But now

$$
D_i=-2<0,
$$

contradicting \(q_i=1\).

Therefore

$$
q_i<1\qquad(i\in J)
\tag{9}
$$

at every core root equilibrium, independently of the continuation.

### The zero-continuation game has a unique equilibrium

Define

$$
\theta:=\frac32-\sqrt2.
$$

The unique four-player one-stage equilibrium with continuation zero is

$$
\boxed{q^*=(2\theta,\theta,4\theta,0).}
\tag{10}
$$

First, there must be a positive probability of a core quit. Otherwise player \(0\) gains one by quitting, while Continue pays zero. Equation (8) therefore forces player \(3\) to Continue surely.

For the core game at continuation zero, (5) becomes

$$
\begin{aligned}
D_0&=(1-q_1)(1-q_2)+q_1-2q_2,\\
D_1&=q_2-2q_0,\\
D_2&=q_0-2q_1.
\end{aligned}
\tag{11}
$$

Every core coordinate must be positive. To see this, suppose first that \(q_0=0\). If \(q_1>0\), then \(D_2<0\) forces \(q_2=0\), after which \(D_0=1>0\), a contradiction. If \(q_1=0\), the condition \(D_1\le0\) forces \(q_2=0\), giving the same contradiction.

Thus \(q_0>0\). If \(q_1=0\), then \(D_2=q_0>0\) forces \(q_2=1\), contradicting (9). Finally, \(q_1>0\) implies \(D_1\ge0\), hence \(q_2>0\).

Together with (9), all three coordinates are interior. Thus all three differences vanish:

$$
q_0=2q_1,\qquad q_2=4q_1.
$$

Putting \(q_1=t\) into \(D_0=0\) gives

$$
4t^2-12t+1=0.
$$

The only root compatible with \(0<4t<1\) is \(t=\theta\). This proves uniqueness.

Let \(u\) be the payoff of this root with zero continuation. Since each core player mixes,

$$
u_i
=
3\left[1-\prod_{\substack{j\in J\\j\ne i}}(1-q_j^*)\right],
\qquad i\in J,
\tag{12}
$$

while

$$
u_3=1-\prod_{j\in J}(1-q_j^*).
\tag{13}
$$

In particular,

$$
u\approx(1.198485,\ 1.367532,\ 0.727922,\ 0.502525),
$$

so

$$
\boxed{u_i>r_i(\{i\})\quad\text{for every player}.}
\tag{14}
$$

### At continuation \(u\), all Continue is the unique equilibrium

Because \(u_3>0\), equation (8) gives \(C_3>0=Q_3\), regardless of the core root. Thus player \(3\) must Continue.

For the core players, every \(u_i-s_i\) is strictly positive. By (9), all opponent Continue probabilities are positive. Consequently, if \(q_i>0\), equations (5)–(6) imply

$$
q_{i+1}>2q_{i-1},
\tag{15}
$$

in particular \(q_{i+1}>0\).

A single positive coordinate would therefore force all three coordinates to be positive. Summing their three inequalities (15) would give

$$
q_0+q_1+q_2>2(q_0+q_1+q_2),
$$

which is impossible.

Hence every core player Continues. Conversely, all Continue is a strict equilibrium at \(u\), by (14).

We have proved the exact two-step structure

$$
\boxed{
0
\ \xleftarrow{\ q^*\ }\ 
u
\ \xleftarrow{\ \mathrm{AllC}\ }\ 
u
\ \xleftarrow{\ \mathrm{AllC}\ }\cdots .
}
\tag{16}
$$

## 3. Why this covers every finite-menu Nash equilibrium

The argument must cover all normal-form menu equilibria, not merely a chosen backward-induction construction.

Let \(\sigma\in\mathcal N_N\). Represent its stopping laws by behavioral hazards before the deadline.

**Every live date through the deadline has positive prescribed survival probability.** Otherwise take the first row with all-Continue probability zero. Its live history is reached with positive probability, so ordinary one-row deviations imply that this row is Nash against its specified continuation.

No core player can quit surely there, by (9) and the effective-continuation identity (7). Thus player \(3\) would have to quit surely.

All continuation payoffs of player \(3\) are nonnegative. Equation (8), together with her prescribed sure Quit, then forces \(H(q)=0\): all core players Continue at that row. But player \(0\) can join player \(3\)’s sure quit and raise her payoff from zero to one. Contradiction.

Therefore all live histories before the deadline are reached with positive probability. A profitable unilateral change in any restarted finite tail would yield a profitable change in the original finite game. Hence the continuation at each such history is itself a finite-menu Nash equilibrium, and every row satisfies the exact one-stage Nash conditions.

At the last row the continuation is zero, so its root must be \(q^*\), with payoff \(u\). At every preceding row, the continuation is \(u\), so the unique Nash root is all Continue and the payoff remains \(u\).

Thus

$$
\boxed{
q_n=
\begin{cases}
(0,0,0,0),&n<N-1,\\
q^*,&n=N-1,
\end{cases}
}
\tag{17}
$$

with all Continue after the deadline.

This also proves existence directly: the displayed profile satisfies the finite backward Nash conditions. Its stopping laws are therefore the unique member of \(\mathcal N_N\).

## 4. The exact obstruction to source production

### The absorption clock does not improve with the horizon

For every exact finite-menu equilibrium,

$$
a_{0,k}=1\qquad(k\le N-1),
$$

and

$$
a_{0,\infty}
=
(1-2\theta)(1-\theta)(1-4\theta)
=
35\sqrt2-49
=
\rho_*.
\tag{18}
$$

Thus neither earlier absorption nor eventual prescribed absorption becomes arbitrarily likely as the menu expands.

The total marginal Quit hazard of every zero-boundary exact Nash–Bellman block is also the same:

$$
\sum_{n<N}\sum_{i\in I}q_n^i
=
2\theta+\theta+4\theta
=
7\theta
=
\beta.
\tag{19}
$$

**Arbitrarily long exact blocks do not imply unbounded hazard capacity, even when the blocks are genuinely generated from the zero terminal boundary.**

### Every exact finite-menu equilibrium has unrestricted debt \(\beta\)

Player \(0\)’s law assigns positive probability to Never. Since the profile is exact menu Nash, Never must attain her prescribed payoff:

$$
U_0(\sigma)
=
U_0(\mathrm{Never},\sigma^{-0})
=
u_0.
\tag{20}
$$

Now replace her law by the pure date \(N\), immediately beyond the menu. This gives the same payoff as Never whenever an opponent quits. If every opponent plays Never, it instead gives her singleton payoff one.

The probability of that latter event is

$$
(1-\theta)(1-4\theta)=7\theta=\beta.
\tag{21}
$$

Therefore the deviation gains exactly \(\beta\).

This is also the full best-response gain. Every displayed date and Never is already bounded by \(u_0\), and all finite dates at least \(N\) give the same payoff \(u_0+\beta\).

For players \(1,2,3\), the own-singleton payoff is zero. Every date beyond the menu therefore has the same payoff as Never. Their menu Nash inequalities already cover all unrestricted deviations.

Consequently,

$$
\boxed{
d(\sigma)=(\beta,0,0,0)
\quad\text{and}\quad
E(\sigma)=\beta
\qquad(\sigma\in\mathcal N_N).
}
\tag{22}
$$

Arbitrary behavioral replacements are covered because their stopping laws are mixtures of pure finite dates and Never.

### The unique diagonal limit is a phantom spine

At every fixed date \(n\), equation (17) eventually gives \(q_n=0\). Thus the unique finite-horizon profiles converge pointwise to all Continue.

Their fixed-date continuation annotations, however, remain \(u\). The limiting annotated spine is

$$
q_n=0,\qquad v_n=u\quad(n\ge0).
$$

It satisfies the exact Nash–Bellman equations, but its actual restarted-tail payoff is zero, not \(u\).

This is not an unfortunate choice of subsequence or equilibrium selector. **There is only one finite-menu equilibrium at each horizon.**

## 5. The game nevertheless has an actual absorbing exact source

At every date prescribe

$$
\bar q=(1/4,0,0,0).
\tag{23}
$$

Every restarted tail terminates geometrically:

$$
a_{m,N}=(3/4)^{N-m}.
$$

Its actual payoff is

$$
v=(1,3,3,1).
\tag{24}
$$

The pure-action root values are

$$
Q=(1,\ 1/4,\ 1,\ 0),
\qquad
C=(1,\ 3,\ 3,\ 1)=v.
\tag{25}
$$

Player \(0\) is indifferent between Quit and Continue; every other player uses Continue, which is optimal. Thus every row satisfies all four perfection inequalities with error zero.

Here the profile is also an exact **terminal** Nash equilibrium, which requires a separate check.

Player \(0\)’s opponents never quit. Every finite stopping date gives her one, while Never gives zero.

For \(i=1,2\), write \(h=1/4\) and \(b=3/4\). Quitting at date \(t\) gives

$$
3(1-b^t)+h b^t r_i(\{0,i\})\le3,
\tag{26}
$$

because

$$
r_1(\{0,1\})=1,\qquad r_2(\{0,2\})=4.
$$

Never gives each of them three.

Player \(3\)’s Never payoff is one. Quitting at date \(t\) gives only the probability that player \(0\) has already quit:

$$
1-b^t\le1.
\tag{27}
$$

Again, mixtures of these pure stopping laws cannot improve the bound.

Thus \(\bar q\) is an actual stationary exact equilibrium and an exact absorbing row-perfect source.

This also separates the two capacity questions sharply. The full reward-box correspondence has a nonzero exact self-loop at \(v\), so its finite exact hazard capacity is unbounded. But the capacity of exact blocks anchored at the zero terminal boundary is only \(\beta\).

## 6. Approximate finite sources escape the obstruction

The distinction between exact and approximate finite-menu sources is essential here.

For each \(N\), prescribe \(q_0=1/4\) for the first \(N\) rows, make the other three players always Continue, and prescribe all Continue after \(N\). Denote this finite-support profile by \(\widetilde\sigma^N\).

Its payoff is

$$
U(\widetilde\sigma^N)
=
(1-b^N)(1,3,3,1),
\qquad b=\frac34.
\tag{28}
$$

Direct best-response calculation gives

$$
d(\widetilde\sigma^N)
=
\left(
b^N,\ 0,\ \frac14 b^{N-1},\ 0
\right).
\tag{29}
$$

Therefore

$$
\boxed{
E(\widetilde\sigma^N)=b^N\longrightarrow0.
}
\tag{30}
$$

Their joint Never probabilities also equal \(b^N\), and their pointwise limit is the absorbing source (23).

In this one game, therefore,

$$
\inf_{N\ge1}\ \inf_{\sigma\in\mathcal N_N}E(\sigma)
=
\beta>0,
\tag{31}
$$

while finite-support profiles with arbitrarily small menu error **and** unrestricted error exist explicitly.

There is no horizon-uniform justification for replacing these approximate finite equilibria by exact finite equilibria while retaining small exploitability or the desired absorption clock.

## 7. What this changes at the construction boundary

The repository’s `SinglePivotFiniteMenuSurePivotFixture.exactNash_jointNever_zero_fullDebt_half` supplies a one-date bad-menu example. The construction here is stronger in a different direction: **every exact menu equilibrium at every deadline is forced to be bad**, and zero-boundary exact Nash–Bellman construction is forced to have bounded total hazard and a nonabsorbing diagonal limit.

The generic backward propagation of a unique all-Continue root is already present as `quittingAnchoredPath_backward_rigidity_of_unique_allContinue` in `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`. The explicit ingredient above is a canonical, punishment-normal four-player table whose **unique zero-boundary predecessor enters such a basin**, together with the argument covering every normal-form menu equilibrium.

The mathematical proof above has not been formalized or compiled in Lean. I checked the algebraic identities exactly and checked the explicit families against every displayed pure deviation, the fresh late deviation, and Never:

[Reproducible algebra and deviation checker](verify_exact_menu_obstruction.py)

**The general Fin4 source producer is still missing.** This result excludes a concrete attempted replacement for it: exact zero-boundary finite Nash selection does not supply either the absorption or the unrestricted-cap control. It does not exclude altering the boundary, completing the profiles, or constructing genuinely approximate finite sources—and it does not eliminate the positive-gap hard residual, since this example itself has an equilibrium.
