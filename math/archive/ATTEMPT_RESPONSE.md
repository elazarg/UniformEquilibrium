A proof must produce profiles with arbitrarily small regret against **all behavioral deviations**; a refutation must give one reward table with a positive regret lower bound for **every** profile. **I have not established either conclusion.** I did obtain a sharper, exact result for the finite-deadline approach in your notes, including its sharpness and why it does not resolve the conjecture.

## A sharp bound for finite-deadline Nash equilibria

Assume \(|r_i(S)|\le M\), with zero payoff on Never. The \(K\)-deadline timing game permits each player to choose a stopping time in

$$
\{0,\ldots,K-1,\infty\}.
$$

Evaluate its equilibria against unrestricted deviations in the original quitting game.

For \(0<x\le1\), define

$$
g_K(x)=
\left[
\frac1x+\frac12\sum_{m=0}^{K-1}
\left(\frac{1+x}{2}\right)^m
\right]^{-1},
\qquad g_K(0)=0,
$$

and set \(C_K=\max_{x\in[0,1]}g_K(x)\).

**Theorem.** Every exact Nash equilibrium of every \(K\)-deadline timing game has unrestricted terminal regret at most \(MC_K\). This bound is sharp for four-player games, even when the selector may choose the best deadline equilibrium for each table. Moreover,

$$
\boxed{
C_1=\frac23,\qquad C_2=\frac12,\qquad C_3=\frac25,\qquad
C_K\longrightarrow\frac14.
}
$$

Thus the three-date bound improves the \(20-8\sqrt6\) bound in the [attached finite-deadline note](sandbox:/mnt/data/ue_notes/notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md) to the exact value \(2/5\).

### Proof of the upper bound

Fix a player with positive unrestricted debt \(d=B_i-U_i\). Let \(s=r_i(\{i\})\), let \(a\) be the probability that every opponent chooses Never, and let \(h_t\) be the probability that the opponents’ earliest quitting date is \(t<K\). Then

$$
a+\sum_{t<K}h_t=1.
$$

All finite deviations at dates \(t\ge K\) have the same payoff, say \(L\). Deadline Nash optimality controls every other pure deviation, including Never. Consequently

$$
d=L-U_i>0,\qquad d\le as.
$$

In particular \(s>0\). Put

$$
x=s/M,\qquad \delta=d/M,\qquad \rho=(1+x)/2.
$$

Comparing late Quit with Quit at \(t<K\) gives

$$
\delta\le 2h_t+(1-x)\sum_{u>t}h_u. \tag{1}
$$

The three relevant events are: opponents quit at \(t\), where leaving rather than joining changes the reward by at most \(2M\); they quit later, where the difference is at most \(M-s\); or everyone else chooses Never, where the two deviations both receive \(s\).

Set \(H_t=\sum_{u=t}^{K-1}h_u\). Rather than summing (1) without weights, retain its backward recurrence:

$$
H_t\ge \frac{\delta}{2}+\rho H_{t+1},\qquad H_K=0.
$$

Therefore

$$
1=a+H_0
\ge
\frac{\delta}{x}
+\frac{\delta}{2}\sum_{m=0}^{K-1}\rho^m,
$$

which is precisely \(\delta\le g_K(x)\).

For \(K\le3\), differentiation shows that \(g_K\) is increasing, giving
\(C_K=g_K(1)=2/(K+2)\). For \(0<x<1\),

$$
g_K(x)=
\frac{x(1-x)}
{1-x\left(\frac{1+x}{2}\right)^K}.
$$

The continuous functions \(g_K\) decrease uniformly on \([0,1]\) to \(x(1-x)\), so \(C_K\to1/4\).

## Sharpness—and why it is not a counterexample

Here is a four-player family attaining the bound. Players \(3,4\) are dummies. Fix \(0<x\le1\). For every nonempty coalition \(S\), write \(A=S\cap\{1,2\}\) and define

| \(A\)      | \(\varnothing\) | \(\{1\}\) | \(\{2\}\) | \(\{1,2\}\) |
| ---------- | --------------: | --------: | --------: | ----------: |
| \(r_1(S)\) |           \(0\) |     \(x\) |     \(1\) |      \(-1\) |
| \(r_2(S)\) |           \(0\) |    \(-1\) |    \(-1\) |       \(0\) |

For each dummy \(d\), let \(r_d(S)=-1\) when \(d\in S\), and zero otherwise. This specifies all fifteen terminal rows.

Write \(\delta=g_K(x)\) and \(\rho=(1+x)/2\). The deadline equilibrium has independent stopping laws

$$
\Pr(T_1=t)=\frac1{K+1}
\quad(t=0,\ldots,K-1,\infty),
$$

$$
\Pr(T_2=t)=\frac{\delta}{2}\rho^{K-1-t}
\quad(t<K),\qquad
\Pr(T_2=\infty)=\frac{\delta}{x},
$$

with both dummies playing Never.

Player \(2\) receives zero when its time matches player \(1\)’s—including when both choose Never—and \(-1\) otherwise. Every permitted action therefore gives \(-K/(K+1)\).

For player \(1\), the geometric probabilities make every inequality (1) an equality. Thus every permitted finite date and Never give the same payoff, while every omitted finite date gives exactly \(\delta\) more. Hence

$$
E_r(p^K)=g_K(x).
$$

These deadline equilibria are unique. The backward-induction argument, including exclusion of sure roots with arbitrary off-path dummy behavior, is in the linked proof. Its active continuation recursion is

$$
u_{n+1}=\frac{x+u_n}{2+x-u_n},\qquad
v_{n+1}=-\frac1{2+v_n},\qquad u_0=v_0=0,
$$

with a unique interior Nash root at each reached date. Choosing a maximizer of \(g_K\) proves sharpness even against favorable equilibrium selection.

In particular, fixing \(x=1/2\) gives one rational table whose unique deadline equilibria satisfy

$$
E_r(p^K)=
\frac{1/4}{1-\frac12(3/4)^K}
>\frac14
\qquad\text{for every }K.
$$

**Nevertheless, this same game has a uniform-equilibrium payoff.** Prescribe player \(2\) to quit at date zero, player \(1\) to choose a uniformly random stopping time in \(\{1,\ldots,L\}\), and the dummies to play Never. The prescribed payoff is

$$
v=(1,-1,0,0).
$$

Player \(1\) and the dummies already receive their maximum possible rewards. A deviation by player \(2\) receives \(-1\), except when it matches player \(1\)’s stopping time and receives zero. Therefore its complete behavioral cap is \(-1+1/L\), and

$$
\boxed{E_r(\sigma^L)=1/L.}
$$

This covers randomized and history-dependent deviations because their payoffs are averages of pure-time payoffs.

Under a deviation by player \(2\), absorption occurs by date \(L\). Consequently the finite-horizon error is bounded by \(1/L+(L+1)/n\), allowing for the convention about when absorbing rewards begin. Thus \(v\) is indeed one fixed uniform-equilibrium payoff.

## What remains unproved

The strengthened calculation gives a sharp guarantee tending to \(M/4\), **not zero**. Its attaining games demonstrate why positive regret throughout an exact-deadline Nash family cannot establish a positive unrestricted gap: off-path punishment profiles escape that family.

The outside source check did not supply the missing construction either: the April 2026 APS paper characterizes a restricted class of equilibrium payoffs and explicitly allows that class to be empty. ([link.springer.com][1])

The [complete derivation](sandbox:/mnt/data/fin4_attempt/SHARP_FINITE_DEADLINE_CEILING.md) includes the uniqueness proof; the [exact-arithmetic verification script](sandbox:/mnt/data/fin4_attempt/check_deadline_ceiling.py) checks the displayed equilibrium and punishment formulas. No Lean formalization was performed.

**The four-player conjecture is not resolved by this attempt: no universal zero-regret construction and no positive-gap reward table have been obtained.**

[1]: https://link.springer.com/article/10.1007/s00182-026-00982-6 "The APS approach for undiscounted quitting games | International Journal of Game Theory | Springer Nature Link"
