Two parts of the formulation can be simplified: **the box can be reduced to \(B=M\)**, and **absorption-weighted ordinary regret can replace the support condition, even with absorption-weighted Bellman errors**. Both reductions have bounds independent of packet length.

I have not established the remaining existence step—unbounded charge under your contrary-case assumptions. Thus the results below do not constitute the requested producer.

## 1. A uniform-box producer automatically gives \(B=M\)

Suppose the requested packets exist in some fixed box \([-B,B]^4\), with \(B\ge M\). Then they exist in \([-M,M]^4\), with the same reward table and punishment vector.

For every \(v\in\mathbb R^4\),

$$
\operatorname{dist}_\infty\!\left(F(q,v),[-M,M]^4\right)
\le
c(q)\operatorname{dist}_\infty\!\left(v,[-M,M]^4\right).
$$

Indeed, each coordinate of the terminal contribution lies between \(-Ma(q)\) and \(Ma(q)\). Consequently, along an exact forward packet,

$$
\operatorname{dist}_\infty\!\left(v_t,[-M,M]^4\right)
\le
(B-M)\prod_{s<t}c(q_s)
\le
(B-M)\exp\!\left(-\sum_{s<t}a(q_s)\right).
\tag{1}
$$

Fix the desired tolerance \(\delta>0\) and charge \(Q\). The case \(B=M\) needs no change. Otherwise set

$$
\eta=\frac{\delta}{2},
\qquad
L=\max\left\{0,\log\frac{B-M}{\eta}\right\}.
$$

Take a packet in the original box with tolerance \(\delta/2\) and charge at least \(Q+L+1\). Let \(j\) be the first index at which the accumulated charge is at least \(L\), taking \(j=0\) when \(L=0\). Since each row has charge at most one,

$$
\sum_{t<j}a(q_t)\le L+1,
\qquad
\sum_{t=j}^{H-1}a(q_t)\ge Q.
$$

Project \(v_j\) coordinatewise onto \([-M,M]^4\), obtaining \(\widehat v_j\), and keep the remaining roots. Define

$$
\widehat v_{t+1}=F(q_t,\widehat v_t),\qquad t\ge j.
$$

Equation (1) gives \(\|\widehat v_j-v_j\|_\infty\le\eta\). Since the two evaluations use the same roots,

$$
\|\widehat v_t-v_t\|_\infty
=
\left(\prod_{s=j}^{t-1}c(q_s)\right)
\|\widehat v_j-v_j\|_\infty
\le\eta.
\tag{2}
$$

All reconstructed values belong to \([-M,M]^4\).

Changing the continuation by at most \(\eta\) changes either pure-action regret by at most \(\eta\): \(Q_i\) is unchanged, and \(C_i\) changes by at most \(\eta\). Thus the retained roots are support-\(\delta\) Nash, and

$$
\widehat v_t(i)\ge P_i-\frac{\delta}{2}-\eta=P_i-\delta.
$$

This proves the reduction. In particular, **a successful producer need not find a game-dependent larger box; the reward box suffices.**

## 2. A length-independent Bellman and support repair

Here is a different sufficient input, with an explicit conversion to your packets.

Fix \(B\ge M\) and \(0<\rho\le 1/8\). Suppose finite data

$$
y_0,\ldots,y_H\in[-B,B]^4,\qquad q_0,\ldots,q_{H-1}
$$

satisfy, writing \(a_t=a(q_t)\),

$$
\begin{aligned}
\|y_{t+1}-F(q_t,y_t)\|_\infty&\le B\rho^2a_t,\\
A_i(q_t,y_t)-F_i(q_t,y_t)&\le B\rho^2a_t,\\
y_t(i)&\ge P_i-B\rho^2.
\end{aligned}
\tag{3}
$$

Then there are reconstructed roots \(\widehat q_t\) and values \(\widehat v_t\in[-B,B]^4\) such that

$$
\begin{aligned}
\widehat v_{t+1}&=F(\widehat q_t,\widehat v_t),\\
\widehat q_t&\text{ is support-}32B\rho\text{ Nash against }\widehat v_t,\\
\widehat v_t(i)&\ge P_i-32B\rho,\\
\sum_ta(\widehat q_t)&\ge(1-4\rho)\sum_ta_t
\ge \frac12\sum_ta_t.
\end{aligned}
\tag{4}
$$

There is no dependence on \(H\) in these estimates.

### Remove actions with large support defects

At row \(t\), remove any action whose payoff against \((q_t,y_t)\) is more than \(B\rho\) below the best pure-action payoff, moving its probability to the other action.

Ordinary regret is the probability-weighted sum of the pure-action regrets. Therefore (3) implies that the probability of a removed action is at most

$$
\frac{B\rho^2a_t}{B\rho}=\rho a_t.
$$

There is at most one such action per player. Hence

$$
\|\widehat q_t-q_t\|_1\le4\rho a_t.
\tag{5}
$$

The absorption probability is \(1\)-Lipschitz in this norm, so

$$
\widehat a_t:=a(\widehat q_t)\ge(1-4\rho)a_t.
\tag{6}
$$

### Recompute the values, rather than carrying inconsistent annotations

Set

$$
\widehat v_0=y_0,\qquad
\widehat v_{t+1}=F(\widehat q_t,\widehat v_t).
$$

This gives exact Bellman matching and keeps every value in \([-B,B]^4\).

Let \(e_t=\|\widehat v_t-y_t\|_\infty\). Coupling the product roots gives

$$
\|F(\widehat q_t,y_t)-F(q_t,y_t)\|_\infty
\le2B\|\widehat q_t-q_t\|_1
\le8B\rho a_t.
$$

Combining this with (3),

$$
e_{t+1}
\le
(1-\widehat a_t)e_t+B(\rho^2+8\rho)a_t
\le
(1-\widehat a_t)e_t+
\frac{B(\rho^2+8\rho)}{1-4\rho}\widehat a_t.
$$

Starting from \(e_0=0\), induction yields

$$
e_t\le
\frac{B(\rho^2+8\rho)}{1-4\rho}
\le17B\rho
\qquad\text{for every }t.
\tag{7}
$$

This is the decisive estimate: the local errors are proportional to absorption, and the Bellman contraction absorbs them. They do not accumulate as \(H\rho\).

### Check every retained action

Every action used by \(\widehat q_t\) had regret at most \(B\rho\) before the changes.

For player \(i\), changing the three opponents’ probabilities changes the difference \(Q_i-C_i\) by at most

$$
4B\sum_{j\ne i}|\widehat q_t(j)-q_t(j)|
\le12B\rho a_t.
$$

Changing the continuation contributes at most \(e_t\). Thus every retained action has regret at most

$$
B\rho+12B\rho a_t+e_t
\le30B\rho
\le32B\rho.
$$

Also, by (7),

$$
\widehat v_t(i)
\ge P_i-B\rho^2-17B\rho
\ge P_i-32B\rho.
$$

Together with (6), this proves (4).

## 3. The weighted-error formulation is equivalent at the producer level

The sufficient input above is not merely an unrelated stronger condition. Your original packet assertion is equivalent to the following assertion:

> There is one fixed finite box such that, for every \(\varepsilon>0\) and every charge target, there are finite data satisfying
>
> $$
> \|y_{t+1}-F(q_t,y_t)\|_\infty\le\varepsilon a(q_t),
> $$
>
> $$
> A_i(q_t,y_t)-F_i(q_t,y_t)\le\varepsilon a(q_t),
> \qquad y_t(i)\ge P_i-\varepsilon,
> $$
>
> with at least the requested total charge.

One direction follows from the repair above: choose \(\rho\) with \(32B\rho\le\delta\), and request twice the desired charge.

For the other direction, start with an original support-\(\delta\) packet and translate every continuation by the same vector:

$$
y_t=v_t+2\delta\mathbf1.
$$

Then

$$
y_{t+1}-F(q_t,y_t)=2\delta\,a(q_t)\mathbf1.
\tag{8}
$$

The ordinary root regret against \(y_t\) is at most \(3\delta a(q_t)\). To see this, write

$$
\alpha_i=p_{q_t,-i}(\varnothing).
$$

The translation increases Continue’s payoff by \(2\delta\alpha_i\) and leaves Quit’s payoff unchanged.

When Continue is best after translation, a used Quit action has regret at most \(3\delta\), so its contribution to ordinary regret is at most

$$
3\delta q_t(i)\le3\delta a(q_t).
$$

When Quit is best and Continue is used, the original support condition implies

$$
0<Q_i-C_i(y_t)\le\delta-2\delta\alpha_i.
$$

Therefore \(\alpha_i<1/2\), whence \(a(q_t)\ge1/2\), and ordinary regret is at most

$$
\delta\le2\delta a(q_t).
$$

Taking \(\delta\le\min\{1,\varepsilon/3\}\) gives the weighted-error conditions in the fixed enlarged box \([-B-2,B+2]^4\). The punishment floor only improves under translation.

Thus the producer can equivalently target **ordinary regret and Bellman defects measured per unit of absorption**. Exact Bellman matching and support rationality can then be recovered without a length-dependent loss.

## What is still missing

Neither argument establishes that the weighted-error packet class has unbounded charge. In particular, constructing arbitrarily long sequences is insufficient: their total absorption may remain bounded, or every row may be all-Continue.

The unresolved step is still

$$
D_*>0,\quad P_i\le r_i(\{i\})
\quad\Longrightarrow\quad
\text{unbounded charge at every positive weighted-error tolerance}.
$$

I have not proved that implication or supplied a counterexample with a positive all-behavior exploitability gap.

The sources checked do not fill it: the repository’s finite-menu completion still assumes an early-absorption or exceptional-scalar source, while the 2026 APS characterization explicitly allows its characterized payoff set to be empty.  ([link.springer.com][1])

[1]: https://link.springer.com/article/10.1007/s00182-026-00982-6 "https://link.springer.com/article/10.1007/s00182-026-00982-6"

---

**The cap-tight branch can be consumed explicitly. In the remaining branch, every near-minimizing actual profile reaches a uniformly absorbing row with probability tending to one, after spending only vanishing charge.** The latter is stronger than extracting an atom from an arbitrarily conditioned suffix, but I have not converted that row into the required support-Nash packet. The full producer remains unproved.

Here is the argument, including the source-preserving estimates.

## 1. The minimum-debt cap margin is uniformly strict

Write \(s_i=r_i(\{i\})\), and let

$$
\mathcal S=\overline{\{(U(p),B(p)):p\text{ is an actual product law}\}},
\qquad
\mathcal M=\{(u,b)\in\mathcal S:\ \sum_i(b_i-u_i)=D_*\}.
$$

The set \(\mathcal M\) is nonempty and compact.

For a semantic pair \(z=(u,b)\), prefixing by \(q\) gives

$$
T_qz=\bigl(F(q,u),A(q,b)\bigr).
$$

This preserves \(\mathcal S\). Define the ordinary root regret against the cap by

$$
g_i(q,b)=A_i(q,b)-F_i(q,b).
$$

The exact debt identity is

$$
d_i(T_qz)=c(q)d_i(z)+g_i(q,b).
\tag{1}
$$

First recall the weak minimum margin

$$
b_i\ge s_i+D_*
\qquad(z=(u,b)\in\mathcal M).
\tag{2}
$$

It follows directly by taking an exact Nash root against \(b-t\mathbf1\), with \(0\le t<D_*\). Such a root satisfies

$$
g_i(q,b)\le t\,q_i\alpha_i(q),
\qquad
\alpha_i(q)=\prod_{j\ne i}(1-q_j).
$$

Consequently,

$$
D(T_qz)
\le c(q)D_*+t\sum_iq_i\alpha_i(q)
\le D_*-(D_*-t)a(q).
$$

Minimality forces \(a(q)=0\). All-Continue being Nash against \(b-t\mathbf1\) then gives \(b_i-t\ge s_i\); let \(t\uparrow D_*\). This is also the constant-shift budget developed in `TerminalSemanticCapNashNearMinimum.lean`.

The useful strengthening is

$$
\boxed{\quad
\exists\rho>0\quad
\forall (u,b)\in\mathcal M,\ \forall i,\qquad
b_i\ge s_i+D_*+\rho.
\quad}
\tag{3}
$$

### Why equality would already produce the requested packets

Suppose instead that some \(z^0=(u^0,b^0)\in\mathcal M\) and player \(k\) satisfy

$$
b_k^0=s_k+D_*.
$$

Put

$$
\lambda=\frac{D_*}{2(D_*+2M)}>0,
$$

and let \(q\) be the fixed root where only \(k\) quits, with probability \(\lambda\).

Iterate actual semantic prefixing:

$$
z^{n+1}=T_qz^n.
$$

Assume inductively that \(z^n\in\mathcal M\) and \(b_k^n=s_k+D_*\). For every \(j\ne k\), (2) implies

$$
\begin{aligned}
C_j(q,b^n)-Q_j(q)
&=(1-\lambda)(b_j^n-s_j)
 +\lambda\bigl(r_j(\{k\})-r_j(\{j,k\})\bigr)\\
&\ge (1-\lambda)D_*-2M\lambda\\
&=\frac{D_*}{2}>0.
\end{aligned}
\tag{4}
$$

Thus the outsiders have zero cap-root regret. For \(k\),

$$
g_k(q,b^n)=\lambda(b_k^n-s_k)=\lambda D_*.
$$

Equation (1) gives

$$
D(z^{n+1})=(1-\lambda)D_*+\lambda D_*=D_*.
$$

Also \(b_k^{n+1}=b_k^n\). The induction therefore continues indefinitely.

Now define the **packet continuation values**

$$
v_k^n=s_k,\qquad v_j^n=b_j^n\quad(j\ne k).
$$

These need not be the prescribed coordinates of \(z^n\); that is permitted by the packet question.

At every \(v^n\), player \(k\) is indifferent between Quit and Continue, while (4) makes Continue optimal for every outsider. Moreover,

$$
v^{n+1}=F(q,v^n).
$$

All values belong to \([-M,M]^4\), and

$$
v_k^n=s_k\ge P_k,\qquad v_j^n=b_j^n\ge P_j.
$$

Hence, for any requested \(Q\), taking

$$
H=\left\lceil\frac{Q}{\lambda}\right\rceil
$$

produces a packet with **zero support error**, exact Bellman matching, and

$$
\sum_{n<H}a(q)=H\lambda\ge Q.
$$

This contradicts the stated exact-capacity obstruction. Therefore equality in (2) is impossible. Compactness of \(\mathcal M\) makes the strict inequality uniform, proving (3).

So the cap-tight boundary is not merely classified: it has an explicit fixed-root packet producer.

## 2. A small first row strictly lowers debt when deleted

The remaining case has the strict margin (3). Compactness supplies an \(\varepsilon_0>0\), which we decrease so that

$$
\varepsilon_0\le \frac{\rho}{32},
$$

such that every \(z=(u,b)\in\mathcal S\) satisfying

$$
D(z)\le D_*+\varepsilon_0
$$

also satisfies

$$
b_i\ge s_i+D_*+\frac{\rho}{2}
\qquad\text{for every }i.
\tag{5}
$$

Fix

$$
h=\min\left\{\frac12,\frac{\rho}{8M}\right\},
\qquad
\kappa=\frac{\rho}{8}.
\tag{6}
$$

Consider an actual profile whose first root is \(q\), with conditional continuation profile \(p^+\). Denote its front and continuation semantic pairs by

$$
z=T_qz^+,\qquad z=(u,b),\quad z^+=(u^+,b^+).
$$

Suppose

$$
D(z)\le D_*+\varepsilon_0,\qquad a(q)\le h.
$$

Quitting now differs from quitting alone only when an opponent quits. Therefore

$$
Q_i(q)\le s_i+2M a(q).
$$

Together with (5)–(6), this gives

$$
b_i-Q_i(q)\ge D_*+\frac{\rho}{4}>0.
\tag{7}
$$

Since \(b_i=A_i(q,b^+)\), the maximizing cap branch must be Continue:

$$
b_i=C_i(q,b^+).
\tag{8}
$$

In particular,

$$
g_i(q,b^+)=q_i\bigl(b_i-Q_i(q)\bigr).
$$

Using (1), (7), and \(\sum_iq_i\ge a(q)\),

$$
D(z)\ge (1-a(q))D(z^+)
       +a(q)\left(D_*+\frac{\rho}{4}\right).
\tag{9}
$$

Rearranging,

$$
\begin{aligned}
(1-a(q))\bigl(D(z)-D(z^+)\bigr)
&\ge a(q)\left(D_*+\frac{\rho}{4}-D(z)\right)\\
&\ge \frac{\rho}{8}a(q).
\end{aligned}
$$

Thus

$$
\boxed{\quad D(z^+)\le D(z)-\kappa a(q).\quad}
\tag{10}
$$

This is a statement about **deleting the first prescribed row of an actual profile**. It does not replace that row by a strategically unrelated root. Deletion also keeps the continuation within the same near-minimum region.

## 3. Every near-minimizer has a uniformly reached large row

Let \(p\) be any actual profile with

$$
D(p)\le D_*+\varepsilon,
\qquad 0<\varepsilon\le\varepsilon_0.
$$

Write \(q_t\) for its live-date roots, and let \(p^{[t]}\) be the actual conditional continuation after \(t\) all-Continue outcomes, with the clock reset to zero.

Define \(T\) as the first date with

$$
a(q_T)>h.
$$

I claim that \(T\) exists and that

$$
\boxed{
\begin{aligned}
\sum_{t<T}a(q_t)&\le \frac{8\varepsilon}{\rho},\\
D(p^{[T]})&\le D(p),\\
\Pr_p(\text{reach }T)&\ge 1-\frac{8\varepsilon}{\rho},\\
\left\|(U(p),B(p))-(U(p^{[T]}),B(p^{[T]}))\right\|_\infty
&\le \frac{16M\varepsilon}{\rho}.
\end{aligned}}
\tag{11}
$$

### The charge bound

While \(t<T\), apply (10) successively. Every continuation remains near-minimizing, so

$$
\kappa\sum_{t<T}a(q_t)
\le D(p)-D(p^{[T]})
\le \varepsilon.
$$

This proves the first two statements.

### Why a large row must occur

Suppose every row had absorption at most \(h\). The same argument would give

$$
\sum_{t\ge0}a(q_t)<\infty,
$$

while every conditional continuation remained near-minimizing.

Summability implies that the probability of any future absorption from date \(t\) tends to zero. Hence

$$
U_i(p^{[t]})\longrightarrow0
\qquad\text{for every }i.
\tag{12}
$$

But (5) and \(d_i(p^{[t]})\le D(p^{[t]})\le D_*+\varepsilon_0\) give

$$
U_i(p^{[t]})
\ge s_i+\frac{\rho}{2}-\varepsilon_0.
\tag{13}
$$

At least one \(s_i\) is positive: otherwise all-Never is an exact terminal Nash profile, contrary to \(D_*>0\). For that player, (12) and (13) contradict each other. Thus \(T<\infty\).

### Reach probability and complete semantic matching

The probability of reaching \(T\) satisfies

$$
\prod_{t<T}(1-a(q_t))
\ge1-\sum_{t<T}a(q_t),
$$

giving the third statement of (11).

For prescribed payoffs, deleting one row changes each coordinate by at most \(2M a(q_t)\). For caps, (8) gives the same estimate:

$$
|B_i(p^{[t]})-B_i(p^{[t+1]})|
\le2M(1-\alpha_i(q_t))
\le2M a(q_t).
$$

Summing proves the last statement of (11).

The estimate therefore preserves **both prescribed payoffs and unrestricted best-response caps**. It is not merely terminal-law matching.

## 4. The resulting atom is not hidden in a rare suffix

There are fifteen nonempty coalitions. Since \(a(q_T)>h\), some nonempty \(S\) satisfies

$$
p_{q_T}(S)>\frac{h}{15}.
$$

Because \(\varepsilon\le\rho/32\), the reach probability in (11) is at least \(3/4\). Consequently,

$$
\boxed{\quad
\Pr_p(\text{the first quitting coalition is }S
       \text{ at date }T)>\frac{h}{20}.
\quad}
\tag{14}
$$

Thus every sufficiently near-minimizing actual profile supplies a finite-date terminal atom with one fixed positive lower bound. Before that atom’s row, the profile spends only \(O(\varepsilon)\) charge.

In particular, start with **any** realizing sequence

$$
(U(p_n),B(p_n))\longrightarrow z_*\in\mathcal M.
$$

Apply the construction to obtain cutoffs \(T_n\). Then

$$
(U(p_n^{[T_n]}),B(p_n^{[T_n]}))\longrightarrow z_*,
$$

the cutoffs are reached with probability tending to one, and the shifted first roots have absorption uniformly bounded below by \(h\).

After a subsequence, the first roots converge to \(q_*\), their continuation semantic pairs converge to \(z^+\in\mathcal S\), and

$$
\boxed{\qquad z_*=T_{q_*}z^+,\qquad a(q_*)\ge h>0.\qquad}
\tag{15}
$$

All approximating roots and continuations come from the same actual profiles. A further subsequence fixes the coalition in (14).

## The remaining obstruction

Equation (15) supplies an actual, uniformly reached, positive-absorption incoming row at a minimum-debt point. **It does not make that prescribed row support-Nash against its continuation.**

The exact information available is

$$
D_*
=c(q_*)D(z^+)+\sum_i g_i(q_*,b^+).
\tag{16}
$$

This permits \(D(z^+)>D_*\), positive cap-root regrets, or both. It gives no small support-error bound against \(u^+\). Replacing \(q_*\) by a Nash root changes its absorption and its front semantic point; the estimates above do not justify treating the replacement as the same row.

So this work eliminates cap-tight minima and produces a stronger same-source large-row representation in the strict case. **The conversion of that row into an arbitrarily charged support-Nash packet—or into debt below \(D_*\)—is still missing. No complete positive construction or counterexample has been established here.**
