The key distinction is between simplifying the deviation tests and simplifying the selection problem. The singleton normalization simplifies the tests, but it preserves—up to a factor of two—the unrestricted exploitability of arbitrary four-player games whose own-singleton rewards are all \(1\).

I can prove that equivalence for the **same profile**, including unbounded stopping laws. I have not established the requested selector or produced a global-gap counterexample.

## 1. An exact terminal-payoff translation identity

Write \(d_i^g(p)=B_i^g(p)-U_i^g(p)\) for unrestricted regret in a reward table \(g\), and put

$$
c(p)=\prod_{j=0}^3p_j(\mathrm{Never}).
$$

Suppose, for one player \(i\), that

$$
g_i(\{i\})=0.
$$

For \(a\ge0\), define another table by adding \(a\) to **every terminal reward of that player**:

$$
g_i^{+a}(S)=g_i(S)+a
\qquad(S\ne\varnothing),
$$

while keeping the Never payoff equal to zero. Then, for every behavioral product profile,

$$
\boxed{\quad d_i^{g^{+a}}(p)=d_i^g(p)+a\,c(p).\quad} \tag{1}
$$

This is not ordinary affine invariance: the Never payoff has not been translated.

### Proof

Fix the opponents’ laws. Let \(f_i^g(t)\) be the payoff from quitting deterministically at date \(t\), and let \(W_i^g\) be the payoff from Never.

Since the own-singleton payoff is zero, bounded convergence gives

$$
\lim_{t\to\infty}f_i^g(t)=W_i^g.
$$

Consequently Never does not increase the supremum over finite deterministic dates, and linearity in the replacement law gives

$$
B_i^g(p)=\sup_{t<\infty}f_i^g(t). \tag{2}
$$

Every finite deterministic quitting date ensures termination. Hence

$$
f_i^{g^{+a}}(t)=f_i^g(t)+a.
$$

In the translated game,

$$
\lim_{t\to\infty}f_i^{g^{+a}}(t)
=
W_i^{g^{+a}}+a\prod_{j\ne i}p_j(\mathrm{Never})
\ge W_i^{g^{+a}}.
$$

Thus its unrestricted cap is also the supremum over finite dates, so

$$
B_i^{g^{+a}}(p)=B_i^g(p)+a. \tag{3}
$$

The prescribed profile terminates with probability \(1-c(p)\). Therefore

$$
U_i^{g^{+a}}(p)=U_i^g(p)+a(1-c(p)).
$$

Subtracting this from (3) proves (1). \(\square\)

The identity concerns complete behavioral deviations, not merely deviations inside a finite menu.

## 2. The positive singleton controls joint nontermination

For the table in the question,

$$
\boxed{\quad c(p)\le d_0^r(p).\quad} \tag{4}
$$

To prove this, leave the finite part of player \(0\)’s law unchanged and move only its Never mass to a deterministic date \(T\). The resulting gain is

$$
p_0(\mathrm{Never})\bigl(f_0^r(T)-W_0^r(p)\bigr).
$$

As \(T\to\infty\),

$$
f_0^r(T)-W_0^r(p)\longrightarrow D_0(p),
$$

because \(r_0(\{0\})=1\). The gains therefore converge to

$$
p_0(\mathrm{Never})D_0(p)=c(p).
$$

Taking the unrestricted supremum proves (4).

Importantly, this bounds **joint nontermination**, not \(D_0(p)\). It does not imply that the late defect is small for a finite-menu Nash profile.

## 3. Same-profile equivalence with the all-ones diagonal

Starting from the user’s table \(r\), define

$$
R_0(S)=r_0(S),\qquad
R_i(S)=r_i(S)+1\quad(i=1,2,3),
$$

for every nonempty coalition \(S\). Both games retain Never payoff zero. Now

$$
R_i(\{i\})=1\qquad\text{for every }i.
$$

By (1),

$$
d_0^R(p)=d_0^r(p),\qquad
d_i^R(p)=d_i^r(p)+c(p)\quad(i=1,2,3). \tag{5}
$$

Writing

$$
E_g(p)=\max_i d_i^g(p),
$$

equations (4)–(5) yield the pointwise bounds

$$
\boxed{\qquad E_r(p)\le E_R(p)\le 2E_r(p)
\qquad\text{for every behavioral product law }p.\qquad} \tag{6}
$$

Conversely, every table \(R\) with all own-singleton rewards equal to \(1\) arises this way: subtract \(1\) from every terminal reward of players \(1,2,3\), leaving player \(0\)’s rewards unchanged.

Thus this is a two-way reduction of the classes in question. In particular:

* A supplied finite law satisfying the user’s two inequalities with error \(\varepsilon\) is, without any modification, an unrestricted \(2\varepsilon\)-equilibrium of the associated all-ones-diagonal game.
* An unrestricted \(\varepsilon\)-equilibrium of that all-ones-diagonal game is, without any modification, an unrestricted \(\varepsilon\)-equilibrium of the user’s game.

The reduction also preserves global counterexamples quantitatively. If an all-ones-diagonal table \(R\) satisfies

$$
E_R(p)\ge\gamma\quad\text{for every behavioral }p,
$$

then its associated table \(r\) satisfies

$$
E_r(p)\ge\gamma/2\quad\text{for every behavioral }p.
$$

In the other direction, \(E_r(p)\ge\gamma\) implies \(E_R(p)\ge\gamma\).

Positive coordinate rescaling converts any table with strictly positive own-singleton rewards into an all-ones-diagonal table. Hence the reduction covers that entire class, not merely a particular payoff family.

## 4. Finite support does not weaken this equivalence

For completeness, the passage from arbitrary stopping laws to finite ones preserves unrestricted regret quantitatively.

Given a product law \(p\), obtain \(p^{[N]}\) by moving each player’s mass on finite dates \(t\ge N\) to Never. Define

$$
\alpha_N=\sum_{j=0}^3p_j(\{N,N+1,\ldots\}),
$$

where these sets contain only finite dates. Then \(\alpha_N\to0\).

Let \(H\) bound the absolute terminal rewards. Coupling the original and truncated stopping times gives

$$
|U_i(p^{[N]})-U_i(p)|\le2H\alpha_N.
$$

For every fixed unilateral replacement law, the same coupling of the opponents gives a payoff difference at most \(2H\alpha_N\), uniformly over the replacement law. Taking suprema,

$$
|B_i(p^{[N]})-B_i(p)|\le2H\alpha_N.
$$

Therefore

$$
\boxed{\quad
|E(p^{[N]})-E(p)|\le4H\alpha_N.
\quad} \tag{7}
$$

Consequently, the following two assertions are equivalent:

$$
\begin{array}{l}
\text{Every table in the question has the requested finite selectors;}\\[2mm]
\text{Every four-player all-ones-diagonal table has behavioral}\\
\text{profiles with arbitrarily small unrestricted exploitability.}
\end{array}
$$

For example, to obtain the user’s error \(\varepsilon\) from the second assertion, choose a behavioral profile with all-ones-game exploitability below \(\varepsilon/2\), apply (6), and then choose \(N\) so that the truncation error in (7) is below \(\varepsilon/2\). The resulting **single** finite product law satisfies both requested inequalities.

## What remains unresolved here

The reduction does not select an approximately unexploitable profile. In particular, using (4) to justify a small nontermination probability before proving small unrestricted regret would be circular.

The external existence results I checked supply general sunspot equilibria, or ordinary equilibria under additional structural hypotheses; they do not supply this independent finite-law selector. The APS work likewise characterizes and constructs particular equilibrium classes rather than establishing the required universal selection. 

So the established result is the exact same-profile identity (5) and the two-sided bound (6). The missing assertion remains

$$
\inf_p\max\{E_N(p),L_0(p)\}=0,
$$

with the infimum taken over all finite menus and their product laws. I have not proved that assertion or exhibited a table refuting it.
