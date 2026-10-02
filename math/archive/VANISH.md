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

---

**Exact finite-menu Nash selection can fail uniformly even when approximate finite selection succeeds—and the infinite game has an exact equilibrium.** I can now prove this with a complete four-player example.

For this game, every deadline \(N\ge1\) has a **unique** exact finite-menu Nash law, and it always has

$$
L_0=\frac12.
$$

Nevertheless, there are explicit independent laws \(p^{(K)}\) on \(F_{3K}\) satisfying

$$
\boxed{E_{3K}(p^{(K)})=L_0(p^{(K)})=8^{-K}.}
$$

This is not a counterexample to your question, nor a solution for arbitrary tables. It establishes that the approximate-selector allowance is essential, rather than merely a convenience.

## 1. The reward table

Use cyclic predecessor and successor on \(\{1,2,3\}\):

$$
1^-=3,\quad2^-=1,\quad3^-=2,
\qquad
1^+=2,\quad2^+=3,\quad3^+=1.
$$

For every nonempty coalition \(S\), define

$$
r_0(S)=
\begin{cases}
1,&0\in S,\\
2,&0\notin S,
\end{cases}
$$

and, for \(i\in\{1,2,3\}\),

$$
r_i(S)=
\begin{cases}
0,&i\in S,\\
-1,&i\notin S,\ 0\in S,\\
2\mathbf1_{\{i^-\in S\}}-\mathbf1_{\{i^+\in S\}},
   &i\notin S,\ 0\notin S.
\end{cases}
\tag{1}
$$

In particular, the singleton rewards are

$$
\begin{aligned}
r(\{0\})&=(1,-1,-1,-1),\\
r(\{1\})&=(2,0,2,-1),\\
r(\{2\})&=(2,-1,0,2),\\
r(\{3\})&=(2,2,-1,0).
\end{aligned}
$$

Formula (1) specifies all the remaining coalitions. The bound is \(M=2\).

## 2. Explicit finite laws controlling both errors

Fix \(K\ge1\), and set \(N=3K\). Player \(0\) chooses Never. For \(i=1,2,3\), prescribe

$$
p_i(3k+i-1)=2^{-(k+1)}
\quad(0\le k<K),
\qquad
p_i(\mathrm{Never})=2^{-K}.
\tag{2}
$$

Thus players \(1,2,3\) take turns. On its designated date, the active player quits with conditional probability \(1/2\). After \(K\) cycles, everyone continues forever. The stopping laws are independent; no public randomization is used.

Write

$$
J=8^{-K}.
$$

The complete payoff and cap calculations are

$$
\boxed{
\begin{aligned}
U(p)&=(2-2J,\ 0,\ 1-J,\ 0),\\
B^N(p)&=(2-2J,\ 0,\ 1,\ 0),\\
B(p)&=(2-J,\ 0,\ 1,\ 0).
\end{aligned}}
\tag{3}
$$

Here \(B\) includes every behavioral replacement, including unbounded stopping times.

Consequently,

$$
E_N(p)=J.
$$

Because player \(0\) is prescribed Never,

$$
W_0(p)=U_0(p),\qquad
D_0(p)=(2^{-K})^3=J,
$$

and therefore

$$
L_0(p)=J.
$$

For this table, the requested construction is consequently

$$
K=\max\!\left\{1,\left\lceil\log_8(1/\varepsilon)\right\rceil\right\},
\qquad N=3K,
$$

together with (2).

### Verification against unrestricted deviations

One full three-date cycle survives with probability \(1/8\). Its unconditional contribution to the payoff vector of players \(1,2,3\) is

$$
(0,7/8,0).
$$

Summing the cycles gives their prescribed payoffs in (3). Player \(0\) receives \(2\) whenever absorption occurs, giving \(2(1-J)\).

Player \(0\)’s payoff from quitting at a deterministic date \(t\) is

$$
2-\Pr(\text{no opponent quits strictly before }t).
\tag{4}
$$

This is nondecreasing in \(t\). At the last menu date, the survival probability in (4) is \(2J\), so the payoff equals its Never payoff \(2-2J\). At any date at or after \(N\), that probability is \(J\), giving the unrestricted cap \(2-J\).

For each other player, **every coalition containing that player pays it zero**. Its payoff from quitting at date \(t\) is therefore just its expected reward from opponents’ absorption strictly before \(t\).

For players \(1\) and \(3\), this cumulative expected reward starts at zero, becomes negative after the first relevant opponent’s date, and returns to zero after the second relevant opponent’s date in each cycle. Its supremum, including Never, is zero.

For player \(2\), at the beginning of opponent cycle \(k\), the cumulative expected reward is

$$
1-4^{-k}.
$$

After player \(1\)’s date it rises to \(1\); after player \(3\)’s date it falls to

$$
1-4^{-(k+1)}.
$$

Its cap is exactly \(1\), already attained by quitting at date \(1\).

These computations cover every deterministic date and Never. An arbitrary replacement law averages these pure-time payoffs, so it cannot exceed their supremum. This proves the unrestricted bounds in (3).

## 3. Every exact finite-menu Nash law has defect \(1/2\)

The quantifier here is important: this is not merely a claim about equilibria selected by backward induction.

### A three-player row lemma

First remove player \(0\), and consider a single row with zero continuation payoff. If the other players’ quit probabilities are \(x_1,x_2,x_3\), player \(i\)’s action payoffs are

$$
Q_i=0,\qquad C_i=2x_{i^-}-x_{i^+}.
$$

**The only Nash equilibrium of this row game is all-Continue.**

Indeed, suppose \(x_m=\max_i x_i>0\). Then

$$
C_{m^+}=2x_m-x_{m^-}\ge x_m>0,
$$

so \(x_{m^+}=0\). Since player \(m\) uses Quit,

$$
C_m=2x_{m^-}\le0,
$$

forcing \(x_{m^-}=0\). But then

$$
C_{m^-}=-x_m<0,
$$

which forces \(x_{m^-}=1\), a contradiction.

### Why off-path punishments cannot escape the classification

Consider any exact finite-menu Nash law. It cannot have a positively reached row at which absorption becomes certain.

Suppose a zero-singleton player quits with conditional probability one at such a row. Player \(0\) then receives \(2\) by continuing and \(1\) by quitting, so it must continue.

Each zero-singleton player has two legitimate conditional deviations: quit now, or continue now and quit at the next date. At the last menu date, replace the latter by Never. In either case, the second deviation gives zero on the current all-Continue branch: quitting next date pays zero in every coalition containing the deviator, while the final Never branch also pays zero.

Since prescribed absorption at the current row is certain, these deviation inequalities make the current zero-player row a Nash equilibrium of the three-player game just analyzed. That is impossible with a sure quitter.

Alternatively, if player \(0\) quits with certainty, every zero-singleton player strictly prefers Quit, paying \(0\), to Continue, paying \(-1\). They would all quit, against which player \(0\) strictly prefers Continue. Again there is a contradiction.

Thus every live date remains positively reached, and all four Never masses are positive. Every conditional suffix must therefore itself be Nash: a profitable suffix replacement would yield a profitable complete-law replacement, multiplied by the positive probability of reaching that suffix.

This permits backward classification of **all** finite-menu Nash laws.

### The last row

Let \(q_i\) denote quit probabilities and put

$$
A=1-\prod_{i=1}^3(1-q_i).
$$

With zero continuation, player \(0\)’s action payoffs are

$$
Q_0=1,\qquad C_0=2A.
$$

For the other players,

$$
Q_i=0,\qquad
C_i=-q_0+(1-q_0)(2q_{i^-}-q_{i^+}).
\tag{5}
$$

The preceding argument excludes any \(q_i=1\). Also \(q_0=0\) would force all other players to continue by the row lemma, against which player \(0\) strictly prefers Quit. Thus \(0<q_0<1\), implying

$$
A=\frac12.
$$

No zero-player probability can vanish: \(q_i=0\) would make \(C_{i^+}<0\), forcing \(q_{i^+}=1\).

All players are consequently interior. The indifference equations in (5) give

$$
2q_{i^-}-q_{i^+}=\frac{q_0}{1-q_0}.
$$

Their unique solution has \(q_1=q_2=q_3\). Defining

$$
a=1-2^{-1/3},\qquad b=\frac{a}{1+a},
$$

the unique last-row equilibrium is

$$
q^*=(b,a,a,a),
$$

with payoff

$$
v=(1,0,0,0).
$$

### Every earlier row

With continuation \(v\), the zero-players’ action payoffs remain (5), while player \(0\)’s Continue payoff becomes

$$
2A+(1-A)=1+A.
$$

If \(A>0\), player \(0\) must continue; the three-player row lemma then forces \(A=0\), a contradiction. Hence the other three players all continue. Any positive quit probability by player \(0\) would then make them strictly prefer Quit.

Therefore the unique equilibrium row with continuation \(v\) is all-Continue, retaining payoff \(v\).

It follows that the unique exact finite-menu Nash law waits until date \(N-1\), plays \(q^*\), and then chooses Never. For this law,

$$
D_0=(1-a)^3=\frac12,\qquad
W_0=2(1-D_0)=1,\qquad U_0=1.
$$

Thus, for every \(N\ge1\),

$$
\boxed{E_N=0,\qquad L_0=\frac12.}
\tag{6}
$$

## 4. What this changes about the selection problem

The infinite version of (2), with \(k\ge0\) and no Never mass for players \(1,2,3\), satisfies

$$
U=B=(2,0,1,0).
$$

It is an **exact behavioral equilibrium**. Conversely, (6) proves that this game has **no exact equilibrium with finite stopping-law support**.

The successful approximate laws are also not small perturbations of the finite-menu equilibrium. At \(N=3K\), player \(1\)’s approximate finite support is

$$
\{0,3,\ldots,3K-3\},
$$

whereas its exact-menu equilibrium finite support is \(\{3K-1\}\). Their only common support point is Never. Their total-variation distance is therefore

$$
1-2^{-K}\longrightarrow1,
$$

even though the approximate law’s menu regret is \(8^{-K}\).

So an argument that first constructs approximate menu equilibria and then projects them onto exact menu equilibria can destroy the desired conclusion completely.

The phenomenon extends to a parameter family: replacing player \(0\)’s reward when absent from the quitting coalition by \(R>1\), and replacing the other players’ loss when \(0\) quits by any \(-h<0\), makes the exact-menu defect

$$
1-\frac1R,
$$

while the same cyclic laws still satisfy \(E_{3K}=L_0=8^{-K}\).

**The arbitrary-table selector remains unproved here.** The new result resolves a narrower but consequential issue: exact finite-menu equilibrium selection is insufficient even after optimizing over every deadline and every equilibrium, whereas a genuinely different approximate construction succeeds.

[Full proof, complete reward table, and parameter family](FINITE_MENU_EXACT_APPROX_SEPARATION.md) · [Exact-arithmetic checker](check_example.py)

The checker passed for \(K=1,2,3,4,6\); the arguments above establish the all-\(K\) construction and all-\(N\) equilibrium classification. These results have not been formalized in Lean.
