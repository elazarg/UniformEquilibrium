# Question 190: Static singleton toggle to an executable near-minimum chronology

## Setting

Consider a finite quitting game chosen, among hypothetical games without a
uniform-equilibrium payoff, with the fewest players. For a behavioral profile
\(\sigma\), let \(U(\sigma)\) be its terminal payoff and let \(B_i(\sigma)\)
be player \(i\)'s supremal terminal payoff over unilateral behavioral
deviations. Let

\[
\mathcal K=\overline{\{(U(\sigma),B(\sigma)):\sigma
\text{ is behavioral}\}},\qquad
D_*=\min_{(u,b)\in\mathcal K}\sum_i(b_i-u_i)>0.
\]

Exact deletion of a player while preserving the same positive terminal gap
would leave a smaller counterexample, so minimality excludes it. Assume in
addition the following static datum:

- distinct players \(k\) and \(j\);
- a nonempty coalition \(Q\) with \(k\notin Q\);
- a strict insertion gain

  \[
  r_k(Q\cup\{k\})-r_k(Q)>0;
  \]

- at the pure absorbing row \(R=Q\cup\{k\}\), player \(j\) has a strictly
  profitable pure action change.

The last condition is an explicit coalition comparison. If \(j\in R\), it
means

\[
r_j(R\setminus\{j\})>r_j(R),
\]

and if \(j\notin R\), it means

\[
r_j(R\cup\{j\})>r_j(R).
\]

The conclusion is static: it does not say that \(R\) occurs at positive
probability in a profile near the minimum, and it does not attach either
strict comparison to a literal continuation payoff.

## Question

Can this pair of strict coalition toggles be realized on one executable
chronology while retaining quantitative proximity to the minimum semantic
face?

A positive answer must produce, from the displayed hypotheses and the
positive minimum, at least one of the following:

1. a reachable \(z'\in\mathcal K\) with \(D(z')<D_*\);
2. terminal \(\varepsilon\)-Nash profiles for every \(\varepsilon>0\); or
3. a finite state-matched Nash--Bellman path on which one of the two strict
   toggle margins appears as a legal unilateral gain with positive
   unconditional weight, together with a telescoping account which forces
   either (1) or (2).

The quantitative weight may depend on the reward table and the two strict
margins, but not on a truncation horizon or on a subsequence index.

A negative answer must prove a genuine realization obstruction for a class
of chronologies containing all exact prefix insertions and all summably
approximate prefix insertions. It must identify an invariant preserved by
that class; observing only that the pure toggle row is not Nash repeats the
known unchanged-row obstruction.

## Acceptance criterion

The static comparisons must be connected to an actual reached row, a literal
tail, and a legal behavioral deviation, or ruled out by a quantitative
invariant. Producing another static coalition alternative does not answer the
question.

# Answer

**Status: a no-go for the prefix-insertion operation class, not a global
refutation of the static branch.**  The one-row cap-defect recursion is proved
in
[`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean).
Its exact and approximate survival-weighted telescopes and the positive-floor
return barrier are proved, without game-specific notation, in
[`Research/Semantics/SurvivalWeightedReachedHistoryAccount.lean`](../../Research/Semantics/SurvivalWeightedReachedHistoryAccount.lean).  These results cover
all literal exact prefix insertions and all prefix insertions whose Bellman and
state-matching residuals have summable survival-weighted budgets.  They do not
exclude a different architecture that creates the required nonvanishing
budget or directly produces an equilibrium.

The hinge is the distinction between an **eventwise coalition margin** and an **incremental Bellman gain**. For literal prefixes there is an exact coordinatewise conservation law. It allows arbitrary state and cap changes, so it is stronger than the known unchanged-tail obstruction.

## 1. The live-debt identity

Let

[
z_t=(u^t,b^t)\in\mathcal K,\qquad
z_t=T_{q^t}(z_{t+1}),\qquad 0\le t<N,
]

be a literal state-matched prefix path. Write

[
s_t=\prod_{i\in I}(1-q^t_i),\qquad
L_0=1,\qquad L_{t+1}=L_ts_t.
]

Thus (s_t) is the conditional survival probability at root (t), and
(L_t) is the unconditional probability of reaching that root.

For player (i), against the cap (b_i^{t+1}), let

[
Q_{i,t}
=\sum_{A\subseteq I\setminus{i}}
p^t_{-i}(A),r_i(A\cup{i}),
]

and

[
C_{i,t}
=\sum_{\varnothing\ne A\subseteq I\setminus{i}}
p^t_{-i}(A),r_i(A)
+p^t_{-i}(\varnothing)b_i^{t+1}.
]

Define the one-root Bellman residual

[
\delta_{i,t}
============

## \max{Q_{i,t},C_{i,t}}

\bigl(q_i^tQ_{i,t}+(1-q_i^t)C_{i,t}\bigr)
\ge 0.
]

This is zero precisely when player (i)'s prescribed root action is optimal in the cap game.

The cap-valued payoff of the prescribed root mixture equals

[
q_i^tQ_{i,t}+(1-q_i^t)C_{i,t}
=============================

\sum_{\varnothing\ne S\subseteq I}P_{q^t}(S)r_i(S)
+s_tb_i^{t+1}.
]

The literal prescribed payoff is the same expression with (u_i^{t+1}) in place of (b_i^{t+1}). Consequently,

[
\boxed{;
d_i(z_t)=s_t,d_i(z_{t+1})+\delta_{i,t}.
;} \tag{1}
]

Multiplying by (L_t) and telescoping gives the coordinatewise invariant

[
\boxed{;
d_i(z_0)
========

L_Nd_i(z_N)
+\sum_{t<N}L_t\delta_{i,t}.
;} \tag{2}
]

Equivalently,

[
\Psi_{i,t}
:=
L_td_i(z_t)+\sum_{\ell<t}L_\ell\delta_{i,\ell}
]

is independent of (t).

This is the relevant invariant. It is preserved by every literal prefix insertion, not merely by prefixes that keep the tail or cap unchanged. In particular:

* on an exact Nash–Bellman path, every (\delta_{i,t}=0), so each coordinate (L_td_i(z_t)) is conserved;
* approximate roots can only spend live debt in the same player coordinate;
* there is no mechanism in (1) transferring a (k)-charge into a (j)-charge.

Summing (1), with (\Delta_t=\sum_i\delta_{i,t}), gives

[
D(z_0)=L_ND(z_N)+\mathcal R_N,
\qquad
\mathcal R_N:=\sum_{t<N}L_t\Delta_t. \tag{3}
]

## 2. The quantitative near-minimum barrier

Put

[
E_t=D(z_t)-D_*\ge 0.
]

Equation (3) is equivalent to

[
\boxed{;
D_*(1-L_N)
==========

L_NE_N+\mathcal R_N-E_0.
;} \tag{4}
]

For a coalition (S), let its total unconditional mass on the path be

[
W_N(S)
:=
\sum_{t<N}L_tP_{q^t}(S).
]

Because quitting stops the game,

[
\sum_{\varnothing\ne S\subseteq I}W_N(S)=1-L_N.
]

Hence, from (4),

[
\boxed{;
D_*W_N(S)
\le L_NE_N+\mathcal R_N
\le E_N+\mathcal R_N.
;} \tag{5}
]

This has several immediate consequences.

If all roots are exact Nash–Bellman roots, then (\mathcal R_N=0). Therefore any exact path beginning and ending on the minimum face satisfies

[
E_0=E_N=0
\quad\Longrightarrow\quad
L_N=1,
]

so it contains no quitting row at positive probability. More generally, if the terminal matched state satisfies (E_N\le\eta), then

[
W_N(S)\le \frac{\eta}{D_*}. \tag{6}
]

Thus an exact path may carry a fixed quitting atom only by ending a fixed positive distance above the minimum face. State and cap changes do not avoid this toll.

For summably approximate roots, suppose (\delta_{i,t}\le\varepsilon_{i,t}). Then

[
\mathcal R_N
\le
\sum_{t<N}L_t\sum_i\varepsilon_{i,t}
\le
\sum_{t<N}\sum_i\varepsilon_{i,t}.
]

If (\sum_t\sum_i\varepsilon_{i,t}<\infty), the residual budget of shifted tail windows tends to zero. For near-minimum shifted windows, (5) therefore yields

[
W_N(S)\longrightarrow 0. \tag{7}
]

The same remains true for summably approximate state matching. Indeed, if

[
|z_t-T_{q^t}(z_{t+1})|_\infty\le\xi_t,
]

then the error in the scalar identity (3) is at most (2|I|\xi_t) per reached root. Thus (5) becomes

[
D_*W_N(S)
\le
E_N+
\sum_{t<N}L_t\bigl(\Delta_t+2|I|\xi_t\bigr). \tag{8}
]

Absolute summability again makes the error budget of shifted windows vanish.

Consequently, a lower bound

[
W_N(R)\ge w>0
]

independent of the truncation or subsequence requires a nonvanishing resource:

[
E_N+\mathcal R_N\ge D_*w. \tag{9}
]

Neither static toggle comparison, by itself, supplies such a resource.

## 3. Why the margins need not be legal gains

For a root with tail cap (b_i), define the eventwise Quit advantage

[
a_i(A)
======

## r_i(A\cup{i})

\begin{cases}
b_i,&A=\varnothing,\
r_i(A),&A\ne\varnothing.
\end{cases}
]

Then the cap-level endpoint difference is

[
G_i:=Q_i-C_i
=\sum_{A\subseteq I\setminus{i}}p_{-i}(A)a_i(A). \tag{10}
]

The root residual is

[
\delta_i
========

(1-q_i)[G_i]*+
+q_i[-G_i]*+. \tag{11}
]

For player (k), the displayed insertion gain says only that one summand is positive:

[
a_k(Q)=r_k(Q\cup{k})-r_k(Q)=:g_k>0,
]

so

[
G_k
===

p_{-k}(Q)g_k
+\sum_{A\ne Q}p_{-k}(A)a_k(A). \tag{12}
]

There is no restriction on the second term.

For player (j), writing the toggle margin as (g_j>0):

* if (j\notin R), then (a_j(R)=g_j);
* if (j\in R), then
  [
  a_j(R\setminus{j})
  =r_j(R)-r_j(R\setminus{j})
  =-g_j.
  ]

Again, all other opponent faces may cancel this contribution exactly.

The literal tail does not repair the cancellation. The gains from deviating at the root to Quit or to Continue-and-best-respond are

[
Q_i-u_i^t=(1-q_i)G_i+s_td_i(z_{t+1}), \tag{13}
]

[
C_i-u_i^t=-q_iG_i+s_td_i(z_{t+1}). \tag{14}
]

These equations separate two effects:

1. (G_i) is the net cap-level action advantage. The static margin is only one term in it and can be canceled.
2. (s_td_i(z_{t+1})) is inherited tail debt. A legal deviation may realize that debt, but this is not a new gain created by the toggle.

If the root is exact and mixed, then (G_i=0). Any literal profitable deviation in (13)–(14) is then exactly inherited tail debt. It cannot be attributed quantitatively to the designated coalition margin.

If cancellation is broken and the margin creates a positive incremental gain, that gain contributes to (\delta_{i,t}), hence to the positive term (\mathcal R_N) in (3). The telescope therefore accounts for it as expenditure of existing debt; it does not force (D<D_*).

This is also why the two toggles do not constitute a handoff. The first is a (k)-deviation from (Q) to (R). The second is a (j)-deviation evaluated at the counterfactual target (R). A unilateral deviation cannot concatenate them: after the nonempty coalition (R) quits, play has stopped, and (j) has no later response date. At a simultaneous mixed root, (j) cannot condition on whether (k) deviated. Prefix insertion preserves this causal fact.

## 4. An executable exact-cancellation witness

The cancellation is not merely formal. Consider the two-player quitting table, with coordinates ordered as ((k,j)),

[
r({k})=(-1,1),\qquad
r({j})=(0,2),\qquad
r({k,j})=(1,0).
]

Take

[
Q={j},\qquad R={k,j}.
]

Then

[
r_k(R)-r_k(Q)=1,
]

and, since (j\in R),

[
r_j(R\setminus{j})-r_j(R)
=r_j({k})-r_j({k,j})
=1.
]

Let both players Quit independently with probability (1/2) at every date. Its literal continuation pair is

[
u=b=(0,1).
]

Indeed, for (k),

[
Q_k=\tfrac12(-1)+\tfrac12(1)=0,
\qquad
C_k=\tfrac12(0)+\tfrac12(0)=0,
]

while for (j),

[
Q_j=\tfrac12(2)+\tfrac12(0)=1,
\qquad
C_j=\tfrac12(1)+\tfrac12(1)=1.
]

Thus the root is exact Nash–Bellman. Both (Q) and (R) have positive reached mass; in fact each is the terminal coalition with probability (1/3). Nevertheless neither strict coalition comparison produces a legal net gain.

The cancellations are explicit:

[
\underbrace{r_k(R)-r_k(Q)}*{+1}
\quad\text{is canceled by}\quad
\underbrace{r_k({k})-b_k}*{-1},
]

and

[
\underbrace{r_j(R)-r_j({k})}*{-1}
\quad\text{is canceled by}\quad
\underbrace{r_j({j})-b_j}*{+1}.
]

This example is not presented as a positive-gap counterexample—the game has an equilibrium. Its role is to show that even after supplying an actual chronology, positive reached mass, and a literal continuation, the proposed static-to-legal implication fails locally. Positive (D_*) does not alter equations (10)–(14); it only adds the quantitative live-debt barrier (5).

## Conclusion

Within exact or summably vanishing-error near-minimum prefix insertion, the
displayed static toggles do not yield alternative 3.  This does not assert
that the hypotheses fail to imply alternatives 1 or 2 through a different
argument.

The preserved invariant is the coordinatewise quantity

[
L_td_i(z_t)+\sum_{\ell<t}L_\ell\delta_{i,\ell},
]

with its scalar consequence

[
D_*(1-L_N)
==========

L_N\bigl(D(z_N)-D_*\bigr)
+\sum_{t<N}L_t\Delta_t
-\bigl(D(z_0)-D_*\bigr).
]

It covers arbitrary state-changing exact prefixes and summably approximate prefixes. It implies that a fixed positive reached weight for (R) must be paid either by a fixed excursion above the minimum face or by a fixed cumulative Bellman/matching residual. On exact or summably vanishing near-minimum returns, that weight necessarily tends to zero.

The two strict comparisons provide neither a noncancellation estimate for (G_k) or (G_j), nor a source for the required tail-excess/residual budget. Minimality only excludes a successful exact deletion; it does not constrain the off-face terms in (12), and it does not defeat the live-debt invariant. A theorem converting persistent cancellation into such a deletion would be an additional strategic result, not a consequence of the stated static datum.
