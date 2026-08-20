# Question 189: Cancellation-safe aggregation of eventwise Quit advantages

## Setting

Let \(I\) be a nonempty finite player set and \(r(S)\in\mathbb R^I\) the
payoff when the nonempty coalition \(S\) Quits. Fix a product mixed action
\(x\), a continuation payoff \(v\), and a player \(i\). For
\(j\in I\), write \(q_j=x_j(\mathrm Q)\) and \(c_j=1-q_j\). For
\(A\subseteq I\setminus\{i\}\), let

\[
p^x_{-i}(A)=
\prod_{j\in A}q_j\prod_{j\notin A\cup\{i\}}c_j
\]

be the probability that precisely the opponents in \(A\) Quit. Define

\[
\widehat r_i(A;v_i)=
\begin{cases}
v_i,&A=\varnothing,\\
r_i(A),&A\ne\varnothing,
\end{cases}
\qquad
a_i(A)=r_i(A\cup\{i\})-\widehat r_i(A;v_i).
\]

If the row is reached with probability \(h\) and player \(i\) currently
Continues with probability \(c_i\), its eventwise positive account is

\[
\mathcal A_i
=hc_i\sum_Ap^x_{-i}(A)[a_i(A)]_+.
\]

The gain from the legal pure-Quit change at that row is instead

\[
G_i^{\rm Q}=hc_i\sum_Ap^x_{-i}(A)a_i(A).
\]

Consequently

\[
[G_i^{\rm Q}]_+\leq\mathcal A_i,
\]

but a positive lower bound on \(\mathcal A_i\) gives no lower bound on
\(G_i^{\rm Q}\): positive and negative opponent-coalition labels may cancel,
and player \(i\) cannot condition its simultaneous action on \(A\).

Assume that an actual profile, a finite collection \(T\) of reached rows on
its unique pre-absorption history, one fixed player \(i\), and the pure-Quit
direction have been selected so that

\[
\sum_{t\in T}\mathcal A_{i,t}\geq\kappa
\]

for a fixed \(\kappa>0\). This is the exact positive-account output available
under the hypotheses of this question. It is stronger than merely locating
unrelated positive labels, but it is not yet a deviation gain.

## Question

Which additional property of the reached rows converts the positive-part
account into one legal behavioral deviation without losing a fixed fraction
to cancellation or causal interference?

An affirmative answer must give a condition stated in terms of the displayed
rows, probabilities, continuation payoffs, and reward table, and prove that
for some explicit \(c>0\),

\[
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
\geq c\sum_{t\in T}\mathcal A_{i,t}
\]

for one legal behavioral strategy \(\tau_i\). The condition must itself be
derivable from the displayed selected-row data, or the answer must state
exactly the new hypothesis being added. The proof must account for the fact
that an earlier change to Quit can prevent later marked rows from being
reached.

A negative answer may give a finite reward table and a finite marked
chronology for which the positive account is bounded below while every
behavioral modification of the selected player supported on the marked rows
has nonpositive gain. Such an example must preserve the actual reach
probabilities and literal continuation payoffs used in the account; a list of
unrelated one-row sign cancellations is not enough.

## Acceptance criterion

The answer must produce either one legal deviation with a quantitative gain,
or a literal finite obstruction showing that no such conversion follows from
the present hypotheses. A further decomposition of the positive summands is
not progress: every summand is already positive only because it conditions on
information unavailable to the player at the row.

# Answer

There are two distinct losses:

1. **Simultaneous-information cancellation:** only the signed row average
   (\Delta_t=\sum_Ap_{-i,t}(A)a_{i,t}(A)) is behaviorally usable.
2. **Chronological interference:** extra quitting at an earlier marked row removes later opportunities.

For a single pre-absorption chronology, the second loss has an exact form: all deviations assembled from the selected pure-Quit directions are subconvex combinations of the one-row signed gains. Consequently, the required additional property is a **signed row concentration** condition, not further concentration of positive event labels.

## 1. Exact causal-convexification identity

For each marked row, write

[
P_t:=\sum_Ap_{-i,t}(A)[a_{i,t}(A)]*+,
\qquad
N_t:=\sum_Ap*{-i,t}(A)[-a_{i,t}(A)]_+,
]

so that

[
\Delta_t:=P_t-N_t
=\sum_Ap_{-i,t}(A)a_{i,t}(A),
]

and hence

[
\mathcal A_{i,t}=h_tc_{i,t}P_t,
\qquad
G_{i,t}^{\rm Q}=h_tc_{i,t}\Delta_t.
]

Discard rows with (\mathcal A_{i,t}=0), and enumerate the remaining rows chronologically as

[
t_1<t_2<\cdots<t_m.
]

Consider any behavioral deviation obtained by moving some of player (i)'s Continue probability to Quit at these rows. Write its new Quit probability as

[
q'_{i,t_k}
==========

q_{i,t_k}+\lambda_kc_{i,t_k},
\qquad
0\leq\lambda_k\leq1.
]

Thus (\lambda_k=1) means pure Quit at (t_k), while (\lambda_k=0) leaves the row unchanged.

Then the payoff gain is exactly

[
\boxed{
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
===================================

\sum_{k=1}^m
\lambda_k
\prod_{\ell<k}(1-\lambda_\ell)
,G_{i,t_k}^{\rm Q}.
}
\tag{1}
]

### Proof

Let (\sigma^{(k)}) modify the first (k) marked rows and leave all later rows unchanged. Under (\sigma^{(k-1)}), the probability of reaching (t_k) is

[
h_{t_k}\prod_{\ell<k}(1-\lambda_\ell).
]

Indeed, at each earlier modified row (t_\ell), player (i)'s Continue probability has been multiplied by (1-\lambda_\ell); all opponent and unmarked-row probabilities remain unchanged.

The strategies (\sigma^{(k)}) and (\sigma^{(k-1)}) differ only at (t_k). Moreover, all later marked rows are still literal (\sigma)-rows in both hybrids, so the Continue endpoint at (t_k) is precisely the displayed continuation payoff (v_{i,t_k}). Therefore

[
U_i(\sigma^{(k)})-U_i(\sigma^{(k-1)})
=====================================

h_{t_k}
\prod_{\ell<k}(1-\lambda_\ell)
\lambda_kc_{i,t_k}\Delta_{t_k}.
]

Summing the hybrid increments gives (1). ∎

The causal weights

[
w_k:=\lambda_k\prod_{\ell<k}(1-\lambda_\ell)
]

satisfy

[
w_k\geq0,
\qquad
\sum_{k=1}^mw_k
===============

1-\prod_{k=1}^m(1-\lambda_k)
\leq1.
\tag{2}
]

Thus every such deviation gain is a subconvex combination of the one-row gains. In particular,

[
\boxed{
\sup_{\substack{\tau_i:,
q'*{i,t}\ge q*{i,t}\
\tau_i=\sigma_i\text{ off }T}}
\bigl(U_i(\tau_i,\sigma_{-i})-U_i(\sigma)\bigr)
===============================================

\max_{t\in T}[G_{i,t}^{\rm Q}]_+.
}
\tag{3}
]

The upper bound follows from (1)–(2); equality is attained by leaving every row unchanged except a maximizing row, where player (i) plays pure Quit.

So there is no genuine addition of gains along this nested chronology. Quitting can happen only once.

## 2. The exact additional property

Let

[
\mathcal A_T:=\sum_{t\in T}\mathcal A_{i,t}.
]

The necessary and sufficient displayed-data condition for a Quit-direction conversion with coefficient (c>0) is

[
\boxed{
\max_{t\in T}
\left[
h_tc_{i,t}
\sum_Ap_{-i,t}(A)a_{i,t}(A)
\right]_+
\geq
c,\mathcal A_T.
}
\tag{4}
]

Under (4), choose a maximizing row and switch to pure Quit only there. Equation (3) gives the required gain. Conversely, (3) shows that no strategy assembled from the selected pure-Quit directions can do better.

A less tautological sufficient hypothesis separates cancellation from temporal concentration. Suppose there are (\theta,\rho>0) and (t^*\in T) such that

[
N_{t^*}\leq(1-\theta)P_{t^*}
\tag{5}
]

and

[
\mathcal A_{i,t^*}
\geq
\rho\sum_{t\in T}\mathcal A_{i,t}.
\tag{6}
]

Condition (5) is an observable rowwise anti-cancellation margin:

[
\Delta_{t^*}=P_{t^*}-N_{t^*}\geq\theta P_{t^*}.
]

Playing pure Quit only at (t^*) therefore gives

[
\begin{aligned}
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
&=G_{i,t^*}^{\rm Q}\
&=h_{t^*}c_{i,t^*}\Delta_{t^*}\
&\geq\theta h_{t^*}c_{i,t^*}P_{t^*}\
&=\theta\mathcal A_{i,t^*}\
&\geq\theta\rho\sum_{t\in T}\mathcal A_{i,t}.
\end{aligned}
]

Hence one may take

[
\boxed{c=\theta\rho.}
\tag{7}
]

If (5) holds at every account-positive marked row, then taking a row of maximal account gives (\rho\geq1/m), and therefore

[
c=\frac{\theta}{m}.
\tag{8}
]

Equivalently, one can use all rows in a single causal lottery: at row (t_k), move the fraction

[
\lambda_k=\frac1{m-k+1}
]

of the remaining Continue mass to Quit. Then every causal weight in (1) equals (1/m), so

[
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
===================================

\frac1m\sum_{t\in T}G_{i,t}^{\rm Q}
\geq
\frac{\theta}{m}\sum_{t\in T}\mathcal A_{i,t}.
]

For a coefficient uniform over chronologies with unbounded (|T|), the concentration parameter (\rho) must itself be bounded below. Rowwise sign coherence alone cannot remove the causal (1/m) obstruction.

## 3. Literal obstruction under the hypotheses as stated

The present positive-account hypothesis does not imply any positive conversion coefficient. The obstruction can be realized by one finite profile in which the continuation payoff at the first marked row is literally generated by the second.

Fix the requested (\kappa>0), and put

[
s:=\frac{8\kappa}{5}.
]

Take two players (I={i,j}), and let the payoff vectors, with coordinates ordered as ((i,j)), be

[
r({i})=(s,0),
\qquad
r({j})=\left(\frac{4s}{3},0\right),
\qquad
r({i,j})=\left(\frac{s}{3},0\right).
\tag{9}
]

Consider the following actual profile:

* player (i) Continues surely at every date;
* at date (1), player (j) Quits with probability (1/4);
* conditional on reaching date (2), player (j) Quits with probability (1/2);
* after date (2), both players Continue forever.

Mark (T={1,2}).

The actual reach probabilities are

[
h_1=1,
\qquad
h_2=\frac34.
]

The literal continuation payoff after all Continue at date (2) is

[
v_{i,2}=0.
]

After all Continue at date (1), date (2) is reached, so the literal continuation payoff is

[
v_{i,1}
=======

# \frac12r_i({j})+\frac12\cdot0

\frac{2s}{3}.
\tag{10}
]

Thus the first continuation value is genuinely generated by the second marked row.

At date (1),

[
a_{i,1}(\varnothing)
====================

# s-\frac{2s}{3}

\frac{s}{3},
\qquad
a_{i,1}({j})
============

# \frac{s}{3}-\frac{4s}{3}

-s.
]

Since (j) Continues with probability (3/4),

[
P_1=\frac34\frac{s}{3}=\frac{s}{4},
\qquad
N_1=\frac14s=\frac{s}{4},
\qquad
\Delta_1=0.
]

Therefore

[
\mathcal A_{i,1}=\frac{s}{4},
\qquad
G_{i,1}^{\rm Q}=0.
\tag{11}
]

At date (2),

[
a_{i,2}(\varnothing)=s,
\qquad
a_{i,2}({j})=-s.
]

Since (j) Quits with probability (1/2),

[
P_2=N_2=\frac{s}{2},
\qquad
\Delta_2=0,
]

and hence

[
\mathcal A_{i,2}
================

# h_2P_2

# \frac34\frac{s}{2}

\frac{3s}{8},
\qquad
G_{i,2}^{\rm Q}=0.
\tag{12}
]

Consequently,

[
\sum_{t\in T}\mathcal A_{i,t}
=============================

# \frac{s}{4}+\frac{3s}{8}

# \frac{5s}{8}

\kappa.
\tag{13}
]

Nevertheless, every behavioral modification of (i) supported on the two marked rows has zero gain.

At date (2), the expected payoff from Quit is

[
\frac12s+\frac12\frac{s}{3}
===========================

\frac{2s}{3},
]

while the expected payoff from Continue is

[
\frac12\frac{4s}{3}+\frac12\cdot0
=================================

\frac{2s}{3}.
]

Thus every randomization at date (2) has continuation value (2s/3).

Using this literal value at date (1), Quit gives

[
\frac34s+\frac14\frac{s}{3}
===========================

\frac{5s}{6},
]

while Continue gives

[
\frac14\frac{4s}{3}
+
\frac34\frac{2s}{3}
===================

\frac{5s}{6}.
]

Therefore, for every behavioral strategy (\tau_i) agreeing with the actual strategy outside (T),

[
U_i(\tau_i,\sigma_{-i})
=======================

# U_i(\sigma)

\frac{5s}{6}.
\tag{14}
]

This is one literal two-row chronology, with the stated reach probabilities and continuation payoffs, not a collection of unrelated static cancellations. Earlier Quit does prevent the second row from being reached, but the Bellman action values are exactly equal at both rows.

Hence the positive-part account alone admits no conversion at all. The missing datum is a uniform lower bound on the signed-concentration ratio

[
\frac{\max_{t\in T}[G_{i,t}^{\rm Q}]*+}
{\sum*{t\in T}\mathcal A_{i,t}},
]

or a structural hypothesis such as the anti-cancellation and temporal-concentration conditions (5)–(6).
