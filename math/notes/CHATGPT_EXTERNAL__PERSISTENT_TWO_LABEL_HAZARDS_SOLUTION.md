# Persistent two-label hazard production: negative solution

## Result

The universal producer is false, even with four players.  There is a reward
table for which every bounded exact Nash--Bellman spine has summable Quit
hazard for every player except one distinguished owner.  Hence no exact spine
has two distinct persistent marginal labels.  The same quantitative estimate
rules out both robust transport alternatives.

## The reward table

Let `I` be any finite player set with at least two elements and fix an owner
`o ∈ I`.  For every nonempty quitting coalition `S`, define

\[
r_o(S)=\begin{cases}
0,&o\in S,\\
-1,&o\notin S,
\end{cases}
\]

and, for every outsider `j ≠ o`,

\[
r_j(S)=\begin{cases}
-1,&o\in S\text{ and }j\in S,\\
0,&\text{otherwise}.
\end{cases}
\]

The reward bound is one.

## Exact-spine hazard potential

Let `(v_t,x_t)_{t≥0}` be any bounded exact Nash--Bellman spine.  Write

\[
p_t=x_{t,o}(Q),\qquad
\beta_t=\prod_{j\ne o}(1-x_{t,j}(Q)),\qquad
h_t=1-\beta_t,
\]

and put `z_t=v_t(o)`.  Thus `h_t` is exactly the owner-deleted opponent
clock charge.

The owner's payoff from pure Quit is always zero, so exact root Nash gives

\[
z_t\ge 0\qquad(t\ge0).
\]

The owner's pure-Continue payoff is

\[
C_t=\beta_t z_{t+1}-(1-\beta_t)
   =z_{t+1}-h_t(1+z_{t+1}),
\]

and Bellman evaluation gives

\[
z_t=(1-p_t)C_t.
\]

We claim

\[
\boxed{\quad h_t\le z_{t+1}-z_t\quad}\tag{1}
\]

for every `t`.

* If `p_t=0`, then `z_t=C_t`, hence
  \[
  z_{t+1}-z_t=h_t(1+z_{t+1})\ge h_t.
  \]
* If `0<p_t<1`, both owner actions are in support.  Exact Nash forces
  `C_t=0`; hence `z_t=0` and
  \[
  z_{t+1}=h_t(1+z_{t+1})\ge h_t.
  \]
* If `p_t=1`, then any outsider who Quits receives `-1`, while deviating to
  Continue receives `0`, independently of the other outsiders.  Exact Nash
  therefore forces every outsider's Quit probability to be zero.  Thus
  `h_t=0`, while `z_t=0` and `z_{t+1}\ge0`.

This proves (1).

Summing (1) over any finite window gives

\[
\sum_{t=m}^{n-1}h_t\le z_n-z_m.\tag{2}
\]

Since the spine is bounded and `z_t≥0`, the series `\sum_t h_t` converges.
For the canonical reward-cube bound, (2) yields

\[
\sum_{t=0}^\infty h_t\le 1-z_0\le1.
\]

For every outsider `j`, its marginal Quit event is contained in the event
that some outsider Quits, so

\[
x_{t,j}(Q)\le h_t.
\]

Consequently every outsider's marginal Quit-hazard series is summable.  Any
pair of distinct labels contains an outsider, and therefore no bounded exact
Nash--Bellman spine for this table has two persistent labels.

## The obstruction is nonvacuous

There is an exact stationary spine: the owner Quits surely, every outsider
Continues surely, and `v_t=0` for every `t`.  The owner is indifferent between
Quit and Continue, while every outsider strictly prefers Continue to joining
the owner.  Thus one label is persistent, but a second one is impossible.
This profile is itself an exact immediate-exit uniform equilibrium.

## Failure of the robust adapters

Let an outsider's nominal nonnegative hazard stream be `\widehat q_t` with
`\sum_t\widehat q_t=\infty`.

* If `\sum_t|q_t-\widehat q_t|<\infty`, then
  `\widehat q_t\le q_t+|q_t-\widehat q_t|`, so summability of the actual
  stream `q_t` would imply summability of the nominal stream, a contradiction.
* If `q_t\ge\theta\widehat q_t` for a fixed `\theta>0`, then divergence of
  the nominal stream forces divergence of the actual stream, again a
  contradiction.

Since every pair of labels includes an outsider, neither robust alternative
can produce two divergent labels on an exact spine for this reward table.

## Exact isolated two-label packets still exist

The failure is chronological, not merely a lack of local mixed roots.  Take
four players `o,b,c,d`.  Let

\[
\lambda_n=\frac1{n+3},\qquad
s_n=1-\sqrt{1-\lambda_n}.
\]

At one root let `o,d` Continue surely and let `b,c` Quit independently with
probability `s_n`.  The probability that at least one outsider Quits is
`\lambda_n`.  Give the successor value

\[
w_n(o)=\frac{\lambda_n}{1-\lambda_n},\qquad
w_n(j)=0\quad(j\ne o).
\]

Then every player's pure Quit and pure Continue endpoint payoff is zero, so
this is an exact Nash--Bellman edge with current value zero.  Both fixed labels
`b,c` have hazard `s_n`, and

\[
s_n\ge\frac{\lambda_n}{2},
\]

so both nominal streams diverge across the family.  The successor values tend
to zero, and all local Nash and Bellman defects are exactly zero.

These edges cannot be concatenated into one bounded exact spine while
retaining their charge: (2) says that outsider charge is paid by a monotone
increase of the owner's continuation value.  Harmonic total charge would
force an unbounded increase.  Therefore any attempted reprojection must incur
nonsummable labelled loss or fail every fixed-fraction retention bound.

## Consequence for the stated producer

The requested universal statement is false.  Two persistent labels are a
sufficient survival certificate, not a necessary feature of exact
Nash--Bellman spines, even in a game with an exact uniform equilibrium.  A
corrected producer must be conditional on the positive-gap/positive-minimum
source regime, or be disjunctive and return an already available equilibrium
certificate in tables such as this one.  This counterexample does not refute
the narrower producer from actual positive-minimum tangent and vanishing-debt
atom data.
