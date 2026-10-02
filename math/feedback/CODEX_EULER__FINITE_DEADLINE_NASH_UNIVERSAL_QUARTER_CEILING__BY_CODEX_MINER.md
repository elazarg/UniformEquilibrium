# Second independent review of the finite-deadline universal quarter ceiling

Reviewer: CODEX_MINER

Source:
[`notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`](../notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md)

## Verdict

**PASS**, including the current repaired fixed-prefix Section 8.  I attempted
to falsify the earliest-time comparison, positive-part logic, general-`K`
summation, scalar constants, hierarchy cutoff, worst-table equilibrium
quantifiers, and the arbitrary finite-tail extension.  I found no remaining
mathematical objection.

The core result is a substantial unrestricted-strategy export candidate.  It
proves a table-uniform bound for every exact `K`-date timing Nash realization,
the exact third-date scalar constant, and the asymptotic `1/4` worst-table
ceiling.  Section 8 is a separate exact fixed-prefix barrier.  Neither result
is a terminal-approximation theorem, and the source correctly keeps that
nonclaim explicit.

## 1. Unrestricted pure-time decomposition

For fixed player `i`, the events

\[
 \{\text{all opponents Never}\},\qquad
 \{\text{opponents' earliest time is }t\},\ 0\le t<K,
\]

are disjoint and exhaustive under the opponents' independent planned-time
laws.  Thus `a+sum_t h_t=1`, including zero-probability dates and boundary
laws.

Finite timing Nash gives

\[
 U_i=\max(V_N,V_0,\ldots,V_{K-1}),
\]

because the prescribed payoff is their mixture and every permitted pure
action is a best-response lower bound.  All finite times at least `K` have one
common value `L`.  The checked behavioral pure-time extremality theorem hence
gives exactly

\[
 B_i=\max(U_i,L),\qquad d_i=\max(0,L-U_i)
\]

against arbitrary randomized history-dependent behavioral deviations.  No
best-response attainment beyond the finite displayed maximum is assumed.

Late Quit and Never differ only on all-opponents-Never:

\[
 L-V_N=as.
\]

Consequently positive debt forces `s>0`; `s<=0` is a literal zero-debt arm.

## 2. Every-date comparison and positive parts

For time `t<K`, opponent exits before `t` cancel, an exit at `t` gives a
leave-versus-join difference at most `2R`, later opponent exits compare an
opponent-only reward with singleton `s` and give at most `R-s`, and all Never
again cancels.  Therefore

\[
 L-V_t\le 2Rh_t+(R-s)\sum_{u>t}h_u.
\]

The right side is nonnegative because `0<s<=R`.  The source correctly uses

\[
 d_i\le\max(0,L-V_t)
 \le2Rh_t+(R-s)\sum_{u>t}h_u,
\]

so the negative raw-difference defect found in the original two-date draft is
not present.  Likewise `d_i<=as` is valid.  All tie, Never, after-support, and
pure boundary cases are covered.

## 3. General scalar calculation and indexing

With `x=s/R`, `delta=d_i/R`, and `H=sum_t h_t=1-a`, summing over all `K`
finite dates gives

\[
 K\delta
 \le2H+(1-x)\sum_{t=0}^{K-1}\sum_{u=t+1}^{K-1}h_u
 =2H+(1-x)\sum_{u=1}^{K-1}u h_u.
\]

The multiplicity of `h_u` is exactly `u`, not `u+1` or `K-u`.  Bounding it by
`K-1` yields

\[
 K\delta\le A H,
 \qquad A=K+1-(K-1)x>0.
\]

Since `delta<=ax`, one has `H<=1-delta/x`.  Rearrangement gives

\[
 \delta\le {Ax\over Kx+A}
 ={x(K+1-(K-1)x)\over K+1+x}=f_K(x).
\]

The denominator and deadline indexing are correct for actions
`0,...,K-1,Never`.  In particular:

* `K=1`: `max f_1=2/3`;
* `K=2`: `max f_2=1/2`;
* `K=3`: the derivative numerator is `16-16x-2x^2`, with unique maximizer
  `x_*=-4+2 sqrt(6)` and

  \[
  c_3=20-8\sqrt6<5/12.
  \]

The rational comparison uses

\[
24x^2-43x+20
=24(x-43/48)^2+71/96>0,
\]

which expands exactly.  Finally

\[
 f_K(x)\le x(1-x)+{x(1+x)\over K}
 \le1/4+2/K.
\]

The divisions occur only in the separately stated `R>0`, positive-debt arm.

## 4. Exact worst-table minimax quantifiers

The defined `W_K` is the supremum over normalized Fin4 tables and over all
exact mixed Nash equilibria at that deadline.  Because the universal theorem
holds for **every** equilibrium,

\[
 W_K\le c_K\le1/4+2/K.
\]

The independently reviewed normalized Fin4 table in
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](../notes/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
has a unique equilibrium and debt

\[
 D_K={2^{K-1}\over2^{K+1}-1}>1/4,
 \qquad D_K\to1/4.
\]

Thus `W_K>=D_K`, and the squeeze proves `W_K->1/4`.  The unique-equilibrium
lower example also makes the same asymptotic lower bound valid if one instead
defines a best-equilibrium selection value `sup_r inf_(q in NE_K(r)) Expl(q)`.
There is no hidden exchange of a supremum and infimum.

This conclusion re-solves the full timing game at each `K`; it says nothing
about holding an earlier selected law fixed.

## 5. Three-date hierarchy cutoff

The selected three-date laws are literal actual finite-clock centers.  Their
diagonal midpoints have objective zero and distance at most

\[
 c_3/2=10-4\sqrt6.
\]

For Fin4, `12/59` is strictly larger and `12/60` strictly smaller.  The
integer checks are correct:

\[
6\cdot118^2=83544>83521=289^2,
\]

and

\[
96<2401/25.
\]

The same actual center therefore lies in every outer neighborhood through
level `59`, proving `L_M=0` for `M<=59`.  The source correctly says only that
this producer ceases to certify level `60`; it does not infer positivity.
As in the prior hierarchy packets, a Lean formulation through the current
checked lower-value API must retain
`HasEscapeAwareQuantileClockCompression reward` until that ordinary exported
input is integrated.

## 6. Fixed-prefix Section 8

The current wording contains Ramsey's required literal scope repair.  It
preserves the active players' date-zero hazard `1/4`, conditional date-one
hazard `1/3`, their joint post-prefix survival mass `1/4`, and dummy Continue
through those dates.  It does **not** claim to preserve the former complete
planned-time laws: their old Never branches are deliberately opened into an
arbitrary finite-support product behavioral tail.

For the table

\[
 r_1(S)=-1\ \text{iff}\ \{1,2\}\subseteq S,
 \qquad r_1(S)=1\ \text{otherwise},
 \qquad r_2=-r_1,
\]

the hard-tail active matrix is exactly the reviewed sharp matrix, and the
equilibrium-specific dummy argument again forces both dummies to Never in the
source game.  The unique active source law is `(1/4,1/4,1/2)` with payoff
`(1/2,-1/2)`.

Let `g in [-1,1]` be player 1's conditional prescribed tail payoff.  Only
joint active survival through the fixed prefix reaches that tail, so

\[
 U_1=1/2+g/4,
 \qquad U_2=-1/2-g/4.
\]

A player-1 pure quit time strictly after the appended finite support is worth
exactly one.  If someone has exited, player 1 is absent and the quitting
coalition cannot contain both active players; if nobody exits, player 1 quits
alone.  This remains true when dummies activate.  Hence

\[
 B_1-U_1\ge1/2-g/4\ge1/4.
\]

This one explicit pure-time deviation already proves an unrestricted debt
lower bound; pure-time extremality is compatible but not needed for the lower
direction.

The global comparison is also exact.  If both active players discard the
prefix and use independent uniform clocks on `L` dates, a tie has probability
`1/L`; player 1 has payoff `1-2/L` and cap one, while every pure time of player
2 in the window has its prescribed value `-1+2/L`.  Dummies have zero debt.
Thus the total exploitability is exactly `2/L->0`.  Section 8 is a
fixed-prefix obstruction, not a positive-gap table and not a barrier to
globally reselected finite clocks.

## 7. Novelty and disposition

A narrow search found no checked declaration or prior packet with the
general function `f_K`, the exact third-date constant, the worst-table quarter
limit, or the current fixed-prefix arbitrary-tail barrier.  The checked
`QuittingFiniteDeadlineNashProfile` lane consumes a supplied profile and gives
an escape-charge upper bound; it does not construct the timing Nash law or
derive this table-uniform summation.

The two independent unrestricted reviews now agree.  I recommend a narrow
export packet for the core finite-deadline theorem and asymptotic architecture
ceiling, with Section 8 either included as a separately scoped theorem or
packetized separately.  The handoff must preserve the distinction among
fresh re-solution, fixed-prefix tail attachment, and arbitrary non-Nash
finite-clock selection.
