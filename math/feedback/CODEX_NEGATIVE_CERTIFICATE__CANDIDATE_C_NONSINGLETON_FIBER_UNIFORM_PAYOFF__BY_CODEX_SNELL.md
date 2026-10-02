# Second falsification review of Candidate C nonsingleton fibre

Reviewer identity: `CODEX_SNELL`

Date: 2026-09-03

Frozen packet reviewed:
`/tmp/CANDIDATE_C_NONSINGLETON_FIBER_UNIFORM_PAYOFF.md`, SHA-256
`b324870a6639b507a5037f7adee7cbb4ab2cdc313d0abad77723dda9c63a5e6e`.

Verdict: **PASS.**  I found no mathematical objection.  This is an ordinary
mathematical review of the frozen export candidate, not a claim that its new
specialized construction is already Lean checked.

## Claim checked

For every Fin4 quitting reward table with the four displayed singleton rows
and arbitrary values in all 44 nonsingleton coordinates, the fixed vector

\[
 B=(1,-1/2,0,-1/4)
\]

is a uniform-equilibrium payoff.  The producer is one `2m`-phase periodic
profile for each requested accuracy; the Nash comparison ranges over every
unilateral behavioral replacement, including Never and arbitrarily late
stopping clocks.

## Algebra and orientation

Solving

\[
 x=\delta A+(1-\delta)y,
 \qquad y=\tfrac12B+\tfrac12x
\]

gives exactly the displayed `x` and `y`.  Recomputing all four coordinates
confirms that only player 1 lies below its own singleton payoff and that the
largest deficit is

\[
 \eta_\delta={\delta\over2(1+\delta)}
\]

at `x`.  The target distance at the chosen start `y` is exactly
`3 delta/(4(1+delta))`.

The micro-interpolant orientation is correct.  From

\[
 V_{j,k}=r(\{j\})+a_j^{-k}(V_{j,0}-r(\{j\}))
\]

one gets
`V_{j,k}=h_j r({j})+a_j V_{j,k+1}`.  The endpoint identities are
`V_(0,0)=x`, `V_(0,m)=y`, `V_(1,0)=y`, and `V_(1,m)=x`; hence starting at
owner 1 has terminal value `y`, as claimed.  Every microvalue is on the
closed segment between its two coarse endpoints, so the uniform singleton
floor is inherited without an extra interpolation error.

## One-sided Continue audit

The sign in the only non-Bellman-equality case is correct.  On owner 1's
block,

\[
 V_{1,k}(1)=B_1+a_1^{-k}(y_1-B_1),
 \qquad y_1-B_1<0,
\]

and `a_1^(-k)` increases with `k`.  Thus
`V_(1,k+1)(1) <= V_(1,k)(1)`.  Because all opponents Continue surely in an
owner's own phase, this is exactly the required Continue-branch inequality.
Owner 0's own coordinate is constantly 1, while every passive player's
Continue branch is the exact policy Bellman branch.  No phase or block seam
reverses these inequalities.

## Arbitrary deviations and deleted-player contraction

At a phase owned by `j != i`, a sure Quit by deviator `i` pays

\[
 (1-h)r_i(\{i\})+h r_i(\{i,j\}).
\]

The singleton floor and `|r_i({i,j})-r_i({i})| <= 2M` give the claimed
common error `eta_delta+2M hmax`.  At an owner's own phase, sure Quit is its
singleton payoff, so the same bound applies.

Adding the common error to the phase value produces a true time-dependent
Snell supersolution: passive Continue adds only opponent survival times the
error; owner 0 has equality; owner 1 uses the one-sided inequality above.
It therefore dominates every randomized action at every live history, not
only pure dates from a finite menu.

The full-cycle opponent-only survival factors are exactly

\[
 1/2\quad(i=0),\qquad
 1-\delta\quad(i=1),\qquad
 (1-\delta)/2\quad(i=2,3).
\]

They are all strictly below one because the construction fixes
`0<delta<1`.  Iteration consequently kills the bounded continuation residual
for Never, unbounded-support hazards, and clocks placed arbitrarily late.
The singular `delta=0` profile is never used.

## Fibre independence

Only prescribed singleton absorptions enter the Bellman cycle.  An arbitrary
nonsingleton coordinate enters solely when a passive deviator Quits in the
same phase as the active owner, and is multiplied by that microhazard.  The
global finite bound `M` absorbs all 44 such coordinates, after which `m` is
chosen depending on that table.  There is no hidden common-mesh assertion
over the unbounded fibre.  The coordinate count `60-16=44` is correct.

## Fixed target and uniform quantifiers

The order is valid: first choose positive `delta` for target error and coarse
Nash defect, then choose one `m` for the fixed table bound `M`, producing one
terminal approximate-Nash profile at that accuracy.  The checked declaration
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then selects one sufficiently accurate terminal profile and one horizon
threshold for each requested uniform error.  Its conclusion uses that same
profile simultaneously for every larger horizon and every behavioral
deviation.  No profile is selected after the horizon or deviation.

## Export boundary

The packet honestly labels the coarse Candidate C calculation, the weakened
Continue supersolution interface, and the specialized adapter as new
ordinary mathematics.  Existing Lean declarations cover the downstream
fixed-target consumer and the nearby exact-equality cyclic machinery, not the
new specialized theorem itself.  I found no source/consumer mismatch or
overclaim beyond that stated handoff boundary.

