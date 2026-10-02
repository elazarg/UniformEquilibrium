# Review of the persistent two-label hazard counterexample

Reviewer: CODEX_ROOT

## Claim reviewed

The note gives a finite quitting-game reward table with a distinguished player
`o` and claims that, on every bounded exact Nash--Bellman spine, every other
player has summable marginal Quit hazard.  It follows that no such spine has
two persistent labels.  The note also gives exact isolated roots with two
divergent nominal labels, showing that the failure is chronological rather
than a lack of local packet exposure.

## Verdict

**Accepted as ordinary mathematics.**  I found no unresolved mathematical
objection.  The main theorem is a complete negative answer to
`questions/PERSISTENT_TWO_LABEL_HAZARDS.md` as that question is currently
quantified over every reward table.  It does not answer the narrower question
restricted to a positive-minimum-debt or no-uniform-equilibrium branch, and the
note states this limitation correctly.

The present notebook is not yet an export packet: it still needs the standard
source-correspondence, semantic-audit, boundary-test, and Lean-handoff sections.
Those are packaging requirements rather than gaps in the argument.

## Verification of the main estimate

Fix a bounded exact spine and write `z_t = v_t(o)`, `p_t` for the owner's Quit
probability, and

\[
\beta_t=\prod_{j\ne o}(1-q_{t,j}),\qquad h_t=1-\beta_t.
\]

The owner's forced-Quit payoff is zero for every opponents' root.  Exact root
Nash therefore gives `z_t >= 0`.  If the owner is forced to Continue, the
outcome pays `-1` when some outsider Quits and otherwise reaches the successor
coordinate, so

\[
C_t=\beta_tz_{t+1}-h_t
   =z_{t+1}-h_t(1+z_{t+1}).
\]

Bellman evaluation gives `z_t=(1-p_t)C_t`.  The three cases in the note are
exhaustive and correct.

1. If `p_t=0`, Continue is used surely and exact Nash gives `C_t >= 0`.
   Bellman equality yields
   \[
   z_{t+1}-z_t=h_t(1+z_{t+1})\ge h_t.
   \]

2. If `0<p_t<1`, both actions have positive support.  Their endpoint payoffs
   must agree, hence `C_t=0=z_t`, and
   \[
   z_{t+1}=h_t(1+z_{t+1})\ge h_t.
   \]
   This identity also excludes the potentially singular case `\beta_t=0`.

3. If `p_t=1`, an outsider who Quits receives `-1`, whereas the same outsider
   forced to Continue receives `0`, even when other outsiders Quit.  Exact
   Nash therefore forces every outsider's Quit probability to be zero.  Thus
   `h_t=0`, `z_t=0`, and `z_{t+1}>=0`.

Consequently

\[
h_t\le z_{t+1}-z_t.
\]

Finite telescoping gives

\[
\sum_{t=m}^{n-1}h_t\le z_n-z_m.
\]

The canonical spine bound is `|z_t| <= quittingRewardBound reward = 1` for
this table, while `z_t>=0`; hence the nonnegative partial sums are bounded and
`\sum_t h_t<\infty`.  Since each outsider marginal is at most `h_t`, every
outsider marginal series is summable.  Every pair of distinct labels contains
an outsider, so no pair can be persistent.

This proof uses only the algebraic exact-spine contract.  It does not assume
that the continuation values are terminal values of an executable infinite
profile, so there is no hidden strategy-class restriction.

## Robust-transport check

The two transport exclusions are correct.  If an outsider's actual stream is
summable, a nominal divergent nonnegative stream can neither differ from it by
a summable absolute error nor be retained pointwise by any fixed positive
fraction.  Since every two-label choice includes an outsider, this rules out
both alternatives for every possible selected pair, not only for the displayed
labels in the local example.

## Independent check of the isolated packets

For the four-player root in the note, put

\[
s=1-\sqrt{1-\lambda},\qquad (1-s)^2=1-\lambda.
\]

Only `b` and `c` Quit, independently with probability `s`; `o` and `d`
Continue.  With successor owner value `\lambda/(1-\lambda)` and all other
successor coordinates zero:

- the owner's Quit endpoint is zero, while its Continue endpoint is
  `(1-\lambda)\lambda/(1-\lambda)-\lambda=0`;
- each of `b,c,d` has both endpoints equal to zero, because `o` never belongs
  to the current quitting coalition and every non-owner successor coordinate
  is zero.

Thus the current value zero and the stated root form an exact Nash--Bellman
edge.  The local joint charge is `\lambda`.  The one-player-deleted charges
are

\[
h_{-b}=s,\quad h_{-c}=s,\quad h_{-o}=\lambda,
\quad h_{-d}=\lambda,
\]

so every deleted clock has positive exposure, in fact at least `s`.  Moreover
`s=\lambda/(1+\sqrt{1-\lambda}) >= \lambda/2`; the two fixed nominal streams
therefore diverge for `\lambda_n=1/(n+3)`.

The packets cannot be concatenated while preserving those charges on a
bounded exact spine, because the proved inequality would make the owner's
coordinate increase by at least their nonsummable total outsider charge.  This
is the required local-positive/chronological-negative boundary test.

## Source and novelty audit

I checked the following interfaces and nearby regressions:

- `IsCanonicalExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
- `quittingRootSuccessorPayoff_eq_max_endpoints_of_endpointNash` and the
  endpoint formulas in
  `UniformEquilibrium/Quitting/Cycles/CycleMismatchContraction.lean`;
- `summable_quittingOpponentClockCharge_iff` and
  `hasTwoPersistentQuittingMarginals_iff_all_opponentClocks` in
  `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`;
- the canonical all-Continue phantom-spine regression in
  `NashBellmanClockReduction.lean`; and
- the general floor-violation summable-clock result in
  `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`.

The phantom regression proves only that one bad exact spine always exists; it
does not prove that a reward table admits no two-persistent exact spine.  The
floor-violation theorem has additional dynamic-debt and floor hypotheses and
does not state this table-specific all-spines obstruction.  A narrow phrase
and symbol search in these subtrees found no existing declaration that
subsumes the new theorem.

## Repairs requested before export

1. Replace “canonical reward-cube bound” by the exact statement
   `|z_t| <= quittingRewardBound reward = 1`.
2. Include the deleted-charge calculation above so that the local packet claim
   explicitly matches the question's packet-side requirement.
3. State the exact product-root, exact-spine, boundedness, and finite-player
   quantifiers in the packet rather than relying on project shorthand.
4. Add the source audit and a Lean handoff centered on the exact-spine
   potential inequality, followed by outsider marginal domination.
5. Preserve the current nonclaim: this refutes the unconditional universal
   two-label selector, not a disjunctive selector that may return an existing
   equilibrium and not a producer restricted to the positive-minimum source
   regime.

Subject to those presentation repairs, I recommend export.
