# Fin4 balanced common-response minimum-fiber attack

Author: `CODEX_EULER`

Status: **IN PROGRESS — producer attack, no theorem claimed yet.**

## Exact target

Work under one `Fin 4` terminal exploitability witness with gap
`Gamma>0`, positive global terminal-semantic debt minimum `D_*>0`, and one
`QuittingPositiveMinimumDebtTangentFamily frontier`.  Fix an active mover `m`
and an off-diagonal observer `o` selected before the rectangle disjunction.
At rank `n` write

\[
X_n=\texttt{frontier.source }n,
\qquad E_n=X_n[m\leftarrow\tau_n],
\]

where `tau_n=frontier.replacement mover n`, and choose the common pure-time
observer response supplied by
`exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise`.  Put

\[
Y_n=X_n[o\leftarrow q_n],
\qquad Z_n=E_n[o\leftarrow q_n].
\]

The required output is not another classification.  It must be a terminal
approximation/uniform payoff, a consumed cumulative exact return, a
contradiction to `D_*`, or a genuinely iterable natural-valued descent with
new literal source data.

## Declarations inspected

- `QuittingPositiveMinimumDebtTangentFamily`,
  `exists_positiveMinimumDebtTangentFamily_of_pair` —
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
- `QuittingStoppingLawCommonResponseWitness`,
  `exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise` —
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
- `quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
  and `...eq_of_minimum_sameDebtSum` —
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`.
- `QuittingStoppingLawResetCubeData` and its square identities —
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`.
- `stageFullBestEndpoint_zeroFace_exact_transfer` and
  `finite_stageFullBestEndpoint_cycle_signedCirculation` —
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumUnitResetCycle.lean`.
- `exists_concentrated_partialReset_sameProfile_twoFaceBridge` —
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTwoFaceBridge.lean`.
- `causalCollision_tailEscape_or_quantitativeBestEndpoint` —
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalNashDispatch.lean`.
- `quittingTerminalSemanticLawCarrier_isCompact` —
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.
- `quittingTerminalSemanticPair_eq_of_twoProper_lawLimits` and the one-proper
  boundary —
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.

The maintained target is
`questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`.

## 1. Exact four-corner data retained upstream

The full replacement satisfies

\[
d_m(E_n)\longrightarrow0,
\]

and the common response can be chosen with error `e_n->0` so that

\[
d_o(Z_n)\le e_n.
\]

The observer response gain at `E_n` exceeds its source debt plus the fixed
off-diagonal charge, up to `e_n`; the endpoint-minus-source response-gain
square has the same positive lower bound.  Every one of
`X_n,E_n,Y_n,Z_n` is a literal behavioral profile and hence has total debt at
least `D_*`.

The public rectangle structure forgets the response-gain inequalities and
the fact that `E_n` is the mover's near-best-response endpoint.  This attack
keeps all four literal profiles.

## 2. Independent two-parameter mixture is literal

Because the two reset coordinates are distinct, for `lambda,s in [0,1]` the
profile obtained by mixing `m` from `X_m` toward `tau_n` with weight `lambda`
and mixing `o` from `X_o` toward `q_n` with weight `s` is a literal product
profile.  Its four endpoint profiles are exactly `X_n,E_n,Y_n,Z_n`.

For fixed `lambda`, observer debt is affine in its **own** mixture weight:

\[
d_o(\lambda,s)=d_o(\lambda,0)-s\,G_o(\lambda),       \tag{2.1}
\]

where `G_o(lambda)` is the prescribed-payoff gain of the common response
against the mover mixture.  The cap is unchanged because the observer's
opponents are fixed.  Similarly, for fixed `s`, mover debt is affine in the
mover's own prescribed strategy only after fixing its cap against that
observer strategy.

The common-response square gives

\[
G_o(1)-G_o(0)\ge c-o(1),                             \tag{2.2}
\]

but it supplies no sign for `G_o(0)`.  Its positive part is bounded by
`d_o(X_n)`; the signed quantity may be order-one negative.  Hence a small
mover reset need not make the common response profitable.  Even when it does,
the newly created observer debt and `G_o(lambda)` are both order `lambda`, so
removing that debt can require `s` of order one.  The observer's strategy/law
may therefore move nonperturbatively while its payoff improvement is small.

This is the precise point at which a naive balanced-small-reset argument can
lose all control of the other debts.

## 3. Minimum-fiber chord geometry

For any one-player chord starting at an exact carrier minimum and ending on
the same total-debt fiber, current main proves coordinatewise affinity:

\[
d_i^\lambda=(1-\lambda)d_i^0+\lambda d_i^1.          \tag{3.1}
\]

Thus an interior mixture cannot have smaller positive-debt support than both
endpoints; its support is their union.  A strict support descent must occur at
an endpoint and must separately exclude every newcomer.  Balanced interior
mixing is therefore not itself a natural-valued support descent.

For a near-minimum source with excess `epsilon_n` and endpoint rise `R_n`, the
coordinate chord-curvature budget is only

\[
0\le(1-\lambda)d_i^0+\lambda d_i^1-d_i^\lambda
 \le \epsilon_n+\lambda R_n.                         \tag{3.2}
\]

It becomes useful only if the full endpoint rise is controlled.  The
four-corner common-response inequalities do not bound `D(E_n)-D_*` or
`D(Z_n)-D_*` from above.

## 4. Conditional two-strategy square and the cap-curvature loss

If the four corners additionally supplied the missing complementarity
conditions

\[
X_o\text{ best at }X,\qquad q_o\text{ best at }E,\qquad
\tau_m\text{ best at }X,\qquad X_m\text{ best at }Z,  \tag{4.1}
\]

then the selected two strategies of `m,o` form a finite `2 x 2` best-response
cycle and have a mixed Nash equilibrium in the restricted square.

However (4.1) still does not prove unrestricted Nash at the mixed profile.
For an arbitrary third strategy `a` of player `m`, endpoint optimality gives

\[
u_m(a,0)\le B_m(0),\qquad u_m(a,1)\le B_m(1).
\]

At an opponent mixture `s`, this only yields

\[
u_m(a,s)\le(1-s)B_m(0)+sB_m(1).                     \tag{4.2}
\]

The restricted equilibrium payoff can be strictly below the right side: the
difference is exactly a convexity/Jensen gap of the unrestricted cap.  Thus
even the completed four-corner complementarity square transfers the terminal
gap into cap curvature unless one proves cap affinity or adds a strategy
attaining both endpoint caps.

This check prevents an invalid finite-game shortcut.  The next active test is
whether the global-minimum equality forces this cap curvature to be paid by a
literal square that enters an already checked cumulative consumer.

## 5. Unit resets and why label recurrence is insufficient

Current main already proves that a full reached-row best-endpoint move which
kills its mover on a constant total-debt fiber transfers exactly the source
debt to the other coordinates.  A closed finite word is a positive **signed
debt circulation**, with every fixed coordinate telescoping to zero.  This
does not orient a monotone debt potential.

The stronger Fin4 hope is to retain, along the same word, the common-response
square and its actual marked row.  If a finite cycle of such rows can be made
tail-consistent, its nonzero cap curvature must either:

1. contribute a fixed reached Nash defect and hence an exact paid endpoint
   move; or
2. vanish on every face, in which case the finite two-strategy mixtures are
   unrestricted-cap affine and the restricted mixed Nash is unrestricted.

Neither implication is yet proved here.  The remaining work is to test the
tail-consistency of the cap-curvature term, not merely recurrence of debtor
labels.

## 6. The minimum fiber is floor-safe, but this does not orient a prefix

Punishment normality and the checked strict singleton separation imply, for
every pair `(U,B)` in the positive minimum fiber and every player `i`,

\[
 P_i\le r_i(\{i\})<U_i.                                \tag{6.1}
\]

Thus the whole minimum fiber is strictly punishment-floor safe.  This is an
immediate composition of
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` with the
same-table punishment-normal inequalities; it is not a new producer.

The conclusion cannot be applied directly to `X,E,Y,Z` as an admissible
edge.  A stopping-law replacement changes an actual strategy profile.  A
punishment-floor Bellman edge instead has the opposite data type: one product
root prefixes a supplied continuation pair.  Floor safety of the endpoints
does not manufacture this root or the equality
`current = quittingTerminalSemanticPrefix reward root tail`.

## 7. Why infinitesimal viability does not yet iterate

Suppose a reset column is flat.  The tangent extraction then gives a literal
partial reset with

\[
 D(\operatorname{Sem}(X_n^{h_n}))-D_*=o(h_n).          \tag{7.1}
\]

This is enough for a first-order tangent statement, but not for an Euler
iteration on the minimum fiber.  Compactness of the carrier and continuity
of `D` imply only

\[
 \operatorname{dist}(\operatorname{Sem}(X_n^{h_n}),K_*)=o(1),             \tag{7.2}
\]

where `K_*={D=D_*}`.  They do not imply an `o(h_n)` retraction error.  An
exposed compact face can have square-root contact with its supporting
hyperplane.  The stopping-law carrier is not known convex, and the projective
hyperplane projection need not be semantic.  Re-extracting at an arbitrary
nearby point of `K_*` therefore loses the literal reset direction and its
common-response row at first order.

This blocks the otherwise natural construction: integrate flat replacement
directions on `K_*`, switch movers when a debt reaches zero, and use compact
payoff recurrence to obtain a cumulative charged near-return.  The obstruction
is not recurrence; it is the absence of a source-preserving, first-order
minimum-face retraction.

## 8. Exact observer-debt curvature and the compensation it forces

For the four literal corners, self-update invariance of the observer's cap
gives the exact identity

\[
\begin{aligned}
 &d_o(Z_n)-d_o(E_n)-d_o(Y_n)+d_o(X_n)\\
 &\quad=-\bigl([U_o(Z_n)-U_o(E_n)]-[U_o(Y_n)-U_o(X_n)]\bigr).
                                                               \tag{8.1}
\end{aligned}
\]

Hence the common-response witness makes the observer-debt rectangle strictly
negative by the retained charge, up to its vanishing error.  If a scaled
two-reset square is tangent to the global minimum to first order, global
minimality forces compensating positive second-order debt curvature in the
other coordinates.  On `Fin 4` this localizes compensation to at most three
labels (and to at most two labels distinct from both mover and observer).

This still does not give a contradiction.  The checked reset-cube orientation
theorems turn the compensating curvature into another actual static edge or
pure-time witness switch, but not into a Bellman edge.  Iterating this routing
can cycle among the remaining labels, while every profile corner continues
to satisfy `D\ge D_*`.  No coordinatewise sign makes the total curvature
negative.

## 9. Compact-law tail resolution attempt

At a nonattained minimum, the selected-law theorem leaves the all-nonproper
limit (or the separately classified one-proper negative-singleton arm).  In
the all-nonproper case the joint all-Never atom has positive limiting mass.
Moving Never mass to a common late date changes the limiting semantic pair
only through that joint tail atom, up to a vanishing finite-tail error.  This
does produce a finite auxiliary timing problem on the tail face.

The tempting shortcut is to insert a Nash equilibrium of the one-stage tail
game.  It is invalid for unrestricted deviations.  If a player Continues at
the selected late date and all opponents also Continue, the player may Quit
one date later and obtain its singleton reward.  Thus the one-stage Continue
payoff `0` is not the unrestricted continuation cap.  Adding one more date
repeats the same defect; the resulting finite-deadline equilibria may escape
to later dates.  This is exactly the compact-law nonattainment seam, not a
finite replacement for it.

The full four-corner response data identify a negative debt curvature on this
tail face, but do not make the auxiliary finite-date Nash suffix diagonal.
Consequently this route has not produced an attained minimum source, an
admissible return, or a smaller support rank.

## Current disposition

No conjecture-facing conclusion has been proved.  In particular, this note
does **not** claim a new residual theorem, export candidate, or conditional
consumer.  The two remaining mathematically live possibilities are:

1. obtain a literal `o(h)` minimum-face retraction which retains the frozen
   common-response row; or
2. turn the compensating cap curvature in (8.1) into a tail-consistent exact
   prefix edge rather than another strategy-replacement edge.

Neither follows from the declarations inspected above.

## 10. Fixed-law variational problem: what is genuinely fixed

Let `mu` be the endpoint terminal-outcome law retained by the fixed-law
observer reset, and let

\[
 {\cal C}_{\mu,o}=
 \{(U,B):( (U,B),\mu)\text{ lies in the joint carrier and }B_o=U_o\}.
\]

The reward-moment theorem makes `U` a function of `mu`.  Consequently the
fixed-law minimizer minimizes `sum_i B_i` on this compact slice.  This is a
real variational statement, but it is not a convex program: the joint carrier
is the closure of product stopping-law profiles, and no checked theorem makes
`C_{mu,o}` convex under whole-profile mixtures.  Coordinatewise mixtures of
two players are executable, but their terminal law generally leaves the
fixed-law slice.

The complete response rectangle lives at the literal endpoint cluster in
this slice.  The fixed-law minimizer need not be the endpoint cluster.  Thus
the exact negative observer-debt rectangle curvature at the cluster cannot be
differentiated at the minimizer.  Sum-cap minimality only says that any
law-preserving observer reset is compensated by the other caps; it does not
transport the common pure-time response or its cross difference.

This rules out one tempting but invalid separation proof: a supporting
functional for the convex hull of the carrier supports the *linear* debt sum,
whereas the useful response square is the Jensen gap between a product
mixture and the convex average of its four semantic endpoints.  The two
objects have opposite data types and do not combine without a purification
map back to the same terminal law.

## 11. A positive collision law does not give two-proper realization

The positive collision orientation gives

\[
 \mu(S)>0,\qquad o\in S,\qquad |S|\ge2.
\]

It is nevertheless false that the fixed-law minimizer can therefore be
realized by `quittingTerminalSemanticPair_eq_of_twoProper_lawLimits`.  The
bridge retains the finite terminal-outcome law only, not coordinatewise weak
limits of the complete stopping laws.  For example, two players may both quit
surely at date `t_n -> infinity`.  Their terminal coalition has mass one for
every `n`, while both weak limiting clocks are Never and hence improper.

The relevant exact declarations confirm the mismatch:

- `QuittingStoppingLawRectangleJointAtomLimit` stores semantic/law limits in
  `RectangleResetFaceMinimizer.lean`; its law coordinate is only
  `QuittingTerminalOutcome -> Real`.
- `quittingTerminalSemanticPair_eq_of_twoProper_lawLimits` in
  `OpponentTightTerminalSemanticRealization.lean` requires coordinatewise
  convergence in `CompactStoppingLaw` and two proper limiting marginals.

Thus positive collision mass is enough to recenter an actual marked stage,
but not enough to realize the retained semantic point or make unrestricted
caps continuous there.

## 12. Recentered flow and the remaining executable test

At the literal marked stage, the observer's pure-time response is a sure Quit
action and the selected collision has fixed conditional mass after the
survival normalization.  The observer root defect tends to zero.  In the
minimum-cluster arm, the checked marked-tail dispatch localizes a fixed total
root defect among the other three players.

This gives a genuinely executable finite-stage repair problem.  If a
defective player outside the marked coalition is repaired to Quit, the marked
collision is preserved.  If the marked coalition has at least three members,
deleting one defective member also leaves a collision.  The only loss of
collision is therefore the sharp pair case

\[
 S=\{o,k\},
\]

with the defect concentrated on `k` and its repair choosing Continue.  The
reached root then becomes the singleton `{o}`.  Punishment normality and the
full-support packet supply a static outsider joiner, but subsequent repair can
move the sure owner again; this is exactly the finite strict-preemption cycle,
not yet an exact Bellman cycle.

The next test is not another sign bound.  It is whether the complete
common-response square supplies a common-tail invariant for this finite
repair cycle.  If it does, the cycle becomes a finite exact charged block.  If
it does not, the response square has no more chronological force than the
already-reviewed atomic collision handoff.  No completed output is claimed
at this checkpoint.
