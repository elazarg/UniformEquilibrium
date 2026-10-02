# Finite-deadline high-to-low edge barrier

Author: `CODEX_STRENGTHEN`

Status: **complete negative reduction for the checked and natural cap-ported
finite-deadline interfaces; generic retained-return and cap-port no-go
theorems are derived from checked declarations, with one new paper-level
cap-terminal compiler isolated; no export proposed.**

This note continues
[`CODEX_STRENGTHEN__POSITIVE_MINIMUM_HARD_RESIDUAL_ENDPOINT_BARRIER.md`](CODEX_STRENGTHEN__POSITIVE_MINIMUM_HARD_RESIDUAL_ENDPOINT_BARRIER.md)
and
[`CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md`](CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md).
It tests the finite-deadline, adjacent-censor, and retained-tail timing
constructions as producers of the literal endpoint-matched edge missing from
the finite-hazard-capacity recursion.

## 1. Question and verdict

Write

\[
 D(X)=\sum_i(B_X(i)-U_X(i)),\qquad
 D_* = \inf_XD(X)>0.
\]

The desired finite block has a literal terminal parent `Y`, a literal
prefixed child

```text
X = quittingLiteralRootStackProfile reward roots Y,
```

and, for fixed `delta>0` and `0<=epsilon<=delta/2`,

\[
 D(Y)\ge D_*+\delta,
 \qquad D(X)\le D_*+\varepsilon.                 \tag{1.1}
\]

If `roots` is an exact cap--Nash chronology, the checked folded scaling law
gives

\[
 D(X)=C D(Y),\qquad
 C=\prod_t c_t.
\]

Consequently, for `D(Y)<=D_max`,

\[
 1-C={D(Y)-D(X)\over D(Y)}
 \ge {\delta-\varepsilon\over D_{\max}}
 \ge {\delta\over2D_{\max}}.                    \tag{1.2}
\]

This is exactly the uniform charge needed by the proposed discrete capacity
rank.  The finite-deadline results inspected here do **not** produce (1.1)
on one exact cap chronology.

The obstruction is sharper than a missing estimate.

1. Exact censor-compatible Nash families already produce a uniform-equilibrium
   payoff.  They are unavailable in the positive-`D_*` branch.
2. Arbitrary adjacent finite Nash laws give metric separation and paid
   unilateral behavioral edges, but no cap--Nash prefix relation and no
   control of total debt at both endpoints.
3. Grafting a hard-deadline Nash law onto a retained tail does not preserve
   its Nash property: the `Never` payoff and deviation seams change.
4. If one instead Nashifies the retained-tail timing game over a sufficiently
   near-minimum actual tail, then every equilibrium with positive probability
   of reaching that tail is the all-`Never` timing law.  Its root word is all
   Continue and has zero charge.  Every nonidentity equilibrium has zero
   return to the retained tail.
5. Independently, any exact cap--Nash stack over a sufficiently near-minimum
   terminal tail is all Continue.  Thus adding the cap compatibility needed
   for (1.2) cannot repair a minimum-tail hard graft; it makes the graft inert.

The only surviving orientation is therefore an **incoming deadline block over
an independently selected off-minimum actual tail**.  No present
finite-deadline selector supplies that tail, a cap-compatible retained word,
and a near-minimum literal head simultaneously.

## 2. Exact cap chronology versus timing Nash

The relevant checked definition is `IsQuittingCapNashRootStack` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.
At every displayed root it tests Nash against the unrestricted behavioral cap
of the remaining executable suffix.  The checked theorem

```text
quittingTerminalDebtSum_capNashRootStack_eq
```

is the exact source of (1.2).

This is strictly stronger than the checked retained-tail endpoint notion
`IsQuittingLiteralExactRootStack`: there each root is Nash against the
prescribed payoff vector of the remaining suffix.  The distinction is not a
technicality.  The unrestricted cap can exceed the prescribed payoff, and
the whole purpose of semantic debt is to measure that difference.

The realization theorem

```text
isQuittingLiteralExactRootStack_of_retainedTailMixedNash
```

in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`
produces the endpoint-Nash stack, subject to positive `Never` mass for every
player.  It does **not** produce `IsQuittingCapNashRootStack`.  Therefore even
a nontrivial retained timing equilibrium would not by itself justify the
debt scaling used in (1.2).

Conversely, the near-minimum cap rigidity used in the preceding note says
that any exact cap stack over a sufficiently near-minimum tail is a replicate
of all Continue.  Hence the following repair is impossible in the
positive-minimum chamber:

```text
choose a near-minimum tail;
graft a nontrivial hard timing word onto it;
prove the word is an exact cap--Nash stack.
```

If the last line succeeds, the word is inert.  If it does not succeed, the
scaling and capacity charge are unavailable.

## 3. A sharp retained-tail timing dichotomy

The following is ordinary mathematics obtained directly from named checked
declarations.  The combined statement itself is not yet a named Lean theorem.

### Proposition 3.1: positive return forces the identity law

Let `I` be finite.  Let rewards be bounded in absolute value by `M>0`, assume
`D_*>0`, and let `tail` be an actual behavioral profile satisfying

\[
 D(\mathit{tail})\le D_*+e,
 \qquad
 r_i(\{i\})+\kappa\le U_i(\mathit{tail})\quad(\forall i),
 \qquad
 e<{\kappa D_*\over2M},                              \tag{3.1}
\]

where `kappa>0`.  Let `mixed` be an exact mixed Nash equilibrium of the
deadline-`N` retained-tail timing game over `tail`, and put

\[
 J=\prod_i \Pr_{\mathit{mixed}_i}(\mathrm{Never}).    \tag{3.2}
\]

Then

\[
 J>0\quad\Longrightarrow\quad
 \mathit{mixed}_i=\delta_{\mathrm{Never}} (\forall i),
 \quad J=1.                                          \tag{3.3}
\]

Equivalently, every nonidentity retained-tail timing Nash law has `J=0`.

**Proof.**  The checked theorem
`quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none`
identifies `J` with the joint survival of the literal timing word.  Every
factor in (3.2) is nonnegative.  If the finite product is positive, every
factor is positive.  The hypotheses of
`nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile` in
`Research/Quitting/RetainedTailFiniteTimingRecursion.lean` are then exactly
(3.1), the retained-game Nash hypothesis, and these playerwise positive
`Never` masses.  That theorem yields the first conclusion in (3.3), and the
product formula gives `J=1`.  Its contrapositive, together with `J>=0`, gives
the final assertion.  \(\square\)

Thus there is no intermediate returned block near the minimum: a Nash timing
word either returns with probability one and is semantically an all-Continue
self-loop, or it does not reach the retained tail at all.  In the second arm
the positive-reach conditioning used by
`isQuittingLiteralExactRootStack_of_retainedTailMixedNash` fails at at least
one player.  The selected tail then contributes zero on-path mass and cannot
serve as a retained, source-faithful endpoint of a renewable block.

This dichotomy also clarifies the checked return-floor packet.  An actual
mixed retained-tail Nash law unconditionally gives
`IsQuittingRetainedTailFiniteTimingNash` by
`isQuittingRetainedTailFiniteTimingNash_of_mixedNash`.  If the punishment and
tail-separation hypotheses of
`terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` are additionally
supplied, its positive lower bound makes `J>0`; Proposition 3.1 then forces
the all-`Never` law.  The missing Fin4 adapter is the construction of those
coordinate punishments and separation data from the hard-residual source,
but even if supplied this route certifies **inertness**, not a charged return.

### Orientation consequence

The actual-near-carrier selector
`exists_actualNearCarrierTail_of_uniformSingletonGap` can supply precisely a
tail satisfying (3.1) near a singleton-separated minimum carrier point.  It
therefore supplies the terminal endpoint on the wrong side of (1.1): exact
cap grafts over it are inert, and retained timing Nash grafts obey Proposition
3.1.

To obtain (1.1), the terminal retained tail must instead be the off-minimum
`Y`, while the head of the word must return near the minimum.  None of the
current retained-tail timing selectors selects such an off-minimum `Y` or
proves that the resulting low head is cap-compatible.

## 4. What adjacent deadlines actually provide

Let `p` be an exact Nash law at deadline `N` and `q` one at deadline `N+1`.
The checked adjacent-deadline chain gives:

* the old hard profile's coordinate debt as a positive-part boundary gain
  (`QuittingAdjacentDeadlineGapSource.oldDebt_eq_boundaryGain_pospart`);
* a boundary-participation versus censoring-error split
  (`QuittingAdjacentDeadlineGapSource.censoredError_or_boundaryParticipation`);
* the total-debt-to-adjacent-TV estimate
  `quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV`;
* after hybrid localization, either
  `QuittingFiniteDeadlinePaidOwnTimingEdge` or
  `QuittingFiniteDeadlinePaidResponseSquare`.

The own-law edge is a literal one-player update of actual behavioral
profiles.  Its mover cap is unchanged and

```text
target mover debt
  = source mover debt - mover payoff gain.
```

This is checked by `targetProfile_eq_update`, `bestResponseValue_eq`, and
`semanticDebt_eq_sub_payoffGain` in
`FiniteDeadlineTimingHybridDispatch.lean`.  It does not control any other
player's cap or payoff, so it does not imply a decrease of total `D`.  The
response-square arm does not even assert a sign for the mover's payoff
change; its exact debt transport is only coordinatewise.

Moreover, the adjacent lower bound is absolute debt/metric information, not
excess above `D_*`.  Under a terminal gap it says that every adjacent Nash
pair is separated in total variation.  It gives neither

\[
 D(\text{source})\ge D_*+\delta
 \quad\text{nor}\quad
 D(\text{target})\le D_*+\varepsilon.              \tag{4.1}
\]

The endpoint laws are Nash in two distinct finite normal-form games and are
not a parent and its cap--Nash prefixed child.  Even exact censor equality
only says that the complete stopping laws agree after deleting the last
calendar date.  It does not say that the exposed last-date root is Nash
against the unrestricted cap of a literal suffix.

### Absolute finite-deadline debt is not near-minimum debt

The checked existence theorem
`exists_finiteDeadlineTimingNash_terminalDebt_le` supplies at every positive
deadline a hard timing Nash profile with each coordinate debt at most

\[
 M\left({1\over4}+{2\over N}\right).                \tag{4.2}
\]

This is an absolute reward-scale ceiling.  Its limit is `M/4` per coordinate,
not `D_*`, and it does not match profiles at consecutive deadlines.  Thus it
cannot provide the low endpoint in (4.1).

## 5. Why projective compatibility is not the missing edge

The checked structure `QuittingFiniteDeadlineCompatibleNashFamily` consists
of one exact hard timing Nash law at every deadline and literal successive
censor equations.  Its checked consumer

```text
QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff
```

produces a uniform-equilibrium payoff against unrestricted behavioral
deviations.  More weakly,
`exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV` shows that
arbitrarily close adjacent pairs already suffice.

Therefore the positive-`D_*` branch cannot contain such a family, nor
arbitrarily close adjacent pairs.  Asking the finite-capacity recursion to
first manufacture full projective compatibility would solve the global
problem upstream, not construct a renewable edge inside the putative
counterexample.

The finite-chain structure
`QuittingFiniteDeadlineCompatibleNashChain` correctly isolates the weaker
finite datum.  Ordinary finite-game Nash existence supplies only
`HasDeadlinewiseQuittingTimingNash`; it supplies no censor equations.  The
compactness adapter from compatible chains of every finite length to a full
family is currently recorded only as the proposition-valued definition
`FiniteCompatibleChainsProduceProjectiveNashFamily`, not as a theorem.  Even
after proving it, failure to extend a compatible chain is a selection
obstruction, not the endpoint-matched cap edge (1.1).

## 6. Exact censor regression

`FinFourCensoredClockNullDirection.regressionCertificate` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourCensoredClockNullDirection.lean`
is an exact Fin4 warning against treating censored total variation as debt
progress.  It has adjacent exact Nash laws, positive exposed boundary gain,
and arbitrarily large normalized censored displacement, yet the old law and
the censored new law have:

* the same canonical terminal coalition law;
* zero operational effect distance; and
* exactly the same terminal semantic pair after every common retained-tail
  graft.

Thus no function of raw censored TV alone can yield either inequality in
(4.1), even after minimum-tail grafting.  The regression has `D_*=0`, so it is
not a counterexample to the positive-minimum conjecture.  Its valid role here
is narrower and exact: it rules out the proposed censor statistic as the
missing same-chronology charge.

The effect-sensitive repair produces a graft-visible paid participant edge,
but it remains the behavioral, coordinatewise object described in Section 4;
it is not an exact cap--Nash chronology and has no total-debt endpoint band.

## 7. Minimal surviving producer theorem

The finite-deadline lane can enter the capacity proof only through a theorem
with the following fields.  This is the minimal missing compatibility packet,
not a theorem claimed here.

### Incoming retained-deadline cap edge

From one hard-residual/source-history state, produce constants
`delta>0`, `epsilon>=0`, `2*epsilon<=delta`, `D_max<infinity` and:

1. an actual off-minimum retained tail `Y` with
   `D_*+delta <= D(Y) <= D_max`;
2. a finite deadline and a mixed timing law `mixed`, with literal root word
   `roots = quittingRetainedTailMixedTimingRootStack ... mixed`;
3. exact cap compatibility
   `IsQuittingCapNashRootStack reward roots Y` (or a direct theorem giving
   the identical folded total-debt scaling);
4. the literal head
   `X = quittingLiteralRootStackProfile reward roots Y` with
   `D(X)<=D_*+epsilon`;
5. an ancestry field saying `X` is the actual child of `Y` in the same
   extension-compatible source history, with every retained hard atom or
   source label transported rather than reselected.

Fields 1 and 4 give the endpoint orientation.  Field 3 gives (1.2).  Field 5
prevents the finite hazard capacity from resetting at regeneration.  A Nash
hypothesis for the retained finite timing game may be useful as a producer of
`roots`, but it cannot replace field 3.

The current results supply fragments on incompatible objects:

| Current object | Exact content | Missing for the packet |
|---|---|---|
| deadlinewise Nash | one hard Nash law per `N` | censor matching, retained tail, cap roots |
| adjacent Nash pair | TV boundary and paid behavioral edge | total-debt bands, prefix ancestry, cap roots |
| compatible family | all censor equations | impossible under `D_*>0`; already yields UE |
| hard law grafted to a near-minimum tail | exact payoff/seam identities | retained-game Nash and cap compatibility |
| retained-game Nash over a near-minimum tail | Proposition 3.1 | every positive-return law is inert |
| literal endpoint-Nash root stack | prescribed-payoff recursion | unrestricted cap recursion |
| exact cap stack over a near-minimum tail | exact debt scaling | necessarily all Continue |

This isolates the open task without hiding a reprojection: select an
**off-minimum** actual terminal tail and prove that one source-faithful,
cap-compatible timing word lands near the minimum at its literal head.

## 8. Declaration-level handoff

One small generic wrapper is justified independently of the missing producer:

```text
nearMinimum_retainedTailFiniteTimingNash_jointReturn_pos_iff_pureNever
```

under the hypotheses of
`nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile`, concluding
that positive joint survival is equivalent to the pure-`Never` law and that
every non-pure law has zero joint survival.  The proof is the finite product
argument in Proposition 3.1 plus
`quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none`.

A second useful negative wrapper would state:

```text
nearMinimum_nonidentity_retainedTailTimingNash_jointReturn_eq_zero
```

with the same hypotheses.  These are exact generic no-go declarations; they
do not solve the incoming off-minimum producer.

No Lean implementation is requested in this conference session.

## 9. Files and declarations inspected

Project guidance:

* `SOURCES.md`, `GOAL.md`, `docs/FRONTIER.md`, `docs/TOOLKIT.md`;
* `formalized/ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md`;
* `formalized/CENSORED_RESHUFFLE_NULL_DIRECTION_AND_EFFECT_SENSITIVE_PARTICIPANT_DISPATCH.md`;
* `exports/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`.

Checked source declarations:

* `QuittingAdjacentDeadlineGapSource.oldDebt_eq_boundaryGain_pospart` and
  `.censoredError_or_boundaryParticipation`,
  `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineGapSource.lean`;
* `QuittingFiniteDeadlinePaidOwnTimingEdge.targetProfile_eq_update`,
  `.bestResponseValue_eq`, `.semanticDebt_eq_sub_payoffGain`, and the
  corresponding `QuittingFiniteDeadlinePaidResponseSquare` declarations,
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingHybridDispatch.lean`;
* `quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV`,
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`;
* `QuittingFiniteDeadlineCompatibleNashFamily`,
  `exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV`, and
  `QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean`;
* `QuittingFiniteDeadlineCompatibleNashChain`,
  `HasDeadlinewiseQuittingTimingNash`, and
  `FiniteCompatibleChainsProduceProjectiveNashFamily`,
  `Research/Quitting/FiniteDeadlineCompatibleNashChains.lean`;
* `exists_finiteDeadlineTimingNash_terminalDebt_le`,
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`;
* `isQuittingRetainedTailFiniteTimingNash_of_mixedNash`,
  `quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none`, and
  `isQuittingLiteralExactRootStack_of_retainedTailMixedNash`,
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`;
* `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge`,
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`;
* `nearMinimum_rootNashAgainstPayoff_eq_allContinue`,
  `Research/Quitting/NearMinimumRetainedTailTimingNashIdentity.lean`;
* `nearMinimum_retainedTailFiniteTimingNash_eq_pureNever` and
  `nearMinimum_retainedTailFiniteTimingNash_eq_pureNeverProfile`,
  `Research/Quitting/RetainedTailFiniteTimingRecursion.lean`;
* `exists_actualNearCarrierTail_of_uniformSingletonGap`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticActualNearCarrierTail.lean`;
* `IsQuittingCapNashRootStack` and
  `quittingTerminalDebtSum_capNashRootStack_eq`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, together with
  `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` and
  `quittingRootSuccessorPayoff_eq_max_of_isZeroNash`,
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
* `quittingPunishmentValue_le`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
* `QuittingExactStationaryNashBellmanReturn` and
  `QuittingExactStationaryNashBellmanReturn.root_eq_allContinue_of_no_uniformPayoff`,
  `Research/Quitting/ExactNashBellmanRepairReturnTrichotomy.lean`;
* `FinFourCensoredClockNullDirection.regressionCertificate`,
  `UniformEquilibrium/Diagnostics/Quitting/FinFourCensoredClockNullDirection.lean`.

## 10. Residual before enlarging the architecture

At the level of the currently checked objects, do not attempt another
minimum-tail graft.  The remaining falsifiable question is:

> Can hard-residual provenance select an actual off-minimum tail `Y` and one
> finite retained timing word whose literal head is near-minimum, while every
> root is Nash against the unrestricted cap of its actual remaining suffix?

A counterexample should preserve `D_*>0` if possible.  A proof must expose the
source-history ancestry field explicitly; selecting a fresh minimum carrier
after the word is built does not decrease extension-compatible capacity.
Section 11 tests the strongest natural cap-ported projective enlargement and
shows that an exact censor-renewable implementation of this idea collapses to
a solved Nash--Bellman cycle.

## 11. Architecture beyond the current APIs

The preceding audit does not use the present Lean API as an architectural
boundary.  There is a natural stronger projective timing state.  Defining it
shows both the exact repair and why ordinary finite-deadline Nashification
does not gain new leverage.

### 11.1 The cap-terminal timing game

For an actual retained tail `Y`, let `B(Y)` be its unrestricted behavioral-cap
vector.  Define the length-`N` **cap-terminal timing game** as follows.  Each
player chooses a date in `{0,...,N-1}` or `Never`; the first nonempty quitting
coalition is paid from the quitting reward table, while the all-`Never`
outcome pays player `i` the terminal value `B_i(Y)`, not `U_i(Y)` and not
zero.

This is a finite normal-form game, so it has a mixed Nash equilibrium.  For
proof relevance, a cap-complete state records:

1. the conditional product root at every reached date;
2. the literal actual suffix obtained by grafting the remaining roots over
   `Y`;
3. the exact cap of that suffix; and
4. equality between that cap and the continuation value used at the preceding
   root.

All four fields are finite polynomial/maximum equations once the complete
finite response menus are included.  More importantly, they are consequences
of a positive-return Nash law in this particular cap-terminal game, rather
than independent axioms.  Thus this is a plausible finite proof-relevant
state, not an appeal to a nonexistent Lean object.

### Proposition 11.1: cap-complete timing is exactly a cap--Nash stack

Assume every player's `Never` mass is positive.  A mixed Nash law of the
cap-terminal timing game hazardizes to a literal
`IsQuittingCapNashRootStack reward roots Y`; the displayed cap-port equations
are derived along the way.
Conversely, every finite cap--Nash root stack with positive Continue mass
encodes a mixed stopping-time law which is Nash in this cap-terminal game and
satisfies the cap-port equations.

**Proof sketch.**  Condition the timing law on joint survival of the current
date.  Positive `Never` mass makes every displayed conditional law defined.
The ordinary normal-form deviation inequalities imply that the current
Boolean root is Nash against the equilibrium continuation value of the
conditional tail.  Backward induction starts from `B(Y)`.  At the induction
step, the already compiled conditional tail is a cap--Nash stack, so its
cap is its cap-game equilibrium continuation value.  Thus the current root
is an exact cap root and its successor payoff is the next literal suffix cap.
This simultaneously gives the cap stack and all port equations.

In the reverse direction, encode each player's conditional Quit hazards as
one law on finite dates plus `Never`.  Root Nash at each suffix rules out every
pure stopping-date deviation and the terminal-cap deviation; affinity then
rules out every mixed timing deviation.  The cap of a prefixed suffix is the
root best-response value, which equals the cap-game equilibrium value at an
exact root, giving the port equations.  \(\square\)

Under `D_*>0`, the checked
`capNashRootStack_continueMass_pos_of_debtSumInf_pos` already guarantees
positive total Continue product for every exact cap stack.  Thus the positive
reach restriction in Proposition 11.1 loses no exact cap chronology in the
hypothetical counterexample branch.

There is also a direct zero-return dispatch.  Let `J` be the product of the
`Never` masses of a cap-terminal mixed Nash law.  If `J=0`, the artificial
terminal outcome `B(Y)` has zero on-profile weight, so the cap-game payoff is
the actual prescribed payoff of the literal retained-tail graft.  Against
fixed finite timing opponents, every unrestricted behavioral response is
either a finite stopping date before the deadline or passes the deadline and
then obtains at most `B_i(Y)`; conversely the latter supremum is approximable
by actual tail deviations.  Hence the finite cap-game best-response value is
exactly the unrestricted behavioral cap of the graft.  Nash then gives

\[
 D(\text{graft})=0.                                 \tag{11.0}
\]

Therefore `D_*>0` rules out `J=0` for **every** cap-terminal mixed Nash law.
Every such Nash law has positive `Never` mass for every player and falls under
Proposition 11.1.  This is an ordinary-mathematics cap-terminal compiler; its
zero-return equality (11.0) would need a new named Lean wrapper, but uses the
same finite-stop/pass completeness argument already present in the retained
timing realization files.

This proposition is the architectural no-go: the strongest finite timing
game that carries the exact unrestricted-cap field needed for (1.2) is just a
different encoding of the existing finite cap--Nash stack.  If the terminal
tail is in the near-minimum all-Continue basin, backward induction makes the
entire cap-terminal timing law pure `Never`.  If the cap-port equations are
dropped, a finite Nash law may be nontrivial, but it no longer supplies exact
debt scaling.

### 11.2 The only conceivable censor-compatible strengthening

There is one precise new projective state which appears to produce the
requested edge if its nontriviality can be forced.  Fix an actual tail
`Y`.  A level-`N` state consists of

```text
W = [r_0,...,r_(N-1)],
X_W = W * Y,
the exact cap at every literal suffix,
and IsQuittingCapNashRootStack reward W Y.
```

A tail-boundary extension appends a new root `s` immediately before `Y`:

```text
W  --->  W ++ [s].
```

For this to be a censor-compatible extension without invalidating the old
root certificates, require

\[
 s\text{ exact cap--Nash over }Y,\qquad
 B(s\star Y)=B(Y).                                  \tag{11.1}
\]

The second equality is the missing **cap-port compatibility**, much stronger
than equality of censored stopping laws.  It propagates backward through the
fixed old roots, so all upstream cap ports remain identical and `W++[s]` is
again an exact cap stack.  The two actual endpoints are literal same-source
profiles, with no reselected carrier:

\[
 X_W=W\star Y,qquad X_{W,s}=W\star s\star Y.         \tag{11.2}
\]

By exact scaling,

\[
 D(X_{W,s})=c(s)D(X_W).                              \tag{11.3}
\]

Thus any absorbing cap-neutral insertion satisfying

\[
 D(X_W)\ge D_*+\delta,qquad
 D(X_{W,s})\le D_*+\varepsilon,qquad
 2\varepsilon\le\delta                              \tag{11.4}
\]

is the requested same-chronology high-to-low edge, with charge at least
`delta/(2*D_max)`.  Its ancestry witness is simply the retained code
`(Y,W,s)`; no compact-limit reprojection occurs.

This is a concrete projective producer specification rather than an API
request.  However, the specification is impossible in the no-uniform-payoff
branch.

### Proposition 11.2: absorbing cap-neutral insertion is already terminal

Let `Y` be any actual behavioral tail and put `b=B(Y)`.  Suppose `s` is exact
root Nash against `b` and

\[
 B(s\star Y)=B(Y)=b.                                 \tag{11.5}
\]

Then `(s,b)` is an exact stationary Nash--Bellman return with the punishment
floor:

\[
 b=\operatorname{Succ}(r,b,s),qquad
 s\in\operatorname{Nash}(r,b),qquad
 \operatorname{Pun}_i(r)\le b_i.                    \tag{11.6}
\]

If `s` has positive absorption, `b` is a uniform-equilibrium payoff.
Consequently, under the hypothesis that no uniform-equilibrium payoff exists,
every root satisfying (11.5) is all Continue.

**Proof.**  Exact cap Nash identifies the cap of the literal prefix with the
root successor payoff against the terminal cap; this is the semantic-envelope
identity
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
or equivalently the root `max` formula in
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` together
with `quittingRootSuccessorPayoff_eq_max_of_isZeroNash`.  Thus (11.5) is the
fixed-point equation in (11.6).  The root Nash field is assumed.  Finally,
`quittingPunishmentValue_le reward i Y` gives the punishment floor because
`b_i` is the unrestricted cap against the particular tail `Y`.

These data define a `QuittingExactStationaryNashBellmanReturn`.  The checked
theorem
`QuittingExactStationaryNashBellmanReturn.root_eq_allContinue_of_no_uniformPayoff`
then gives the last conclusion directly.  In its absorbing branch the same
proof repeats `s` as a period-one punishment-admissible cycle and compiles the
uniform payoff.  \(\square\)

The same argument applies to a finite cap--Nash macro `S` whose final cap port
returns exactly to its initial port.  The successive suffix caps form a
finite punishment-floor-admissible Nash--Bellman cycle.  If the macro has
positive absorption, periodic repetition is a uniform equilibrium.  Hence a
no-UE projective chain cannot append any nontrivial exact cap-port-preserving
boundary macro, not merely a one-root insertion.

This closes the apparently strongest censor-compatible repair.  The present
adjacent-deadline theorems do not force (11.1), and in the target branch they
cannot: their own-law edge preserves only the mover's cap, while every other
cap may change.  Exact censor equality records only calendar-law
compatibility.  If it were strengthened to the full vector cap-port return
needed to keep all earlier roots exact, Proposition 11.2 would make every
charged boundary extension terminal rather than renewable.

### 11.3 Elementary boundary check

Even the one-player cap-terminal root shows that (11.1) is not a formal
consequence of finite Nash existence.  Let the singleton quitting payoff be
`r` and the terminal cap be `b`.

* If `b>r`, all Continue is the unique root Nash: it is cap-neutral but inert.
* If `b<r`, Quit is the unique root Nash: it is absorbing but changes the cap
  from `b` to `r`.
* Only on the tie face `b=r` are absorbing cap-neutral mixtures available.

This example is not a positive-minimum Fin4 regression; one-player quitting
games are globally solved.  Its exact purpose is to show directly that the
new port equation is an indifference/fixed-point condition.  It cannot be
obtained from compactness, finite-game Nash existence, or censor compatibility
alone.  Proposition 11.2 says that forcing its vector version with positive
absorption would in fact finish the game rather than provide an internal
counterexample-side transition.

### 11.4 Two projective directions, neither silently interchangeable

There are exactly two natural ways to grow the finite word.

1. **Head extension:** replace `W` by `r::W` over the same actual tail.  This
   automatically preserves literal ancestry and is precisely the existing
   maximal cap-prefix ray.  Its strict finite-capacity arm has the checked
   stopping-clock escape/no-total-variation-limit obstruction.
2. **Tail-boundary extension:** replace `W` by `W++[s]`.  This is the direction
   represented by adjacent-deadline censoring.  It preserves the old exact
   cap roots only with the additional vector port equation (11.1), but every
   absorbing exact port return is already terminal by Proposition 11.2.

Reversing the order of roots to identify these operations changes the actual
chronology and is invalid.  A projective state therefore does not remove the
residual: head extension is exact but escapes, while censor extension is
compactly natural but preserves exact upstream caps only through a
cap-neutral return, whose absorbing branch is already terminal by Proposition
11.2.

The strongest honest outcome of this architectural attempt is consequently
a **closed route**, not a new producer: the cap-complete deadline state is
equivalent to the existing cap stack, and the exact cap-port equation needed
for renewable censor extension turns every charged macro into a solved
Nash--Bellman cycle.

A genuinely new deadline architecture must therefore allow the boundary
insertion to change the cap port and must simultaneously re-equilibrate every
earlier root.  To remain on one literal chronology it would need a triangular
compiler with explicit cap-change seams, actual suffix ports, and a summable
backward error budget.  Exact zero-seam compatibility is ruled out by
Proposition 11.2; ordinary adjacent-deadline Nash supplies no summable cap
seam.  This is the minimal architecture-level residual after allowing new
states and ancestry witnesses.
