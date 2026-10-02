# Exhaustive signed-causal rectangle orientation and the endpoint-flip boundary

Author: **CODEX_MINER**  
Status: **ordinary-mathematical synthesis plus exact local regression;
independent review PASS; internal/no export**  
Date: 2026-08-26

## 1. Question and answer

Fix a positive-global-minimum stopping-law tangent family, a terminal
exploitability witness with gap `Gamma>0`, and the literal source/target
profiles in a
`QuittingStoppingLawVanishingDebtRectangleSequence`.  The packet selects an
observer `j`, a nonempty terminal coalition `T`, and a positive signed atom

```text
(mass(target,T)-mass(source,T))*r_j(T)>0.           (1.1)
```

What does the exhaustive classification by `j in T` and the sign of
`r_j(T)` actually compile to?

The exact answer is:

1. `r_j(T)=0` is impossible.
2. If `j in T`, `|T|>1`, and `r_j(T)>0`, the literal **target** row feeds the
   checked marked-tail consumer, hence also its same-profile reached-gain
   localization.
3. If `j in T`, `|T|>1`, and `r_j(T)<0`, the literal **source** row feeds the
   checked negative-target atomic dispatcher: fixed legal outsider gain or a
   persistent observer-refusal certificate.
4. If `T={j}`, either sign feeds the checked singleton static dispatcher,
   which compresses to an atomic toggle or exact player deletion.
5. If `j notin T`, either sign feeds the checked forced-owner wall.  Current
   all-clock declarations reduce the wall to legal deviations, a fixed Quit
   atom, or a **certified endpoint flip** at a literal supported row.  The two
   signs also retain different conjunctive law data: positive reward gives a
   zero-observer-debt reset-face law point (and a concentrated packet for a
   collision), whereas negative reward gives positive-`Never` or absorbing
   target compensation and, in the latter case, a reset-face law point.

Thus membership and sign do give a complete **orientation compiler**, but
not a complete conjecture consumer.  If one deliberately forgets the
certification and the sign-specific law passports, the sole residual of that
weakened observer-absent baseline projection is
`quittingFiniteForcedOwnerContinueFaceLossOccupation`.  Section 6 gives an
exact rational Fin4 realization in which the entire positive forced-owner
rectangle is stored in that raw loss while the corresponding unrestricted
source-profile deviation gain is zero.  The same row is, correctly, a
certified endpoint flip.  The example is punishment-normal for every player,
so punishment-normality alone does not convert even that stronger passport
to a matching source action.  It has global minimum debt zero and therefore
does not refute a theorem using the full positive-minimum/Fin4 hard residual.

Section 8 does use that missing global-minimum field.  By returning to the
upstream forced-outsider alternative before the certified source/face split,
it adds a literal half-reset with either quantitative total-debt descent or
quantitative debt transfer.  This is an additional contraction of that
upstream alternative, not a replacement for the certified endpoint flip or
the positive-law/negative-compensation passports.  Its transfer arm is not
iterable: the reset does not preserve the rectangle packet, and debt support
can rotate on a fixed finite carrier.

An arbitrary signed window produced by the prescribed-payoff arm does **not**
have the pure-time common-response and vanishing-target-debt fields of the
rectangle packet.  It remains outside this compiler; Section 7 records the
exact interface boundary.

## 2. Input and same-profile provenance

Let `frontier` be a `QuittingPositiveMinimumDebtTangentFamily reward` and let
`packet` be a
`QuittingStoppingLawVanishingDebtRectangleSequence frontier`.  At rank `n`
write

```text
rho_n = frontier.source(packet.rank n),
chi_n = update rho_n packet.mover
          (frontier.replacement packet.mover (packet.rank n)),
zeta_n = pureTime(packet.observer,packet.quitTime n),

P_n = update chi_n packet.observer zeta_n,      -- literal target
Q_n = update rho_n packet.observer zeta_n.      -- literal source
                                                        (2.1)
```

These are actual behavioral profiles.  The atom in the packet is exactly

```text
A_n = (mass(P_n,T)-mass(Q_n,T))*r_j(T)>0,        (2.2)
```

with the same mover, observer, terminal, response clock, source, and full
replacement at every occurrence below.  No compact representative is
substituted for either profile.

Put

```text
mu = (packet.charge/4) /
       (card(QuittingTerminalOutcome I)*quittingRewardBound reward). (2.3)
```

The checked reward-bound lemmas give `mu>0`.  The atom sign gives the exact
mass polarity

```text
r_j(T)>0  => mass(Q_n,T)<mass(P_n,T),
r_j(T)<0  => mass(P_n,T)<mass(Q_n,T).             (2.4)
```

In particular the selected carrier is `P_n` in the first line and `Q_n` in
the second, and that carrier has terminal `T`-mass at least `mu`.

For the pure-time observer, membership fixes chronology:

- if `j in T`, the event occurs exactly at its finite stopping date, so the
  reached carrier root has `j` surely Quit;
- if `j notin T` and the stop is finite, the event is preemption strictly
  before that stop, so `j` literally Continues at every charged row;
- if the observer is `Never`, only the second geometry is possible and its
  terminal mass is the infinite sum of the finite preemption rows.

These are stopping-law identities, not off-path equality of the complete
strategies.

## 3. The exhaustive six-cell table

Since `T` is nonempty, `j in T` with `|T|=1` means `T={j}`.  The six nonzero
cells are:

| Geometry | Reward sign | Literal carrier | Checked output | What remains |
|---|---:|---|---|---|
| `j in T`, `|T|>1` | `>0` | target `P_n` | positive marked-tail dispatch and fixed-other reached legal gain | tail excursion / no re-entry |
| `j in T`, `|T|>1` | `<0` | source `Q_n` | fixed outsider legal gain or observer atomic refusal | refusal arm lacks a positive-to-negative reset word |
| `T={j}` | `>0` | target | atomic toggle or exact deletion | toggle is static, not source-row chronology |
| `T={j}` | `<0` | source | atomic toggle or exact deletion | same |
| `j notin T` | `>0` | target | all-clock deviations/atom/certified endpoint flip **and** target reset-face law; collision gives concentrated packet | endpoint flip has no matching actual-source gain or return |
| `j notin T` | `<0` | source | all-clock deviations/atom/certified endpoint flip **and** target `Never`/absorbing compensation | source flip/refusal and target compensation are not a common Bellman edge |

There is no zero-reward cell.  Indeed `(2.2)` would then be zero, contradicting
the positive atom lower bound.  This is the checked
`QuittingStoppingLawVanishingDebtRectangleSequence.reward_ne_zero` argument.

This table is an exhaustive disjunction, not a claim that the displayed
leaves are mutually exclusive.  It is the ordinary-language expansion of
`openOrientation_or_positiveTargetCollision`,
`refineOpenOrientation`, and
`exists_prescribed_or_orientationPreservingStrategicDispatch`.

## 4. Observer-containing rows

### 4.1 Positive collision: literal target and marked tail

Assume

```text
j in T,  1<|T|,  0<r_j(T).                         (4.1)
```

By `(2.4)`, target mass is at least `mu`.  Membership makes
`packet.quitTime n` finite and equal to the selected causal date.  The packet
also gives

```text
debt(P_n,j) -> 0.                                  (4.2)
```

Therefore
`positiveTargetCollision_markedTailDispatch`, equivalently
`exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`,
applies with the unchanged profiles `P_n`.  Along a strict subsequence its
literal after-row tails converge to a carrier point `cluster`, and either

```text
D(cluster)>D_*                                     (4.3)
```

or

```text
D(cluster)=D_*  and eventually
mu*D_*/2 <= sum_{i != j} rootNashDefect_i.          (4.4)
```

The nearby checked theorem
`positiveCollisionMarkedTailDispatch_reachedRowLocalization` freezes one
`i!=j` on a further subsequence.  Its one-stage best-endpoint behavioral
deviation on the **same actual target profile** has gain at least

```text
mu*D_* /(2*card(univ.erase j)) > 0.                 (4.5)
```

Thus this branch has a literal unrestricted-deviation compiler.  Neither
`(4.3)` nor `(4.5)` is a return to the original minimum source; the checked
files explicitly retain that re-entry boundary.

### 4.2 Negative collision: literal source and the refusal survivor

Assume

```text
j in T,  1<|T|,  r_j(T)<0.                         (4.6)
```

Now `(2.4)` puts mass `mu` on the literal source `Q_n`, not on `P_n` where
the vanishing observer debt is known.  The theorem
`negativeTargetAtomicDispatch_fixedActualSourceSubsequence` freezes one of
two alternatives without changing that source row:

1. one fixed outsider `i!=j` has coordinate Nash defect at least `Gamma`, and
   the canonical stage-best-endpoint behavioral deviation has full-profile
   gain at least `mu*Gamma`; or
2. at the same source roots, where `j` surely Quits,

```text
Gamma <= max(0,-quittingAtomicBlockerBalance(root,j)). (4.7)
```

The first arm is fully source-matched and unrestricted.  The second source-row
arm is not removed by `TerminalSemanticAtomicBlockerResetAdapter`.  That adapter's
finite-word trichotomy requires a word whose blocker balance starts
**positive** and ends at most `-Gamma`.  Here only the negative endpoint
`(4.7)` is supplied.  The half-best-endpoint theorem consumes a forced-owner
**outsider defect**, not a refusal.  Supplying a new positive start by
reselecting a cap root would lose the source row, terminal atom, and stopping
date.  Consequently the exact negative-collision **source-row refusal**
residual is:

```text
uniform source-stage mass + sure-Quit observer
+ blocker balance <= -Gamma,
but no source-matched positive-blocker predecessor.                 (4.8)
```

Punishment-normality does not provide that predecessor.  Its checked Fin4
consequence is a full-gap collision at each **singleton** row
(`exists_terminalGap_collision_at_singleton`), whereas `(4.8)` is a reached
nonsingleton row with a fixed tail.  This does not describe the whole negative
orientation packet: conjunctively,
`negativeObserver_harmonic_or_absorbingResetFaceCompensation` gives on the
literal zero-debt target endpoints either uniformly positive `Never` mass or
a fixed positive absorbing outcome different from `T`.  The absorbing arm
further has a checked reset-face law point.  No current declaration aligns
that target compensation with the source refusal in `(4.8)`.

### 4.3 Observer singleton

If `T={j}`, the reward sign only selects which profile carries mass.  The
counterexample witness's
`singletonStaticStrategicDispatch_compress` gives

```text
HasQuittingStaticAtomicToggleHandoff reward
or HasQuittingExactPlayerDeletionAtGap reward j Gamma.              (4.9)
```

Deletion is a strict player-cardinality descent and is excluded in a
cardinality-minimal counterexample.  In that regime only the atomic-toggle
handoff remains.  For the maintained punishment-normal Fin4 residual,
`exists_terminalGap_collision_at_singleton` independently supplies a
full-gap joiner at `{j}`.  It still does not identify the toggle/joiner with
the mover, the reached date, or either actual profile in `(2.1)`.  Thus the
signed singleton atom adds no source-matched chronology to the existing
static collision handoff.

## 5. Observer absence: the checked all-clock passports

Let `j notin T`, select the carrier from `(2.4)`, and choose the fixed
`owner in T` used by `observerAbsent_forcedOwnerDispatch`.  At every charged
preemption row the carrier root has `j` surely Continue.  Forcing only
`owner` to Quit retains the terminal cylinder and invokes the atomic-blocker
barrier.  Put

```text
q = mu*Gamma > 0.                                  (5.1)
```

The current checked theorem
`observerAbsent_anyClock_certifiedEndpointFlip` treats finite and `Never`
observer clocks together.  At the unchanged literal carrier and its literal
all-Continue spines it gives one of:

1. one unrestricted owner deviation (with the finite-clock scale and the
   universal all-clock weakening `q/4-delta`);
2. one fixed player's unrestricted Continue deviation;
3. one fixed player/coalition Quit-directed occupation atom; or
4. a fixed `(who,action)`, `who!=owner`, and finite cutoff with

```text
q /(48*card(I x Bool))
 <= quittingFiniteCertifiedPacketContinueFaceLoss
      reward carrier T owner who action cutoff.     (5.2)
```

The finite and `Never` constants inside the stronger theorem are exactly the
ones obtained by retaining all finite mass or half of the infinite stage sum.
In particular `observerAbsent_neverClock_strategicSplit` gives outsider
occupation or one legal owner deviation at scale `q/4`.  This is already
Lean checked in `ObserverAbsentNeverClockTruncation.lean`; the earlier raw-
loss Proposition 5.1 in this note was only a weaker rederivation and is
withdrawn as a novelty claim.

The certified loss in `(5.2)` is stronger than an anonymous occupation.
By `exists_literal_endpointFlip_of_positive_supportedLoss`, it contains one
literal supported time at which:

- the selected action is best on the owner-Quit face and has positive
  coordinate Nash defect there;
- the same action has negative gain on the owner-Continue face;
- its Boolean opposite is best on that Continue face; and
- the forced-owner rectangle is positive.

This is the current common observer-absent strategic survivor.  If one
forgets these rowwise certifications, it projects to the raw
`quittingFiniteForcedOwnerContinueFaceLossOccupation` used in Section 6.
That raw loss is therefore the sole leaf only of the **weakened baseline
projection**, not of the maintained frontier.

The sign retains further information conjunctively:

- if `r_j(T)>0`,
  `exists_positiveObserver_carrierResetFaceLawPoint` gives a limit in the
  terminal-semantic law carrier with observer debt zero and `T`-mass at least
  `mu`; when `T` is a collision,
  `exists_positiveObserver_resetFaceConcentratedPacket_of_collision` turns
  that reset-face law into a concentrated recurrent packet;
- if `r_j(T)<0`,
  `negativeObserver_harmonic_or_absorbingResetFaceCompensation` gives on the
  literal zero-observer-debt target endpoints either positive `Never` mass or
  a fixed positive absorbing outcome different from `T`; the finite
  absorbing arm has a checked law-preserving reset-face limit.

None of these declarations identifies the endpoint flip with the positive
law packet, the negative source refusal, or the negative target compensation
as one source-matched Bellman edge.  They must nevertheless be carried as
part of the exact residual interface.

## 6. Exact punishment-normal Fin4 face-loss realization

The Continue-face term cannot be deleted by an algebraic sign argument or by
punishment-normality alone.

Use players `a,b,c,d`; `b` is the observer and `a` the terminal owner.  All
payoffs of `a,c,d` are zero.  Player `b`'s rewards are:

```text
r_b(S)=-1                         if d in S;
r_b({a})=1,  r_b({a,b})=2,
r_b({b})=-1                       if d notin S;
r_b(S)=0                          otherwise.         (6.1)
```

In both displayed profiles `d` is Never, `c` Quits surely at date one, and
`b` Quits surely at date two.  The source `Q` has `a` Never.  The target `P`
has `a` Quit at date zero with probability `1/2` and play Never after
survival.  Thus, for `T={a}`,

```text
mass(P,0,T)=1/2,  mass(Q,0,T)=0,
(mass(P,0,T)-mass(Q,0,T))*r_b(T)=1/2.               (6.2)
```

This is a positive observer-absent pure-time rectangle stage.  The observer
is an exact unrestricted best response at both endpoints:

- at `P`, Quit at date zero gives
  `(1/2)*2+(1/2)*(-1)=1/2`, while Continue gives
  `(1/2)*1+(1/2)*0=1/2`;
- after survival, `c` Quits at date one for payoff zero, so no later or mixed
  behavioral response does better;
- at `Q`, immediate Quit gives `-1`, while Continue gives zero when `c`
  Quits, and all later choices give at most zero.

At the actual date-zero target root, use `owner=a`, `who=b`, and pure action
`Quit`.  The literal next-date tail payoff of `b` is zero.  On the two owner
faces,

```text
g_Q = r_b({a,b})-r_b({a}) = 1,
g_C = r_b({b})-0           = -1,
g_actual = (1/2)g_Q+(1/2)g_C = 0,
rectangle = g_Q-g_C = 2.                              (6.3)
```

For cutoff two, only date zero contributes to the `T={a}` cylinder, and the
definitions give the exact equalities

```text
quittingFiniteForcedOwnerRectangleOccupation =
  (1/2)*(1/2)*2 = 1/2,
quittingFinitePureActionSourceGainOccupation = 0,
quittingFiniteForcedOwnerContinueFaceLossOccupation =
  1*(1/2)*1 = 1/2.                                  (6.4)
```

So the positive rectangle is paid entirely by the counterfactual
owner-Continue face, while the corresponding pure action has zero gain
against the actual source profile.  This is exactly the last branch of the
sharp baseline identity, not a loose estimate.

Every player is punishment-normal.  For `a,c,d`, all own-coordinate rewards
are zero, hence punishment and solo values are zero.  To punish `b`, let `d`
Quit surely at date zero.  Whether `b` Quits with `d` or Continues while `d`
Quits, `(6.1)` pays `b` exactly `-1`; hence

```text
quittingPunishmentValue reward b <= -1 = r_b({b}).    (6.5)
```

The example has an exact zero-debt profile and therefore `D_*=0`; it is not a
Fin4 hard-residual counterexample.  Its exact scope is nevertheless useful:

```text
positive observer-absent rectangle
+ literal pure-time clock and exact observer best response
+ punishment-normality of every player
does not imply positive matching source-action gain.                 (6.6)
```

The core face-loss/source-action separation is already checked more strongly
in `ForcedOwnerContinueFaceLossSupportNoGo.lean` and
`ObserverAbsentNegativeTargetAtomicSourceNoGo.lean`.  The new content of
this regression is only its literal Fin4 chronology and simultaneous
punishment-normality for all four players.  It also realizes, rather than
refutes, the certified endpoint-flip sign pattern in Section 5.

Any theorem consuming the certified survivor `(5.2)` in the maintained hard
residual must use a
field absent here—positive global minimum, a source-connected reset word, or
an actual collision/preemption alignment—not merely punishment-normality or
the local terminal-gap wall.

## 7. Prescribed signed windows are a separate residual

The first arm of the stopping-law atom decoder compares

```text
rho_n  versus update rho_n mover replacement_n                 (7.1)
```

without installing a common pure-time approximate best response.  Signed
stage disintegration and the repaired sprinkler retain exact profiles and
produce a finite half-charge window, but they do not manufacture the packet
field `(4.2)`.  Therefore none of the marked-tail, negative-source, or
observer-absent packet declarations may be applied to `(7.1)` merely after
classifying membership and sign.

Two reviewed exact boundaries explain why:

- `FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO` puts a fixed positive signed
  atom entirely in unequal row reach while its marked normalized root is
  strategically neutral; its repaired scope allows an earlier
  first-disagreement consumer but refutes same-marked-row reprojection.
- `CounterfactualAtomExternalityRegression` has common reach and a literal
  one-stage mover update, but the positive observer atom is an externality:
  the observer has no positive unrestricted deviation and total debt merely
  rotates between labels.

Thus the exhaustive top-level output is

```text
prescribed signed-window comparison (still uncompiled)
or pure-time rectangle, classified by Sections 3--6.                (7.2)
```

## 8. A global-minimum contraction before the endpoint-flip projection

The endpoint-flip certificate in Section 5 is downstream of the aggregate
forced-owner outsider defect.  If the positive global minimum stored in
`frontier.base` is used on the forced-outsider arm **before** the later
source/face split, the half-reset adapter gives an additional
conjecture-facing output.  This route does not consume an already isolated
certified flip, and the reset it constructs does not retain the original
rectangle law or either sign-specific passport from Section 5.

Put `q=mu*Gamma` as in `(5.1)`.

### Proposition 8.1 (global-minimum reset lift of the observer-absent wall)

For one fixed rank of an observer-absent packet and every `delta>0`:

1. if the observer clock is finite, either the fixed owner has one legal
   behavioral deviation of gain at least `q/2-delta`, or there are one
   reached date, its literal owner-forced-Quit root and tail, and a half-best-
   endpoint reset of one outsider such that

   ```text
   D(source)-D(target) >= q/8                       (8.1)
   ```

   or

   ```text
   sum_{recipient != who} [d_recipient(target)-d_recipient(source)]
       >= q/8.                                      (8.2)
   ```

2. if the observer clock is `Never`, the same conclusion holds with owner
   gain `q/4-delta` and `q/16` in `(8.1)--(8.2)`.

Here `source` and `target` are actual terminal-semantic pairs of
`quittingRootThenContinuationProfile` at the selected normalized reached
suffix.  The source uses the packet's literal shifted continuation and the
literal root with the selected terminal owner forced to Quit; the target
changes only the selected outsider halfway toward its best endpoint at that
same root.  In `(8.1)`, global minimality gives additionally

```text
D(source) >= D_*+q/8                               (8.3)
```

in the finite-clock case, and the analogous `q/16` bound for `Never`.

For Fin4, `(8.2)` freezes one actual recipient with debt increase at least
`q/24` in the finite-clock case or `q/48` in the `Never` case.

#### Proof

For a finite stop, the checked
`observerAbsent_finiteClock_strategicSplit` gives either the owner deviation
or

```text
O = sum_{t<stop} m_t F_t >= q/2,                    (8.4)
```

where `m_t` is the literal carrier's `T`-stage mass and `F_t` is the
forced-owner outsider defect at its owner-forced-Quit reached root.  Since

```text
sum_{t<stop} m_t <= 1,                              (8.5)
```

some date has `F_t>=q/2`.  Notice that this selection loses no factor
depending on the stopping date.

At that root invoke
`exists_halfBestEndpoint_excess_or_outsiderTransfer_of_forcedOwnerDefect`
with `eta=F_t`.  Its displayed half-reset has a coordinate debt drop

```text
g >= F_t/2 >= q/4.                                  (8.6)
```

Let

```text
R = sum_{recipient != who}
      [d_recipient(target)-d_recipient(source)].    (8.7)
```

The exact coordinate identity in the adapter gives

```text
D(target)-D(source)=-g+R.                           (8.8)
```

If `R>=g/2`, then `(8.2)` follows from `(8.6)`.  Otherwise `(8.8)` gives
`D(source)-D(target)>g/2>=q/8`, proving `(8.1)`.  The target belongs to the
terminal-semantic carrier, so `D(target)>=D_*`; this proves `(8.3)`.

For `Never`, the checked
`observerAbsent_neverClock_strategicSplit` first chooses a cutoff with half
the terminal mass.  Its barrier/refusal split gives either the owner
deviation or outsider occupation `O>=q/4`.
Equations `(8.5)--(8.8)` then give `g>=q/8` and the two bounds `q/16`.

In Fin4 the recipient set has three members.  A sum of their changes at least
`c>0` has one coordinate at least `c/3`, giving the last assertion.  All
deviations used for the owner arm are unrestricted behavioral deviations;
all reset profiles in the other arm are literal behavioral profiles.  □

### 8.2 Exact transfer interface of this additional route

Proposition 8.1 avoids projecting the upstream forced-outsider arm down to a
Continue-face loss.  It neither replaces the checked certified endpoint-flip
branch nor consumes the positive reset-face law or negative target
compensation.  It also does not make its reset iterable.  In the transfer
arm:

- one debtor decreases and another increases at the same normalized reached
  source;
- total debt need not decrease;
- the recipient may already be in positive debt support;
- changing the outsider root generally changes the selected terminal law and
  destroys the fixed rectangle atom; and
- the output contains no regenerated tangent-family source.

These are not verbal possibilities.  At the exact output interface, the
four cyclic debt vectors

```text
(1,0,0,0) -> (0,1,0,0) -> (0,0,1,0)
 -> (0,0,0,1) -> (1,0,0,0)                         (8.9)
```

all have the same positive total `D_*=1`; every arrow drops the selected
coordinate by one and transfers one to a distinct recipient; support
cardinality stays one.  Thus positive minimum, total-debt nonincrease, and
finite support alone admit a transfer cycle.  This is an exact algebraic
model of the **post-reset debt interface**, not a claim that `(8.9)` is a
terminal-semantic carrier of an actual quitting table.  To turn `(8.2)` into
a well-founded rank, a new theorem must preserve the source/terminal packet
or forbid return to a previous debtor label.  No cited reset declaration has
such a field.

## 9. Source and novelty audit

Checked declarations/files inspected:

- `StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`:
  `openOrientation_or_positiveTargetCollision`,
  `positiveTargetCollision_markedTailDispatch`;
- `TerminalSemanticPositiveSlopeMarkedRowProvenance.lean`:
  `exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`;
- `StoppingLaw/OffDiagonal/PureTimeReachedRowLocalization.lean`:
  `positiveCollisionMarkedTailDispatch_reachedRowLocalization`;
- `StoppingLaw/OffDiagonal/StaticOrientationDispatch.lean` and
  `StoppingLaw/StaticStrategicCompression.lean`:
  singleton orientation and compression;
- `StoppingLaw/NegativeTargetAtomicDispatch.lean`:
  `negativeTarget_atomicDispatch` and
  `negativeTargetAtomicDispatch_fixedActualSourceSubsequence`;
- `StoppingLaw/ObserverAbsent/ForcedOwnerDispatch.lean` and
  `StoppingLaw/ObserverAbsent/FiniteClockDispatch.lean`:
  exact carrier, clock, forced-owner, and finite-clock dispatches;
- `Research/Quitting/ObserverAbsentNeverClockTruncation.lean`:
  `observerAbsent_neverClock_strategicSplit`,
  `observerAbsent_neverClock_certifiedEndpointFlip`, and
  `observerAbsent_anyClock_certifiedEndpointFlip`;
- `Research/Quitting/CertifiedForcedOwnerEndpointFlip.lean`:
  `exists_literal_endpointFlip_of_positive_supportedLoss` and its exact
  literal row passport;
- `Research/Quitting/PositiveRectangleResetFaceLawCausalDispatch.lean`:
  the positive carrier reset-face law point and collision concentration;
- `Research/Quitting/NegativeRectangleResetFaceCompensation.lean`:
  the negative target `Never`/absorbing compensation and absorbing
  reset-face law point;
- `Research/Quitting/ForcedOwnerContinueFaceLossSupportNoGo.lean` and
  `Research/Quitting/ObserverAbsentNegativeTargetAtomicSourceNoGo.lean`:
  checked core local face-loss/source-action separations;
- `TerminalSemanticForcedOwnerRefusalCollector.lean`,
  `StoppingLaw/ForcedOwnerDefectPolarity.lean`, and
  `StoppingLaw/ForcedOwnerRectangleBaseline.lean`:
  the finite refusal collector, factor-six polarity compiler, and sharp
  source/Continue-face split;
- `TerminalSemanticAtomicBlockerResetAdapter.lean`:
  exact hypotheses of the half-reset and finite blocker-word trichotomies;
- `Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`:
  the punishment-normal Fin4 singleton collision map;
- `Quitting/Classification/LCP/NormalPrincipalQBar.lean` and
  `Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  exact hard-residual and all-normal fields.

The six-cell classification, all-clock endpoint-flip theorem, and
sign-specific law passports are already checked in the cited files.  The
withdrawn raw Proposition 5.1 was a weaker rederivation, not new mathematics.
Section 6 contributes only the exact chronological/all-player-punishment-
normal Fin4 embedding of an already checked local separation.  Proposition
8.1 is the new ordinary-mathematical contraction: retaining the upstream
forced-outsider defect and applying the checked half-reset gives
quantitative total descent or a fixed Fin4 debt-transfer edge.  It does not
consume the isolated endpoint flip, preserve the original rectangle/law
passport, or make the transfer iterable.

Requested independent checks:

1. the sign/carrier and membership/time table;
2. the marked-tail and negative-source declaration matching;
3. the exact correspondence with the checked all-clock certified endpoint
   flip and both sign-specific law passports;
4. every unrestricted best-response assertion and equality `(6.2)--(6.5)`;
5. the exact profile provenance and `q/8,q/16,q/24,q/48` constants in
   Proposition 8.1;
6. the exact scope: no claim that the Section 6 regression satisfies `D_*>0`
   or the full Fin4 hard residual, and no claim that the algebraic cycle
   `(8.9)` is realized by a quitting table.

Independent review and required source/minimality repairs:
[`CODEX_RAMSEY review`](../feedback/CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY__BY_CODEX_RAMSEY.md).
