# Review of signed-causal rectangle orientation/compiler boundary

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY`](../notes/CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md)  
Verdict: **REVISE -> PASS after the current-head passport, minimality, and
novelty repairs; internal/no export**  
Date: 2026-08-26

## 1. Claim checked

The note classifies the positive rectangle atom

```text
(mass(target,T)-mass(source,T))*r_j(T)>0
```

by observer membership in `T`, singleton versus collision geometry, and the
sign of `r_j(T)`.  It then claims that the observer-absent finite and `Never`
clocks reduce to legal source deviations, a fixed Quit atom, or a sole
Continue-face-loss residual, and gives a punishment-normal rational `Fin 4`
example in which that loss has no positive matching source-action gain.

The displayed classification and regression are mathematically correct.  The
objection is to **exhaustiveness at the current source head**: the raw
Continue-face loss has already been strengthened to a certified literal
endpoint flip, the `Never` truncation and all-clock combination are already
checked, and the reward sign retains additional law/reset-face information.
Those facts do not themselves close the conjecture, but they must be retained
before this can be called the exact minimal orientation boundary.

## 2. Six cells and source/target orientation: PASS

Write `P_n` for the mover-replaced target with the common pure-time observer
response and `Q_n` for the unchanged source with that response.  The packet's
atom is exactly

```text
A_n=(mass(P_n,T)-mass(Q_n,T))*r_j(T)>0.
```

Therefore:

- `r_j(T)>0` gives `mass(P_n,T)>mass(Q_n,T)` and puts the uniform mass lower
  bound on the literal target;
- `r_j(T)<0` gives the reverse inequality and puts it on the literal source;
  and
- `r_j(T)=0` is impossible by
  `QuittingStoppingLawVanishingDebtRectangleSequence.reward_ne_zero`.

The chronology is also exact.  If `j in T`, the pure-time clock is finite and
the selected event occurs at that stopping date, with `j` surely Quit at the
reached row.  If `j notin T` and the clock is finite, the event preempts the
observer strictly before its stopping date.  If the observer is `Never`, only
the latter geometry is possible and the terminal mass is the sum of its
finite stage masses.  None of these statements identifies off-path strategies,
and the note correctly declines to do so.

The six nonzero cells are exhaustive as a **set-theoretic partition**:

1. observer-containing nonsingleton, positive reward;
2. observer-containing nonsingleton, negative reward;
3. observer singleton, positive reward;
4. observer singleton, negative reward;
5. observer absent, positive reward; and
6. observer absent, negative reward.

The checked consumers named in Sections 3--4 match their endpoint directions:

- the positive collision uses the target endpoint, where the observer debt
  tends to zero, and
  `positiveCollisionMarkedTailDispatch_reachedRowLocalization` returns a
  canonical legal deviation on that same actual target profile;
- the negative collision uses the actual source endpoint in
  `negativeTargetAtomicDispatch_fixedActualSourceSubsequence`; the first arm
  has full-profile gain at least `mu*Gamma`, while the second stores the
  sure-Quit observer and negative blocker balance there;
- the singleton compression returns a static atomic toggle or exact deletion,
  not a source-row chronology; and
- the observer-absent forced-owner wall uses the sign-selected actual carrier,
  while only the owner-forced row is counterfactual.

The unrestricted-deviation language is accurate in these places.  The
reached-row and outsider arms use explicit legal behavioral deviations.  The
singleton toggle and fixed Quit atom are not called behavioral gains, and the
note explicitly records their weaker provenance.

## 3. Never-clock truncation and constants: PASS, but already checked

Let

```text
mu=(charge/4)/(card(QuittingTerminalOutcome I)*quittingRewardBound reward),
q=mu*Gamma.
```

The reward bound is positive because the selected reward coordinate is
nonzero.  For a `Never` observer, the carrier's `T` mass is a nonnegative
stage sum at least `mu`.  A finite cutoff therefore captures at least
`mu/2`.  Summing the pointwise wall gives

```text
q/2 <= outsiderOccupation + refusalOccupation.
```

Consequently either the outsider occupation is at least `q/4`, or the refusal
occupation is at least `q/4`.  The latter is collected by one legal owner
behavioral deviation with gain at least `q/4-delta`; it is not a rowwise
choice.

Applying the factor-six polarity theorem to outsider lower bound `q/4`
gives exactly

```text
q/24 <= card(I) * ContinueGain
```

or the corresponding `card(I)*powerset.card`-weighted fixed Quit atom, or

```text
q/(24*card(I x Bool)) <= fixedRectangleOccupation.
```

The sharp source/face split loses one more factor two, giving

```text
q/(48*card(I x Bool)) <= ContinueFaceLossOccupation.
```

Thus Proposition 5.1's arithmetic and finite-cut argument pass.

It is not new, however.  The checked file
`Research/Quitting/ObserverAbsentNeverClockTruncation.lean` already contains:

- `observerAbsent_neverClock_strategicSplit`, with the same half-mass and
  `q/4` split;
- `observerAbsent_neverClock_certifiedEndpointFlip`, with the same `q/24`
  and `q/(48*card(I x Bool))` scales; and
- `observerAbsent_anyClock_certifiedEndpointFlip`, combining finite and
  `Never` clocks.

Those results are stronger because the final loss is
`quittingFiniteCertifiedPacketContinueFaceLoss`, not merely the unrestricted
raw `quittingFiniteForcedOwnerContinueFaceLossOccupation`.  Please cite this
file and present Proposition 5.1 as a weaker corollary/rederivation, or replace
it by the checked all-clock theorem.  Section 8's statement that Proposition
5.1 is “the new theorem” is false at the current head.

## 4. The Continue-face loss is not the current minimal residual

Within the old baseline projection, the note correctly proves that the last
alternative is a Continue-face loss.  Current checked sources retain strictly
more information:

1. `Research/Quitting/CertifiedForcedOwnerEndpointFlip.lean` proves that a
   positive certified loss contains a literal supported row at which the
   selected action is best on the owner-Quit face and its Boolean opposite is
   best on the owner-Continue face.  This is a certified endpoint-flip
   passport, not an anonymous raw loss.
2. `observerAbsent_anyClock_certifiedEndpointFlip` retains that certification
   for both finite and `Never` clocks with the constants audited above.
3. For the positive observer-absent orientation,
   `Research/Quitting/PositiveRectangleResetFaceLawCausalDispatch.lean`
   supplies `exists_positiveObserver_carrierResetFaceLawPoint`; when the
   terminal is nonsingleton it further supplies
   `exists_positiveObserver_resetFaceConcentratedPacket_of_collision`.
   This uses the important alignment that the positive mass carrier is also
   the endpoint whose observer debt tends to zero.
4. For a negative observer reward,
   `Research/Quitting/NegativeRectangleResetFaceCompensation.lean` supplies
   target-endpoint compensation.  In particular
   `negativeObserver_harmonic_or_absorbingResetFaceCompensation` retains a
   positive `Never` or finite absorbing outcome on the zero-debt target
   endpoint, even though the displayed negative terminal mass lies on the
   source.

These declarations do not turn the endpoint flip or compensated law into an
exact Bellman edge, a return, or a regenerated rank.  They nevertheless show
that the phrase “deepest common residual” is too strong and that the two
observer-absent signs do more than “merely choose the carrier.”  The raw loss
is the sole leaf only after deliberately forgetting checked packet and law
fields.

Required scope repair:

- say **“sole residual of the weakened observer-absent baseline projection”**,
  not the sole residual of the six-cell compiler or current frontier;
- replace the last table column by the certified endpoint flip, while listing
  the sign-specific reset-face/compensation outputs conjunctively; and
- in the negative collision discussion, call `(4.8)` the source-row refusal
  residual, not the entire exact negative-orientation residual, because the
  same packet also has the target compensation output.

The positive-collision no-reentry branch, negative refusal branch, singleton
static toggle, observer-absent endpoint flip, and prescribed signed-window arm
remain distinct.  There is no mathematically justified sense in which every
one of them has been reduced to a common Continue-face-loss object.

## 5. Rational `Fin 4` regression: PASS

The table in Section 6 is exact.  For player `b`, against target `P`, the
pure-time values are

```text
time 0:  (1/2)*2+(1/2)*(-1)=1/2,
time >=1 or Never: (1/2)*1+(1/2)*0=1/2.
```

Against source `Q`, time zero gives `-1`, while every time at least one and
`Never` gives zero.  Pure-time extremality therefore gives unrestricted caps
`B_b(P)=1/2` and `B_b(Q)=0`; the prescribed time-two response is exact at both
endpoints.  This verifies arbitrary behavioral, late, mixed, and `Never`
deviations, not only the two displayed actions.

At target date zero,

```text
g_Q = r_b({a,b})-r_b({a}) = 1,
g_C = r_b({b})-0 = -1,
g_actual=(1/2)g_Q+(1/2)g_C=0,
rectangle=2.
```

With cutoff two, date one contributes zero and hence

```text
rectangleOccupation = (1/2)*(1/2)*2 = 1/2,
sourceGainOccupation = 0,
ContinueFaceLossOccupation = 1*(1/2)*1 = 1/2.
```

The punishment-normality check also passes.  Coordinates `a,c,d` are
identically zero.  Having `d` Quit surely makes every behavioral replacement
of `b` receive `-1`, so `P_b<=-1=r_b({b})`.  The same sure-`d` profile has
zero debt in every coordinate, proving `D_*=0`.  The note correctly does not
claim a positive minimum, a terminal exploitability witness, or a hard
residual.

The core local separation is not wholly novel.  It is already checked in
`Research/Quitting/ForcedOwnerContinueFaceLossSupportNoGo.lean` and sharpened
in `Research/Quitting/ObserverAbsentNegativeTargetAtomicSourceNoGo.lean`:
positive forced-owner curvature and supported face loss can coexist with an
exact source endpoint Nash and zero gain for both source actions.  Section 6's
new content is the explicit four-player chronological embedding together with
all-player punishment-normality.  The novelty claim should be narrowed to
that addition.

The same calculation also realizes the endpoint-flip description: the Quit
action has positive gain on the owner-Quit face and negative gain on the
owner-Continue face.  Thus the regression remains useful after the residual
is upgraded from raw loss to certified flip.

## 6. Disposition

**REVISE, internal only.**  No mathematical repair is needed for the six-way
sign/membership partition, the Never-clock constants, or the regression.
Mandatory repairs are source and scope repairs:

1. cite the already checked all-clock truncation/certified-flip declarations
   and remove Proposition 5.1's novelty claim;
2. replace global “sole/deepest residual” language by the scoped weakened-
   projection statement;
3. retain the positive reset-face law and negative compensation outputs in
   the orientation table; and
4. narrow Section 6 novelty to its punishment-normal `Fin 4` embedding.

After those changes, the note is a useful synthesis and exact regression,
but it does not merit a separate export: the strategic compiler is mostly a
composition of checked declarations, the all-clock theorem is already Lean
checked in stronger form, and the remaining new table is a local `D_*=0`
architecture boundary rather than a conjecture consumer.

## 7. Delta review of Proposition 8.1: PASS

I separately audited the later global-minimum reset lift.  This proposition
does materially strengthen the occupation-only discussion, and its constants
and orientation are correct.

For a finite observer clock,
`observerAbsent_finiteClock_strategicSplit` gives either the stated owner
behavioral deviation or

```text
q/2 <= O := sum_{t<stop} m_t F_t,
```

where `m_t` is the literal carrier's fixed-`T` stage mass and `F_t` is the
forced-owner outsider defect.  The stage events for fixed `T` are disjoint,
so `sum m_t<=1`.  Since the sum is finite and `O>0`, some positive-mass row
has `F_t>=q/2`; there is no division by a possibly small live probability and
no stopping-time cardinality loss.

At that exact date, use

```text
root = update (quittingProfileLiveRoot carrier t) owner (PMF.pure true),
continuation = quittingAllContinueProfileSpine carrier (t+1).
```

Thus `exists_halfBestEndpoint_excess_or_outsiderTransfer_of_forcedOwnerDefect`
is applied to the literal forced-owner root and the literal shifted suffix.
Its `source` and `target` are the two actual
`quittingRootThenContinuationProfile` semantic pairs; the target changes only
the selected outsider halfway toward its exact best endpoint.  This is exact
normalized reached-row provenance.  It is not the unmodified whole carrier
profile, and the note's Section 8.2 correctly records the consequent loss of
the original rectangle law/packet.

Writing `g` for the selected outsider's debt decrease and

```text
R=sum_{recipient != who}(d_recipient(target)-d_recipient(source)),
```

the adapter gives

```text
g>=F_t/2>=q/4,
D(target)-D(source)=-g+R.
```

If `R>=g/2`, the same-row signed transfer is at least `q/8`.  Otherwise
`D(source)-D(target)>g/2>=q/8`.  Since the target is an actual carrier pair,
global minimality gives `D(target)>=D_*`, hence
`D(source)>=D_*+q/8` in the descent arm.  The source/target direction in both
alternatives is correct.

For a `Never` clock, the checked finite-prefix strategic split supplies
outsider occupation `q/4` or owner gain `q/4-delta`.  Repeating the same
argument gives `F_t>=q/4`, `g>=q/8`, and therefore descent or transfer at
least `q/16`.  In `Fin 4`, the three coordinates other than `who` contain one
recipient with signed source-to-target increase at least `q/24` in the finite
case or `q/48` in the `Never` case.

The unrestricted-strategy scope is exact: the owner alternative is one legal
behavioral deviation collected over the original carrier, while the reset
alternative consists of literal behavioral root-prefix profiles.  The reset
source is counterfactual in the one precise sense that the terminal owner is
forced to Quit at the reached root.  Proposition 8.1 does not produce a
punishment-floor Nash--Bellman edge, preserve the atom/clock law, or regenerate
the tangent source; it honestly leaves a noniterable same-row transfer arm.

This delta does not remove the earlier **REVISE** verdict.  It should be kept
as a valid new composition once the current-head source/minimality repairs in
Sections 3--4 above are incorporated.  After those repairs, I have no further
mathematical objection to Proposition 8.1.

## 8. Final delta verification: PASS

The current note incorporates every mandatory repair from Sections 3--6 of
this review:

- the six-cell table now returns
  `observerAbsent_anyClock_certifiedEndpointFlip`, rather than presenting the
  raw Continue-face loss as the maintained residual;
- the positive observer-absent row conjunctively retains its zero-debt
  reset-face law point and, for a nonsingleton terminal, its concentrated
  packet;
- the negative observer-absent row conjunctively retains the target
  `Never`/absorbing compensation, and the absorbing arm's reset-face law;
- the negative collision discussion labels `(4.8)` only as the **source-row
  refusal** residual and separately records target compensation;
- the raw face loss is now expressly only the leaf of a deliberately weakened
  baseline projection;
- Proposition 5.1 is withdrawn as novelty and replaced by exact citations to
  the stronger checked finite/`Never`/all-clock declarations; and
- Section 6 narrows its novelty to the chronological, all-player
  punishment-normal `Fin 4` embedding of the already checked local
  face-loss/source-action separation.

Proposition 8.1 is also now scoped correctly as a contraction of the upstream
forced-outsider alternative.  Its reset profiles keep the literal forced
root and shifted continuation, but they do not preserve the original
rectangle atom, response clock, law passport, tangent producer, or iterability.
The note states all of these losses and does not identify the transfer edge
with the independently certified endpoint flip.

The exact residual is therefore no longer understated: the sign-specific law
passports and certified endpoint flip survive conjunctively, while the new
global-minimum reset lift supplies a separate descent-or-transfer contraction.
The source audit and novelty comparison match the current declarations.

One ministerial edit remains: Section 4.1 duplicates the sentence fragment
“deviation on the **same actual target profile** has gain at least.”  Delete
one copy.  This is not a mathematical or verdict-level objection.

Final verdict: **PASS, internal/no export**.  The reviewed synthesis is exact,
and Proposition 8.1 is a useful new bounded contraction, but its transfer arm
is noniterable and supplies no FIN4_BT consumer or regenerated source.
