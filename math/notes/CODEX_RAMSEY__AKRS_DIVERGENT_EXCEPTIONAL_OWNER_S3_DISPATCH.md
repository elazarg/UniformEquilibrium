# AGKRS divergent exceptional owner: singleton-floor S.3 dispatch

**Author:** CODEX_RAMSEY  
**Status:** independently reviewed PASS; export packet assembled for a second falsification and whole-packet gate  
**Date:** 2026-08-25  
**Head audited:** `76479d5`

**Independent review:**
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH__BY_CODEX_EULER.md)

## Question and result

The negative-exceptional-owner obligation in
[`AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`](../questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md)
asks for an S.1/S.2/S.3 consumer of an actual
`QuittingDivergentNegativeExceptionalOwnerResidual`.  The checked local split

\[
  \mathrm{S.2}\quad\text{or}\quad
  r_o(\{o\})<P_o\quad\text{or}\quad
  \exists j\ne o:\ r_j(\{o\})<r_j(\{o,j\})
\]

looks as if it leaves two scalar arms.  The source's global Nash inequality
and its divergent-prefix concentration contain more information than that
split uses.

The result of this note is the stronger dispatch

> **Main theorem (ordinary mathematics, not yet Lean checked).** Every
> `QuittingUniqueExceptionalOwnerSource reward` whose selected horizons tend
> to infinity yields
> `QuittingInstantPunishmentεEquilibriumExistence reward` or
> `QuittingWellSupportedAbsorbingSequenceExistence reward`.

Consequently every `QuittingDivergentNegativeExceptionalOwnerResidual`
closes S.2 or S.3.  Neither its negative-solo field nor the outsider-join
alternative is needed.  In particular the purported floor-above-solo arm is
actually impossible at this source.

## Exact source audit

I inspected the following checked declarations and their files.

1. `QuittingUniqueExceptionalOwnerSource` and its literal family/selection
   fields in
   `UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`.
2. `QuittingDiffuseStationaryPrefixFamily`,
   `exists_fixedPlayer_strictMono_subsequence`, and
   `quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero` in
   `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`.
3. `QuittingUniqueExceptionalOwnerSource.tendsto_initialValue_soloReward` and
   `fixedOpponentsQuitValue_le_initialValue` in
   `UniformEquilibrium/Quitting/Classification/Existence/ExceptionalOwnerPrefixConcentration.lean`.
4. `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` and
   `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one` in
   `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`.
5. `abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` in
   `UniformEquilibrium/Quitting/Cycles/ConditionedDiffuseStrategicRescaling.lean`.
6. `quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing` in
   `UniformEquilibrium/Quitting/Cycles/SoloRootSequenceValues.lean`, and the
   solo endpoint formulas in
   `UniformEquilibrium/Quitting/Punishment/SoloQuitterEquilibrium.lean`.
7. `QuittingWellSupportedAbsorbingSequenceExistence` and its equivalence with
   S.3 in
   `UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`.
8. `quittingPunishmentValue_le` in
   `UniformEquilibrium/Quitting/Stationary/MinMax.lean` and
   `punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash` in
   `UniformEquilibrium/Quitting/Boundary/Holonomy/TwoOwnerCommonWordRealization.lean`.
9. `QuittingDivergentNegativeExceptionalOwnerResidual` and
   `instant_or_floorAboveSolo_or_joinGain` in the two checked negative-owner
   boundary files named in the question.

A narrow search found no existing singleton-floor S.3 theorem and no existing
consumer of the whole divergent exceptional source.  The closest theorem,
`isUniformEquilibriumPayoff_soloReward_of_soloFloor_of_punishmentIR`, produces
a uniform payoff by punishment completion and assumes owner punishment IR;
the elementary S.3 construction below neither needs that assumption nor
claims a terminal Nash profile.

## 1. The floor-above-solo arm is inconsistent with the source

Let `source` be a unique exceptional-owner source, let `o=source.owner`, and
assume its selected horizons diverge.  Write

\[
 V_n(i)=\texttt{quittingStationaryPrefixFamilyValue}
        (\texttt{source.selected }n)(0)(i),
 \qquad e_n=\texttt{source.family.error(source.selected }n).
\]

The family plan at index `source.selected n` is a full behavioral
`2e_n`-Nash profile.  Every behavioral profile has best-reply value at least
the punishment value.  Hence approximate individual rationality gives

\[
                       P_i-2e_n\le V_n(i).                 \tag{1.1}
\]

This is exactly the composition of
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash`,
`punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash`, and the
definition of `quittingStationaryPrefixFamilyValue`.

The selected errors tend to zero, while the checked whole-prefix
concentration theorem gives

\[
                         V_n(i)\longrightarrow r_i(\{o\}). \tag{1.2}
\]

Passing to the limit in (1.1) proves

\[
                              P_i\le r_i(\{o\})             \tag{1.3}
\]

for every player `i`.  At `i=o`, (1.3) is the opposite of the strict
`floorAboveSolo` arm.  Thus the first non-instant alternative in
`instant_or_floorAboveSolo_or_joinGain` cannot occur for a genuine divergent
source.  This argument uses the source's global unrestricted Nash field; it
does not require the punished label to equal `o`.

## 2. A singleton-floor compiler for branch S.3

### Proposition 2.1

Fix an owner `o`.  Suppose its singleton payoff vector dominates every
player's own singleton payoff in the corresponding coordinate:

\[
             r_i(\{i\})\le r_i(\{o\})\qquad\text{for every }i.       \tag{2.1}
\]

Then `QuittingWellSupportedAbsorbingSequenceExistence reward` holds.

### Proof

Let `M=quittingRewardBound reward` and fix `delta>0`.  Choose

\[
 q=\min\!\left\{\frac12,\frac{\delta}{4M+2}\right\}.
\]

Then `0<q<1` and `2Mq<delta`.  At every date use the same solo product row:
`o` Quits with probability `q`, while every other player Continues surely.
The sequence absorbs almost surely because its survival after `N` dates is
`(1-q)^N`.  By
`quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing`, every tail
continuation vector is exactly `r(\{o\})`.

At this continuation vector, `o`'s Quit and Continue endpoints coincide.
For `i != o`, the Continue endpoint is `r_i({o})`, while the Quit endpoint is

\[
       (1-q)r_i(\{i\})+q r_i(\{o,i\}).                         \tag{2.2}
\]

Using (2.1) and the reward bound,

\[
 \begin{aligned}
 &(1-q)r_i(\{i\})+q r_i(\{o,i\})-r_i(\{o\})\\
 &\qquad\le q\bigl(r_i(\{o,i\})-r_i(\{o\})\bigr)
 \le 2Mq <\delta.                                             \tag{2.3}
 \end{aligned}
\]

Thus both used actions of `o` are exactly optimal, and the sole used action
Continue of every other player is within `delta` of Quit.  This is precisely
`IsQuittingRootSequenceSupportApproxNash reward roots delta`.  Since the
sequence is completely absorbing, it is the requested well-supported witness.
As `delta` was arbitrary, S.3 follows.  Notice that no punishment-floor or
global terminal-Nash assertion is made: an owner with negative singleton
payoff can still gain by Continuing forever, which is irrelevant to the
literal S.3 predicate.

## 3. Dispatch of every divergent exceptional source

### Theorem 3.1

Let `source : QuittingUniqueExceptionalOwnerSource reward` and assume

\[
  \texttt{Tendsto (fun n => source.family.horizon (source.selected n))}
  \;\texttt{atTop atTop}.
\]

Then

\[
 \texttt{QuittingInstantPunishmentεEquilibriumExistence reward}
 \quad\lor\quad
 \texttt{QuittingWellSupportedAbsorbingSequenceExistence reward}. \tag{3.1}
\]

### Proof

First take a strict subsequence on which the finite label
`source.family.punished` is constant.  Next take a strict subsequence on which
the one-row joint Continue mass converges to some `lambda in [0,1]`.  All
source fields survive this combined strict reindexing, including horizon
divergence, vanishing error, and the concentration (1.2).

There are three cases.

#### Case `lambda=0`

The checked
`quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero` applies
to this literal family and combined subsequence.  This is S.2.

#### Case `0<lambda<1`

Apply
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` using the
constant punished label, the positive live limit, and the divergent horizons.
It returns a `QuittingPositiveLiveStationaryPrefixLimit` whose recorded live
mass is literally `lambda`.  Since this mass is below one,
`QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one` gives
S.3.

#### Case `lambda=1`

For every player `i`, let `Q_n(i)` be its immediate-Quit value at the selected
root.  Since joint Continue mass tends to one, player `i`'s opponents also all
Continue with probability tending to one.  Therefore

\[
                   Q_n(i)\longrightarrow r_i(\{i\}).          \tag{3.2}
\]

Quantitatively, joint Continue mass is at most the player-deleted Continue
mass, and
`abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` bounds the
error in (3.2) by twice `M` times the complementary deleted mass.

The checked source Nash consequence
`fixedOpponentsQuitValue_le_initialValue` says

\[
                         Q_n(i)\le V_n(i)+2e_n.                 \tag{3.3}
\]

Combining (3.2), (3.3), the concentration (1.2), and `e_n -> 0` yields

\[
                         r_i(\{i\})\le r_i(\{o\})              \tag{3.4}
\]

for every `i`.  Proposition 2.1 now gives S.3.

The cases exhaust `[0,1]`, proving (3.1).

## 4. AGKRS consequence

Given
`residual : QuittingDivergentNegativeExceptionalOwnerResidual reward`, apply
Theorem 3.1 to `residual.source` and `residual.horizon_tendsto`.  Its two
outputs already have exactly the codomain required by the `hnegative` input of
`theorem3_4_of_prioritizedSourceClosures`:

* S.2 maps to the instant-punishment disjunct;
* the well-supported output maps to the S.3 disjunct.

Thus the negative-owner source class is completely consumed.  The strict
negative singleton field and
`instant_or_floorAboveSolo_or_joinGain` become unnecessary for this consumer.
This does **not** close AGKRS Theorem 3.4: the prioritized pointwise residual
and positive-joint no-sure-exit residual remain.

## 5. Regression and boundary checks

1. **Collision can be arbitrarily favorable.**  In Proposition 2.1 take
   equality `r_i({i})=r_i({o})` and a maximal collision payoff.  No positive
   solo rate is an exact row equilibrium, but the defect is `O(q)` and the
   vanishing-rate S.3 construction remains valid.  This is why a sure-set
   enlargement is unnecessary.
2. **Negative owner payoff is allowed.**  If `r_o({o})<0`, the owner may gain
   by Never quitting from the complete infinite profile.  The construction
   claims only the literal sequential-perfect S.3 branch, not terminal Nash
   or uniform payoff.
3. **The live-one case is essential.**  If the live limit is below one, a
   limiting absorbing row already gives S.3 and no singleton-floor passage is
   needed.  The singleton floor is extracted only at the all-Continue face.
4. **The punishment label is not the owner.**  The proof first fixes the
   punishment label solely to invoke the positive-live compact-limit theorem.
   No equality between it and the exceptional owner is assumed.
5. **Empty and singleton player types.**  An exceptional source supplies an
   owner, so the player type is nonempty.  For one player the floor (3.4) is
   equality and Proposition 2.1 is the familiar positive-rate solo S.3
   sequence.

## Novelty and exact nonclaims

The new point is not another scalar split.  It combines the actual source's
live-mass compactification with an elementary singleton-floor S.3 compiler and
removes one of the three maintained source classes in the AGKRS capstone.
The punishment-floor impossibility (1.3) is also a direct source-native repair
of the current boundary description.

No claim is made that the constructed S.3 sequence is a terminal approximate
Nash profile, a uniform equilibrium, or a punishment-floor Bellman orbit.
No claim is made about either of the two remaining source classes in
`theorem3_4_of_prioritizedSourceClosures`.

## Requested independent falsification

Please check especially:

1. the unrestricted individual-rationality passage (1.1) and its exact
   identification with `quittingStationaryPrefixFamilyValue`;
2. Proposition 2.1 against the support-local—not weighted—definition, including
   negative owner payoff and the collision error `2Mq`;
3. the two nested finite/compact subsequence selections and preservation of
   horizon divergence;
4. the `lambda=1` implication from joint Continue to every player-deleted
   Continue mass and the limit passage in (3.2)–(3.4); and
5. the use of the `_with_liveMass_eq` compact-limit theorem rather than the
   target-free wrapper that discards the displayed equality.
