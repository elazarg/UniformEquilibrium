# Weak-core forced-pair collision normal form

Author: external contribution, corrected after independent audit

## Status

Ordinary mathematics with a Lean-facing construction plan.  The ingredients
named below are checked individually, but the composed source-retaining
wrapper and its two capstone declarations are not yet present in Lean.

The result is a strict Fin4 atlas contraction, not a completed consumer.  From
an arbitrary weak concentrated-singleton core it constructs a literal forced
pair packet whose only possible consumer output is the existing
collision-minimum residual.  That residual has an exact actual-tail normal
form.  On the cofinal owner-compressed minimum chronology, the off-minimum tail
arm disappears and no Boolean-action subsequence is needed.

The remaining minimum-tail output is a fixed-gain exact own-debt subtraction.
No total-debt descent, admissible return, terminal approximation, or
minimum-fibre support drop is proved.

## Question

Let

```text
source : FinFourMinimumAtomProducer reward bound
core   : FinFourAtlasWeakConcentratedSingletonCore source
```

The core supplies an actual target profile, a marked date, a singleton stage
atom of mass at least a fixed \(\lambda>0\), a literal reference profile, and
exact equality of the target and reference tails after the marked date.  Can
the core always be normalized to the collision-minimum branch of the checked
strong-packet consumer, without selecting a different reward table, minimum,
or post-date tail?

The answer is yes.  The hard residual supplies a fixed full-gap outsider for
the core's arbitrary singleton owner.  Pureifying the marked root and routing
that outsider forces the packet into pair mode.

## 1. Full-gap collision at every singleton

Write the core terminal as

\[
\texttt{core.singleton}=\{j\}.
\]

This owner is arbitrary: it may arise from the reached low-row origin or from
owner-clock compression.  The checked theorem

```text
FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton
```

applied to `source.residual` and \(j\) gives a player \(o\ne j\) such that

\[
r_o(\{j\})+\gamma\le r_o(\{j,o\}),
\qquad
\gamma:=\texttt{source.residual.witness.terminalGap}>0.
\tag{1}
\]

Thus \(o\)'s join at the singleton is strictly profitable by at least the
same gap \(\gamma\) used throughout the hard residual.  This is a theorem for
every singleton label; no finite pigeonhole or reselected source is involved.

## 2. Literal pureification and the forced pair

Put

\[
\tau:=\texttt{core.targetProfile},qquad
t:=\texttt{core.stage},qquad
\lambda:=\texttt{core.resolution}.
\]

Let \(L\) be the probability that the live history reaches date \(t\) under
\(\tau\).  Since the displayed singleton stage mass is one cylinder inside
that live event,

\[
L\ge
\Pr_\tau(\{j\}\text{ occurs at }t)
\ge\lambda>0.
\tag{2}
\]

Replace the entire marked product root of \(\tau\) by the pure root in which
exactly \(j\) Quits.  Call the resulting actual behavioral profile
\(\widehat\tau\).  This replacement has four exact properties:

1. every live root away from date \(t\) is unchanged;
2. the complete post-date live-root tail is unchanged;
3. the probability of reaching date \(t\) remains \(L\); and
4. the singleton stage mass at date \(t\) becomes exactly \(L\).

Now use \(o\) as the owner of a
`QuittingStageAtomConcentratedPacketAdapter` with source profile
\(\widehat\tau\), source terminal \(\{j\}\), marked date \(t\), and
resolution \(\lambda\).

At the pure singleton root, \(o\)'s Continue payoff is \(r_o(\{j\})\) and its
Quit payoff is \(r_o(\{j,o\})\).  The tail is irrelevant to both endpoint
values because \(j\) Quits surely.  Equation (1) therefore forces

\[
\texttt{adapter.action}=\texttt{true}.
\tag{3}
\]

The adapter's target profile \(\rho\) has the pure pair \(\{j,o\}\) at date
\(t\).  Its exact data are:

\[
\Pr_\rho(\{j,o\}\text{ occurs at }t)=L\ge\lambda,
\tag{4}
\]

\[
\operatorname{tail}_{t+1}(\rho)
=\operatorname{tail}_{t+1}(\widehat\tau)
=\operatorname{tail}_{t+1}(\tau),
\tag{5}
\]

and the marked root-coordinate defect of \(o\) is exactly zero.  The literal
unilateral payoff gain from the pure singleton profile to the pair profile is

\[
\begin{aligned}
U_o(\rho)-U_o(\widehat\tau)
&=L\bigl(r_o(\{j,o\})-r_o(\{j\})\bigr)\\
&\ge L\gamma\\
&\ge\lambda\gamma.
\end{aligned}
\tag{6}
\]

The generic adapter repeats \(\rho\) constantly and therefore gives an actual
`QuittingReprojectionConcentratedPacket` with fixed pair terminal, fixed
marked date, positive resolution \(\lambda\), identically zero normalized
owner defect, and any canonical positive scale tending to zero.

## 3. Required source-retaining wrapper

The construction must **not** be stored in the existing structure

```text
FinFourAtlasWeakStrongConcentratedPacket core
```

because that structure indexes its strong packet by `core.targetProfile`.
After pureification, the generic strong packet is instead indexed by
\(\widehat\tau\).  Those profiles are not equal unless the original weak core
already had a pure singleton marked root.

The correct object retains the weak core externally and indexes the strong
packet by the literal pureified profile.  Schematically:

```lean
structure FinFourWeakCoreForcedPairPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (core : FinFourAtlasWeakConcentratedSingletonCore source) where
  singletonOwner : Fin 4
  singleton_eq : core.singleton.val = {singletonOwner}
  collisionOwner : Fin 4
  collisionOwner_ne : collisionOwner ≠ singletonOwner
  collision_gain :
    quittingSetReward reward {singletonOwner} collisionOwner +
        source.residual.witness.terminalGap ≤
      quittingSetReward reward {singletonOwner, collisionOwner} collisionOwner
  pureSingletonProfile : (quittingGame reward).BehaviorProfile
  pureSingletonProfile_eq : pureSingletonProfile =
    quittingLiteralPureRootProfile reward core.targetProfile core.stage
      (quittingPureRootOfCoalition {singletonOwner})
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    pureSingletonProfile core.singleton core.stage core.resolution
  action_eq_true : strong.adapter.action = true
```

The exact spelling of the pure singleton root may use a dedicated helper
rather than the nonsingleton-only wrapper.  The essential dependent point is
that `strong` is indexed by `pureSingletonProfile`, while `core` remains a
field of the same object.

## 4. Collision residual is forced

Apply

```text
FinFourSingletonStageStrongConcentratedPacket.consumerResult
```

to the new strong packet and the original `source`.  Its strategic arm begins
with

```text
strong.adapter.routedTerminal.val = {strong.singletonOwner}.
```

But (3) and the checked routing geometry give

\[
\texttt{strong.adapter.routedTerminal.val}=\{o,j\},
\qquad |\{o,j\}|=2.
\tag{7}
\]

Hence the strategic arm is impossible.  The consumer necessarily returns

```text
Nonempty (QuittingConcentratedCollisionMinimumResidual
  reward source.point.1 collisionOwner
    strong.adapter.routedTerminal strong.adapter.packet).
```

This collision residual is attached to the original source and the exact
forced-pair packet.  It is not an existentially reselected packet.

## 5. Constant-packet cluster normal form

Let

\[
\sigma:=
\text{the literal all-Continue spine of }\tau\text{ after }t.
\]

The packet's profiles and marked dates are constant.  Pureification and the
one-coordinate endpoint update preserve all post-date live roots.  Therefore
the tail semantic sequence appearing in
`QuittingConcentratedCollisionMinimumResidual.tail_tendsto` is the constant
sequence at \(\operatorname{Sem}(\sigma)\).  Uniqueness of limits gives the
exact identity

\[
\boxed{
\texttt{collisionResidual.cluster}=\operatorname{Sem}(\sigma).}
\tag{8}
\]

By `core.postDateTail_eq`, this is also the post-date semantic tail of
`core.referenceProfile`.

The residual's `escape_or_otherDefect` field now becomes the exact split

\[
D_*<D(\operatorname{Sem}(\sigma))
\tag{E}
\]

or

\[
D(\operatorname{Sem}(\sigma))=D_*,
\qquad
\frac{\lambda D_*}{2}
\le
\sum_{p\ne o}\delta_p,
\tag{M}
\]

where \(\delta_p\) is the coordinate root Nash defect of the pure pair root
against the actual tail prescribed-payoff vector \(U(\sigma)\).  The actual
tail belongs to the carrier, so global minimality gives
\(D_*\le D(\operatorname{Sem}(\sigma))\); there is no third case.

In Fin4 the sum in (M) has three nonnegative terms.  Hence some \(p\ne o\)
satisfies

\[
\delta_p\ge\frac{\lambda D_*}{6}.
\tag{9}
\]

The live mass of the pure pair row is \(L\ge\lambda\).  Updating \(p\) at the
marked date to its exact best Boolean endpoint therefore gives a literal
whole-profile payoff gain

\[
g_p=L\delta_p
\ge\frac{\lambda^2D_*}{6}.
\tag{10}
\]

Because only \(p\)'s own behavioral strategy changes, its unrestricted
best-response envelope is unchanged.  Thus the update subtracts the gain
exactly from \(p\)'s terminal debt:

\[
d_p(\text{target})=d_p(\rho)-g_p.
\tag{11}
\]

The pair cannot be erased to the empty coalition by one endpoint update, so
the marked atom routes without losing its stage mass.

Equations (9)--(11) are executable one-date data.  They do not control the
change in the other three unrestricted caps.

## 6. Stronger cofinal owner-compressed contraction

The minimum-law singleton source retains more than one weak core.  Its checked
owner-clock producer supplies one fixed chronology and, for every requested
depth and every

\[
0<\lambda<\nu_*(\{j\}),
\]

an actual concentrated-singleton endpoint with a reference profile selected
cofinally far along that chronology.  The reference-profile debts converge
to \(D_*\) by

```text
FinFourMinimumAtomChronology.prefix_debt_tendsto.
```

Choose endpoints \(e_n\) with retained ranks tending to infinity.  For each
one:

1. form the two-profile cross-tail splice which copies the compressed target's
   literal live roots through its mark and then attaches its near-minimum
   reference profile \(\sigma_n\);
2. pureify the marked row to the fixed singleton \(\{j\}\);
3. use the same full-gap outsider \(o\) supplied once by (1); and
4. route \(o\) to its exact best endpoint.

The marked action is Quit at every rank, independently of the changing tails.
Consequently the moving family has:

* one fixed packet owner \(o\);
* one fixed terminal pair \(\{j,o\}\);
* one fixed mass resolution \(\lambda\);
* exact zero marked \(o\)-defect at every rank;
* literal post-row tail \(\sigma_n\); and
* \(D(\operatorname{Sem}(\sigma_n))\to D_*\).

This is a moving `QuittingReprojectionConcentratedPacket` with no Boolean
action subsequence.  Applying the concentrated consumer cannot return its
strategic arm because every routed terminal is the pair \(\{j,o\}\).  If a
collision residual chooses a tail cluster \(z\), continuity of total debt and
the last bullet force

\[
D(z)=D_*.
\tag{12}
\]

Thus arm (E) is impossible.  Eventually,

\[
\frac{\lambda D_*}{2}
\le\sum_{p\ne o}\delta_{n,p}.
\tag{13}
\]

After a finite-label subsequence, one fixed \(p\ne o\) satisfies

\[
\delta_{n,p}\ge\frac{\lambda D_*}{6},
\qquad
g_{n,p}\ge\frac{\lambda^2D_*}{6}
\tag{14}
\]

cofinally.  Every gain in (14) is an actual one-date behavioral gain with
exact own-debt subtraction and lossless marked-atom routing.

This is the strongest form of the result:

\[
\boxed{
\begin{array}{c}
\text{owner-compressed minimum-law singleton source}
\\[1mm]\Longrightarrow\\[1mm]
\text{source-matched moving pair packet with minimum-tail cluster}
\\[1mm]\Longrightarrow\\[1mm]
\text{cofinal fixed-gain exact collision transfers.}
\end{array}}
\tag{15}
\]

It strengthens the earlier minimum-return moving-packet construction in two
ways: the full-gap outsider fixes the Quit action at every rank, so neither an
action subsequence nor a surviving strategic-singleton branch remains.

## 7. Why the tail does not make the pair near-minimal

The pure pair row has two sure quitters.  Under every unilateral behavioral
deviation, at least one of them still Quits at the marked date.  Absorption is
therefore immediate, and the whole semantic pair of the forced-pair target is
independent of its post-date tail.

This is the exact channel switch:

* at a pure singleton, the singleton owner's Continue deviation exposes the
  tail cap;
* after forcing the outsider to Quit, every coordinate is governed by static
  pair-toggle rewards and the tail becomes unreachable under unilateral
  deviations.

Accordingly, (8) and (12) describe the residual's stored **tail cluster**.
They do not say that the forced-pair whole profile is on or near the minimum
fibre.  Replacing the tail cannot repair the pair's whole debt, and the fixed
gains (10) and (14) do not by themselves form temporal Bellman edges.

## 8. Exact remaining obligation

The result has removed the arbitrary singleton strategic mode and, in the
cofinal owner-compressed version, the off-minimum tail mode.  The remaining
object is:

\[
\boxed{
\begin{array}{c}
\text{a source-matched pure pair row of mass at least }\lambda,\\
\text{a literal post-row tail on the minimum fibre, and}\\
\text{a fixed coordinate endpoint gain at least }\lambda^2D_*/6,
\end{array}}
\tag{16}
\]

with exact mover-debt subtraction and no known aggregate cap control.

A completion still has to turn (16) into at least one of:

* a positive cumulative admissible return;
* terminal approximate Nash profiles;
* a regenerated minimum-fibre support drop; or
* another genuinely smaller atlas obligation.

It is not enough to repeat the pair profile, replace its tail, or use the
single-coordinate drain as total-debt descent.

## 9. Checked declarations used

The arbitrary-core normal form uses:

```text
FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton

FinFourAtlasWeakConcentratedSingletonCore.singleton_card
FinFourAtlasWeakConcentratedSingletonCore.resolution_le_stageMass
FinFourAtlasWeakConcentratedSingletonCore.postDate_liveRoot_eq
FinFourAtlasWeakConcentratedSingletonCore.postDateTail_eq

quittingProfileLiveRoot_literalPureRootProfile_of_ne
quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq

QuittingStageAtomConcentratedPacketAdapter
QuittingStageAtomConcentratedPacketAdapter.sourceStageMass_le_targetStageMass
QuittingStageAtomConcentratedPacketAdapter.targetTail_eq_sourceTail
QuittingStageAtomConcentratedPacketAdapter.ownerMarkedDefect_eq_zero
QuittingStageAtomConcentratedPacketAdapter.packet

FinFourSingletonStageStrongConcentratedPacket.routedTerminal_mode_and_card
FinFourSingletonStageStrongConcentratedPacket.consumerResult

HasQuittingConcentratedSingletonStrategicDispatch
QuittingConcentratedCollisionMinimumResidual

quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain
```

The cofinal strengthening additionally uses the interfaces around:

```text
FinFourMinimumAtomChronology.prefix_debt_tendsto
FinFourOwnerCompressedSingletonEndpoint.referenceProfile
FinFourOwnerCompressedSingletonEndpoint.target_stageMass_gt
FinFourOwnerCompressedSingletonEndpoint.targetProfile_postDate_liveRoot_eq
quittingSelfTailRootStack
quittingLiteralRootStackProfile
quittingProfileLiveRoot_literalRootStackProfile_of_lt
quittingAllContinueProfileSpine_literalRootStackProfile_length
```

This is not the one-argument `quittingSelfTailClosure` of the compressed target:
that operation would restart the same generally non-near-minimum target.  The
required object is the two-profile literal root-stack splice whose prefix roots
come from the compressed target and whose successor is `referenceProfile`.
The existing `FinFourSelfTailLowRow` theorems provide checked examples of the
underlying root-stack identities, but no existing declaration packages the
moving forced-pair family in (15).

## 10. Lean handoff

Suggested declarations, in dependency order:

```text
quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
```

Generalize or add a singleton-capable version of the currently
nonsingleton-wrapped pure-root stage-mass theorem.

```text
structure FinFourWeakCoreForcedPairPacket (core)

FinFourAtlasWeakConcentratedSingletonCore
  .nonempty_forcedPairPacket

FinFourWeakCoreForcedPairPacket.action_eq_true
FinFourWeakCoreForcedPairPacket.pairStageMass_eq_liveMass
FinFourWeakCoreForcedPairPacket.sourceToPair_gain_ge
FinFourWeakCoreForcedPairPacket.nonempty_collisionMinimumResidual
FinFourWeakCoreForcedPairPacket.collisionCluster_eq_postDateTail
```

Then expose the constant normal form:

```lean
theorem FinFourWeakCoreForcedPairPacket
    .tailEscape_or_minimumTail_fixedGain :
  quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalDebtSum reward packet.postDateTail ∨
    (quittingTerminalDebtSum reward packet.postDateTail =
        quittingTerminalSemanticDebtSum source.point.1 ∧
      ∃ p ≠ packet.collisionOwner,
        packet.resolution *
            quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
          packet.rootDefect p ∧
        packet.resolution ^ 2 *
            quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
          packet.endpointGain p)
```

For the moving strengthening, introduce one dependent family rather than a
collection of separately selected profiles:

```text
structure FinFourOwnerCompressedMinimumReturnForcedPairPacket
  (source) (producer) (lambda)
```

It should retain the endpoint ranks, reference profiles, self-tail closures,
pure singleton profiles, the one fixed outsider, forced pair targets, marked
dates, fixed pair terminal, and the exact post-date tail equations.  Then prove:

```text
FinFourOwnerCompressedSingletonProducer
  .nonempty_minimumReturnForcedPairPacket

FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .nonempty_minimumTailCollisionResidual

FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .eventually_fixedGainEndpointTransfer
```

The last theorem may freeze the recipient \(p\) on one further strict
subsequence.  It must not claim a total-debt decrease.

## Nonclaims

* The construction does not reuse
  `FinFourAtlasWeakStrongConcentratedPacket core` after pureification.
* The forced pair's whole semantic pair is not its residual tail cluster.
* The forced pair target is not asserted minimum or near-minimum.
* The full-gap singleton-to-pair edge and the later
  \(\lambda^2D_*/6\) edge are horizontal one-date deviations, not exact
  prescribed-payoff Bellman chronology.
* Exact own-debt subtraction does not bound cap leakage at other coordinates.
* No cumulative return, terminal approximate equilibrium, support descent, or
  uniform-equilibrium payoff is claimed.

## Independent review

The corrected arbitrary-core proof, cluster identification, constants, and
cofinal strengthening were checked in
`feedback/WEAK_CORE_FORCED_PAIR_COLLISION_NORMAL_FORM__BY_SINGLETON_INCENTIVE_AUDITOR.md`.
The cross-tail construction and all-behavior boundary were independently
checked again in
`feedback/EXTERNAL__WEAK_CORE_FORCED_PAIR_COLLISION_NORMAL_FORM__BY_FORCED_PAIR_REVIEW.md`.
