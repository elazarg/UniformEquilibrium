# Review of the weak-core forced-pair collision normal form

Reviewer: `SINGLETON_INCENTIVE_AUDITOR`

## Verdict

The mathematical construction is correct, with one necessary interface
correction.  The arbitrary weak-core singleton owner really does have a
**fixed distinct outsider with the full terminal-gap join**.  Pureifying the
marked row to that singleton and routing this outsider to its exact best
endpoint therefore forces the Quit mode, retains the complete post-row tail,
and produces a source-attached collision-minimum residual.

The resulting residual has the sharper exact normal form

\[
\boxed{
\begin{aligned}
&D(\operatorname{Sem}(\sigma))>D_* \\
&\qquad\lor\\
&D(\operatorname{Sem}(\sigma))=D_*
  \ \land\ 
  \exists p\ne o,\quad
  \delta_p\ge \frac{\lambda D_*}{6},
  \quad g_p\ge\frac{\lambda^2D_*}{6}.
\end{aligned}}
\]

Here \(\sigma\) is the **literal post-row behavioral tail**, \(o\) is the
forced outsider, \(\delta_p\) is the marked root defect against
\(U(\sigma)\), and \(g_p\) is the exact payoff gain of the corresponding
one-date best-endpoint behavioral deviation.  The residual cluster is
exactly \(\operatorname{Sem}(\sigma)\), not the semantic pair of the pure
pair target.

The existing structure `FinFourAtlasWeakStrongConcentratedPacket core` cannot
store this packet: it is indexed by `core.targetProfile`, while the proposed
construction first replaces that profile's marked root by the pure singleton.
The result needs a new dependent wrapper retaining `core` externally and
indexing the generic strong packet by the pureified profile.  This is a Lean
interface repair, not a mathematical gap.

I recommend export in this corrected form, preferably together with the
cofinal minimum-return strengthening described below.  The arbitrary-core
theorem strictly reduces the weak singleton node to an actual-tail escape or
a minimum-tail paid collision transfer.  The cofinal owner-clock version
removes the escape arm entirely.  Neither statement consumes the remaining
minimum-tail transfer, so neither should be presented as a terminal or return
compiler.

## Claim audited

Let

```text
source : FinFourMinimumAtomProducer reward bound
core   : FinFourAtlasWeakConcentratedSingletonCore source
```

and put

```text
tau := core.targetProfile
t   := core.stage
lambda := core.resolution
```

Write `core.singleton = {j}`.  The proposed construction is:

1. replace the entire marked product root of `tau` by the pure singleton
   root `{j}`;
2. choose a fixed `o != j` whose join at `{j}` gains the full terminal gap;
3. use `o` as the exact-best-endpoint packet owner;
4. consume the resulting constant strong packet;
5. identify the collision residual's constant tail cluster and quantify its
   minimum-fibre branch.

## Narrow source audit

I inspected the following declarations and only their immediate interfaces.

* `FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean`.
* `quittingLiteralPureRootCoalitionProfile`,
  `quittingProfileLiveRoot_literalPureRootProfile_of_ne`, and
  `quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.
* `QuittingStageAtomConcentratedPacketAdapter`,
  `.sourceStageMass_le_targetStageMass`, `.targetTail_eq_sourceTail`,
  `.ownerMarkedDefect_eq_zero`, and `.packet` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`.
* `FinFourSingletonStageStrongConcentratedPacket` and
  `FinFourAtlasWeakStrongConcentratedPacket` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`.
* `FinFourStrongConcentratedPacketConsumerResult` and
  `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in
  `Research/Quitting/FinFourProducerAtlas/
  StrongConcentratedPacketConsumer.lean`.
* `HasQuittingConcentratedSingletonStrategicDispatch` and
  `QuittingConcentratedCollisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`.
* `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  and `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` in the
  checked terminal-semantic collision files.

The composed action normal form recorded in
`FIN4_STRATEGIC_CONCENTRATED_ARM_ACTION_NORMAL_FORM` is not yet a named Lean
declaration at the inspected head.  It is not needed as an assumption here:
the strategic arm definition itself begins with the singleton identity, so a
literal pair terminal contradicts that arm directly.

## 1. The full-gap outsider exists for the arbitrary owner

This is not a stale or overgeneralized theorem name.  The checked declaration
says, for **every** `owner : Fin 4`,

\[
\exists o\ne j,\qquad
r_o(\{j\})+\gamma\le r_o(\{j,o\}),
\tag{1}
\]

where \(\gamma=\texttt{source.residual.witness.terminalGap}>0\).
Its proof applies the terminal witness's atomic-collision theorem using the
hard residual's punishment-normality field for that same arbitrary owner.
Thus it applies to both constructors of the weak concentrated core; no
selection of a different singleton source is involved.

Because (1) is strict after using \(\gamma>0\), the outsider's exact best
endpoint at a pure `{j}` root is Quit.  Its Continue payoff is
\(r_o(\{j\})\), its Quit payoff is \(r_o(\{j,o\})\), and the tail is not
reached under either action because `j` quits surely.

## 2. Pureification and the full-gap pair edge are literal

Let \(L\) be the probability of reaching date \(t\) under `tau`.  The original
singleton stage mass is at most \(L\), so

\[
L\ge \Pr_\tau(\{j\}\text{ at }t)\ge\lambda.
\tag{2}
\]

Replace the marked root by the pure singleton root `{j}` and call the resulting
profile \(\widehat\tau\).  Every live root off date \(t\), in particular every
root after \(t\), is copied literally.  Its singleton stage mass is exactly
\(L\), hence at least \(\lambda\).

Now construct the generic stage-atom adapter with packet owner \(o\).  By (1)
its selected Boolean action is Quit, so its target profile has the pure pair
`{j,o}` at date \(t\).  Its pair stage mass is still exactly \(L\), the
post-date tail is still literal, and its marked `o`-defect is zero.  Moreover
the unilateral source-to-target payoff gain is exactly

\[
L\bigl(r_o(\{j,o\})-r_o(\{j\})\bigr)
\ge L\gamma\ge\lambda\gamma.
\tag{3}
\]

The generic adapter already repeats this literal pair target constantly and
provides the positive vanishing packet scale.  No approximate cap argument is
used.

## 3. The existing core-indexed wrapper is the wrong index

The field of

```text
FinFourAtlasWeakStrongConcentratedPacket core
```

has source profile exactly `core.targetProfile`.  Our adapter instead has
source profile \(\widehat\tau\).  These profiles need not be equal: the weak
endpoint originally has only a positive singleton atom, not a pure marked
root.

Therefore the proposed theorem must not claim to construct the old wrapper.
A suitable new object is schematically

```text
structure FinFourWeakCoreForcedPairPacket (core) where
  singletonOwner : Fin 4
  outsider : Fin 4
  outsider_ne : outsider != singletonOwner
  pureSingletonProfile : BehaviorProfile
  pureSingletonProfile_eq : ...
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    pureSingletonProfile core.singleton core.stage core.resolution
  action_eq_true : strong.adapter.action = true
  result : Nonempty (QuittingConcentratedCollisionMinimumResidual ...)
```

The original `core`, its source, reference profile, marked date, resolution,
and literal tail remain dependent fields of this wrapper.  The generic theorem
`strong.consumerResult` accepts the new strong packet without requiring the
old core-indexed wrapper.

## 4. The strategic arm is impossible

The routed terminal is exactly `{o,j}`, of cardinality two.  But
`HasQuittingConcentratedSingletonStrategicDispatch ... packet j` has as its
first conjunct

```text
terminal.val = {j}.
```

Thus the left arm of `strong.consumerResult` is contradictory.  The returned
right arm is necessarily

```text
Nonempty (QuittingConcentratedCollisionMinimumResidual
  reward source.point.1 o {o,j} strong.adapter.packet).
```

This uses the same source and the same literal forced-pair packet.  It is not
an independently selected collision residual.

## 5. The residual cluster is exactly the actual post-row tail

The adapter's packet profiles, marks, and first subsequence are all constant
at the pair target and date \(t\).  Its post-row semantic-tail sequence is
therefore the constant sequence at

\[
z_\sigma:=\operatorname{Sem}(\sigma),
\tag{4}
\]

where \(\sigma\) is the literal all-Continue spine after date \(t\).  The
residual may choose a further strict subsequence, but a subsequence of a
constant sequence is still constant.  Its `tail_tendsto` field and uniqueness
of limits give

\[
\boxed{\texttt{residual.cluster}=z_\sigma.}
\tag{5}
\]

For a weak core, `core.postDateTail_eq` further identifies this tail with the
post-date semantic tail of `core.referenceProfile`.  It is important not to
replace (5) by the semantic pair of the pure pair target.  The pair target
absorbs at date \(t\), so its whole terminal semantics are tail-insensitive;
the residual deliberately records the shifted tail separately.

The residual's exhaustive split is consequently

\[
D_*<D(z_\sigma)
\quad\lor\quad
D(z_\sigma)=D_*\ \land\
\frac{\lambda D_*}{2}
\le\sum_{p\ne o}\delta_p.
\tag{6}
\]

Since \(\sigma\) is actual, global minimality already gives
\(D_*\le D(z_\sigma)\), so there is no missing third case.

## 6. The \(\lambda^2D_*/6\) endpoint gain is correct

In the minimum-tail arm of (6), Fin4 leaves exactly three indices in
`univ.erase o`.  Root defects are nonnegative, so some \(p\ne o\) satisfies

\[
\delta_p\ge\frac{\lambda D_*}{6}.
\tag{7}
\]

Because this is a constant packet, the eventual inequality in the residual
reduces to an inequality at the one fixed pair row.  No moving-label
pigeonhole is required.

The pair stage mass equals its live mass \(L\), and \(L\ge\lambda\).  The
checked best-endpoint identity therefore gives the exact whole-profile gain

\[
g_p=L\delta_p\ge\frac{\lambda^2D_*}{6}.
\tag{8}
\]

The route remains nonempty because the source coalition has two members.
Changing only \(p\)'s behavioral strategy leaves its unrestricted best-response
envelope fixed, so the checked own-strategy transport theorem gives exact
debt subtraction

\[
d_p(\text{after})=d_p(\text{before})-g_p.
\tag{9}
\]

Equations (7)--(9) do not control the other three caps and hence do not imply a
drop in total debt.

## 7. Cofinal minimum-return strengthening

For the owner-compressed minimum-singleton origin, the construction combines
with the reviewed minimum-return moving-packet argument and becomes strictly
stronger.

Choose cofinally deep owner-compressed endpoints, self-tail-close each marked
prefix onto its own near-minimum `referenceProfile`, and then pureify the
marked row to `{j}`.  The same outsider \(o\) from (1) works at every rank and
its action is always Quit.  Thus:

* the packet owner is fixed;
* the routed terminal is the fixed pair `{j,o}`;
* no Boolean-action subsequence is needed;
* the post-row tail debts converge to \(D_*\); and
* the strategic singleton arm is impossible at every rank.

Every returned collision residual is therefore automatically in its
minimum-tail arm.  After a finite-label subsequence for \(p\), it supplies
cofinally many literal gains satisfying (8), with exact own-debt subtraction
and lossless marked-atom routing.

This strengthens `MINIMUM_RETURN_STRONG_SINGLETON_PACKET`: full-gap forced
pair selection eliminates both its action-index issue and its remaining
strategic branch.  The remaining mathematical problem is still to control
the other coordinates well enough to compile these gains into a return or a
well-founded support drop.

## 8. Comparison with the channel-switch no-go

There is no contradiction with the two-sure-quitter tail-replacement no-go.
The forced pair deliberately changes strategic channels:

* before forcing \(o\), the singleton owner's only nonlocal coordinate is its
  Continue-to-tail cap;
* after forcing \(o\), two players quit surely, absorption at the marked row is
  unavoidable after every unilateral deviation, and the whole pair profile's
  semantics depend only on static pair toggles.

The tail is preserved as **provenance** and is exactly the residual cluster,
but it cannot repair or alter the pair profile's whole semantic debt.  Thus
(6) is a statement about the stored tail; it is not a claim that the pair
target lies on the minimum fiber or that its edge gains form a chronology.

## Export assessment

This passes the mathematical gate as an exact producer-normal-form theorem:
it starts from the maintained arbitrary weak singleton source, uses a checked
table-level full-gap selector, constructs a literal packet, and eliminates
the strategic arm without any supplied certificate.  Its output is strictly
narrower:

\[
\text{weak singleton core}
\Longrightarrow
\text{actual-tail escape}
\ \lor\ 
\text{minimum-tail fixed-gain collision transfer}.
\]

The cofinal owner-clock corollary removes the first disjunct and is the
strongest export-worthy form.  A second independent review should check the
self-tail family indexing, since that is the only nonlocal part of the
strengthening.

The export must retain these nonclaims:

* the old `FinFourAtlasWeakStrongConcentratedPacket core` is not constructed;
* the pair target's whole semantics are not the residual cluster;
* (8) is one exact own-debt drain, not total-debt descent;
* no cumulative admissible return, terminal approximation, or regenerated
  support rank follows yet.
