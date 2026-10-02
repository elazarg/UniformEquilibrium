# Fin4 weak singleton sources force minimum-tail paid pairs

Author: external contribution, corrected after independent audit

Independent reviews:
[singleton-incentive and source-index audit](../feedback/WEAK_CORE_FORCED_PAIR_COLLISION_NORMAL_FORM__BY_SINGLETON_INCENTIVE_AUDITOR.md),
[adversarial all-behavior and cofinal-splice audit](../feedback/EXTERNAL__WEAK_CORE_FORCED_PAIR_COLLISION_NORMAL_FORM__BY_FORCED_PAIR_REVIEW.md)

## Exact statement

Let

\[
r:\{S\subseteq\operatorname{Fin}4:S\ne\varnothing\}
  \longrightarrow\mathbb R^{\operatorname{Fin}4}
\]

be a quitting-game reward table.  Let

```text
source : FinFourMinimumAtomProducer reward bound
```

be a retained Fin4 positive-minimum source.  Write

\[
D_*:=D(\texttt{source.point.1})>0,
\qquad
\gamma:=\texttt{source.residual.witness.terminalGap}>0.
\]

The following two statements hold.

### A. Arbitrary weak-core normal form

For every

```text
core : FinFourAtlasWeakConcentratedSingletonCore source
```

put

\[
\lambda:=\texttt{core.resolution}>0.
\]

There are players \(j,o\in\operatorname{Fin}4\), with \(o\ne j\), an
actual pure-singleton profile \(\widehat\tau\), an actual pure-pair profile
\(\rho\), and a source-retaining forced-pair packet such that:

1. `core.singleton.val = {j}`;
2. the marked root of \(\widehat\tau\) is the pure singleton \(\{j\}\),
   and the marked root of \(\rho\) is the pure pair \(\{j,o\}\);
3. both modifications preserve every live root strictly after the marked
   date and retain the complete post-date semantic tail of `core`;
4. the pair has unconditional marked stage mass at least \(\lambda\);
5. the table-level join satisfies

   \[
   r_o(\{j\})+\gamma\le r_o(\{j,o\});
   \tag{1}
   \]

6. the literal unilateral change from pure \(\{j\}\) to pure
   \(\{j,o\}\) gains player \(o\) at least \(\lambda\gamma\);
7. the pair packet's marked coordinate defect for \(o\) is exactly zero;
   and
8. the existing strong-packet consumer is forced into its
   `QuittingConcentratedCollisionMinimumResidual` arm on this same source and
   literal packet.

Let \(\sigma\) be the actual all-Continue spine of `core.targetProfile`
strictly after its marked date.  The returned collision residual has the exact
cluster identity

\[
\boxed{
\texttt{collisionResidual.cluster}=\operatorname{Sem}(\sigma).}
\tag{2}
\]

Consequently exactly one of the following holds:

\[
D_*<D(\operatorname{Sem}(\sigma)),
\tag{3}
\]

or

\[
D(\operatorname{Sem}(\sigma))=D_*
\quad\text{and}\quad
\exists p\ne o,
\begin{cases}
\delta_p\ge \lambda D_*/6,\\
g_p\ge \lambda^2D_*/6.
\end{cases}
\tag{4}
\]

Here \(\delta_p\) is player \(p\)'s marked root-coordinate Nash defect at
the pure pair against the prescribed-payoff vector of the actual tail, and
\(g_p\) is the payoff gain from replacing \(p\)'s complete behavioral
strategy by the corresponding one-date exact best-endpoint deviation.  This
gain obeys the exact own-debt identity

\[
d_p(\text{target})=d_p(\rho)-g_p.
\tag{5}
\]

### B. Cofinal owner-compressed minimum-tail normal form

Assume the selected minimum-law atom is a singleton:

\[
\texttt{source.atom.terminal.val}=\{j\},
\qquad
\mu:=\texttt{source.point.2}(\operatorname{some}\{j\})>0.
\]

Fix any \(\lambda\) with

\[
0<\lambda<\mu.
\tag{6}
\]

Choose the one chronology retained by the checked owner-compression producer.
Then there are cofinally deep retained source ranks, actual reference profiles
\(\sigma_n\), marked dates \(t_n\), actual pair profiles \(\rho_n\), a fixed
outsider \(o\ne j\), and a fixed player \(p\ne o\), after passage to one
strict subsequence, such that:

\[
D(\operatorname{Sem}(\sigma_n))\longrightarrow D_*;
\tag{7}
\]

the marked root of every \(\rho_n\) is the same pure pair \(\{j,o\}\);

\[
\Pr_{\rho_n}(\{j,o\}\text{ occurs at }t_n)\ge\lambda;
\tag{8}
\]

the complete all-Continue spine of \(\rho_n\) after \(t_n\) is literally
\(\sigma_n\); player \(o\)'s marked coordinate defect is zero; and

\[
\delta_{n,p}\ge\lambda D_*/6,
\qquad
g_{n,p}\ge\lambda^2D_*/6
\tag{9}
\]

at every index of the reindexed subsequence.  Every \(g_{n,p}\) is an actual
all-behavior unilateral payoff gain, routes the nonempty marked atom without
mass loss, and subtracts exactly from player \(p\)'s own terminal debt.

Equivalently, this family forms one moving concentrated packet with fixed
owner \(o\), fixed terminal pair \(\{j,o\}\), fixed resolution \(\lambda\),
and identically zero marked \(o\)-defect.  Every collision residual selected
from it has a cluster \(z\) satisfying

\[
\boxed{D(z)=D_*.}
\tag{10}
\]

Thus the strategic-singleton arm and the off-minimum-tail arm are both absent
in the cofinal construction.

## Conjecture-facing change

The maintained Fin4 atlas had reduced the positive-minimum source to a
source-attached strong concentrated-singleton packet, but its checked consumer
still allowed:

* Continue routing and a strategic singleton output;
* Quit routing and a collision-minimum residual; and
* inside the latter, an off-minimum tail or a minimum-tail defect transfer.

This theorem uses the hard residual's full-gap collision selector at the
**actual arbitrary singleton label**.  It deliberately chooses the packet
owner so the marked action is Quit, rather than accepting an arbitrary owner
from the generic strong-packet constructor.  Therefore the strategic mode is
eliminated.  On the cofinal owner-compressed chronology, the literal
post-row tails converge in debt to the retained global minimum, so the
off-minimum mode is eliminated as well.

The surviving named obligation is strictly narrower:

\[
\boxed{
\begin{array}{c}
\text{source-matched pure pair of fixed stage mass}\\
+\ \text{literal minimum-tail cluster}\\
+\ \text{fixed all-behavior endpoint gain }\lambda^2D_*/6
\end{array}}
\tag{11}
\]

with exact own-debt subtraction.  What remains is to control the other three
unrestricted caps well enough to produce a terminal approximation, charged
admissible return, or regenerated finite-rank minimum-fibre descent.

## Definitions and assumptions

A behavioral strategy may be history-dependent, privately randomized, Quit
at an arbitrarily late date, or Never.  Before absorption, the only live
public history at a date is that everyone has previously Continued.

For an actual tail payoff vector \(u\), product root \(q\), and player \(i\),
write

\[
\delta_i(u,q)
 :=\max\{Q_i(u,q),C_i(u,q)\}-V_i(u,q)
\]

for the root-coordinate Nash defect.  This is a local one-row quantity
against the prescribed tail payoff, not the tail cap.  The checked reached-row
identity converts it into a complete terminal payoff gain:

\[
U_i(\text{best-endpoint update})-U_i(\text{profile})
=L\,\delta_i(u,q),
\tag{12}
\]

where \(L\) is the actual probability of reaching the row.  Because only
player \(i\)'s own strategy changes, its unrestricted best-response envelope
against the opponents is unchanged; this proves the exact debt subtraction
(5).

The cofinal construction uses a two-profile cross-tail splice.  If
\(\eta_n\) is the compressed target, \(\sigma_n\) is its retained reference
profile, and \(t_n\) is its marked date, define

\[
\zeta_n
:=
\operatorname{RootStack}(\eta_n;0,\ldots,t_n)
  \mathbin{\triangleright}\sigma_n.
\tag{13}
\]

In Lean-facing terms this is

```text
quittingLiteralRootStackProfile reward
  (quittingSelfTailRootStack reward eta_n t_n) sigma_n
```

or a dedicated two-profile helper.  It is **not** the one-profile
`quittingSelfTailClosure reward eta_n t_n`, which would restart the generally
non-near-minimum compressed target itself.

## Source correspondence

The source-side full-gap selector is the checked theorem

```text
FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
PunishmentNormalAtomicCollisionHandoff.lean`.  It is quantified over every
singleton owner and returns a distinct outsider with the full terminal gap.

The weak core and its literal provenance are checked in
`Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean` through:

```text
FinFourAtlasWeakConcentratedSingletonCore
FinFourAtlasWeakConcentratedSingletonCore.singleton_card
FinFourAtlasWeakConcentratedSingletonCore.resolution_le_stageMass
FinFourAtlasWeakConcentratedSingletonCore.postDate_liveRoot_eq
FinFourAtlasWeakConcentratedSingletonCore.postDateTail_eq
```

Pure-root replacement and post-date semantic-tail preservation are supported
by `quittingLiteralPureRootProfile` and
`quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq` in
`Research/Quitting/SameStageEndpointMonodromy.lean`.

The literal one-date packet adapter is checked in
`Research/Quitting/PositiveStageAtomConcentratedPacket.lean`:

```text
QuittingStageAtomConcentratedPacketAdapter
QuittingStageAtomConcentratedPacketAdapter.sourceStageMass_le_targetStageMass
QuittingStageAtomConcentratedPacketAdapter.targetTail_eq_sourceTail
QuittingStageAtomConcentratedPacketAdapter.ownerMarkedDefect_eq_zero
QuittingStageAtomConcentratedPacketAdapter.packet
```

The strong Fin4 packet and its routing geometry are in
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`.  Its
checked consumer and action normal form are in
`Research/Quitting/FinFourProducerAtlas/
StrongConcentratedPacketConsumer.lean`:

```text
FinFourSingletonStageStrongConcentratedPacket.consumerResult
FinFourSingletonStageStrongConcentratedPacket
  .hasStrategicDispatch_iff_action_eq_false
FinFourSingletonStageStrongConcentratedPacket
  .collisionMinimumResidual_of_action_eq_true
```

The collision residual and its tail-cluster split are in
`Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean` as
`QuittingConcentratedCollisionMinimumResidual`.

The fixed chronology, owner-compressed endpoints, cofinal rank selection, and
near-minimum reference debts are in
`Research/Quitting/FinFourProducerAtlas/
MinimumSingletonClockCompression.lean`, especially:

```text
FinFourMinimumAtomChronology.prefix_debt_tendsto
FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton
FinFourOwnerCompressedSingletonEndpoint.referenceProfile
FinFourOwnerCompressedSingletonEndpoint.target_stageMass_gt
FinFourOwnerCompressedSingletonEndpoint.targetProfile_postDate_liveRoot_eq
```

The exact prefix/tail operation uses `quittingSelfTailRootStack` and
`quittingLiteralRootStackProfile` from
`UniformEquilibrium/Quitting/Root/SelfTailClosure.lean` and the underlying
literal root-stack profile API.

Finally, the all-behavior payoff and own-debt identities are checked as

```text
quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain
```

in the terminal-semantic reached-row and live-weighted collision files.

The individually checked ingredients do not already provide the composed
forced-owner wrapper or moving cofinal packet.  The new mathematical content
is their exact source-retaining composition, the forced Quit mode, the exact
tail-cluster normal form, and the cofinal elimination of tail escape.

## Proof

### 1. Choose the full-gap outsider

Since `core.singleton` has cardinality one, write it as \(\{j\}\).  Apply
`exists_terminalGap_collision_at_singleton` at this same \(j\).  It returns
one \(o\ne j\) satisfying (1).  The choice depends only on the table and
\(j\), so it remains fixed throughout the cofinal construction.

### 2. Pureify the actual marked row

Let \(t\) be the core's marked date and \(L\) its live mass.  The displayed
singleton stage atom has mass at least \(\lambda\) and is contained in the
live event, so \(L\ge\lambda\).

Overwrite the complete marked product root by pure \(\{j\}\).  Earlier live
roots are unchanged, so the live mass is still \(L\).  The pure singleton
has conditional root mass one, so its unconditional stage mass is exactly
\(L\).  Every post-date live root is copied literally.

This simultaneous pureification is not a unilateral profitable deviation and
no such claim is needed.  It is an actual profile constructor feeding the
generic stage-atom adapter.

### 3. Force the pair and its packet

At the pure singleton root, player \(o\)'s Continue and Quit endpoint values
are exactly

\[
r_o(\{j\}),\qquad r_o(\{j,o\}).
\]

The post-date tail cannot be reached under either endpoint because \(j\)
Quits surely.  Equations (1) and \(\gamma>0\) therefore force the exact
best-endpoint action to be Quit, even though ties in the checked selector are
resolved toward Continue.

The resulting marked root is pure \(\{j,o\}\), still reached with probability
\(L\).  This proves (4), the zero owner defect, the literal tail equality, and
the gain bound \(L\gamma\ge\lambda\gamma\).

The source-retaining object must be a new dependent wrapper.  The existing

```text
FinFourAtlasWeakStrongConcentratedPacket core
```

indexes its packet by `core.targetProfile`, whereas this packet is indexed by
the new pure-singleton source profile.  The new wrapper stores `core`
externally and the strong packet at the pureified profile internally.  This
retains the exact minimum source and endpoint provenance without asserting
the two profiles are equal.

### 4. Eliminate the strategic output

The generic adapter repeats the actual pair profile as a constant
`QuittingReprojectionConcentratedPacket`.  Its routed terminal has cardinality
two.  The checked strategic dispatch is equivalent to Continue mode and in
particular requires a singleton routed terminal.  It is therefore impossible
here.  The checked consumer must return the collision-minimum residual on the
same packet.

### 5. Identify the constant residual and derive the gain

The packet profiles, marks, and first subsequence are constant.  Any further
subsequence selected by the collision residual still has the same post-date
tail \(\sigma\).  Its convergence field and uniqueness of limits prove (2).

Global minimality gives \(D_*\le D(\operatorname{Sem}(\sigma))\).  The
residual's exhaustive field therefore becomes (3) or (4).  In the
minimum-tail case its three nonnegative defects other than \(o\) sum to at
least \(\lambda D_*/2\).  Hence some \(p\ne o\) has
\(\delta_p\ge\lambda D_*/6\).

At a pure pair root, its unconditional pair mass equals the live mass \(L\),
so \(L\ge\lambda\).  The checked reached-row identity yields

\[
g_p=L\delta_p\ge\lambda^2D_*/6.
\]

Updating only \(p\)'s strategy leaves its unrestricted envelope fixed and
proves (5).  One endpoint update cannot erase both members of the pair, so
the routed coalition remains nonempty and its marked mass is not lost.

### 6. Construct the cofinal cross-tail packet

Fix \(0<\lambda<\mu\).  For requested depth \(n\), choose an
owner-compressed endpoint whose retained source rank is at least \(n\).  Let
\(\eta_n\) be its compressed target, \(t_n\) its mark, and \(\sigma_n\) its
reference profile.

Form the two-profile splice (13).  Its roots through \(t_n\) are those of
\(\eta_n\), so it preserves the compressed singleton stage mass.  Its exact
spine after \(t_n+1\) is \(\sigma_n\).  Pureify the marked root and force the
same fixed outsider \(o\) to Quit.  This produces \(\rho_n\) with fixed pair,
fixed resolution, and zero marked \(o\)-defect.

Because the retained ranks tend to infinity,
`prefix_debt_tendsto` and the source equality between its minimum and the
literal debt infimum prove (7).  The profiles \(\rho_n\), varying marks
\(t_n\), cutoffs \(t_n+1\), identity first subsequence, and any positive scale
tending to zero form one moving concentrated packet.

Its strategic branch is impossible by the fixed pair cardinality.  Let a
collision residual choose a further strict subsequence and tail cluster
\(z\).  Along that subsequence the tail semantic pairs converge to \(z\),
while their debt sums converge to \(D_*\).  Continuity of total debt proves
(10).  The residual must therefore satisfy its eventual other-defect
inequality.

At each sufficiently late rank choose one of the three labels other than
\(o\) carrying at least one third of the sum.  Finite pigeonhole and one
further strict subsequence fix the label \(p\).  Reindexing gives (9) at every
index, together with exact own-debt subtraction and lossless routing.

## Boundary tests

### Nonpure source row

The weak core promises only positive singleton mass, not a pure marked root.
Pureification may change every player's whole semantic coordinate.  The
theorem does not compare the original and pureified semantic pairs; it retains
the original source externally and uses the pureified profile as a new literal
packet source.

### Never and arbitrarily late deviations

At the pure singleton and pure pair rows, another player Quits surely.  The
full-gap outsider comparison and the one-date edge do not expose the tail.
The endpoint-gain theorem itself is stated for a complete unilateral
behavioral replacement, and the mover's cap is the unrestricted behavioral
envelope.  No stationary or finite-deadline restriction is used.

### Arbitrary post-date tail

Part A permits any actual behavioral tail, including infinite support and
Never mass.  It may land in the strict tail-escape arm (3).  Part B removes
that arm only by the source-matched cofinal cross-tail construction and the
checked convergence of the literal reference-profile debts.

### Pair semantics versus tail semantics

Two sure quitters screen the whole pure-pair profile from its continuation
under every unilateral deviation.  Therefore replacing the tail cannot make
the pair profile minimum or near-minimum.  Equations (2), (7), and (10) concern
the residual's stored **tail**, not the whole pair source.  The theorem never
identifies them.

### Recipient inside or outside the pair

The selected \(p\) may be the original singleton owner or a third player.  A
best-endpoint update may remove one pair member or add an outsider, but cannot
erase the nonempty coalition.  The gain and own-debt identities hold in every
case.  No support-cardinality descent is inferred.

### Negative rewards and cap nonattainment

The proof uses reward differences, the positive witness gap, and supremal
behavioral caps.  It assumes neither nonnegative rewards nor attainment of a
best behavioral response.

### Cross-coordinate leakage

Exact reduction of \(p\)'s debt does not bound changes in the other three
caps.  A finite static regression can circulate such debt.  Therefore the
result is not promoted to total-debt descent or minimum-fibre support descent.

## Adapter and consumer

The arbitrary-data adapter is the maintained weak singleton core supplied by
the Fin4 minimum-atom atlas.  The new forced-pair wrapper retains this exact
core and applies the table-level full-gap outsider theorem at its actual
singleton label.  The downstream checked consumer is

```text
FinFourSingletonStageStrongConcentratedPacket.consumerResult
```

with its strategic arm eliminated by the checked action/cardinality normal
form.

For the stronger statement, the actual-data adapter is the checked
`FinFourOwnerCompressedSingletonProducer` on one retained chronology.  The
new mathematics builds the two-profile cross-tail family and applies the same
concentrated-packet consumer once to that moving family.

The downstream semantic endpoint is not yet reached.  The theorem strictly
narrows the remaining consumer input to (11), which still needs a
source-faithful cross-coordinate cap-control theorem.

## Lean handoff

Suggested declarations, in dependency order:

```text
quittingStageCoalitionMass_literalPureRootProfile_eq_liveMass

structure FinFourWeakCoreForcedPairPacket (core)

FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket
FinFourWeakCoreForcedPairPacket.action_eq_true
FinFourWeakCoreForcedPairPacket.pairStageMass_eq_liveMass
FinFourWeakCoreForcedPairPacket.sourceToPair_gain_ge
FinFourWeakCoreForcedPairPacket.nonempty_collisionMinimumResidual
FinFourWeakCoreForcedPairPacket.collisionCluster_eq_postDateTail
FinFourWeakCoreForcedPairPacket.tailEscape_or_minimumTail_fixedGain
```

The first helper should accept any nonempty pure coalition; the currently
nearby convenience wrapper is restricted to nonsingletons.

For the cofinal theorem, first package the corrected two-profile splice:

```text
quittingCrossTailClosure reward prefixProfile tailProfile stage
quittingProfileLiveRoot_crossTailClosure_eq_of_le
quittingStageCoalitionMass_crossTailClosure
quittingAllContinueProfileSpine_crossTailClosure
```

Then use one dependent family retaining all source ranks and profiles:

```text
structure FinFourOwnerCompressedMinimumReturnForcedPairPacket
  (source) (producer) (lambda)

FinFourOwnerCompressedSingletonProducer
  .nonempty_minimumReturnForcedPairPacket

FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .nonempty_minimumTailCollisionResidual

FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .exists_fixedRecipient_fixedGainSubsequence
```

The composite declarations are not currently checked.  The formalization
must derive the fields from the named source data; it must not add the forced
action, minimum-tail equality, or gain estimates as hypotheses.

## Scope and nonclaims

* The result does not construct the existing
  `FinFourAtlasWeakStrongConcentratedPacket core` after pureification; it uses
  a new wrapper with the pureified source profile and retains `core`
  externally.
* The pair profile's whole semantic pair is not its residual tail cluster and
  is not asserted minimum or near-minimum.
* The full-gap singleton-to-pair move and the later fixed-gain pair move are
  horizontal one-date deviations, not prescribed-payoff Bellman edges.
* Exact own-debt subtraction does not control the other coordinates' caps or
  total debt.
* No cumulative admissible return, terminal approximate Nash profile,
  minimum-fibre support drop, uniform-equilibrium payoff, or counterexample is
  produced.

## Formalization record

The maintained realization is checked Lean, Research-only at the game-facing
source and consumer layers, and reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean`.  The earlier Lean
handoff above records the pre-formalization interface proposal; the exact
maintained declarations are the following.

1. `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean` defines the generic
   two-profile splice `quittingCrossTailClosure`.
   `quittingProfileLiveRoot_crossTailClosure_eq_of_le` preserves every live
   root through the marked stage, while
   `quittingAllContinueProfileSpine_crossTailClosure` identifies the complete
   post-date `BehaviorProfile` literally with the independently supplied tail
   profile.  In
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSelfTailClosure.lean`,
   `quittingStageCoalitionMass_crossTailClosure` preserves the marked
   unconditional coalition mass,
   `quittingTerminalSemanticPair_spine_crossTailClosure` transports the exact
   semantic tail, and `quittingSpineDebtExcess_crossTailClosure` gives the
   exact restarted-tail debt minus the displayed reference value.  These are
   generic finite-quitting declarations and assume no minimum, Fin4 source,
   or equilibrium certificate.
2. `Research/Quitting/ConcentratedSingleton/NonSingletonResidual.lean` proves
   the reusable bridge
   `QuittingReprojectionConcentratedPacket.nonempty_collisionMinimumResidual_of_terminal_card_ne_one`.
   It applies the raw concentrated compiler and rules out its singleton arm
   from the supplied terminal-cardinality inequality; it needs no strategic
   opponent or terminal-exploitability witness.
3. Part A is implemented in
   `Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`.
   For every supplied `FinFourAtlasWeakConcentratedSingletonCore source`,
   `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairResidualCapstone`
   returns a `FinFourWeakCoreForcedPairPacket.ResidualCapstone`.  This one-shot
   object retains the exact supplied core, the selected literal forced-pair
   packet, a collision-minimum residual, its cluster equality to the core's
   actual post-date semantic tail, and a typed
   `FinFourWeakCoreForcedPairPacket.TailOutcome`.

   The outcome is either strict tail escape or a minimum-tail equality with a
   payer distinct from the forced owner, defect at least
   `lambda * D_* / 6`, and gain at least `lambda^2 * D_* / 6`.
   The granular declarations
   `FinFourWeakCoreForcedPairPacket.nonempty_collisionMinimumResidual`,
   `FinFourWeakCoreForcedPairPacket.collisionCluster_eq_corePostDateTail`, and
   `FinFourWeakCoreForcedPairPacket.tailEscape_or_minimumTail_fixedGain`
   expose the same composition separately.  The source packet in
   `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` retains the
   stronger direct payer defect `D_* / 3`, gain `lambda * D_* / 3`, outsider
   gain `lambda * gamma`, and canonical `mu^2 * D_* / 24` bound, together with
   exact own-debt subtraction, marked mass, off-date profile, and post-date
   tail provenance.
4. Part B is implemented in
   `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`.
   `FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone`
   takes the retained singleton minimum-atom source and its literal
   cardinality proof, then returns one
   `FinFourOwnerCompressedMinimumReturnForcedPairFamilyCapstone source`.
   Its `returnSource` stores one owner-compressed producer chronology and one
   table-selected outsider before the universal resolution quantifier.  For
   every later `lambda` with `0 < lambda < mu`, its `resolution` field returns
   a `FinFourOwnerCompressedMinimumReturnForcedPairPacket.ResolutionCapstone`.

   Each resolution capstone retains one strictly cofinal moving packet, one
   payer label fixed after a strict finite-label subsequence, an actual
   collision-minimum residual, the exact equality of that residual's cluster
   debt with `D_*`, and at every outer index the stronger directly selected
   payer bounds `D_* / 3` and `lambda * D_* / 3`.  The payer is fixed across
   the selected sequence at one resolution; it is not asserted independent of
   `lambda`.  The granular declarations
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingCollisionResidual_clusterDebt_eq_minimum`,
   `.movingCollisionResidual_not_offMinimum`,
   `.movingCollisionResidual_minimumTail`, and
   `.movingCollisionResidual_minimumTail_fixedPayer` expose the convergence,
   global off-minimum-arm elimination, minimum-tail result, and the packet's
   weaker verbatim `lambda * D_* / 6` and `lambda^2 * D_* / 6` bounds.
   The named forced and paid target tail/debt equalities, exact own-debt
   subtraction, routed mass equalities, and `lambda * gamma` outsider gain
   remain available on the packet.
5. `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` imports both
   source-level modules.  The reader records this as a forward contraction of
   the weak-singleton atlas branch; it does not redefine the older granular
   packet interfaces.

Evidence seals:

- **M:** PASS.  The two-profile splice identities, finite-label payer freeze,
  exact concentrated-packet construction, debt-limit uniqueness argument,
  and tail-escape/minimum-tail split match the corrected proof and its
  boundary tests.
- **L:** PASS.  The exact declarations above are checked by Lean.  At
  promotion, both capstone modules direct-compiled, the named reader build and
  documentation check passed, and the remaining repository checks are
  recorded in the associated commit report.
- **A:** PASS.  Part A begins with an arbitrary actual weak core and constructs
  its packet and residual.  Part B begins with one retained singleton
  minimum-atom source, selects one chronology and outsider before every
  admissible resolution, and constructs every later packet and residual
  without supplied certificate fields.
- **C:** PASS only for the checked forced-pair collision/minimum-tail
  contraction.  The nonsingleton packet is consumed into an actual
  `QuittingConcentratedCollisionMinimumResidual`; in Part B its off-minimum
  arm is eliminated and its cluster debt is proved exactly `D_*`.  No theorem
  consumes the surviving minimum-tail collision residual to a return,
  regeneration, completion, or uniform payoff.

Nonclaims:

- the whole pure-pair source is not identified with the residual tail and is
  not asserted minimum, near-minimal, cap--Nash, or terminal approximate Nash;
- the payer can be the original singleton owner or a third player, and no
  support-cardinality descent follows;
- exact own-debt subtraction supplies no cross-coordinate cap control or
  total-debt descent;
- Part A's strict tail-escape alternative remains live for an arbitrary weak
  core;
- Part B fixes the source chronology and outsider before `forall lambda`, but
  freezes the payer only after choosing each resolution's strict subsequence;
- no fixed original target, cumulative admissible return, minimum-fibre
  support drop, recurrence, regeneration, recursive descent, terminal
  approximation, atlas completion, uniform-equilibrium payoff, or
  counterexample is proved.

The mathematical provenance is this corrected external-contribution packet
and the two independent reviews linked at its head.  No external paper theorem
or off-main Lean implementation is imported.
