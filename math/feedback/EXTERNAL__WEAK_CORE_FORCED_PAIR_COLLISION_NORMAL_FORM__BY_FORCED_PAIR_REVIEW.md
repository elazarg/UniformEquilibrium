# Adversarial review of the weak-core forced-pair normal form

Reviewer: `FORCED_PAIR_REVIEW`

## Verdict

The mathematical result passes the export gate, subject to one small but
important correction to the proposed Lean handoff for the cofinal theorem.
The arbitrary-core construction is literal and sound.  The cofinal
owner-compressed construction also works, but its repair profile is not the
one-argument `quittingSelfTailClosure`: it must splice the marked root prefix
of the compressed endpoint onto the endpoint's separate reference profile.
That is a direct `quittingLiteralRootStackProfile` construction (or a new
two-profile helper), with the same elementary root, mass, and spine proofs.

After that correction, the strongest valid statement is

\[
\boxed{
\begin{array}{c}
\text{one fixed owner-compressed minimum-singleton chronology}
\\[1mm]\Longrightarrow\\[1mm]
\text{a moving pure-pair packet with fixed owner, pair, and mass floor,}
\\
\text{whose actual post-row tail debt tends to }D_*
\\[1mm]\Longrightarrow\\[1mm]
\text{cofinally many fixed-label endpoint gains at least }
\lambda^2D_*/6 .
\end{array}}
\]

Every gain is an actual all-behavior unilateral payoff gain and subtracts
exactly from the mover's own terminal debt.  The theorem does not control the
other three caps and therefore does not prove total-debt descent, support
descent, recurrence, or terminal approximation.

I attempted to falsify the result through arbitrary post-row tails, Never and
late behavioral deviations, nonpure original singleton roots, changing packet
owners, and the distinction between the pair profile and the residual tail
cluster.  None survives the literal pure-singleton/pure-pair screening.  The
remaining limitation is correctly stated as cross-coordinate cap leakage.

## Claim audited

For

```text
source : FinFourMinimumAtomProducer reward bound
core   : FinFourAtlasWeakConcentratedSingletonCore source
```

the note first replaces the core's marked root by its displayed pure
singleton `{j}`.  It chooses the hard residual's full-gap outsider `o != j`,
forces `o` to its exact best endpoint, and obtains a constant strong packet
whose marked terminal is the pure pair `{j,o}`.  It then identifies the
collision residual's cluster with the literal post-row tail and derives the
off-minimum-tail/minimum-tail split.  Finally it repeats the construction on
cofinally deep owner-compressed endpoints, but splices each marked prefix onto
its near-minimum reference profile, thereby removing the off-minimum arm.

## Narrow source audit

I inspected these declarations and their immediate definitions.

* `FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean`.
* `FinFourAtlasWeakConcentratedSingletonCore`, `.singleton_card`,
  `.resolution_le_stageMass`, `.postDate_liveRoot_eq`, and
  `.postDateTail_eq` in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.
* `quittingLiteralPureRootProfile`,
  `quittingProfileLiveRoot_literalPureRootProfile_of_ne`, and
  `quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.
* `QuittingStageAtomConcentratedPacketAdapter`,
  `.sourceStageMass_le_targetStageMass`, `.targetTail_eq_sourceTail`,
  `.ownerMarkedDefect_eq_zero`, and `.packet` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`.
* `FinFourSingletonStageStrongConcentratedPacket`,
  `.routedTerminal_mode_and_card`, and the weak-core wrapper in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`.
* `FinFourSingletonStageStrongConcentratedPacket.consumerResult`,
  `.hasStrategicDispatch_iff_action_eq_false`, and
  `.collisionMinimumResidual_of_action_eq_true` in
  `Research/Quitting/FinFourProducerAtlas/
  StrongConcentratedPacketConsumer.lean`.
* `QuittingConcentratedCollisionMinimumResidual` and the packet capstone in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`.
* `FinFourMinimumAtomChronology.prefix_debt_tendsto`,
  `FinFourOwnerCompressedSingletonEndpoint`, and its literal tail and mass
  fields in
  `Research/Quitting/FinFourProducerAtlas/
  MinimumSingletonClockCompression.lean`.
* `quittingLiteralRootStackProfile`, `quittingSelfTailRootStack`, and
  `quittingAllContinueProfileSpine_selfTailClosure` in
  `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`, together with the
  stage-mass and semantic projections in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticSelfTailClosure.lean`.
* `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  and `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` in the
  terminal-semantic reached-row files.

No checked declaration presently packages the forced full-gap owner choice
with the pureification and the moving minimum-return family.  The result is
therefore new rather than a restatement of the existing arbitrary-owner
strong-packet constructor.

## 1. The arbitrary owner has a fixed full-gap joiner

The checked singleton collision theorem is quantified over every
`owner : Fin 4`.  It gives `o != j` and

\[
r_o(\{j\})+\gamma\le r_o(\{j,o\}),\qquad \gamma>0.
\]

At a pure singleton root `{j}`, both of `o`'s endpoints absorb immediately:
Continue pays `r_o({j})`, while Quit pays `r_o({j,o})`.  The comparison is
therefore independent of every behavioral continuation, including Never and
arbitrarily late stopping.  Strictness forces
`quittingRootBestEndpointAction = true`; the tie-to-Continue convention does
not intervene.

The outsider is selected from the table and label `j`, so the same `o` works
at every cofinal endpoint carrying that fixed minimum singleton.  No
subsequence is needed to stabilize the packet owner or action.

## 2. Pureification preserves exactly the required source data

Let `L` be the live mass at the marked date.  The weak core's singleton stage
mass is at most `L`, hence `L >= lambda`.  Replacing the entire marked product
root by pure `{j}`:

* leaves all earlier live roots and therefore `L` unchanged;
* makes the singleton stage mass exactly `L`;
* leaves every post-date live root unchanged; and
* produces an actual behavioral profile.

Forcing `o` to Quit then makes the marked root pure `{j,o}`.  The pair stage
mass is still exactly `L`, the post-date tail is literal, and the selected
owner defect is zero.  The pure-singleton-to-pair update has exact payoff gain

\[
L\bigl(r_o(\{j,o\})-r_o(\{j\})\bigr)\ge\lambda\gamma.
\]

This gain starts at the pureified profile, not at the original weak-core
profile.  The note now states that distinction correctly and makes no claim
about the strategic cost of the simultaneous pureification.

The existing `FinFourAtlasWeakStrongConcentratedPacket core` is indeed the
wrong dependent wrapper: its source profile is definitionally
`core.targetProfile`.  A new wrapper must retain `core` externally and index
the strong packet by the pureified profile.  This is an interface issue, not a
loss of minimum/source provenance.

## 3. Pair mode forces the collision residual

The routed terminal in Quit mode is `{o,j}` and has cardinality two.  The
checked strategic dispatch is equivalent to Continue mode; equivalently its
first field requires a singleton terminal.  Thus the strategic arm of
`consumerResult` is impossible, and the collision-minimum residual is on the
same literal packet and original minimum source.

No exact-deletion or static-handoff disjunct survives inside this forced Quit
mode.  Those table-level alternatives occur only after the strategic
singleton dispatch, which has already been excluded by the pair cardinality.

## 4. The constant residual cluster and constants are exact

For the arbitrary-core construction, the adapter's profiles and marks are
constant and its packet subsequence is the identity.  Every further strict
subsequence selected by the collision residual therefore has the same
post-row semantic tail.  Uniqueness of limits yields

\[
\texttt{residual.cluster}=\operatorname{Sem}(\sigma),
\]

where `sigma` is the actual post-row spine, not the whole pure-pair profile.
The weak core identifies this tail with the reference profile's post-row tail.

In the minimum-tail arm, the residual gives

\[
\lambda D_*/2\le\sum_{p\ne o}\delta_p.
\]

There are exactly three nonnegative terms, so one is at least
`lambda * D_* / 6`.  The pure-pair stage mass is its live mass `L`, with
`L >= lambda`.  The reached-row identity gives

\[
g_p=L\delta_p\ge\lambda^2D_*/6.
\]

Changing only `p`'s own complete strategy leaves `p`'s unrestricted
best-response envelope unchanged, so the checked own-strategy theorem
subtracts this gain exactly from `p`'s debt.  The reasoning does not replace
the unrestricted cap by a stationary or one-step cap.

No inequality controls the other coordinates.  In particular the exact own
debt subtraction is not an aggregate debt decrease.

## 5. The cofinal strengthening works with a two-profile splice

For each depth `n`, choose an owner-compressed endpoint whose retained source
rank is at least `n`.  Let `eta_n` be its compressed target, `sigma_n` its
reference profile, and `t_n` its marked date.  The required repaired profile
is

\[
\operatorname{RootStack}(\eta_n;0,\ldots,t_n)
   \mathbin{\triangleright}\sigma_n,
\]

not `quittingSelfTailClosure reward eta_n t_n`, whose tail would be `eta_n`
itself.  Concretely it can be defined by

```text
quittingLiteralRootStackProfile reward
  (quittingSelfTailRootStack reward eta_n t_n) sigma_n
```

or by a dedicated two-profile splice helper.

The existing self-tail proofs adapt literally:

* roots through `t_n` are those of `eta_n`;
* its marked singleton mass is unchanged;
* its spine after `t_n + 1` is exactly `sigma_n`.

The chronology has `rank_n >= n`, and
`chronology.prefix_debt_tendsto`, together with the source's
`debt_eq_inf`, gives

\[
D(\operatorname{Sem}(\sigma_n))\longrightarrow D_*.
\]

Pureifying and forcing the same outsider `o` preserves this post-row spine.
The resulting moving packet has fixed owner `o`, fixed pair `{j,o}`, fixed
resolution `lambda`, zero marked `o`-defect at every rank, and tail debt
tending to `D_*`.

The collision residual may choose its own subsequence and cluster, but total
debt is continuous.  Hence every such cluster has debt exactly `D_*`, so its
strict tail-escape disjunct is impossible.  The eventual other-defect
inequality remains.  Finite choice and pigeonhole on the three labels other
than `o` yield one fixed recipient on a further strict subsequence, with the
same `lambda^2 D_*/6` actual gain floor.

This is the only place where the note's implementation wording needed repair.
It does not require an additional mathematical hypothesis.

## Boundary and falsification tests

1. **Arbitrary original marked root.**  The original core need only have
   positive `{j}` mass.  Simultaneous pureification can change every player's
   whole-profile payoff and cap.  The theorem does not compare those semantic
   pairs; it uses pureification solely to construct a new literal packet.

2. **Never or late owner deviation.**  At pure `{j}` and pure `{j,o}` roots,
   absorption is unavoidable under the selected outsider's unilateral action.
   The full-gap endpoint comparison is tail-independent.  Later behavioral
   choices cannot falsify it.

3. **Arbitrary post-row tail.**  The arbitrary-core theorem allows any tail.
   It is stored as the collision residual's cluster and may be off the minimum
   fiber.  Only the cofinal splice forces its debt to converge to `D_*`.

4. **Two-sure-quitter channel switch.**  Once the pair is pure, no unilateral
   player can expose the tail.  Thus changing the tail cannot make the pair
   profile near-minimal.  The theorem claims only a minimum *tail* cluster,
   exactly as required by the residual interface.

5. **Recipient may belong to the pair.**  If the selected `p` is `j`, its best
   endpoint may remove it and leave `{o}`.  If it is an outsider, its best
   endpoint may insert it.  In either case the routed terminal stays nonempty,
   the reached-row payoff identity and exact own-debt subtraction remain
   valid, and no support-descent conclusion is inferred.

6. **Negative or zero rewards.**  Only reward differences and the positive
   terminal gap are used.  No positivity of individual rewards or cap
   attainment is assumed.

7. **Vanishing live mass.**  The fixed stage-mass floor and pure pair root give
   `L >= lambda > 0`; the endpoint gain cannot vanish through reach loss.

8. **Changing source ranks.**  Choosing `rank_n >= n` is sufficient for
   convergence along the retained chronology.  The packet does not reselect
   a minimum point, atom, owner, or reward table.

## Export recommendation

Export the corrected note in maximal form after replacing the cofinal
`self-tail-close` shorthand by the explicit two-profile prefix/tail splice.
The packet should state both:

1. the arbitrary-core reduction to actual-tail escape or a minimum-tail
   `lambda^2 D_*/6` transfer; and
2. the owner-compressed cofinal corollary eliminating both the strategic mode
   and the tail-escape arm.

This is a strict contraction of the maintained concentrated-singleton atlas
obligation.  It does not claim to consume the resulting fixed-gain pair
transfer.  The existing review by `SINGLETON_INCENTIVE_AUDITOR` and this
independent all-behavior falsification leave no unresolved mathematical
objection once the splice wording is corrected.
