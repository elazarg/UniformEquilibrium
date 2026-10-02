# Collision minimum: the sole compiler seam is whole-source return

Author: `ATLAS_GATEKEEPER`

## Status

This is outcome **(b)** of the collision-minimum synthesis: there is one
precise near-composition, with exactly one missing hypothesis.

The independently reviewed minimum-return construction produces a
source-attached Quit-mode concentrated packet with a fixed pair terminal,
literal tails converging to the chosen positive global minimum, zero marked
defect for the packet owner, and a fixed aggregate defect on the other three
coordinates.  Every hypothesis of the checked three-role compiler is then
co-realized except

\[
 D(\text{whole packet source at rank }n)\longrightarrow D_*.
 \tag{SR}
\]

If `(SR)` is supplied, the checked collision machinery produces recurrent
three-role transfers and a compact signed limit chord; its tail-escape arm is
eventually impossible.  Conversely, `(SR)` cannot be obtained by changing
only the post-row tail: in the Quit mode two distinct players Quit surely at
the marked row, so the entire terminal semantic pair is exactly independent
of that continuation, even against arbitrary unilateral behavioral
deviations.

Thus the one missing producer is a **whole-source return** which changes or
controls the marked past/root, not another minimum-return tail splice.

## Exact reviewed input

Fix an owner-clock minimum-singleton source, its retained chronology, and

\[
 0<\lambda<\mu(\{j\}),
\]

where (j) is the singleton owner.  The repaired construction in
`CODEX_ROOT__MINIMUM_RETURN_STRONG_SINGLETON_PACKET.md`, independently audited
in
`feedback/CODEX_ROOT__MINIMUM_RETURN_STRONG_SINGLETON_PACKET__BY_SINGLETON_INCENTIVE_AUDITOR.md`,
selects cofinally deep owner-compressed endpoints and then:

1. copies each literal source word through its marked singleton row;
2. restarts the actual minimum-approaching source profile after that row;
3. fixes one packet owner (o\ne j);
4. changes only (o)'s marked action to its exact best Boolean endpoint; and
5. passes to one fixed-action subsequence.

In the Quit subsequence, write the resulting packet as `packet`, its profiles
as \(\rho_n\), and its marked dates as \(t_n\).  It has the following literal
fields:

\[
 T=\{j,o\},\qquad |T|=2,
 \tag{1}
\]

\[
 \lambda\le
 \Pr_{\rho_n}(T\text{ absorbs at }t_n),
 \tag{2}
\]

\[
 \delta_o(\operatorname{root}_{\rho_n}(t_n);
 U(\operatorname{tail}_{t_n+1}\rho_n))=0,
 \tag{3}
\]

and, for the selected minimum semantic pair (X_*),

\[
 \operatorname{Sem}(\operatorname{tail}_{t_n+1}\rho_n)
 \longrightarrow X_*.
 \tag{4}
\]

The two members (j,o) both Quit surely at the marked row.  Equation (2) is
not merely a positive pair cylinder in this owner-clock subcase: the pair's
conditional root mass is the probability that the other two players
Continue, while (j) and (o) are pure Quit.

Applying
`QuittingTerminalExploitabilityWitness.concentratedPacket_singletonStrategic_or_collisionMinimumResidual`
to this pair packet first gives its stated singleton/collision disjunction.
The singleton arm contains the equality `terminal.val = {other}`, which is
incompatible with (1); therefore the returned object is a
`QuittingConcentratedCollisionMinimumResidual`.  Uniqueness of limits and
(4) identify its stored `cluster` with (X_*).  Hence its strict tail-escape
disjunct is false and its exact second arm gives eventually

\[
 \frac{\lambda D_*}{2}
 \le
 \sum_{i\ne o}
 \delta_i(\operatorname{root}_{\rho_n}(t_n);
 U(\operatorname{tail}_{t_n+1}\rho_n)).
 \tag{5}
\]

This is a strict narrowing of a generic collision-minimum residual: its tail
cluster is the actual selected minimum, not merely an arbitrary carrier
point satisfying the residual's inclusive escape/equality split.

## The one-field checked composition

The checked theorem

```text
ConcentratedCollisionFourRole.
  packet_eventually_tailEscape_or_threeRoleTransfer
```

requires:

1. a positive global carrier minimum and (D_*>0);
2. a fixed nonsingleton packet terminal;
3. positive packet scale and scale tending to zero;
4. vanishing marked defect for the packet owner; and
5. convergence of the **whole packet source debts** to (D_*).

Items 1--4 are exactly the fields above and the generic packet fields.  Item
5 is `(SR)`.  No further label, atom, cap, or strategy-class premise is
missing.

Assume `(SR)`.  The checked theorem gives eventually

\[
 \operatorname{packetEscape}(n)
 \quad\lor\quad
 \operatorname{Nonempty}(\operatorname{packetTransfer}(n)).
 \tag{6}
\]

But by (4),

\[
 D(\operatorname{tail}_{t_n+1}\rho_n)-D_*\longrightarrow0,
\]

whereas `packetEscape` requires the fixed positive lower bound

\[
 \frac{\lambda D_*}{2}
 \le D(\operatorname{tail}_{t_n+1}\rho_n)-D_*.
\]

Therefore the first arm of (6) is eventually false.  Consequently

\[
 \boxed{
 \forall^\infty n,\quad
 \operatorname{Nonempty}(\operatorname{packetTransfer}(n)).}
 \tag{7}
\]

Finiteness freezes one mover--recipient pair and one decoder mode/terminal
label on a cofinal subsequence.  The checked theorems

```text
packet_tailEscapeFrequently_or_fixedThreeRoleTransfer
packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel
exists_threeRoleLimitChord_of_frequently_packetTransferRoles
```

then give a `ThreeRoleLimitChord` with:

- source total debt exactly (D_*);
- a fixed mover distinct from the packet owner;
- a fixed recipient distinct from the mover;
- a fixed positive mover-debt loss;
- a fixed positive recipient-debt rise; and
- target total debt either (D_*) or strictly above (D_*).

This is the complete checked consequence of `(SR)`.  No stationarity or
bounded-deviation restriction is introduced: the semantic debts and endpoint
recipient atoms use unrestricted behavioral caps.

## Exact no-go for the obvious repair

The missing field cannot be generated by replacing the continuation in (4).

### Two-sure-quitter shielding theorem

Fix any finite prefix through a row at which two distinct players (j,o)
Quit surely.  Attach arbitrary complete behavioral tails (Z,Z') after the
all-Continue outcome of that row.  The resulting profiles have exactly the
same terminal semantic pair:

\[
 \boxed{\operatorname{Sem}(P\triangleright Z)
       =\operatorname{Sem}(P\triangleright Z').}
 \tag{8}
\]

Under prescribed play the row absorbs surely.  Under a deviation by (j),
(o) remains a sure quitter; under a deviation by (o), (j) remains; and
under any other player's deviation both remain.  Thus the continuation is
unreachable under every unilateral behavioral deviation.  Prescribed payoff
and every fixed deviation payoff are tail-independent, and taking the
supremum preserves equality of caps.  This includes Never, arbitrarily late
stopping, and randomized/history-dependent strategies.

This is the theorem recorded in
`SINGLETON_INCENTIVE_AUDITOR__TWO_SURE_QUITTER_TAIL_REPLACEMENT_NOGO.md`.
Applied to the Quit packet, it says that installing the minimum-approaching
tail proves (4) but cannot change

\[
 D(\rho_n)-D_*.
 \tag{9}
\]

In particular no self-tail closure, two-anchor tail closure, delayed minimum
tail, or other post-row repair can prove `(SR)` unless the whole source was
already returning to the minimum for a separate reason.

## Why the other reviewed routes do not supply `(SR)`

The fixed-weight independent-law graft in
`CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md` does construct new
actual sources inside a fixed near-minimum tube while retaining the pair atom.
Its universal estimates, however, have incompatible scales for this
compiler.  With graft weight \(a\), source excess is controlled only at order
\(a\), while the four independent marginal branches retain the marked atom
at order \(a^4\); the collision threshold in the three-role theorem is
quadratic in that mass, hence order \(a^8\).  The reviewed calculation shows
that the universal bounds cannot make the order-(a\) toll smaller than the
order-(a^8\) threshold.  Taking (a_n\to0) restores exact source-debt
convergence but destroys the fixed positive packet resolution.

Same-stage purification and endpoint routing have the opposite behavior:
they retain the literal pair row and tail at fixed scale, but can alter the
whole semantic pair and all cross-coordinate caps by order one.  The
recipient and support-drop results require the very near-minimum whole-source
premise they therefore do not preserve.

These are not two additional missing lemmas.  They are failed constructions
of the single field `(SR)`.

## Precise missing lemma

The remaining producer can be stated without another diagnostic split.

> **Whole-source return for the source-attached Quit packet.**  Starting from
> the owner-clock minimum-return Quit-mode construction above, produce either
> an accepted atlas output directly, or a (possibly modified) concentrated
> pair packet with the same fixed positive resolution and source attachment,
> whose whole source debts converge to (D_*), while retaining vanishing
> marked owner defect and literal tails converging to (X_*).

Only the second output is needed to invoke (7) and the checked three-role
limit-chord machinery.  By (8), any proof of this lemma must control or modify
the marked past/root; a proof acting solely after the pair row is impossible.

No current regression rules out such a past/root repair under the full
positive-minimum hard residual.  The available exact regressions have global
minimum zero or omit the ambient terminal witness.  Conversely, no current
declaration or reviewed theorem provides the required fixed-resolution
whole-source convergence.

## Scope after the missing lemma

The resulting `ThreeRoleLimitChord` is a strictly smaller exact residual, not
yet a uniform-equilibrium theorem.  In its minimum-target arm, the reviewed
maximum-support common-chord theorem can give a source-regenerated strict
support drop when its maximum-support base hypothesis is arranged.  In its
strict-target arm, a fixed off-minimum excursion remains.  Those are the
honest downstream obligations; they are not folded into the single producer
lemma above.

## Declarations and records inspected

- `QuittingConcentratedCollisionMinimumResidual` and
  `concentratedPacket_singletonStrategic_or_collisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
- `ConcentratedCollisionFourRole.tailEscape_or_threeRoleTransfer`,
  `.packet_eventually_tailEscape_or_threeRoleTransfer`,
  `.packet_tailEscapeFrequently_or_fixedThreeRoleTransfer`,
  `.packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel`, and
  `.exists_threeRoleLimitChord_of_frequently_packetTransferRoles` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
- `FinFourOwnerCompressedSingletonEndpoint` and
  `FinFourMinimumAtomChronology.profiles_tendsto` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `QuittingStageAtomConcentratedPacketAdapter.targetTail_eq_sourceTail` and
  `.ownerMarkedDefect_eq_zero` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `formalized/FIN4_MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET.md`,
  `formalized/SAME_STAGE_ENDPOINT_MONODROMY_REDUCTION.md`, and
  `formalized/FIN4_MONODROMY_PRODUCER_IMPOSSIBLE.md`;
- `CODEX_ROOT__MINIMUM_RETURN_STRONG_SINGLETON_PACKET.md` and its independent
  audit;
- `SINGLETON_INCENTIVE_AUDITOR__TWO_SURE_QUITTER_TAIL_REPLACEMENT_NOGO.md`;
- `CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md` and its two
  independent reviews; and
- `CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md` and its
  independent review.
