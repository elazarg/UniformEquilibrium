# Minimum-return strong singleton packet

Author: `CODEX_ROOT`

## Status

Proof candidate.  The literal construction and scalar convergence argument
are complete below.  The remaining audit is whether the existing packet
consumer can be instantiated without an index mismatch after selecting the
cofinal endpoints and the fixed auxiliary packet owner.

If the audit passes, this removes the off-minimum-cluster alternative from the
collision-minimum branch of the strong concentrated-singleton consumer.  It
does not consume the remaining positive other-coordinate root defects.

## Question

The checked singleton route presently converts each positive singleton stage
atom into a **constant** concentrated packet.  Its post-row tail is then a
fixed arbitrary tail, so the existing collision residual may select a cluster
strictly above the positive minimum fiber.

Can one instead use the retained cofinal minimum chronology to build one
nonconstant packet whose post-row tails converge back to the selected minimum?

## Construction

Fix

```text
source : FinFourMinimumAtomProducer reward bound
producer : FinFourOwnerCompressedSingletonProducer source
```

and a resolution

\[
0<\lambda<\nu_*(\{j\}).
\]

For each depth `n`, choose one checked owner-compressed endpoint `e_n` with
`e_n.rank >= n`.  Write

```text
sigma_n := e_n.referenceProfile,
t_n     := e_n.stage.
```

The checked source account gives

\[
D(\sigma_n)\longrightarrow D_*,
\tag{1}
\]

because `sigma_n` is the retained cap-prefixed profile at rank `e_n.rank`, the
ranks tend to infinity, and `chronology.prefix_debt_tendsto` holds.

The endpoint `e_n.targetProfile` copies `sigma_n` except that the singleton
owner is forced to Quit at `t_n`; its singleton stage mass is greater than
`lambda`.

Now form the self-tail closure

\[
\widehat\sigma_n
  :=[\operatorname{root}_{e_n.targetProfile}(0),\ldots,
      \operatorname{root}_{e_n.targetProfile}(t_n)]
      \triangleright \sigma_n.
\tag{2}
\]

Exactly as in the nonsingleton self-tail theorem:

1. every live root through `t_n` is copied literally;
2. the singleton stage mass at `t_n` remains greater than `lambda`;
3. the complete behavioral tail strictly after `t_n` is literally `sigma_n`.

Choose one fixed player `o != j` after finite pigeonhole if necessary, and at
the marked row replace only `o` by its exact best endpoint against
`U(sigma_n)`.  Call the result `rho_n`.  This update:

1. retains stage mass at least `lambda`, routed to `{j}` or `{j,o}`;
2. retains the complete post-row tail `sigma_n`;
3. makes `o`'s marked root-coordinate defect exactly zero.

Thus the moving family `rho_n`, with marks `t_n`, cutoffs `t_n+1`, resolution
`lambda`, identity subsequence, and any positive scale tending to zero, is a
`QuittingReprojectionConcentratedPacket`.  Unlike the existing constant
adapter, its post-row tail semantic pairs satisfy the scalar account (1).

## Consequence for every collision residual

Apply

```text
concentratedPacket_singletonStrategic_or_collisionMinimumResidual
```

to this moving packet.  In the collision arm the returned subsequence has a
semantic tail cluster `z`.  Continuity of total debt and (1) give

\[
D(z)=D_*.
\tag{3}
\]

Therefore the strict tail-escape disjunct

\[
D_*<D(z)
\]

is impossible.  The residual is forced into its second arm:

\[
\sum_{i\ne o}\operatorname{Defect}_i
\ge \lambda D_*/2
\quad\text{eventually},
\tag{4}
\]

while `o`'s marked defect tends to zero and all rows retain the same positive
stage-mass floor and their literal minimum-approaching tails.

For Fin4, (4) freezes one player `p != o` with root defect at least
`lambda D_*/6` on a subsequence.  Since the live mass at the marked row is at
least the stage mass, the corresponding exact best-endpoint one-date update
has actual behavioral gain at least

\[
\lambda^2D_*/6.
\tag{5}
\]

It subtracts (5) exactly from `p`'s unrestricted debt and routes the marked
atom without loss.  This last transfer is executable, but no checked theorem
currently turns it into a return or well-founded support descent.

## Source audit

Inspected declarations:

- `FinFourMinimumAtomChronology.profiles_tendsto` and
  `.prefix_debt_tendsto` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `FinFourOwnerCompressedSingletonEndpoint.referenceProfile`,
  `.targetProfile`, and `.target_stageMass_gt` in the same file;
- `QuittingStageAtomConcentratedPacketAdapter` and its exact tail, mass,
  endpoint-defect, and packet fields in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `QuittingConcentratedCollisionMinimumResidual` and
  `concentratedPacket_singletonStrategic_or_collisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`; and
- the self-tail identities used by
  `FIN4_NONSINGLETON_MINIMUM_LAW_SELF_TAIL_CONTRACTION`.

The present checked strong adapter repeats one target profile constantly.  No
existing declaration builds the moving minimum-return packet (2).

## Boundary and nonclaims

- Scalar debt convergence suffices only to force (3); semantic convergence of
  the whole `sigma_n` sequence is unnecessary because the consumer selects a
  cluster.
- The copied prefix roots are not asserted cap--Nash against the restarted
  tail, and the packet definition does not require this.
- The whole profiles `rho_n` need not approach the minimum fiber.
- Equation (5) is an exact one-player debt subtraction, not a total-debt
  decrease.  Other caps may rise.
- This note does not claim terminal approximants, a cumulative return, or
  atlas regeneration.

## Next exact check

Verify the dependent construction of one family `rho_n` in which the selected
endpoint ranks tend to infinity and one auxiliary packet owner is fixed.  If
that succeeds, seek an independent review of (3)--(5) and decide whether
eliminating the off-minimum collision arm is a strict enough atlas contraction
for export.
