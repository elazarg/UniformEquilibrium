# KEPLER_CLOCKCONE — star activation source-index audit

Author: `KEPLER_CLOCKCONE`

Status: **exact local nonactivation theorem; no global hard-residual no-go.**
The checked minimum-source interfaces produce one positive atom, and the
checked forced-pair route sends one source-attached singleton cylinder to one
pair edge on one target profile.  Neither owner-clock compression nor the
subsequent paid endpoint produces three incident pair floors on that same
profile.  Moreover the canonical mass scale is numerically below even the
three-copy star threshold.  These are ordinary mathematical consequences of
the checked interface fields; the new clock law itself is not Lean-checked.

This note continues the activation question after the frozen law proof in
`KEPLER_CLOCKCONE__ADJACENT_PAIR_REWARD_PRODUCER_SEARCH.md`.  It does not edit
that note, claim that all future source-faithful constructions fail, or enter
the export queue.

## 1. Exact activation target

For one actual four-clock profile `sigma`, let

```text
q_ij(sigma)=P_sigma({i,j} is the exact finite first-quitter coalition).
```

The sharp star law says

```text
sqrt(q_01)+sqrt(q_02)+sqrt(q_03)<=2/sqrt(3).       (1.1)
```

Consequently three common floors `q_0j>=lambda` contradict the law exactly
when

```text
lambda>4/27.                                      (1.2)
```

The word “one” in “one actual profile” is essential.  Pair masses obtained
on three different replacement profiles cannot be inserted into (1.1).

## 2. Checked source interfaces inspected

The following declarations were read under their actual imports.

- `finFourHardResidual_minimumLaw_causalSuffixAtom` and
  `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`
  attach one positive finite coalition coordinate to a minimum joint-law
  point.  The terminal is existential and need not be a pair or singleton.
- `FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton` and
  `FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`
  in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
  apply when that terminal is a singleton.  They change only the singleton
  owner at one selected date and prove one singleton stage-mass floor.
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`
  selects one strict table-level outsider join at a pure singleton.
- `FinFourAtlasWeakConcentratedSingletonCore.pureSingletonProfile`,
  `FinFourWeakCoreForcedPairPacket.pairProfile_eq_purePair`,
  `resolution_le_forcedPairStageMass`, and
  `payerTargetProfile_eq_pureRouted` in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` give the exact
  one-date pure singleton, forced pair, retained mass, and paid endpoint.
- `FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone`
  in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
  allows every resolution `0<lambda<mu` on one retained chronology and with
  one table outsider fixed outside the resolution quantifier.

The docstrings explicitly make no target-side Nash, near-minimality,
total-debt descent, or whole-source return claim.

## 3. What owner compression says about the three star coordinates

Orient the singleton owner as player `0`.  At the selected date write `L` for
live reach, `y_j` for opponent `j`'s Quit hazard, and `Y_j=1-y_j`.  The
owner-compressed target makes player `0` Quit surely, so its four relevant
stage masses are exactly

```text
m_0  =L*Y_1*Y_2*Y_3,
m_01 =L*y_1*Y_2*Y_3,
m_02 =L*Y_1*y_2*Y_3,
m_03 =L*Y_1*Y_2*y_3.                              (3.1)
```

The checked field is only `m_0>lambda`.  It implies `Y_j>0` and the identities

```text
m_0j=m_0*y_j/Y_j,                                 (3.2)
```

but gives no positive lower bound on any `y_j`.  All three values may be zero
at the level of the stated local fields.  Thus clock compression supplies a
large singleton cylinder, not three star edges.

This is not a claim that a full hard residual realizes arbitrary values in
(3.1).  It is the exact information content of the checked compression
conclusion, and identifies the additional field an activation proof would
need.

## 4. One strict outsider replacement routes to exactly one edge

Suppose the collision theorem selects outsider `1`, and replace player `1`'s
marked action by sure Quit.  On the same reached row, (3.1) becomes

```text
m'_01=L*Y_2*Y_3=m_0/Y_1>lambda,
m'_02=m'_03=0.                                   (4.1)
```

In the checked forced-pair compiler the row is first overwritten by the pure
singleton, so `Y_1=Y_2=Y_3=1`; then (4.1) is the literal pure pair and its mass
is the entire reached live mass.  This is precisely
`pairProfile_eq_purePair` and `resolution_le_forcedPairStageMass`.

Therefore one source-faithful strict join does not duplicate a singleton
atom over several pair labels.  It routes that atom exclusively to the one
edge `{0,1}`.  Pair events already present before the marked date remain in
the whole law, but the packet supplies no lower bound on any of them.  The
post-date minimum tail is unreachable on the marked cylinder and supplies no
later pair event there.

## 5. The paid endpoint does not create a second pair label

Let `C={0,1}` be the forced pair and let `p!=1` be the payer selected by the
checked defect pigeonhole.  Its best-endpoint update toggles membership of
`p` in the pure coalition `C`.

- If `p=0`, the routed coalition is either `{0,1}` or `{1}`.
- If `p` is outside `C`, the routed coalition is either `{0,1}` or the triple
  `{0,1,p}`.

Thus every pair terminal reachable by the paid endpoint is still the same
edge `{0,1}`.  The positive payer-gain and exact debt-subtraction fields are
real, but they do not furnish `q_02` or `q_03`.

There is also a chronology obstruction to stacking checked pure-pair
packets.  Once two players Quit surely at a reached date, absorption is sure
on every surviving path.  Any later marked pair has zero mass.  If another
sure pair is inserted earlier, it instead kills the later one.  Hence several
pure forced-pair packets can coexist only as objects on different profiles,
not as three positive chronological rows of one profile.

## 6. Two independent quantitative blockers

Write

```text
mu=source.point.2(some source.atom.terminal).
```

The common weak-core interface uses the canonical resolution

```text
lambda_can=mu^2/8<=1/8<4/27.                     (6.1)
```

Even if three copies of this floor could somehow be synchronized, they would
give at most

```text
3*sqrt(lambda_can)<=3/sqrt(8)<2/sqrt(3).         (6.2)
```

So the canonical packet is too small for the star consumer before the
same-profile issue is reached.  The arbitrary-resolution minimum-return
family removes this numerical loss, but only conditionally: a star
contradiction would require `mu>4/27` so that one may choose
`4/27<lambda<mu`.  The minimum-law atom theorem proves only `mu>0`.

Even under that extra mass hypothesis, the arbitrary-resolution family fixes
one outsider and returns one pair edge per target profile.  It does not fix
the synchronization failure of Sections 4--5.

## 7. Exact quantifier and law-cone regressions

For every `0<lambda<=1` and each `j=1,2,3`, there is an independent-clock law
`rho_j` with

```text
q_0j(rho_j)=lambda, all other exact pair masses zero:  (7.1)
```

make player `0` stop at date zero surely, player `j` stop there with
probability `lambda` and otherwise `Never`, and every other player `Never`.
Thus the separate-profile statement

```text
for every j, there exists rho_j with q_0j(rho_j)>=lambda
```

is consistent even for `lambda=1`.  When `lambda>4/27`, (1.1) proves that the
quantifier-swapped statement

```text
there exists rho such that every q_0j(rho)>=lambda
```

is false.  This is the smallest exact regression against combining forced
pair packets selected on different source-faithful targets.

More generally, the four-clock law cone contains the entire one-edge ray
`0<=q_e<=1` by the same construction.  Therefore no reward-independent
inequality in the six pair masses can contradict the only mass datum
`q_e>=lambda<=1`.  A weighted or global `K_4` consumer still needs a second
same-profile law coordinate, or a non-mass quantity tied to the law by a new
theorem.  Table-level collision gains alone provide no such tie.

## 8. Precise surviving activation question

The present source data do not activate the star law.  A successful next
theorem must add at least one of the following genuinely new fields:

1. one actual profile carrying three incident pair floors with at least one
   scale pattern crossing (1.1);
2. a source-faithful mixed marked root, rather than a pure endpoint, whose
   three leaf hazards have quantitative lower bounds and whose whole debt is
   controlled;
3. a cross-profile inequality that legitimately couples several replacement
   laws before applying a clock-law consumer; or
4. a new law inequality involving the one forced pair mass and an existing
   same-profile quantity already present in the minimum source.

The first three are producers, not consequences of the star law.  The fourth
is currently only a search direction: the checked minimum-source packet has
one law atom and reward/debt inequalities, but no second pair-law coordinate
linked to them.

## 9. Next exact question

At an arbitrary-resolution owner-compressed singleton with `mu>4/27`, can one
retain a genuinely mixed marked row and use three different players' complete
cap inequalities to lower-bound all three ratios `y_j/Y_j` in (3.2), without
pureifying the row or losing minimum-source control?  A negative answer should
be an explicit same-table product-root regression; a positive answer must
return one profile, not three separately indexed endpoints.
