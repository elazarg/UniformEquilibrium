# Audit of the completion transition system

Reviewer: `CODEX_RIEMANN`

## Verdict

**FAIL as a typed transition graph; the underlying declarations are sound.**

The new section conflates three different objects:

1. a scalar maximal-ray minimum return, which supplies a semantic chord but
   no endpoint law or regenerated source;
2. an actual three-role endpoint law, whose exhaustive result is strict ascent
   **or** minimum-source regeneration; and
3. the regeneration disjunct itself, which really contains a new
   `FinFourMinimumAtomProducer`.

It also says that the support handoff reconstructs an atlas source.  It does
not: it reconstructs a positive-minimum tangent family.  These distinctions
invalidate the displayed strongly connected pattern as a presently proved
SCC.

## 1. The entrance to `ForcedPair` is singleton-typed

The checked constructor is

```text
FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairSource
```

in `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`.
It requires

```text
source.atom.terminal.val.card = 1.
```

The quantified version is

```text
FinFourMinimumAtomProducer.exists_minimumReturnForcedPairSource_for_all_resolutions.
```

Therefore the table edge is not

```text
MinimumSource -> ForcedPair
```

for an arbitrary `FinFourMinimumAtomProducer`.  It is

```text
SingletonMinimumSource -> ForcedPair.
```

The checked reductions from nonsingleton atoms to concentrated singleton
endpoints do not by themselves change the selected atom of the incoming
minimum joint-law source into a singleton minimum-law atom.

## 2. `MaximalPrefixRayMinimumReturn` does not contain regeneration

The exact scalar-ray dichotomy is

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket.
  nonempty_maximalPrefixRayMinimumReturn_or_stall
```

in `MaximalPrefixRayDichotomy.lean`.  Its equality object
`MaximalPrefixRayMinimumReturn` has precisely:

- `limit_eq`;
- `eventuallyTransfer`; and
- `limitChord : exists mover recipient, Nonempty ThreeRoleLimitChord`.

It does **not** contain an endpoint terminal law, a routed-law atom, or a
`FinFourMinimumAtomProducer`.  Accordingly, the `MinimumReturn` table row must
not say that a regenerated endpoint source is part of this node.

The source-attached support refinement is separately proved by

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket.
  nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_of_return
```

in `CanonicalPairMinimumEndpointSupportRankHandoff.lean`.  That still does not
turn the scalar `MinimumReturn` itself into a source-return object.

## 3. The exact three-role return theorems

The actual endpoint-law constructor is

```text
QuittingMarkedPairMinimumReturnActualizer.
  nonempty_threeRoleEndpointLaw_of_minimumReturn
```

in `ConcentratedCollisionThreeRoleEndpointLaw.lean`.  Its output retains the
actual endpoint joint law and routed atom.

For such an endpoint, the exact exhaustive Fin4 theorem is

```text
ConcentratedCollisionThreeRoleEndpointLaw.
  nonempty_finFourRegenerationOrAscent
```

in `FinFourProducerAtlas/ThreeRoleRegeneration.lean`.  The output
`FinFourThreeRoleRegenerationOrAscent.outcome` is

```text
strict target-debt ascent
or
Nonempty (FinFourThreeRoleMinimumTargetRegeneration source endpoint).
```

Only the second disjunct is a return edge.  It is constructed by

```text
ConcentratedCollisionThreeRoleEndpointLaw.
  nonempty_finFourMinimumTargetRegeneration
```

under the explicit equality of target debt with the incoming minimum.  The
result really contains

```text
next : FinFourMinimumAtomProducer reward bound
```

together with `next_residual_eq`, `next_point_eq`, `next_terminal_eq`, and the
retained mass floor.  This justifies the conditional typed edge

```text
ThreeRoleMinimumRegeneration -> MinimumSource.
```

It does not justify `MinimumReturn -> MinimumSource`, and the exhaustive
three-role result must retain its strict-ascent arm.

The current source-facing composition is exposed by

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket.
  nonempty_normalizedReturnThreeRole_or_strictInert
FinFourNormalizedReturnSourceCapstone.
  regenerationOrAscent_or_strictInert.
```

Those statements likewise return regeneration-or-ascent in the equality arm,
not unconditional regeneration.

Finally, `next_point_eq` means that the regenerated source is at the exact
**endpoint** semantic/law point.  It is generally not the incoming
`source.point`.  The phrase “same-point regeneration” is safe only if it is
explicitly qualified as same endpoint point/law, not return to the incoming
point.

## 4. `SupportHandoff` does not reconstruct an atlas source

The generic structure

```text
QuittingMinimumEndpointSupportRankHandoff
```

in `StoppingLawMinimumEndpointSupportRankHandoff.lean` contains
`parentFamily` and `nextFamily`, both of type
`QuittingPositiveMinimumDebtTangentFamily reward`, and proves

```text
nextFamily.positiveDebtSupport < parentFamily.positiveDebtSupport.
```

The source-facing wrapper

```text
CanonicalPairMinimumEndpointSupportRankHandoff
```

retains the incoming ray packet and the generic handoff, but has no field of
type `FinFourMinimumAtomProducer` for the endpoint.  In particular it does not
retain a new joint law, named causal atom, causal chronology, or regenerated
hard-residual source object.

Thus the sentence “`SupportHandoff` also reconstructs a source” is false in
the atlas sense used by this section.  Replace it by:

> `SupportHandoff` re-extracts a tangent family at the endpoint and proves a
> one-time support drop relative to a newly constructed half-mixture tangent
> parent.  No checked adapter reconstructs a `FinFourMinimumAtomProducer` at
> that endpoint.

There is consequently no `SupportHandoff -> MinimumSource` edge.

## 5. The claimed SCC is not currently proved

The displayed pattern

```text
MinimumSource -> ForcedPair -> MinimumReturn/ThreeRoleReturn -> MinimumSource
```

is not a proved strongly connected component.

- The first arrow requires a singleton selected source atom.
- `MaximalPrefixRayMinimumReturn` has no regenerated source.
- The actual three-role classifier may return strict ascent instead of
  regeneration.
- Even in the regeneration arm,
  `FinFourThreeRoleMinimumTargetRegeneration.next_terminal_eq` identifies the
  next atom with the routed terminal but proves no singleton-cardinality fact.
  Hence the regenerated `MinimumSource` is not automatically in the domain of
  `nonempty_minimumReturnForcedPairSource`.

What is checked is a conditional one-way return:

```text
ThreeRoleMinimumRegeneration -> MinimumSource.
```

A loop exists only after additionally proving that the regenerated named atom
is singleton (or producing a different forced-pair constructor for arbitrary
minimum atoms).  The loss of the paid orientation is a further obstacle to a
ranked loop, but it is not the first typing obstruction.

## 6. Infinite-ray cardinality is also conditional

The three-way declaration

```text
FinFourBindingPairParityCertificate.
  positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three
```

in `StrictRayBindingCardinality.lean` requires a supplied
`FinFourBindingPairParityCertificate`.  The same file explicitly states that
no theorem constructs this certificate.  Its fields include both the
cardinality-one exclusion and the parity data excluding cardinality two.

Therefore `InfiniteRay -> PositiveLimitRoot/FullBindingRay/CardThreeRay` is a
conditional edge, not checked exhaustive outgoing information.  Without the
certificate, both cardinality-one and cardinality-two binding nodes remain;
the text currently mentions only the latter.

## Required table correction

Split the overloaded nodes as follows:

```text
SingletonMinimumSource
  -> ForcedPair
  -> RayMinimumReturn or StrictRay

RayMinimumReturn
  -> SupportHandoff or EndpointDebtAscent

ActualThreeRoleEndpointLaw
  -> ThreeRoleTargetAscent or ThreeRoleMinimumRegeneration

ThreeRoleMinimumRegeneration
  -> MinimumSource

SupportHandoff
  -> TangentFamilyChild only (open atlas-source adapter)
```

No nonterminal SCC is presently established by checked typed edges.  The
three-role regeneration arrow is a genuine and important source-return edge,
but the graph must not close it into a cycle until the next source is shown to
re-enter a proved source constructor.

## Post-repair verification

**PASS.**  The revised section now separates `MinimumSource` from
`SingletonMinimumSource`, keeps scalar `RayMinimumReturn` distinct from the
actual endpoint-law and regeneration objects, records the ascent disjunct,
types `SupportHandoff` only as a tangent-family child, and states only the
genuine one-way `ThreeRoleMinimumRegeneration -> MinimumSource` edge.  It no
longer claims a checked SCC.  The infinite-ray split is correctly conditional
on the supplied parity certificate and retains both cardinality-one and
cardinality-two nodes without it.  I find no remaining source-typing error in
the repaired transition section.

## Files inspected

- `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
- `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
- `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`
- `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`
- `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`
- `Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`
- `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`
