# Review of `SOURCE_PRESERVING_ATLAS.md`

## Verdict

I find the proposed reduction mathematically sound at ordinary-mathematics
level, subject to formalizing the four explicitly identified stream-packaging
lemmas.  I found no source-provenance substitution and no hidden claim that a
horizontal paid update is a chronological Nash--Bellman edge.

The result is important, but its importance is precise: it answers the
effective finite-roadmap question by reducing every hypothetical Fin4
counterexample to one of two source-attached stream capstones.  It does not
consume either capstone and therefore does not prove Fin4 UE.

## Claim reviewed

For every four-player reward table without a uniform-equilibrium payoff, one
fixed hard-residual/minimum-law source can be retained and organized into a
cofinal sequence of literal singleton frames.  Applying the checked forced-pair
construction framewise and stabilizing the finite labels gives a nonnegative
tail-excess sequence

```text
e_n = D(actual post-row tail_n) - D_*.
```

After a strict subsequence, either:

1. `e_n >= delta > 0` at every retained frame (`uniformEscape`); or
2. `e_n -> 0` (`minimumReturn`).

Dropping the first frame gives literal self-transitions in either mode.  Thus
the finite mode graph has one entrance mode and two terminal self-shift SCCs.

## Checked ingredients inspected

The following current declarations support the game-theoretic content of the
proposal.

- `uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy` in
  `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` supplies
  the four surviving source-attached entrances.
- `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer` and
  the endpoint accessors in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
  retain one chronology, cofinal source ranks, a one-date literal target,
  the exact root stack over the reference suffix, and the post-date tail.
- `SelectedRows.eventually_stageMass_gt_square_div_eight` and
  `SelectedRows.prefix_debt_tendsto` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean` permit the
  nonsingleton construction on one fixed selected-row family at every
  sufficiently late rank.
- `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` and the
  source wrapper in
  `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean`
  provide the literal singleton endpoint, no-loss mass, at most three paid
  preterminal edges, and complete off-date profile preservation.
- `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` proves the
  singleton-to-pair gap, zero forced-owner defect, a payer defect at least
  `D_* / 3`, reached gain at least `lambda * D_* / 3`, exact payer-debt
  subtraction, and literal post-date tail preservation.
- `FinFourWeakCoreForcedPairPacket.collisionCluster_eq_corePostDateTail` and
  `nonempty_forcedPairResidualCapstone` in
  `Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`
  identify the collision residual's cluster with the actual frame tail.

Current repository head during this review was
`768d4ea23fe1f270237906c92ab7b5d26cd43bcc`, newer than the source note's
recorded audit head.  The named declarations remain present.  I did not treat
their presence as compilation evidence for the new atlas structures.

## Reconstruction of the new steps

### One cofinal singleton stream

If the retained minimum-law atom is a singleton, recursively request an
owner-compressed endpoint beyond the previous selected rank.  Its actual ranks
are strictly increasing.  Since the reference-prefix debt converges along the
whole chronology, it also converges along this strict subsequence.

If the atom is nonsingleton, select one `SelectedRows` object.  Its stage-mass
lower bound is eventual, so ranks `N + n` give a cofinal stream.  Apply pure
nonsingleton screening independently at each retained rank.  Each output is a
literal singleton at the same marked date, with the same post-date tail and at
least the canonical mass.  This construction does not use the old residual
tag; hence it applies uniformly to every monodromy-free entrance carrying the
same source.

These two origins have the common interface claimed in the note.  In the
singleton origin, the reference owner is already pure Continue on the
intervening live rows, and the target is definitionally a single selected-date
override; there is no hidden multi-date modification.

### Framewise forced pair

Pureifying a singleton frame changes only its marked root, preserves the live
mass reaching that root, and leaves the complete post-date tail unchanged.
The hard-residual table gap forces one outsider to Quit, producing a pure pair
with zero defect in that outsider coordinate.  Pure-nonsingleton screening of
the continuation then gives

```text
D_* <= sum_{i != forcedOwner} markedDefect_i,
```

so one of the three remaining players has defect at least `D_* / 3`.
Multiplication by the retained live mass gives the stated paid gain.  The
checked collision consumer identifies its cluster with this exact frame's
post-date tail, so `e_n` is attached to the same literal row rather than an
independently selected carrier point.

### Exhaustive scalar split

For a nonnegative real sequence `e_n`, failure of convergence to zero gives
some positive threshold exceeded infinitely often; retaining those indices
gives `uniformEscape`.  Otherwise `e_n -> 0`, giving `minimumReturn`.  Finite
pigeonhole stabilizes the owner, forced outsider, payer, and Boolean payer
action first, and composition with a further strict subsequence preserves the
strictly increasing source ranks.

This is an exhaustive priority split.  It should not be advertised as saying
that the original sequence cannot possess both a positive-excess subsequence
and a zero-excess subsequence.

## Required corrections and presentation cautions

1. `CertifiedGap` is displayed as a pair `(gamma,h)`, but `h` is unused.  The
   definition should contain only `gamma`, or state the intended role of `h`.
2. The reward bound should be explicitly existentially chosen in the global
   theorem, preferably the canonical finite reward bound, because the checked
   coverage theorem takes a supplied bound.
3. `FinFourCompletionTerminal` should name the exact checked return/compiler
   proposition rather than say “accepted by an existing compiler.”  This is
   an interface clarification, not a mathematical gap.
4. “Exactly one” in the stream dichotomy should mean the priority
   construction used in the proof.  The two kinds of subsequence need not be
   intrinsically mutually exclusive for one raw sequence.
5. The two terminal SCCs are terminal in the deliberately defined
   three-mode transition system.  They are not claimed to be intrinsic SCCs
   of every finer semantic transition graph.  Their substance comes from the
   source-attached packet fields and exhaustive entrance theorem, not from the
   self-loop computation itself.

## What this does and does not settle

If formalized as stated, this resolves the maintained question
`FIN4_EFFECTIVE_FINITE_COMPLETION_ROADMAP.md`: every indefinite positive-gap
Fin4 obstruction is reduced to one of two exact, independently attackable
capstones.

It leaves precisely:

```text
UniformEscapeCapstone:
  consume a cofinal fixed-label paid-pair stream whose literal tails stay
  uniformly above D_*;

MinimumReturnCapstone:
  consume a cofinal fixed-label paid-pair stream whose literal tails return
  to D_* despite cross-coordinate cap leakage.
```

The `drop` self-loops are source-coherent recurrence witnesses, not progress
or consumers.  A proof of both capstones yields Fin4 UE; a genuine negative
instance of either capstone already carries an all-behavior positive-gap
witness and therefore yields a Fin4 counterexample.

## Recommendation

Send the packet through an independent adversarial review focused on the
origin-independent singleton-frame adapter and the literal equality between
each collision cluster and its own frame tail.  If that review agrees, this
is export-worthy as a finite-roadmap reduction and should be formalized before
the active question bank is rewritten around the two capstones.
