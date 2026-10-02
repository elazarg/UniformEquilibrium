# Historical resolution: the Fin4 common-host atlas leaf

## Resolution

The checked theorem `not_nonempty_finFourMonodromyProducer` in
`Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` answers
acceptable alternative 3 in stronger form: the shared
`FinFourMonodromyProducer` is empty, without using common-host or hard-residual
assumptions. The material below records the former question and its exact
entrance; it should not be treated as a live mathematical leaf.

## Objective

Prove that a `FinFourCommonHostMonodromyProducer` cannot survive in a
four-player quitting game without a uniform-equilibrium payoff, or convert it
source-faithfully into a strictly smaller well-founded atlas state.

The target is the entire common-host leaf, not merely one favorable induced
face-game chamber.

## Checked entrance

The arbitrary-data theorem

```text
uniformPayoff_or_nonempty_finFourProducerResidual
```

is checked in `Research/Quitting/FinFourProducerAtlas/Coverage.lean`.
Its common-host constructor retains:

- one hard residual and positive global minimum `D_*`;
- the selected minimum joint law and causal source;
- one literal low-tail row and its exact post-date tail;
- a simple horizontal endpoint cycle of period at most eight;
- one player contained in every cycle coalition;
- a fixed stage-mass floor `lambda = mu^2 / 8`;
- literal edge gain at least `mu^2 * D_* / 64`;
- exact mover-debt subtraction; and
- no loss of routed stage mass.

The cycle is horizontal: its vertices are sibling profiles differing at one
reached date.  It is not a chronology visiting those vertices successively.

## Known finite semantic screen

For a supplied strict cycle with nonempty common intersection `B`, solve the
finite induced binary game on the free labels.  The finite-game calculation
gives:

1. an induced Nash point whose host-leave and outsider-join excesses are all
   nonpositive, which compiles to an exact terminal Nash profile and a
   uniform-equilibrium payoff; or
2. a strict positive residual on every induced Nash point.

This screen has not been connected to
`FinFourCommonHostMonodromyProducer` by a checked Lean declaration.  More
importantly, its second arm has no consumer.

A separate checked theorem constructs a same-reward paid-cap semantic dispatch
for every prescribed two-player base.  It does not preserve the atlas minimum,
low row, trace, tail, or edge certificates.

## Exact remaining theorem

Prove one exhaustive implication of the form

```text
FinFourCommonHostMonodromyProducer source
  -> uniform-equilibrium payoff
     or SourcePreservingAtlasDescent source next
```

where `SourcePreservingAtlasDescent` carries an actual successor source,
retains every passport needed to re-enter the atlas, and strictly decreases a
declared natural-valued rank.

Equivalently, after consuming the nonpositive-excess induced-game arm, prove

```text
common-host positive face residual
  -> uniform-equilibrium payoff
     or source-preserving well-founded descent.
```

The proof may use the prescribed-pair paid-cap dispatch, but must construct a
literal dependent bridge if it transfers atlas edge data to that independently
selected source.

## Acceptable answers

Any one of the following closes the question:

1. a proof that every common-host atlas leaf yields a uniform-equilibrium
   payoff;
2. a source-preserving transition to a strictly smaller atlas rank, together
   with regeneration of all data required to repeat it;
3. a proof that the common-host leaf is impossible under the retained hard
   residual; or
4. an actual four-player reward table satisfying the all-behavior terminal-gap
   witness and the complete common-host atlas premises, thereby refuting the
   conjecture.

## Outputs that do not answer the question

- another finite sign or support split without consuming every new arm;
- an independently selected persistent-base or paid-cap profile;
- a stationary Nash screen whose negative branch is merely named;
- reading the horizontal cycle as a temporal path;
- real debt decrease without a regenerated source and well-founded rank; or
- exactifying an edge while changing or forgetting its source data.

## Principal sources

- `Research/Quitting/FinFourProducerAtlas/Leaves.lean`
- `Research/Quitting/FinFourProducerAtlas/LiteralNoGo.lean`
- `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`
- `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`
