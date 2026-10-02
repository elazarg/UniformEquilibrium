# Historical resolution: the Fin4 complementary-pair atlas leaf

## Resolution

The checked theorem `not_nonempty_finFourMonodromyProducer` in
`Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` eliminates
the shared `FinFourMonodromyProducer`, hence this refinement is empty. No
boundary stationary consumer or atlas descent is required. The material below
records the former question and should not be treated as a live mathematical
leaf.

## Objective

Prove that a `FinFourComplementaryPairMonodromyProducer` yields a
uniform-equilibrium payoff or a source-preserving well-founded atlas descent.

## Checked entrance

The leaf retains the complete common monodromy packet:

- the hard residual, positive minimum, selected joint law, and causal source;
- one low-tail row with fixed post-date tail;
- a simple horizontal cycle of period at most eight;
- fixed stage mass at least `lambda = mu^2 / 8`;
- edge gains at least `mu^2 * D_* / 64`;
- exact mover-debt subtraction and mass-preserving routing; and
- two displayed pair coalitions which are disjoint exact complements.

The complementary vertices force empty total intersection and full union of
the four labels.  This removes a persistent sure-quitter compiler and makes
boundary escape the central difficulty.

## Known finite semantic screen

The finite-game calculation associates to a supplied empty-base strict cycle
an explicit stationary product system.  Its equations express active
Quit-versus-Never complementarity; its inequalities keep passive outsiders
from joining.  In the exact complementary-pair Fin4 geometry there are no
outside labels.

The screen gives:

1. an interior product solution, which compiles to an exact terminal Nash
   profile and uniform-equilibrium payoff; or
2. no interior solution, with a positive residual on every compact interior
   rate box.

Thus every vanishing-defect stationary repair in the second arm must approach
the boundary.  Neither this screen nor its atlas adapter is currently a
checked Lean declaration, and the boundary arm remains open.

A newly checked theorem supplies a same-reward paid-cap semantic dispatch for
either prescribed complementary pair.  It does not preserve the atlas source,
trace, low row, tail, or cycle edges.

## Exact remaining theorem

Prove

```text
FinFourComplementaryPairMonodromyProducer source
  -> uniform-equilibrium payoff
     or SourcePreservingAtlasDescent source next.
```

After the interior stationary arm is consumed, the precise residual task is:

```text
complementary-pair boundary escape
  -> terminal approximants,
     charged admissible return,
     or source-regenerated well-founded descent.
```

Any small-rate limiting construction must retain the literal atlas tail and
control unrestricted behavioral deviations; stationary complementarity alone
is insufficient at a boundary where clocks can escape.

## Acceptable answers

1. consume every complementary-pair leaf into a uniform payoff;
2. prove an exhaustive boundary classification whose every arm is consumed;
3. construct a source-preserving strict finite-rank descent with full
   regeneration; or
4. give an actual positive-gap Fin4 reward table satisfying the complete leaf
   premises.

## Outputs that do not answer the question

- the interior polynomial screen alone;
- positive separation on compact interior boxes without consuming boundary
  escape;
- a separately selected pair-base paid-cap source;
- treating complementary pair vertices as successive play dates;
- finite-horizon or stationary-only deviation control; or
- a boundary classification with a new unconsumed exceptional owner.

## Principal sources

- `Research/Quitting/FinFourProducerAtlas/Leaves.lean`
- `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`
- `Research/Quitting/AnchoredCyclicPatienceBridge.lean`
- `Research/Quitting/FinFourPeriodicAnchorResidualAdapter.lean`
