# Fin4 producer-atlas semantic connections

Authors: `CODEX_ROOT`, based on the checked six-leaf atlas of Elazar
Gershuni

Independent source audits:

- [atlas falsification audit](../feedback/PRODUCER_ATLAS_PRS_74_75__BY_ATLAS_FALSIFIER.md)
- [atlas export-gate audit](../feedback/PRODUCER_ATLAS_PRS_74_75__BY_ATLAS_GATEKEEPER.md)
- [atlas mathematical audit](../feedback/PRODUCER_ATLAS_DELIVERY_PRS_74_75__BY_CODEX_ROOT.md)

## Exact statement

Let `reward` be a quitting-game reward table on `Fin 4`, let `bound` bound
every reward coordinate, and let

```text
residual : FinFourProducerResidual reward bound.
```

The checked constructors retain six provenance-distinct source forms.  They
admit the following smaller **semantic normalization**, without identifying
their distinct provenance.

### A. Common concentrated-singleton endpoint

Define `FinFourAtlasConcentratedSingletonEndpoint source` to contain:

- one `low : FinFourLowTailRow source`;
- one actual behavioral profile `profile`;
- the marked date `low.stage`;
- one nonempty terminal coalition `terminal` with `terminal.card = 1`;
- the stage-mass floor

  ```text
  low.lambda <= quittingStageCoalitionMass reward profile low.stage terminal;
  ```

- equality of the complete live-root tail strictly after `low.stage` with the
  tail of `low.profile`; and consequently
- equality of the corresponding post-date terminal-semantic pairs.

Then both checked singleton endpoint producers map to this one semantic
interface:

```text
FinFourPurifiedSingletonProducer source
  -> FinFourAtlasConcentratedSingletonEndpoint source

FinFourTerminalSingletonProducer source
  -> Nonempty (FinFourAtlasConcentratedSingletonEndpoint source).
```

The first map uses `singletonTargetProfile`,
`singleton_stageMass_floor`, `singletonTarget_postDate_liveRoot_eq`, and
`singletonTarget_postDateTail_eq`.

The second map uses `terminalVertexTargetProfile` and
`exists_singleton_with_stageMass_floor_and_postDateTail_eq`, together with
`terminalVertexTarget_postDate_liveRoot_eq`.

This normalization does not assert that the two profiles, paths, singleton
labels, or source histories are equal.  It records exactly the semantic data
that their downstream singleton consumer may use in common.

### B. Common monodromy endpoint with retained geometry

Define a geometry wrapper over one fixed

```text
monodromy : FinFourMonodromyProducer source
```

with constructors:

```text
commonHost
  (host : Fin 4)
  (host_mem : every cycle coalition contains host)

complementaryPair
  (first second : cycle offsets)
  (first_card : first coalition has card 2)
  (second_card : second coalition has card 2)
  (complementary : second coalition = first coalition complement).
```

Both checked monodromy leaves then map to one source-preserving node carrying
the common monodromy plus this geometry:

```text
FinFourCommonHostMonodromyProducer source
  -> FinFourAtlasMonodromyNode source

FinFourComplementaryPairMonodromyProducer source
  -> FinFourAtlasMonodromyNode source.
```

No gain, debt, mass, period, source, date, past, or tail datum is copied or
reselected: these remain fields of the common `FinFourMonodromyProducer`.

### C. Same-trace geometry incompatibility

For one fixed monodromy trace, common-host and complementary-pair geometry
cannot both hold.

Indeed, if `A` and `A^c` are two displayed cycle coalitions, a common host
would belong to both.  But `A` and `A^c` are disjoint.  Thus:

```text
theorem not_commonHost_and_complementaryPair_sameTrace
    (monodromy : FinFourMonodromyProducer source) :
    Not (
      (Exists fun host => every coalition of monodromy contains host) /\
      (Exists fun first second =>
        secondCoalition = firstCoalitionᶜ))
```

with the existing cardinality and nonempty-cycle fields included as needed by
the concrete Lean formulation.

This theorem concerns one exact trace.  It does not say that a reward table,
minimum-law source, or low-tail row cannot admit two different traces with the
two different geometries.

### D. Four data-carrying directed nodes

Define a normalized data family with four constructors:

```text
minimumLawSingleton
  -- selected minimum-law singleton, possibly temporally diffuse

concentratedSingleton
  -- the common endpoint from A

tailEscape
  -- the existing TailEscapeSubsequence

monodromy
  -- the common monodromy plus geometry from B.
```

There is a source-preserving total map, or equivalently a nonempty-output
theorem,

```text
FinFourProducerResidual reward bound
  -> Nonempty (FinFourAtlasDirectedNode reward bound).
```

It sends:

- `minimumSingleton` to `minimumLawSingleton`;
- `purifiedSingleton` and `terminalSingleton` to
  `concentratedSingleton`;
- `tailEscape` to `tailEscape`; and
- the two monodromy constructors to `monodromy`, retaining their geometry.

Composed with

```text
uniformPayoff_or_nonempty_finFourProducerResidual,
```

this gives the checked arbitrary-data boundary in its semantically directed
four-node form:

```text
uniform-equilibrium payoff
or minimum-law singleton
or concentrated reached singleton
or quantitative tail escape
or geometric same-stage monodromy.
```

The final `or` is a four-node residual family after the uniform-payoff arm;
the displayed prose has four residual alternatives, with monodromy retaining
its two exact geometries.

## Conjecture-facing change

The six-leaf atlas is already exhaustive, but its public inductive type keeps
provenance distinctions and semantic completion classes at the same level.
The normalization above makes the actual directed proof obligations explicit
in Lean:

1. diffuse minimum-law singleton;
2. concentrated reached singleton;
3. quantitative tail escape; and
4. horizontal monodromy with retained Fin4 geometry.

It prevents two recurrent tracking errors:

- treating Leaves 2 and 3 as unrelated even though they expose the same
  consumer-facing endpoint data; and
- treating Leaves 5 and 6 as unrelated dynamics even though all dynamic and
  quantitative data live in one common monodromy structure.

It also prevents the opposite error: Leaf 1 must not be merged with the
concentrated singleton node, because no uniform literal-date mass floor is
available there.

This is a normalization of the checked atlas, not a consumer of any node.

## Definitions and assumptions

All profiles are literal behavioral profiles of the standard discrete-time
quitting game.  Randomization at a live row is independent product
randomization.  A unilateral deviator may use an arbitrary behavioral
stopping rule, including Never and arbitrarily late quitting.

The terminal-semantic pair contains the prescribed payoff and the supremum
over all such unilateral behavioral deviations.  The mass floor is
unconditional stage mass, including the probability of reaching the marked
date.

The concentrated-singleton interface must retain an actual target profile and
literal post-date live-root equality.  Equality of semantic pairs alone is
not a replacement for those fields.

## Source correspondence

The required source declarations are all in the checked Research atlas:

- `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `Research/Quitting/FinFourProducerAtlas/Leaves.lean`;
- `Research/Quitting/FinFourProducerAtlas/Coverage.lean`; and
- `Research/Quitting/FinFourProducerAtlas/LiteralNoGo.lean`.

In particular:

- `FinFourPurifiedSingletonProducer.singletonTargetProfile`;
- `FinFourPurifiedSingletonProducer.singleton_stageMass_floor`;
- `FinFourPurifiedSingletonProducer.singletonTarget_postDate_liveRoot_eq`;
- `FinFourPurifiedSingletonProducer.singletonTarget_postDateTail_eq`;
- `FinFourTerminalSingletonProducer.terminalVertexTargetProfile`;
- `FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`;
- `FinFourCommonHostMonodromyProducer.exact_geometry`;
- `FinFourComplementaryPairMonodromyProducer.exact_geometry`; and
- `uniformPayoff_or_nonempty_finFourProducerResidual`.

No new probabilistic or game-theoretic estimate is required.  The new content
is a small dependent adapter layer and one finite-set incompatibility lemma.

## Proof

For the purified singleton, take `singletonTargetProfile` and the singleton
already stored by the producer.  The four required endpoint fields are the
four named theorems above.

For the terminal-orbit singleton, eliminate the existential returned by
`exists_singleton_with_stageMass_floor_and_postDateTail_eq`; package its
profile, singleton, mass floor, and semantic tail equality.  Obtain literal
live-root tail equality from `terminalVertexTarget_postDate_liveRoot_eq`.

For either monodromy leaf, reuse its stored `monodromy` field and wrap the
already stored geometry.  No profile or edge is reconstructed.

For same-trace incompatibility, choose the alleged common host.  Apply its
membership proof at the two complementary offsets.  Rewrite the second
coalition as the complement of the first.  Membership in a set and its
complement is impossible.

Finally, eliminate `FinFourProducerResidual` by constructors and use the
preceding adapters.  Composition with the global coverage theorem is direct.

## Boundary tests

1. A minimum joint law may assign positive singleton mass while every
   realizing profile spreads that mass over dates with maximal atom tending
   to zero.  Hence Leaf 1 cannot enter the concentrated endpoint structure.
2. Leaves 2 and 3 may have different singleton labels and different finite
   source paths.  The common structure must not assert equality of those
   fields.
3. A fixed trace containing complementary coalitions has empty total
   intersection and therefore no common host.
4. Different traces on the same table are not compared; same-trace
   incompatibility must not be generalized to table-level exclusivity.
5. A tail-escape subsequence may coexist with occasional low-tail rows, so the
   normalized nodes must not claim pairwise semantic exclusivity.

## Adapter and consumer

The arbitrary-data adapter is the checked
`uniformPayoff_or_nonempty_finFourProducerResidual`.  The result of this
packet is the normalized four-node residual, not a uniform-payoff consumer.

The following arrows are the exact tracked completion obligations.  They are
**not** conclusions of this packet and must not be added as structure fields:

```text
minimum-law singleton
  -> concentrated singleton, terminal approximants, or regenerated descent

concentrated singleton
  -> terminal approximants, charged return, or regenerated descent

tail escape
  -> absorption-spending causal return or regenerated descent

monodromy
  -> source-matched common-response potential,
     source-anchored constrained repair with leakage control,
     or another well-founded source-regenerated exit.
```

For monodromy, a separate reviewed ordinary-mathematics screen dispatches a
supplied common-host cycle to a finite induced-game residual and a supplied
complementary-pair cycle to an interior stationary polynomial residual.  No
checked atlas adapter currently exposes those outputs.  That adapter should
be attempted only after the screen itself has checked declarations; the open
negative residuals must remain explicit.

## Lean handoff

Suggested file:

```text
Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean
```

Suggested declarations:

```text
structure FinFourAtlasConcentratedSingletonEndpoint ...

def FinFourPurifiedSingletonProducer.toConcentratedEndpoint ...

theorem FinFourTerminalSingletonProducer.nonempty_concentratedEndpoint ...

inductive FinFourAtlasMonodromyGeometry (monodromy : ...) ...

structure FinFourAtlasMonodromyNode ...

def FinFourCommonHostMonodromyProducer.toAtlasMonodromyNode ...

def FinFourComplementaryPairMonodromyProducer.toAtlasMonodromyNode ...

theorem not_commonHost_and_complementaryPair_sameTrace ...

inductive FinFourAtlasDirectedNode ...

theorem FinFourProducerResidual.nonempty_directedNode ...

theorem uniformPayoff_or_nonempty_finFourAtlasDirectedNode ...
```

The formalizer should preserve source indices definitionally where possible.
For the terminal-orbit singleton, a `Nonempty` theorem is sufficient and
avoids adding arbitrary choice to the public data.  The common endpoint should
store live-root tail equality and derive semantic equality, unless existing
dependent types make retaining both fields substantially simpler.

Do not add hypothetical consumers, common-response fields, repair leakage
bounds, or pairwise table-level exclusivity as constructor premises.

## Scope and nonclaims

This packet does not:

- consume any atlas node;
- prove the Fin4 conjecture;
- make the four normalized nodes pairwise exclusive;
- merge the diffuse singleton with a concentrated singleton;
- preserve transient paid edges which the terminal-orbit record does not
  store;
- formalize the supplied-cycle semantic screens;
- produce a common-response potential or constrained repair;
- identify independently selected paid/reset profiles with an atlas source;
  or
- construct a recursive or well-founded atlas.

## Formalization record

The checked semantic normalization is maintained in two Research modules.

1. `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean` defines
   `FinFourAtlasConcentratedSingletonOrigin`,
   `FinFourAtlasConcentratedSingletonEndpoint`,
   `FinFourAtlasMonodromyGeometry`, `FinFourAtlasMonodromyNode`, and
   `FinFourAtlasDirectedNode`.  The endpoint accessors expose the literal low
   row, actual target profile, singleton terminal, stage-mass floor, and
   post-date live-root equality; the checked
   `FinFourAtlasConcentratedSingletonEndpoint.postDateTail_eq` derives the
   semantic tail equality.  The declarations
   `FinFourPurifiedSingletonProducer.toConcentratedEndpoint` and
   `FinFourTerminalSingletonProducer.nonempty_concentratedEndpoint` retain the
   two distinct endpoint origins.  The two
   `toAtlasMonodromyNode` adapters reuse the stored monodromy and exact
   geometry, while `not_commonHost_and_complementaryPair_sameTrace` excludes
   simultaneous common-host and complementary-pair geometry only on one fixed
   trace.  Finally, `FinFourProducerResidual.nonempty_directedNode` normalizes
   all six residual constructors to the four data-carrying directed nodes.
2. `Research/Quitting/FinFourProducerAtlas/SemanticCoverage.lean` proves the
   arbitrary-data composition
   `uniformPayoff_or_nonempty_finFourAtlasDirectedNode`.  Its uniform-payoff
   arm is unchanged from the six-leaf coverage theorem; only the residual arm
   is mapped through `FinFourProducerResidual.nonempty_directedNode`.  The same
   module proves the separately scoped
   `FinFourComplementaryPairMonodromyProducer.nonempty_prescribedPairPaidCapSemanticDispatch_reselectingSource`.
   This bridge retains the reward table, the exact terminal-exploitability
   witness stored in the hard residual, and the first displayed cardinality-two
   pair as a prescribed base label.  It freshly selects the semantic minimum,
   stationary profile, paid row, and cap chronology and does not use the
   monodromy orbit or edge data.

The latter bridge calls the production declarations in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidCapSemanticDispatch.lean`.
That module defines `FinFourPairBasePaidCapSemanticDispatch` and proves
`nonempty_finFourPairBasePaidCapSemanticDispatch`,
`FinFourQuantitativeFullSupportHardResidual.nonempty_pairBasePaidCapSemanticDispatch`,
and `uniformPayoff_or_exists_pairBasePaidCapSemanticDispatch`.  The dispatch
contains one stationary paid source on the prescribed pair, one positive
global terminal-semantic minimum, and the summable cap port lifted from the
same source row.  It does not identify that source with an atlas minimum-law
source, selected low row, or monodromy trace.

The production module was branch-mined from
`origin/fin4-semantic-dispatch`, commit
`61c5517125835de3f4ddb66efbd16e2300762f58` (`Formalize pair-base paid cap
semantic dispatch`).  The maintained version adds the explicit atlas
source/trace nonclaim and the accessor
`FinFourPairBasePaidCapSemanticDispatch.base_card`; its mathematical producer
and proof are otherwise the branch result.

`Research/Quitting/FinFourExhaustiveProducerAtlas.lean` imports the semantic
coverage module, and the production dispatch is reachable through
`UniformEquilibrium/Diagnostics/Quitting/All.lean`.

Evidence seals:

- **M:** PASS.  The packet's semantic normalization, finite-set
  incompatibility argument, boundary tests, and source audit are retained
  without strengthening the reviewed statement.
- **L:** PASS.  The two Research modules and the production module are checked
  Lean and reachable from their stated umbrellas.  Direct module checks, the
  Research build, full build, generated axiom audit, trust scan, import-graph
  check and tests, documentation check, proof-duplicate check,
  derivable-telescope check, and source-format checks passed at promotion.  The
  audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **A:** PASS.  `uniformPayoff_or_nonempty_finFourAtlasDirectedNode` starts
  from an arbitrary bounded Fin4 reward table and returns the existing
  uniform-payoff arm or one normalized directed node.  The scoped pair bridge
  starts from an actual complementary-pair atlas producer and sends its
  literal first pair label, together with the same residual witness, to the
  checked production dispatch.
- **C:** ABSENT.  No directed node is consumed by a checked completion theorem.
  The pair-label bridge is a fresh prescribed-base producer, not a consumer of
  the supplied monodromy.

The checked result closes none of the four atlas completion obligations.  It
does not make the directed nodes mutually exclusive, compare independently
selected traces, preserve terminal-orbit transient edges not stored by the
source record, construct a recursive descent or rank, provide a backward
compiler or regeneration, or produce a chronology return or downstream
uniform-equilibrium consumer.
