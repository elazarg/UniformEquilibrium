# Fin4 source-preserving six-leaf producer atlas

Authors: Elazar Gershuni (PR 75); mathematical packet assembled by
`CODEX_ROOT`

Independent reviews:

- [adversarial proof audit and finite-cycle falsification by ATLAS_FALSIFIER](../feedback/PRODUCER_ATLAS_PRS_74_75__BY_ATLAS_FALSIFIER.md);
- [freshness and export-gate audit by ATLAS_GATEKEEPER](../feedback/PRODUCER_ATLAS_PRS_74_75__BY_ATLAS_GATEKEEPER.md); and
- [initial mathematical audit by CODEX_ROOT](../feedback/PRODUCER_ATLAS_DELIVERY_PRS_74_75__BY_CODEX_ROOT.md).

This packet contains only the narrow six-leaf reduction of PR 75. It does not
include the stronger recursive or mixed-radix claims in
`ephemeral/producer_atlas_delivery/`.

## Exact statement

Let the player set be `Fin 4`, and let

\[
r:\{S\subseteq\operatorname{Fin}4:S\ne\varnothing\}\longrightarrow
\mathbb R^{\operatorname{Fin}4}
\]

be a quitting-game reward table. Assume a finite bound \(M\) is supplied with
\(|r_i(S)|\le M\) for every player and nonempty coalition.

For a behavioral profile \(\sigma\), write

\[
U_i(\sigma)=\text{its prescribed terminal payoff},\qquad
B_i(\sigma)=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i]),
\]

where the supremum is over all behavioral strategies of player \(i\). Put

\[
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\qquad D(\sigma)=\sum_i d_i(\sigma).
\]

The terminal-semantic carrier is the compact closure of pairs \((U,B)\)
arising from actual behavioral profiles, and \(D(U,B)=\sum_i(B_i-U_i)\).

Then one of the following holds.

1. The game has a uniform-equilibrium payoff.
2. There are one selected Fin4 hard-residual packet, one minimum joint
   semantic/law point \((z_*,\nu_*)\), and one positive finite terminal-law
   atom \(S\) of mass
   \[
   \mu:=\nu_*(S)>0,
   \]
   all attached to the same causal realizing source, such that one of the six
   source-distinct alternatives below holds.

Here

\[
D_*:=D(z_*)>0,
\qquad
\lambda:=\frac{\mu^2}{8},
\qquad
h:=\frac{\mu^2D_*}{16}=\frac{\lambda D_*}{2}.
\]

### Leaf 1: minimum-law singleton

The selected positive atom is a singleton: \(|S|=1\). The selected minimum
point and its causal realizing source remain part of the output.

Assume henceforth that \(|S|\ge2\). The causal atom supplies one fixed family
of actual source profiles, exact cap-prefix roots, and marked reached dates.
All remaining leaves use this same family.

### Leaf 2: singleton during partial purification

At one marked low-tail row, after at most four literal same-date pure-endpoint
updates, the routed marked coalition becomes a singleton. The complete
partial-purification path is retained. The post-date tail is unchanged, and
the singleton's actual stage mass is at least \(\lambda\).

### Leaf 3: terminal singleton of the pure-root orbit

The preliminary process reaches a total pure root, and the subsequent finite
same-stage endpoint dispatch reaches a singleton terminal vertex. The output
retains the common literal base profile, selected date and tail, together with
the terminal singleton route and its mass floor \(\lambda\).

This statement does not assert that the public orbit record retains certified
edges along the entire transient segment leading to that terminal vertex.

### Leaf 4: quantitative tail escape

There is a strictly increasing subsequence of the selected causal rows such
that at every selected rank:

\[
\operatorname{StageMass}(S)>\lambda
\]

and

\[
\operatorname{TailExcess}
:=D(\text{actual shifted tail})-D_*
\ge h.
\]

The actual profiles, exact prefix roots, marked dates, and source atom remain
attached to this subsequence.

### Leaf 5: common-host monodromy

There is a simple closed same-stage pure-root endpoint orbit of period at most
eight and a player contained in every coalition of the orbit. At every cycle
offset:

\[
\operatorname{StageMass}\ge\lambda,
\]

and the next edge is a literal pure best-endpoint update with actual payoff
gain \(g_e\) satisfying

\[
g_e\ge\frac{\lambda D_*}{8}
=\frac{\mu^2D_*}{64}>0.
\]

The edge also carries the exact mover-debt identity and the no-loss routed
mass comparison furnished by the same-stage endpoint construction.

### Leaf 6: complementary-pair monodromy

The same conclusions as in Leaf 5 hold, except that the simple cycle contains
two disjoint two-player coalitions. Since the player set has four elements,
the two coalitions are complements.

The monodromy in Leaves 5 and 6 is a horizontal family of literal profiles
differing at one fixed reached date. It is not a temporal play path visiting
the cycle coalitions in succession.

## Conjecture-facing change

This proves the first accepted outcome of
[`FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`](../questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md):
the broad Fin4 hard residual is replaced by a finite, natural,
source-preserving family of residual obligations.

The six source-distinct leaves give four conjecture-facing completion
problems:

1. consume or source-faithfully regenerate one of the three singleton
   origins;
2. consume or regenerate quantitative tail escape;
3. consume or regenerate common-host monodromy; and
4. consume or regenerate complementary-pair monodromy.

The theorem does not solve these four problems. Its progress is that any
successful consumer or genuine no-go now removes a branch of one proved
finite normal form rather than another independently selected residual.

## Definitions and source data

The common source packet is the mathematical content of
`FinFourMinimumAtomProducer`. It contains:

- the supplied `FinFourQuantitativeFullSupportHardResidual`;
- the selected joint semantic/law point \((z_*,\nu_*)\);
- membership of that point in the joint carrier and of \(z_*\) in the
  semantic carrier;
- global minimality of \(z_*\);
- positivity of the terminal debt infimum and the equality \(D(z_*)=D_*\);
  and
- one `QuittingMinimumLawCausalSuffixAtom`, including its literal realizing
  source subsequence and causal suffix access.

For a nonsingleton atom, `SelectedRows` retains the same actual profiles,
exact cap-root stacks, shifted marked dates, and source atom. No downstream
branch selects a different minimum point, law, chronology, or reward table.

At a low-tail row, partial purification changes only one player's prescribed
action at the marked date. The live probability before the date and the
complete behavioral tail after it remain literal. The marked coalition is
routed by toggling that player's membership, and its stage mass does not
decrease.

## Proof

The global Fin4 reduction first gives either a uniform-equilibrium payoff or a
`FinFourQuantitativeFullSupportHardResidual`. Work in the latter case.

### Step 1: select the minimum causal atom

The Fin4 hard-residual finite-atom theorem selects one joint semantic/law point
\((z_*,\nu_*)\) with \(D(z_*)=D_*>0\), together with a positive finite
terminal atom \(S\) and its causal actual-source realization. In particular,
the generic alternative in which only the all-Never coordinate is positive
has already been removed by the hard residual's punishment-normality data.

If \(|S|=1\), return Leaf 1. Suppose \(|S|\ge2\).

### Step 2: obtain fixed-resolution selected rows

Collision anti-diffusion and causal suffix selection produce `SelectedRows`
such that eventually

\[
\operatorname{StageMass}_n(S)>\frac{\mu^2}{8}=\lambda.
\]

All rows lie in the same selected source family.

### Step 3: make the exhaustive high-tail/low-tail split

Let \(E_n\) be the shifted-tail debt excess at selected rank \(n\). Consider
the predicate

\[
h\le E_n.
\]

If it occurs frequently, intersect it with the eventual stage-mass floor and
extract a strictly increasing subsequence. This gives Leaf 4.

If it does not occur frequently, then eventually \(E_n<h\). Intersecting this
eventual set with the same stage-mass floor yields one literal row satisfying

\[
\lambda<\operatorname{StageMass}_n(S),
\qquad
E_n<\frac{\lambda D_*}{2}.
\]

The inclusive high inequality and strict low inequality cover the equality
case exactly.

### Step 4: purify the low-tail row

Process the four players once at the selected date. At each step, replace the
current player's root coordinate by a pure best endpoint against the actual
unchanged tail.

The update preserves the probability of reaching the date, preserves the
post-date tail exactly, and sends the marked coalition to its membership
toggle by that player. The routed coalition's stage mass is no smaller than
the previous one. Thus the mass floor \(\lambda\) is invariant.

If a routed coalition becomes singleton, return Leaf 2. Otherwise all four
coordinates are processed in at most four updates and the selected root is
pure and nonsingleton. Because only the selected date was changed, its shifted
tail is still the original low-tail one.

### Step 5: run the finite pure-root endpoint orbit

At a pure nonsingleton root, apply the collision charge at the same marked
date. The mass floor and the inequality

\[
E_n<\frac{\lambda D_*}{2}
\]

exclude the tail-escape side of the local dichotomy. Hence either the routed
coalition is singleton or one player has a literal best-endpoint update with
gain at least

\[
\frac{\lambda D_*}{2\cdot4}=\frac{\lambda D_*}{8}.
\]

The update again preserves the tail and does not reduce the marked mass. The
same dispatch is therefore available at every subsequent nonsingleton pure
root.

The nonsingleton Boolean state space is finite. The dispatched orbit either
reaches a singleton, giving Leaf 3, or contains a simple closed segment. A
simple one-coordinate cycle through nonsingleton subsets of `Fin 4` has period
at most eight and has either a common player or two disjoint pair vertices.
These give Leaves 5 and 6. The gain and mass estimates hold freshly at every
edge of the closed segment.

This completes the six-way exhaustive reduction.

## Boundary tests

### No missing Never leaf

The generic joint-law causalization theorem has a positive-Never alternative.
The stronger Fin4 hard-residual theorem used here produces a positive finite
atom unconditionally. The atlas may therefore omit a separate Never-only leaf
only at this exact starting interface.

### No threshold gap

The high arm uses \(h\le E_n\); its negation gives \(E_n<h\). Thus equality at
the threshold is classified as high-tail escape.

### No mass loss under purification

Every same-date pure endpoint update preserves live mass and weakly increases
the displayed routed coalition mass. If routing produces a singleton, it is a
concentrated singleton with the same fixed scale rather than a diffuse clock.

### No hidden near-minimum transfer premise

The proof never claims that an endpoint target is near the global minimum and
never uses a routed recipient-debt lower bound. It repeatedly uses only the
unchanged tail-excess inequality, global positivity of \(D_*\), literal mover
gain, and mass routing. Hence it is unaffected by the separate gap in attempts
to infer recipient transfer from deletion and near-cap data alone.

### Fin4 cycle geometry

An independent exhaustive enumeration by the falsification reviewer found 53
simple cycles in the one-coordinate graph on the eleven Fin4 nonsingleton
coalitions. Every cycle has length at most eight and has a common vertex label
or two disjoint pair vertices. This agrees with the finite combinatorial
classification used in the proof.

### Local exactification no-go

Each monodromy edge has positive literal best-endpoint gain. Therefore it
cannot be embedded as an exact Nash--Bellman row while preserving its current
prescribed payoff, displayed root, and displayed tail payoff: such exactness
would force the corresponding coordinate defect to vanish.

This no-go does not exclude changing the root or tail, nonlocal repair,
approximate rows, source-anchored verticalization, or a different regenerated
source.

## Adapter and remaining consumers

The actual-data adapter is the global coverage map

```text
uniformPayoff_or_nonempty_finFourProducerResidual
```

which takes an arbitrary Fin4 reward table with a supplied finite reward bound
and returns either a uniform-equilibrium payoff or a source-carrying member of
the six-leaf family.

No downstream semantic consumer is claimed. The completion-contract names in
PR 75 are research obligations only. In particular, mapping the three
singleton origins to one name does not prove that one consumer handles all
three.

## Source correspondence and freshness

The proof composes the following existing mathematical interfaces:

- `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`;
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` and
  `SelectedRows.eventually_stageMass_gt_square_div_eight` in
  `NonsingletonMinimumLawLinearTransfer.lean`;
- `quittingPartialPurification_then_sameStage_dispatch` in
  `SameStageEndpointPurification.lean`;
- `quittingPartialPurification_then_finFourSameStage_dispatch` in
  `FinFourSameStageEndpointMonodromy.lean`; and
- the exact local root-tail no-go from
  `TerminalSemanticLiteralSourceReturnNoGo.lean`.

The individual minimum-law, selected-row, purification, and geometry results
predate the atlas. The new content is their dependent composition on one fixed
source chain and the unconditional six-leaf coverage theorem from arbitrary
Fin4 game data. Before this result, those pieces were separate conditional
interfaces rather than one finite source-preserving normal form.

PR 74 contains essentially the same mathematics in one monolithic file. PR 75
is the maintained modular version and mathematically supersedes PR 74.

## Lean handoff

The intended declarations and structures are those in PR 75:

- `FinFourMinimumAtomProducer`;
- `FinFourLowTailRow`;
- `FinFourPurifiedSingletonProducer`;
- `FinFourTotalPurificationProducer`;
- `FinFourTerminalSingletonProducer`;
- `FinFourMonodromyProducer`;
- `FinFourCommonHostMonodromyProducer`;
- `FinFourComplementaryPairMonodromyProducer`;
- `FinFourProducerResidual`;
- `nonempty_finFourProducerResidual_of_hardResidual`;
- `uniformPayoff_or_nonempty_finFourProducerResidual`; and
- `FinFourMonodromyProducer.every_edge_no_literalExactification`.

The maintained implementation is split under
`Research/Quitting/FinFourProducerAtlas/`, with
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean` as aggregator.

A formalization audit should specifically verify:

1. the exact source fields retained by each leaf;
2. strict versus weak inequalities at the high/low split;
3. equality of the post-date tail after partial purification;
4. invariant stage-mass routing;
5. the cycle gain and period constants; and
6. that no theorem documentation claims certified transient orbit edges which
   are not stored by `DispatchedOrbit` or `DispatchedClosedSegment`.

## Scope and nonclaims

This result does not:

- prove the Fin4 or general finite-quitting conjecture;
- consume any of the four completion obligations;
- construct a recursive atlas or a well-founded regeneration;
- instantiate the delivery folder's mixed-radix rank on actual Fin4 states;
- construct canonical `NeverIrreducible` or `AtomIrreducible` records;
- prove that a high-debt tail contradicts minimum debt;
- turn horizontal monodromy into a temporal chronology;
- attach an independently produced response rectangle to every monodromy edge;
- claim that the three singleton origins already have a common consumer; or
- exclude any nonlocal exact or approximate repair of a monodromy leaf.

## Formalization record

The maintained checked realization consists of exactly five Research modules:

1. `Research/Quitting/FinFourProducerAtlas/Source.lean` defines
   `FinFourMinimumAtomProducer` and `FinFourLowTailRow`.  The declarations
   `FinFourMinimumAtomProducer.nonempty_of_hardResidual`,
   `FinFourMinimumAtomProducer.minimumDebt_pos`,
   `FinFourMinimumAtomProducer.tailThreshold_pos`, and
   `FinFourMinimumAtomProducer.nonempty_tailEscape_or_lowTailRow` retain one
   hard residual, minimum joint-law point, causal finite atom, and selected-row
   family through the exact inclusive-high/strict-low split.  The
   `FinFourLowTailRow` accessors expose its actual profile, marked stage, exact
   cap-root stack, selected tail, positive `mu^2 / 8` scale, mass floor, and
   strict `mu^2 D_* / 16` low-tail inequality.
2. `Research/Quitting/FinFourProducerAtlas/Leaves.lean` defines
   `FinFourPurifiedSingletonProducer`, `FinFourTotalPurificationProducer`,
   `FinFourTerminalSingletonProducer`, `FinFourMonodromyProducer`,
   `FinFourCommonHostMonodromyProducer`,
   `FinFourComplementaryPairMonodromyProducer`, and
   `FinFourProducerResidual`.  The declarations
   `FinFourLowTailRow.nonempty_leaf`,
   `FinFourTerminalSingletonProducer.exists_singleton_with_stageMass_floor_and_postDateTail_eq`,
   `FinFourMonodromyProducer.edge_gain_floor_mu_square_div_sixty_four`,
   `FinFourMonodromyProducer.edge_mover_debt`, and
   `FinFourMonodromyProducer.edge_stageMass_noLoss` give the four-way low-row
   dispatch and the packet's literal singleton, tail, gain, debt, and mass
   interfaces.  `FinFourProducerResidual.completionContract` is only an
   obligation classifier.
3. `Research/Quitting/FinFourProducerAtlas/Coverage.lean` proves
   `nonempty_finFourProducerResidual_of_hardResidual` and the actual-data
   adapter `uniformPayoff_or_nonempty_finFourProducerResidual`.
4. `Research/Quitting/FinFourProducerAtlas/LiteralNoGo.lean` defines
   `QuittingSameStageEndpointEdge.literalPositiveActualRowPacket` and proves
   the local obstruction
   `FinFourMonodromyProducer.every_edge_no_literalExactification`.
5. `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` is the maintained
   import-only aggregator for `Coverage` and `LiteralNoGo`; it introduces no
   stronger declaration.

Evidence seals:

- **M:** PASS.  The exact six-leaf proof, boundary tests, source audit, and
  provenance above were retained after the independent reviews named at the
  start of this packet.
- **L:** PASS.  All five modules are checked Lean and are reachable from the
  `Research` umbrella.  The named atlas and umbrella builds, trust scan,
  import-graph check, telescope check, and proof-duplicate check pass.
- **A:** PASS.  `uniformPayoff_or_nonempty_finFourProducerResidual` takes an
  arbitrary Fin4 reward table with a supplied finite reward bound and returns
  either a uniform-equilibrium payoff or one source-carrying member of the
  six-leaf family.  No leaf, high/low witness, minimum point, atom, selected
  row, or hard residual is supplied to this global theorem.
- **C:** ABSENT.  No returned leaf has a checked downstream semantic consumer.

The six constructors are provenance-distinct tags, not a uniqueness or
mutual-exclusivity theorem; in particular, the two cycle geometries may
overlap.  The checked realization constructs no recursive atlas,
well-founded or mixed-radix rank, backward compiler, regeneration, chronology
return, or downstream uniform-payoff consumer.  The selected minimum semantic
point is retained through an asymptotic actual-profile chronology; no actual
profile is asserted to equal or attain that minimum point.
