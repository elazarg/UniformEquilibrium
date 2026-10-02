# A source-preserving finite completion atlas for four-player quitting games

Authors: conference external contribution; Codex Root (export consolidation)

Independent reviews:
[Codex Root](../feedback/SOURCE_PRESERVING_ATLAS__BY_CODEX_ROOT.md),
[Codex Kleene, adversarial review](../feedback/SOURCE_PRESERVING_ATLAS__BY_CODEX_KLEENE.md)

## Exact statement

Let the player set be `Fin 4`.  Let

```text
r : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be an arbitrary finite quitting-game reward table.  Play ends at the first
nonempty quitting coalition and all-Never pays zero.  Strategies are arbitrary
behavioral strategies.  For an actual behavioral profile `sigma`, write

```text
U_i(sigma) = prescribed terminal payoff,
B_i(sigma) = supremum over all behavioral deviations by i,
d_i(sigma) = B_i(sigma) - U_i(sigma),
D(sigma)   = sum_i d_i(sigma).
```

The same notation is used on the terminal-semantic carrier.  Let `D_*` denote
its global minimum total debt.

There is a finite source-preserving completion atlas with mode type

```text
cofinalSingleton | uniformEscape | minimumReturn.
```

It has the following properties.

1. If `r` has no uniform-equilibrium payoff, then `D_*>0` and one fixed
   positive-gap/minimum-law source produces a `cofinalSingleton` packet.
2. Every `cofinalSingleton` packet produces, on that same source, either a
   `uniformEscape` packet or a `minimumReturn` packet.
3. Every `uniformEscape` packet has a literal self-shift successor of the same
   mode, and every `minimumReturn` packet has a literal self-shift successor of
   the same mode.
4. There are no rank exits and no other regular transitions.

The declared regular mode graph is therefore

```text
cofinalSingleton ---> uniformEscape ---> uniformEscape ---> ...
                 \
                  ---> minimumReturn ---> minimumReturn ---> ...
```

Its strongly connected components are the three singleton mode sets.  The
terminal SCCs of this declared completion graph are exactly

```text
{uniformEscape}, {minimumReturn}.
```

Consequently,

```text
no Fin4 uniform-equilibrium payoff
  -> UniformEscapeRealizable(r) or MinimumReturnRealizable(r).
```

The two realizability predicates are defined below and retain one literal
source chronology throughout.  This is a complete answer to
`FIN4_EFFECTIVE_FINITE_COMPLETION_ROADMAP.md`: no additional recurrent mode is
needed outside these two exact capstones.

## Definitions and assumptions

### Terminal and counterexample predicates

Define

```text
FinFourCompletionTerminal(r) :=
  exists v, IsUniformEquilibriumPayoff(quittingGame r, v).
```

The checked theorems

```text
quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns
```

allow terminal approximate Nash profiles at every positive error or a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily r` to be used as
ways of proving this exact terminal predicate.

Define

```text
CertifiedGap(r) :=
  exists gamma > 0, forall behavioral profile sigma,
    exists i, gamma <= B_i(sigma) - U_i(sigma).
```

Every nonterminal packet below retains such a witness through the checked hard
residual.  No finite-horizon, stationary, periodic, or bounded-controller
replacement of this all-behavior predicate is used.

### Common minimum-law source

The common source is the exact `FinFourMinimumAtomProducer` carried by the
checked monodromy-free producer residual.  It contains:

- the reward table and a finite reward bound;
- a `FinFourQuantitativeFullSupportHardResidual`, including a fixed terminal
  exploitability gap `gamma>0` against every behavioral profile;
- one joint semantic/law point `(z_*,nu_*)` in the joint carrier;
- global minimality of `z_*` and

  ```text
  D_* = D(z_*) = inf_sigma D(sigma) > 0;
  ```

- one nonempty terminal coalition `A` and mass

  ```text
  mu = nu_*(A) > 0;
  ```

- one actual causal source chronology, including profiles, marked dates,
  exact cap-Nash root words of length `n+1`, convergence to `(z_*,nu_*)`,
  convergence of the literally prefixed profile debts to `D_*`, and exact
  causal survival of the selected atom.

Set

```text
lambda = mu^2 / 8 > 0.
```

The checked entrance is

```text
uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy.
```

Its residual has exactly four constructors:

```text
minimumSingleton | purifiedSingleton | terminalSingleton | tailEscape.
```

The two former monodromy constructors are impossible and are not modes of the
completion atlas.

### Cofinal singleton packet

A `cofinalSingleton` packet stores the common source and, for every natural
index `n`, literal data

```text
(k_n, sigma_n, tau_n, t_n, j_n, W_n),
```

with the following properties.

1. `k_n < k_(n+1)`.
2. `W_n` is the retained exact cap-Nash source word and has length `k_n+1`.
3. `sigma_n` is the literal prefixed source profile at rank `k_n`.
4. `tau_n` is an actual profile differing from `sigma_n` only at the marked
   date `t_n`.
5. The marked terminal is the singleton `{j_n}`.
6. Its unconditional marked-stage mass is at least `lambda`.
7. Every live root strictly after `t_n` is literally the corresponding source
   live root.  Hence the complete behavioral continuation tail is identical,
   including unrestricted best-response caps and all terminal-law data.
8. `D(sigma_n) -> D_*`.

The packet also retains its exact entrance residual and origin data.  No
target-side cap-Nash or near-minimum statement is added.

### Forced-pair stream row

From one singleton frame, first pureify the marked root to the literal
singleton `{j_n}`.  This leaves the live mass reaching the date and the entire
post-date tail unchanged.

The hard residual gives `q_n != j_n` with

```text
r_qn({j_n,q_n}) >= r_qn({j_n}) + gamma.
```

Force `q_n` to its exact best endpoint.  The action is Quit and the marked
coalition is the pure pair `{j_n,q_n}`.  Its live mass remains at least
`lambda`, the actual source-to-pair gain is at least `lambda*gamma`, and the
marked `q_n`-defect is zero.

At a pure nonsingleton root the continuation is screened from every unilateral
behavioral deviation.  If `delta_i^n` is player `i`'s marked root-coordinate
defect against the actual post-date payoff, then global minimality gives

```text
D_* <= sum_i delta_i^n = sum_{i != q_n} delta_i^n.
```

Choose `p_n != q_n` satisfying

```text
delta_pn^n >= D_*/3.
```

Replace only `p_n`'s marked action by its exact best Boolean endpoint.  If
`g_n` is the resulting whole-profile gain, then

```text
g_n >= lambda*D_*/3 > 0,
d_pn(paidTarget_n) = d_pn(pairProfile_n) - g_n.
```

The marked mass is routed without loss, all off-date behavior is unchanged,
and the complete post-date tail is still literal.

The same frame produces the checked
`QuittingConcentratedCollisionMinimumResidual`.  Its cluster is exactly—not
merely semantically equivalent to—the frame's actual post-date semantic tail

```text
T_n = Sem(Spine(tau_n,t_n+1)).
```

Define the nonnegative excess

```text
e_n = D(T_n) - D_* >= 0.
```

### Stabilized forced-pair stream

The tuple

```text
(j_n,q_n,p_n,payerAction_n)
```

takes values in a finite type.  A strict subsequence therefore fixes one tuple
`(j,q,p,a)`.  The child packet stores the parent and the strict index embedding,
so every profile, word, date, law, tail, residual, and source rank remains a
literal parent object.

### Uniform-escape packet

A `uniformEscape` packet is a stabilized forced-pair stream together with one
`delta>0` such that

```text
D(T_n) >= D_* + delta
```

for every retained `n`.

### Minimum-return packet

A `minimumReturn` packet is a stabilized forced-pair stream satisfying

```text
D(T_n) -> D_*.
```

It includes both exact-minimum tails and strictly off-minimum tails whose
excess vanishes.

### Realizability

For `X` equal to `uniformEscape` or `minimumReturn`, define
`XRealizable(r)` to mean that there is one `X`-packet `P` on `r` and a packet
sequence

```text
P^0 = P,
P^(n+1) = drop(P^n),
```

where `drop` deletes the first stream frame.  All source data and fixed labels
are unchanged, and row `m` of `drop(P)` is row `m+1` of `P`.

## Source correspondence

The following game-theoretic ingredients are already checked in Lean.

1. `uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy` in
   `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` gives the
   four-constructor entrance while retaining the exact source.
2. `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer` in
   `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
   fixes one singleton chronology and supplies an endpoint beyond every
   requested rank.  The endpoint changes one selected date and retains the
   exact post-date tail.
3. `SelectedRows.eventually_stageMass_gt_square_div_eight` and
   `SelectedRows.prefix_debt_tendsto` in
   `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean` give the
   eventual canonical mass floor and minimum-debt convergence on one retained
   nonsingleton row family.
4. `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` in
   `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean` gives the
   literal singleton, mass preservation, at most three paid preterminal edges,
   and complete off-date preservation.
5. `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` and
   the accessors of `FinFourWeakCoreForcedPairPacket` in
   `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` give the full-gap
   forced pair, zero forced-owner defect, `D_*/3` payer defect,
   `lambda*D_*/3` paid gain, exact own-debt subtraction, and tail provenance.
6. `FinFourWeakCoreForcedPairPacket.nonempty_collisionMinimumResidual` and
   `collisionCluster_eq_corePostDateTail` in
   `Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`
   give the source-attached collision residual and its exact cluster identity.
7. `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
   and
   `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
   are the checked terminal consumers.

The new ordinary mathematics in this packet is limited to:

- packaging the two origins into one cofinal singleton stream;
- recursively choosing strictly increasing owner-compressed ranks;
- factoring the forced-pair proof through the common singleton-frame fields;
- applying the local construction and residual choice framewise;
- simultaneous finite-label stabilization;
- the nonnegative excess-stream dichotomy;
- the two `drop` transitions and the finite SCC calculation; and
- composing the checked entrance with those steps.

No theorem in the repository currently states this complete atlas reduction.

## Proof

### Step 1: obtain the fixed source

Choose the canonical finite reward bound.  Apply
`uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy`.

If its first arm holds, `FinFourCompletionTerminal(r)` holds.  Otherwise retain
the returned monodromy-free residual and the exact `FinFourMinimumAtomProducer`
inside it.  Under the hypothesis that no uniform-equilibrium payoff exists,
only the second arm is possible.

### Step 2: construct one cofinal singleton stream

There are four residual constructors.

#### `minimumSingleton`

The checked owner-compression producer chooses one chronology before every
depth request.  Choose the first endpoint at requested depth zero.  Having
chosen rank `k_n`, request the next endpoint at depth `k_n+1`.  Then

```text
k_n < k_(n+1).
```

All endpoints use the same chronology.  Strict increase implies `k_n ->
infinity`, so the chronology's prefix-debt convergence gives
`D(sigma_n)->D_*` along this stream.

#### `purifiedSingleton`

Reuse the already stored row family

```text
producer.low.rows.
```

#### `terminalSingleton`

Reuse the already stored row family

```text
producer.purification.low.rows.
```

#### `tailEscape`

Reuse the already stored row family

```text
producer.rows.
```

In each of these last three constructors the stored atom is nonsingleton.  The
eventual stage-mass theorem supplies a cutoff `N`.  Use ranks `N+n`; do not
select another chronology or row family.  At each rank apply pure
nonsingleton screening.  It returns a literal singleton at the same marked
date, with mass at least `lambda`, equality at every other date, and the same
complete post-date tail.  Prefix-debt convergence along `N+n` gives
`D(sigma_n)->D_*`.

This constructs a `cofinalSingleton` packet for every possible entrance.

### Step 3: build one forced-pair row at every frame

Pureify the singleton frame, preserving reached live mass and the literal
tail.  Apply the hard-residual singleton-collision theorem to obtain `q_n` and
the terminal-gap join inequality.  At the pure singleton, Quit is therefore
the unique best endpoint for `q_n`; its target is the pair `{j_n,q_n}` and its
marked defect is zero.

Apply the pure-nonsingleton debt identity to the actual spine beginning at
this pair row.  This spine is an actual behavioral profile, so global
minimality gives total debt at least `D_*`.  Screening identifies this total
debt with the sum of marked defects.  Since the `q_n` term is zero, one of the
three other terms is at least `D_*/3`.  Choose it as `p_n` and apply its exact
best endpoint.  The literal one-date gain identity and the live-mass floor
give `g_n>=lambda*D_*/3`; changing only `p_n` preserves its best-response cap,
so its debt decreases by exactly `g_n`.

Construct the constant concentrated packet on the literal pair frame and its
collision-minimum residual.  The residual tail sequence is constant.  The
checked cluster theorem therefore identifies its cluster with that exact
frame's post-date tail `T_n`.  Since `T_n` is realized by an actual profile,
global minimality gives `e_n>=0`.

All choices are made framewise on the retained stream.  Classical countable
choice packages them into one forced-pair stream.

### Step 4: stabilize finite labels

There are finitely many values of `(j_n,q_n,p_n,payerAction_n)`.  Infinite
pigeonhole gives a strict index embedding on which the tuple is constant.
Composing this embedding with the strictly increasing source-rank sequence
preserves strict increase and therefore cofinality.  Restrict every stored
object along the same embedding.

### Step 5: split the excess stream

Consider the proposition

```text
exists delta > 0, Frequently (fun n => delta <= e_n) atTop.
```

If it holds, extract a strict subsequence satisfying `e_n>=delta` everywhere.
This is a `uniformEscape` packet.

If it fails, then for every `delta>0`, eventually `e_n<delta`.  Together with
`e_n>=0`, this is exactly `e_n->0`.  This is a `minimumReturn` packet.

This is a priority dichotomy.  It does not assert that a raw sequence in the
first arm lacks a different subsequence converging to zero.

### Step 6: prove the transition graph and its terminal components

The preceding split is the exhaustive outgoing dispatch from
`cofinalSingleton`.

For either terminal mode, define `drop` by deleting its first frame.  Uniform
positive excess and convergence to zero are both invariant under this shift.
Every source object and fixed label is unchanged, and child row `n` is
definitionally or propositionally parent row `n+1`.  Thus `drop` gives the two
literal self-transitions.

There are no rank-exit constructors.  Hence the complete allowed-edge matrix
of the declared atlas is

```text
                       target
source              C     E     R
cofinalSingleton    0     1     1
uniformEscape       0     1     0
minimumReturn       0     0     1
```

The SCCs and condensation graph follow by finite inspection.  The unique
nonterminal mode must leave in one step, so no fairness assumption is used.
Iterating `drop` realizes whichever terminal component was selected.

This proves the stated global implication.

## The two exact capstones

### Uniform-escape capstone

For every Fin4 reward table and every source-attached `uniformEscape` packet,
prove `FinFourCompletionTerminal(r)`.

The input includes one fixed all-behavior gap witness, one minimum source and
chronology, fixed labels `j,q,p,a`, fixed `lambda,delta>0`, literal forced-pair
and paid endpoints at cofinally increasing source ranks, exact payer-debt
subtraction by at least `lambda*D_*/3`, exact full post-date tail provenance,
and

```text
D(T_n) >= D_* + delta.
```

A negative answer must give an actual reward table and packet; its retained
gap witness is already a Fin4 all-behavior counterexample.

### Minimum-return capstone

For every Fin4 reward table and every source-attached `minimumReturn` packet,
prove `FinFourCompletionTerminal(r)`.

The fixed data are the same, but

```text
D(T_n) -> D_*.
```

This is the renewable cross-coordinate cap-leakage question: one marked payer
loses a fixed amount of debt at every frame, but the other unrestricted caps
may absorb that loss while the actual continuation tails return to the
minimum region.

A negative answer again supplies an actual positive-gap Fin4 table.

If both capstones are solved positively, the global reduction proves the
four-player uniform-equilibrium conjecture.

## Boundary tests

### Scalar classification

- `e_n=1` enters `uniformEscape` with `delta=1`.
- `e_n=1/(n+1)` enters `minimumReturn`.
- `e_(2n)=1` and `e_(2n+1)=1/(n+1)` enters `uniformEscape` under the priority
  rule, although another subsequence tends to zero.  This falsifies any claim
  that the two kinds of raw subsequence are intrinsically exclusive and is why
  the priority formulation is used.

### Source-provenance falsifier

Selecting a fresh `SelectedRows` independently in each nonsingleton frame
would prove existence of frames but not the advertised literal source stream.
The proof avoids this by using exactly `producer.low.rows`,
`producer.purification.low.rows`, or `producer.rows`, according to the
entrance constructor.

### Cluster-substitution falsifier

Compactness alone could select a residual cluster unrelated to a given frame.
Here the concentrated packet is constant for that frame, and the checked
cluster theorem rewrites its tail sequence to a constant function.  Thus the
cluster is the same frame's literal tail before the stream dichotomy is formed.

### Graph-theoretic falsifiers

An arbitrary infinite path in a finite graph need not enter a terminal SCC if
it may ignore an available exit forever.  An integer rank also does not stop
infinitely many rank drops if regular transitions may reset it.  Neither
argument is used: `cofinalSingleton` has no self-loop and must leave in one
step, while this atlas has no rank transitions.

### Semantic boundary

The horizontal payer update is not called a Nash--Bellman chronology, and the
`drop` transition is not called debt descent.  Other coordinates' caps may
increase.  This is precisely why the two capstones remain terminal components
rather than being declared solved.

## Adapter and consumer

The arbitrary-data adapter is the checked theorem

```text
uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy.
```

The new constructor-by-constructor stream adapter is exhaustive and preserves
the actual source data listed above.  It maps every nonterminal entrance first
to `cofinalSingleton` and then to exactly one priority branch `uniformEscape`
or `minimumReturn`.

The semantic consumer of this export is the maintained finite-roadmap
question.  The theorem closes that question by proving that every indefinite
Fin4 positive-gap obstruction lies in one of the two explicitly defined
terminal components.  The remaining mathematical consumers are exactly the
two capstones, not an unspecified residual family.

## Lean handoff

The minimal proposed interface is:

```lean
inductive FinFourCompletionMode
  | cofinalSingleton
  | uniformEscape
  | minimumReturn

structure FinFourCofinalSingletonFrame ...
structure FinFourCofinalSingletonPacket ...
structure FinFourForcedPairStreamRow ...
structure FinFourStabilizedForcedPairStream ...
structure FinFourUniformEscapePacket ...
structure FinFourMinimumReturnPacket ...

def FinFourCompletionPacket : FinFourCompletionMode -> ...
def FinFourCompletionTerminal reward :=
  ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff

-- Empty inductive type or `False`-valued relation.
def FinFourCompletionRankExit ... := False

inductive FinFourCompletionRegularStep ...
  | classifyUniformEscape ...
  | classifyMinimumReturn ...
  | dropUniformEscape ...
  | dropMinimumReturn ...

FinFourCompletionAtlas.coverage
FinFourCompletionAtlas.dispatch
FinFourCompletionAtlas.modeGraph
FinFourCompletionAtlas.terminalComponents
FinFourCompletionAtlas.counterexample_enters_terminalComponent

FinFourUniformEscapeCapstone
FinFourMinimumReturnCapstone
FinFourCompletionAtlas.all_capstones_imply_finFour
```

Formalization should first factor the forced-pair proof through a small common
singleton-frame structure rather than duplicate the current weak-core proof.
For the nonsingleton constructors, it must reuse the exact stored row fields:

```text
purifiedSingleton -> producer.low.rows
terminalSingleton -> producer.purification.low.rows
tailEscape -> producer.rows.
```

The new theorem must derive the stream, labels, residuals, scalar alternative,
and transitions.  They must not be supplied as certificate fields.  Focused
tests should include strictness of the recursively selected ranks, composition
of strict subsequences, literal cluster-tail equality at each index, `drop`
preservation, and finite enumeration of all nine possible mode pairs.

## Scope and nonclaims

- This is not a proof of either capstone or of the Fin4 conjecture.
- The terminal SCCs are SCCs of this declared completion-mode graph, not of
  every finer graph formed by opening internal normalized-inert, support, or
  strict-ray refinements.
- The self-shifts are source-coherent recurrence witnesses, not progress.
- No whole forced-pair profile is asserted minimum, near-minimum, cap-Nash, or
  terminal approximate Nash.
- No horizontal paid endpoint is reinterpreted as a temporal exact edge.
- Exact payer-debt subtraction does not control the other three caps or total
  debt.
- No compact carrier representative replaces an actual frame tail.
- No new Lean declarations are claimed here.  The cited local ingredients are
  checked; the atlas packaging and global composition are ordinary mathematics
  awaiting formalization.

## Formalization record

The packet is proved in Lean at its corrected source-preserving scope in three
checked Research modules.

`Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`
contains the exact entrance and cofinal-frame layer.

- `FinFourSourcePreservingSingletonEntrance.toResidual` projects every
  entrance back to its literal four-tag monodromy-free residual.
- `FinFourSourcePreservingSingletonFrame` is dependently indexed by that
  entrance.  The minimum-singleton constructor therefore uses one stored
  owner-clock producer, while the other constructors definitionally use the
  selected rows already stored by their original producer.
- `FinFourProducerResidualWithoutMonodromy.exists_cofinalSingletonPacket`
  returns the source, entrance, packet, and the literal equality
  `packet.residual = residual`.
- `FinFourSourcePreservingCofinalSingletonPacket.sourceRank_tendsto_atTop`,
  `suffixLaw_tendsto`, `referenceDebt_tendsto`, `rootStack_nash`, and
  `postDateSpine_eq_reference` expose cofinal source ranks, convergence of the
  suffix semantic/outcome law to the fixed joint source point, convergence of
  literal prefix debt to `D_*`, exact cap--Nash source words, and the complete
  post-date behavioral spine.
- `uniformPayoff_or_exists_sourcePreservingCofinalSingletonPacket` is the
  bounded-data entrance theorem and retains the exact residual equality in its
  nonterminal arm.

`Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`
contains the origin-independent frame compiler.

- `FinFourSourcePreservingSingletonFrame.nonempty_forcedPairPacket` constructs
  the literal full-gap pair and paid endpoint from every actual frame.
- `FinFourSourcePreservingForcedPairPacket.forcedTerminal_card`,
  `forcedOwnerDefect_eq_zero`, `canonical_payerGain_floor`,
  `payerTargetDebt_eq_sourceDebt_sub_gain`, and
  `payerRoutedStageMass_eq_forcedPairStageMass` prove the pair cardinality,
  zero forced-owner defect, canonical `mu^2 * D_* / 24` gain floor, exact
  payer-debt subtraction, and no-loss marked mass.
- `forcedPair_postDateSpine_eq_reference`,
  `payerTarget_postDateSpine_eq_reference`, and their outcome-law projections
  retain the literal complete continuation profile and law.
- `FinFourSourcePreservingForcedPairPacket.nonempty_collisionMinimumResidual`
  constructs the standard collision residual, while
  `collisionCluster_eq_framePostDateTail` proves that its cluster is the same
  frame's actual continuation tail.
- `FinFourSourcePreservingSingletonFrame.nonempty_forcedPairResidualCapstone`
  bundles the packet, residual, and exact cluster identity without accepting
  any of them as supplied certificate data.

`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`
contains the finite-label stabilization, exact-tail classification, graph,
and reward-level composition.

- `FinFourStabilizedForcedPairStream.nonempty` simultaneously fixes the
  singleton owner, forced owner, payer, and payer action on one strict
  subsequence.  Its source-rank, suffix-law, prefix-debt, full-spine, semantic
  tail, and outcome-law accessors all delegate to literal parent rows.
- `FinFourStabilizedForcedPairStream.uniformEscape_or_minimumReturn` is the
  exhaustive priority split of the nonnegative tail-debt excess.  It does not
  claim that a raw sequence in the first arm lacks another minimum-return
  subsequence.
- `FinFourUniformEscapePacket.tailDebt_floor` states the uniform positive
  excess literally, and
  `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` states convergence of
  the literal tail debts to `D_*`.
- The two `drop` definitions and their row, frame, fixed-label, and iterated
  trajectory laws prove the exact source-coherent self-shifts.
- `FinFourCompletionMode.reachable_iff_explicit` identifies the displayed
  reachability table with the reflexive--transitive closure of the declared
  regular edges.  `sameComponent_iff_eq`, `isTerminal_iff`, and
  `regularEdge_iff` prove the singleton SCCs, the two terminal structural
  components, and all nine edge cases.  `RankExit` is definitionally false.
- `uniformPayoff_or_sourcePreservingCompletionOutcome` is the strongest
  dependent capstone: arbitrary bounded Fin4 rewards have a uniform payoff or
  an exact-residual-indexed uniform-escape/minimum-return outcome.
  `uniformPayoff_or_sourcePreservingUniformEscape_or_minimumReturn` and
  `sourcePreservingUniformEscape_or_minimumReturn_of_no_uniformPayoff` are its
  reward-level realizability forms with literal infinite self-shift
  trajectories.
- `FinFourUniformEscapeCapstone` and `FinFourMinimumReturnCapstone` are open
  proposition definitions.  `finFourCompletion_of_capstones` proves the Fin4
  conclusion only conditionally on proofs of both.

The atlas reduction has mathematical, Lean, and actual-source seals `M`, `L`,
and `A`.  Its only `C` is structural: the checked frame compiler, priority
dispatch, and self-shift/graph composition consume the preceding entrance
data.  Neither terminal exact-tail mode has a semantic or uniform-payoff
consumer, so there is no terminal conjecture-level `C`.

No forced-pair target is asserted minimum, near-minimum, full-root Nash, or a
temporal Nash--Bellman successor.  The self-shifts are recurrence witnesses,
not progress or debt descent.  No cross-coordinate cap control, return,
regeneration, terminal approximation, solution of either open capstone, or
unconditional Fin4 uniform-equilibrium theorem is proved.  The SCC statement
concerns only the declared three-mode completion graph, not every finer graph
obtained by opening the internal residual packets.
