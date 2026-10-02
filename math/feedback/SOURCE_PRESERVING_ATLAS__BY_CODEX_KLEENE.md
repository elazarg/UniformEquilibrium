# Adversarial review of `SOURCE_PRESERVING_ATLAS.md`

## Verdict: PASS

I found no mathematical counterexample to the claimed source-preserving
three-mode reduction.  In particular, the two capstones are exhaustive: from
one fixed monodromy-free Fin4 entrance residual, one can construct one
cofinal stream of literal singleton frames, apply the forced-pair/collision
construction framewise, stabilize all finite labels, and split the resulting
nonnegative tail-excess stream into uniform escape or minimum return.

The result answers the maintained effective-roadmap question.  It does not
consume either terminal component, and it does not prove Fin4 uniform
equilibrium.  Those are not qualifications on the roadmap claim itself.

Three small interface edits should be made before export or formalization:

1. spell out the constructor-by-constructor reuse of the already stored
   `SelectedRows`, so the phrase “no chronology is reselected” is literal;
2. replace the informal third disjunct of `FinFourCompletionTerminal` by the
   exact checked type
   `Nonempty (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward)`
   or omit that disjunct; and
3. state that the SCCs are SCCs of this deliberately defined completion-mode
   graph, not intrinsic SCCs of every finer semantic graph.

These are exact repairs, not missing mathematical implications.

## Claim tested

The claim is the ordinary-mathematics implication

```text
no Fin4 uniform-equilibrium payoff
  -> source-attached uniformEscape packet
     or source-attached minimumReturn packet,
```

where both outputs retain one hard residual and terminal-gap witness, one
minimum semantic/law point, one causal atom, one literal chronology, a
cofinal stream of actual source rows, fixed player/action labels, literal
forced-pair and payer updates, and each row's actual post-date continuation.

The regular graph is

```text
cofinalSingleton -> uniformEscape -> uniformEscape -> ...
                \
                 -> minimumReturn -> minimumReturn -> ...
```

so its two terminal SCCs are the singleton modes `uniformEscape` and
`minimumReturn`.

## Sources inspected

I inspected the exact declarations in:

- `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`;
- `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`;
- `Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean`;
- `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`;
- `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`; and
- `Research/Quitting/FinFourProducerAtlas/ForcedPairMinimumTailConsumer.lean`.

At repository head `fbe009fee5cb89dbb1217658452ce9cde5050f2b`, the focused Lean
checks of `MonodromyImpossible.lean`,
`MinimumSingletonClockCompression.lean`,
`PureNonsingletonCollisionScreening.lean`, `ForcedPair.lean`, and
`ForcedPairMinimumTailConsumer.lean` all completed successfully.  This is
evidence for the cited ingredients, not a compilation claim for the new atlas
structures.

## 1. Exhaustive entrance and one cofinal singleton stream

### Attempted falsification

The first possible failure was that one of the four constructors of
`FinFourProducerResidualWithoutMonodromy` might expose only one isolated
singleton or one unrelated chronology, rather than a cofinal stream on the
same source.

No such constructor exists.

### Singleton constructor

For `.minimumSingleton source terminal_card`, the checked theorem

```text
FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer
```

selects one `FinFourMinimumAtomChronology source` before all depths.  Its
field `cofinal_endpoint` gives an actual endpoint at a rank at least any
requested depth.  Recursively choose

```text
endpoint 0     at requested depth 0,
endpoint (n+1) at requested depth endpoint(n).rank + 1.
```

Then the actual ranks are strictly increasing.  This use of countable choice
is legitimate in the project's noncomputable classical setting.  Every
endpoint retains the same chronology, and
`FinFourOwnerCompressedSingletonEndpoint.rootStack_length` gives root-stack
length `rank + 1`.

The reference-prefix debt converges along the entire chronology by
`FinFourMinimumAtomChronology.prefix_debt_tendsto`; composing with a strictly
increasing natural sequence preserves convergence to `D_*`.

### The three nonsingleton constructors

The other constructors already contain the exact selected-row family that
should be reused:

| residual constructor | retained selected rows |
| --- | --- |
| `.purifiedSingleton source producer` | `producer.low.rows` |
| `.terminalSingleton source producer` | `producer.purification.low.rows` |
| `.tailEscape source producer` | `producer.rows` |

Every listed family carries `collision : 1 < atom.terminal.card`, the source
profiles, exact cap-root stacks, root-stack lengths, and prefix-debt
convergence.  Therefore no new call to
`QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows` is required after
the entrance residual has been selected.

For the retained rows,
`SelectedRows.eventually_stageMass_gt_square_div_eight` supplies a cutoff
`N`.  Ranks `N+n` are cofinal and strictly increasing.  At each such rank,
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` yields a
literal singleton target at the same marked date.  The relevant checked
fields give:

- singleton cardinality one;
- stage mass at least `mu^2/8`;
- at most three strict preterminal edges;
- a final pair-to-singleton route that need not be profitable;
- equality with the original profile at every other date; and
- literal equality of the complete post-date live-root tail.

Thus all four entrance constructors produce the claimed common stream.

### Required repair

The note should state the table above explicitly.  Saying only “select one
`SelectedRows` from the common source” is mathematically sufficient for an
existence theorem, but it is weaker than the note's advertised literal
no-reselection discipline.  Reusing the fields already present in each
constructor removes even that presentational ambiguity.

This objection is repaired by constructor projection; it is not a missing
producer theorem.

## 2. Recursive selection, cofinality, and convergence

### Attempted falsification

The endpoint theorem has quantifiers

```text
for every depth, Nonempty (Endpoint depth),
```

rather than supplying a sequence.  A careless simultaneous selection could
choose bounded or repeated actual ranks.

### Verdict

The recursive requested-depth construction above forces

```text
rank(n) < rank(n+1).
```

For the nonsingleton arm, `rank(n)=N+n` already has this property.  Every
later finite-label or scalar extraction is by a strict subsequence, so source
ranks remain strictly increasing and hence tend to infinity.  All convergence
claims used by the atlas survive these subsequences.

No compactness or diagonal argument is needed here, and there is no
depth-dependent change of chronology.

## 3. Origin-independent pureification and forced pair

### Attempted falsification

The checked declaration

```text
FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket
```

is currently stated for the existing weak-core inductive type.  The new
nonsingleton screened endpoint is not a constructor of that type.  Therefore
the new atlas cannot cite the checked theorem verbatim for every frame.

This is the most substantive new adapter obligation, but its proof does not
use hidden origin-specific data.

### Minimal frame interface actually used

The proof of `nonempty_forcedPairPacket` uses only:

1. an actual target profile and marked date;
2. a literal singleton coalition at that date;
3. a fixed positive stage-mass floor `lambda`;
4. a reference profile with identical complete post-date live roots;
5. the retained minimum point and its positive debt; and
6. the retained hard residual and terminal-gap collision theorem.

Both owner-compressed endpoints and pure-screened nonsingleton endpoints
satisfy these fields exactly.

Pureifying the frame to the displayed singleton preserves the reached live
mass and the post-date tail.  The theorem

```text
FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton
```

selects an outsider whose Quit endpoint exceeds its Continue endpoint by at
least the same terminal gap.  Hence the first best-endpoint action is
literally Quit and the routed coalition is a pair.  At that pure pair the
forced owner's marked defect is zero.

The checked pure-nonsingleton debt identity then gives

```text
D_* <= sum_i markedDefect_i
     =  sum_{i != forcedOwner} markedDefect_i.
```

There are three remaining coordinates, so one payer has defect at least
`D_*/3`.  Multiplication by the reached live mass, which is at least
`lambda`, gives payer gain at least `lambda*D_*/3`.  The existing endpoint
adapter gives exact own-debt subtraction and exact same-date mass routing.

### Verdict

The required origin-independent theorem is a genuine new declaration, but
not new game-theoretic mathematics.  I found no counterexample: every step
depends only on the six frame fields above.  Formalization should factor the
current proof through this small interface rather than duplicate its
origin-specific implementation.

## 4. Collision cluster equals the same frame's literal tail

### Attempted falsification

The dangerous substitution would be to attach the forced pair from frame
`n` to a collision residual whose compact cluster came from another source,
another frame, or merely a semantically equivalent carrier point.

That substitution is unnecessary.

For one forced-pair frame, use the existing constant-profile concentrated
packet.  `FinFourWeakCoreForcedPairPacket.nonempty_collisionMinimumResidual`
constructs the residual on that literal packet.  The proof of

```text
FinFourWeakCoreForcedPairPacket.collisionCluster_eq_postDateTail
```

rewrites the entire residual tail sequence to a constant function before
using uniqueness of limits.  Therefore every possible residual selected from
that packet has cluster exactly equal to that frame's `referenceTail`.

The origin-independent frame has the same literal post-date live-root
equality, so the same rewrite proves

```text
cluster_n = Sem(Spine(frame.targetProfile, frame.stage+1)).
```

No convergence of the frames with respect to `n` is involved.  The equality
is proved separately and literally for each frame.

Consequently

```text
e_n = D(actual frame tail_n) - D_*
```

is nonnegative by global minimality, because that tail is the semantic pair
of an actual behavioral profile.

## 5. Finite stabilization and the scalar dichotomy

The label tuple

```text
(singletonOwner, forcedOwner, payer, payerAction)
```

takes values in a finite type.  Infinite pigeonhole yields a strict
subsequence on which all four are fixed.  Composing its index map with the
already strict source-rank sequence preserves strictness and cofinality.

For the nonnegative sequence `e_n`, define

```text
U := exists delta > 0, Frequently (fun n => delta <= e_n) atTop.
```

If `U`, `extraction_of_frequently_atTop` gives a strict subsequence with the
uniform floor.  If not `U`, then for every `delta>0` eventually
`e_n<delta`; together with `e_n>=0`, this is exactly `e_n -> 0`.

The two priority branches are exclusive.  A raw sequence in the uniform arm
may also possess a different subsequence tending to zero; the note does not
need, and should not claim, otherwise.  The `minimumReturn` packet is produced
only in the negation of the frequent-positive-floor branch.

## 6. Allowed-edge graph and terminal SCCs

I found no hidden edge or fairness assumption.

The `cofinalSingleton` mode has one exhaustive dispatch to either `E` or `R`
and no self-loop.  `drop` supplies literal self-transitions for `E` and `R`:
all source data and fixed labels are unchanged, and row `n` of the child is
row `n+1` of the parent.  Uniform excess and convergence to zero are both
tail properties, so they survive `drop`.

Because the terminal conclusion is a reward-level proposition, the backward
compiler for each step is literally the identity.  No profile-level
chronology is inferred from this identity.

The SCC computation is therefore exact for the declared mode relation:

```text
{cofinalSingleton}, {uniformEscape}, {minimumReturn},
```

with the latter two terminal.  The result avoids both defects mentioned in
the note: there are no rank resets, and the unique nonterminal mode must leave
in one step rather than relying on fairness to take an available exit.

The self-loops are recurrence witnesses, not consumers or descent.  This is
compatible with `FIN4_EFFECTIVE_FINITE_COMPLETION_ROADMAP.md`, whose requested
output is a finite list of exact terminal-component questions rather than a
proof of those capstones.

The note should keep saying explicitly that these are SCCs of the new mode
graph.  They are not asserted to be the SCCs of every finer atlas obtained by
opening the internal normalized-inert, support-handoff, or strict-ray
certificates.

## 7. Checked content versus new ordinary mathematics

### Already checked

The current Lean development supplies:

- four-way monodromy-free producer coverage on a retained source;
- the fixed singleton chronology and cofinal endpoint access;
- selected nonsingleton rows, exact root stacks, mass retention, and
  source-front debt convergence;
- source-faithful pure nonsingleton screening;
- all local forced-pair and payer inequalities;
- exact one-date profile and post-date tail preservation; and
- collision-residual cluster equality for the constant packet.

### Still ordinary mathematics in this packet

The following should not be labeled Lean-checked until implemented:

1. the common cofinal singleton-stream structure;
2. recursive extraction of strictly increasing owner-compressed ranks;
3. the generic singleton-frame version of the forced-pair/collision proof;
4. framewise choice of rows and collision residuals;
5. finite simultaneous label stabilization;
6. the nonnegative stream dichotomy;
7. the packet `drop` transitions and finite SCC computation; and
8. the global composition from monodromy-free coverage to the two
   realizability alternatives.

The gap between these lists is honest and local.  It is not a hidden
chronological producer problem.

## Exact interface corrections

These edits should accompany, but need not delay, mathematical export.

1. Define the return arm of `FinFourCompletionTerminal` exactly, for example
   as

   ```text
   Nonempty
     (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward).
   ```

   Its checked consumer is
   `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
   in `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.
   Alternatively omit this redundant disjunct and use only `ApproxTerminal`
   and the uniform-payoff proposition.

2. In the global coverage proof, existentially choose a finite reward bound
   (or use the project's canonical finite bound) before invoking
   `uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy`.

3. Remove the unused symbol `h` from the displayed definition of
   `CertifiedGap`, or explain it.  A structure with fields `gamma`,
   `gamma_pos`, and the all-behavior exploitability proof is sufficient.

None of these repairs changes the two capstone packets or their exhaustivity.

## Final judgment

No tested objection produced a counterexample or an unclassified branch.
After the small exact-interface edits above, the result is export-worthy as a
complete finite, source-preserving roadmap reduction.  The two resulting
questions are genuinely independent targets:

```text
UniformEscapeCapstone:
  consume the fixed-label forced-pair stream whose literal tails stay a
  uniform positive distance above D_*.

MinimumReturnCapstone:
  consume the fixed-label forced-pair stream whose literal tails return to
  D_* while horizontal paid moves may leak debt into other cap coordinates.
```

A positive solution of both yields Fin4 UE via the atlas reduction.  An
actual packet falsifying either universal capstone already contains an
all-behavior terminal-gap witness and therefore gives a Fin4 counterexample.
