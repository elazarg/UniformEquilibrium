# Simon 2007: chain-reduction words and the initial action

## Source question

Simon, *The Structure of Non-Zero-Sum Stochastic Games* (2007), Section 3.4,
printed page 12, specifies a chain set associated with each retained root.
The root is outside its chain set. For each state in the chain set outside
the removable set, every action either completes the block or has a
probability-one next state in the chain set, after skipping the removable
states. Composite actions nevertheless begin with an action at the root.

Are root actions intended to satisfy the same deterministic-or-completing
alternative? In particular, is an immediately completing root action a
one-action composite? The displayed definition uses the next-state notation
on the initial action without explicitly providing this alternative there.
This was checked against the rendered journal page, not only extracted text.

The question concerns the definition of chain reduction. It is not a claim
that the paper's Lemma 1 is false. A normalized, correctly specified reduced
action law provides positive first-action coverage through the mass bounds
and normalization argument below. The completed-block probability formula is
proved, and the completed blocks form a full-mass disjoint partition from
every retained state. The concatenated trace law is also proved; the balanced
pathwise prefix comparison remains.

## Separate encoding error

The formalization audit found a distinct error in a permissive formulation
of `IsCompositeActionList` (`Literature/Simon2007.lean`): it allowed the root
at every position in a composite word. The paper requires actions after
the first to occur at the specified targets inside the chain set outside
the removable set. The corrected definition restricts the tail to that set,
retaining the first action at the root and the existing probability-one
links and final completion condition. Adding a stronger root-action
hypothesis to every witness is not a substitute for this correction.

The rejected permissive encoding admits the following countermodel. This
is an ordinary mathematical audit, not a Lean-checked counterexample or a
counterexample to the corrected definition.

There are five states: a root, an interior state, a zero sink, and two
absorbing states with values respectively zero, zero, zero, one, and minus
one. At the root, two actions have probability one half each:

- the first action returns to the root;
- the second moves with equal probabilities to the interior state and the
  zero sink.

At the interior state, two equally likely actions move to the two nonzero
absorbing states. The three sinks have deterministic self-loops. Action
values are the expected values of their successor states, so the state and
action values satisfy the required harmonic equations. A common difference
bound is two.

Take the removable set empty and the chain set to consist only of the
interior state. Every visit begins at the root, and a controlled path from
the interior state leaves it permanently after one visit. Both of its
actions complete the block.

Under the permissive word predicate, all valid root composites are the
nonempty repetitions of the root self-loop action. Their product
probabilities are one half, one quarter, one eighth, and so on, and sum to
one. They can therefore constitute the entire reduced action law even
though the second root action is omitted. Each reduced action returns to
the root and has zero advantage. The other retained states are unchanged.
The retained-state, action-bijection, transition, product-probability,
telescoping, harmonicity, and value-bound fields are all satisfied.

In the original process, choosing the second root action, reaching the
interior state, and choosing the positive action has probability one eighth
and cumulative advantage one. The reduced process has cumulative advantage
zero on every path. With both error parameters equal to one quarter, the
encoded Lemma 1 inequality fails. Normalization alone therefore cannot
repair the permissive word predicate.

## Formalization consequence

With the corrected tail restriction, a completing action cannot be followed
by another action in the same composite: the next action would be at a
chain-set state with probability-one first-exit mass, contradicting
completion. The private `compositeActionList_prefix_eq`
(`Literature/Simon2007.lean`) proves that completed words are prefix-free.
Their cylinder masses, full-mass partition, and concatenated sampled path law
are proved below using reduced-law normalization. No field asserting the
desired trace law or Lemma 1 is assumed.

The generic mass inequality is available as `sum_prefixFree_mass_le` and
`tsum_prefixFree_mass_le`
(`MathUE/Probability/PrefixFreeSubstochasticMass.lean`). It bounds actual
prefix-free word sets under finite-child substochasticity, without an
alphabet finiteness or countability restriction.

`compositeActionList_tsum_tailChoiceProduct_le_one` and
`compositeActionList_tsum_choiceProduct_le_first`
(`Literature/Simon2007.lean`) apply it to the actual valid composite words.
For a fixed first action, the tail products sum to at most one, and the
whole-word products sum to at most that action's choice probability.
The prefix mass is the choice product on deterministic first-exit chains
and zero elsewhere. All permitted next actions at a nonempty chain belong
to one state, by probability-one first-exit uniqueness; its action law
therefore supplies the finite-child mass bound. No finite action assumption
or initial-root alternative is added.

`ChainReductionData.rootFirstAction_map`
(`Literature/Simon2007.lean`) proves that the literal first-action marginal
of the reduced choice law equals the original choice law at every retained
root. The proof injects each fixed-first reduced-action fiber into the valid
composite tails, applies the mass bound, and uses normalization to turn
pointwise domination into equality.
`ChainReductionData.exists_positive_composite_with_first` in the same file
therefore supplies a positive-probability composite for every original root
action of positive probability. These are consequences of the existing
reduction data, not additional coverage fields.

`CompositeBlockEvent` (`Literature/Simon2007.lean`) records the literal action
word at successive first exits from the removable set, followed by the first
retained exit. `ChainReductionData.compositeBlockEvent_probability` in that
file proves, at every retained state, that its original-path probability
equals the reduced action probability times the reduced transition
probability. The proof uses the
existing path law and its restart identity, including arbitrary measurable
continuation events, rather than a new trajectory-law assumption.

`ChainReductionData.positive_root_actionStructure`
(`Literature/Simon2007.lean`) derives the completing-or-deterministic-successor
alternative for every positive-probability root action from normalized
composite coverage. No extra root-action hypothesis is required for existing
reduction data.

`ChainReductionData.pairwise_disjoint_compositeBlockEvent`,
`ChainReductionData.compositeBlockEvent_union_measure`, and
`ChainReductionData.ae_existsUnique_compositeBlock`
(`Literature/Simon2007.lean`) prove the disjoint partition and almost-everywhere
unique completed block and retained exit from every retained start. The
action and transition PMF normalizations give total mass one. These results
include the unchanged singleton actions outside the root set.

`ChainReductionData.completedBlockIndex`
(`Literature/Simon2007.lean`) decodes the actual action, retained exit, and
elapsed original time, returning `none` off the completed-block partition.
Its measurability and almost-everywhere successful decoding are proved.
`ChainReductionData.completedBlockIndex_firstRetained` in the same file
identifies the recorded time as the first positive retained return, including
the absence of earlier retained visits.
`ChainReductionData.completedBlockIndex_restart` proves that continuation
after the decoded block has the original state-started law at its endpoint:
the block-and-continuation event has probability equal to the reduced action
probability times the reduced transition probability times that continuation
probability. The elapsed time is read from the path, not supplied as a
certificate.

`ChainReductionData.retainedTrace` (`Literature/Simon2007.lean`) iterates that
decoder. `ChainReductionData.retainedTraceFrom_cylinder` and
`ChainReductionData.map_retainedTrace` in the same file prove all finite
cylinder probabilities and identify the mapped original law with the actual
reduced path law. The total definition uses a fallback after decoding failure;
`ChainReductionData.ae_retainedRemainderFrom_decodes` proves that every
iteration succeeds on one common full-measure set. Thus the fallback does not
affect the path law. The balanced pathwise prefix comparison remains;
Lemma 1 remains open.

The checked nonroot result
`ChainReducibilityWitness.observedFirstOutside_classification`
(`Literature/Simon2007.lean`) is unaffected: a positive-mass observed first
exit determines which of the stated nonroot alternatives holds. It does not
complete the sampled-law construction. The positive-root classification above
uses the normalized reduction data, whereas this nonroot result uses the
chain witness alone.
