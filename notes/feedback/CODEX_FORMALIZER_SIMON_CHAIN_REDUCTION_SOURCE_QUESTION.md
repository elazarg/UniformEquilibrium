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
action law may itself provide the necessary positive-probability coverage;
proving that implication requires a partition argument.

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
The remaining construction must prove their cylinder
masses, use reduced-law normalization to establish coverage, and transport
the resulting sampled path law. These are proof obligations, not assumed
fields asserting the desired trace law or Lemma 1.

The generic mass inequality is available as `sum_prefixFree_mass_le` and
`tsum_prefixFree_mass_le`
(`MathUE/Probability/PrefixFreeSubstochasticMass.lean`). It bounds actual
prefix-free word sets under finite-child substochasticity, without an
alphabet finiteness or countability restriction. To apply it here, products
must be restricted to supported composite prefixes: arbitrary tagged
actions can belong to different states, so their choice probabilities do
not form one probability distribution. Probability-one next-state
uniqueness and that state's action law must supply the local child bound.

The checked nonroot result
`ChainReducibilityWitness.observedFirstOutside_classification`
(`Literature/Simon2007.lean`) is unaffected: a positive-mass observed first
exit determines which of the stated nonroot alternatives holds. It does not
assert the missing initial-root classification or complete the sampled-law
construction.
