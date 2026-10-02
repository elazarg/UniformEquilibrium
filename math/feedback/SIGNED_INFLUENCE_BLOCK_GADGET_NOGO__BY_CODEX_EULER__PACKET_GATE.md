# Whole-packet gate for `SIGNED_INFLUENCE_BLOCK_GADGET_NOGO`

Reviewer: `CODEX_EULER`

## Packet checked

I independently audited
[`SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md`](../exports/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md)
against every item of [`exports/README.md`](../exports/README.md), after the
author incorporated the proof-writing repair from my theorem review and after
the second falsification review by `CODEX_CEDAR`.

The packet concerns a finite quitting reward table whose ordered membership
influences have one fixed weak sign over every coalition background and whose
every directed simple influence cycle has positive sign product.  It proves
that the table has a pure sure-exit coalition, and hence that the proposed
class cannot force two disjoint strict-first pair atoms to be uniformly
positive at every sufficiently accurate terminal approximate Nash profile.

## Verdict

**PASS.  Keep the packet in `exports/`.**  I found no unresolved mathematical,
semantic, source, or scope objection.

The packet is a complete negative answer of the precise kind accepted by
[`INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md): it eliminates the
entire sign-consistent, directed-cycle-balanced gadget architecture by an
exact all-behavior equilibrium escape.  It does not claim a universal
impossibility theorem for arbitrary quitting games.

## Statement and proof audit

The player set is finite, the payoff extension to the empty coalition is
explicit, and the gain and cross-influence functions are defined on every
legal coalition background.  The positive/negative/absent trichotomy has the
right strict-witness convention, and the directed-cycle hypothesis quantifies
over every directed simple cycle.

Inside a strongly connected component, path-sign independence follows by
closing two root-to-vertex paths with one common return path and deleting
directed simple cycles.  Hence every internal signed edge satisfies

```text
epsilon_i epsilon_j sigma_(j->i)=1.
```

The revised transformed-gain calculation is now literal.  It includes the
fixed outside coalition `E` in `B_i(T)` and separates the two cases:

- `epsilon_j=+1`: transformed addition inserts original player `j`;
- `epsilon_j=-1`: transformed addition removes original player `j`.

In both cases the gain increment is
`epsilon_i epsilon_j d_(j->i)(S)` at a background omitting `i,j`.  Thus all
internal transformed cross-effects are nonnegative, while absent effects are
exactly invariant.

The finite monotone-addition procedure therefore returns a pure Nash action
inside each component.  Solving components in a topological order with every
influence edge directed from an earlier to a later component is valid: an
unsolved later component has no edge into an already solved earlier one, and
the absent clause makes all such later changes exactly irrelevant to earlier
membership gains.  This produces one full coalition satisfying both sure-exit
inequalities.  No deferred existence or selection lemma remains.

## Probability and unrestricted-deviation audit

The construction itself is deterministic finite data from the complete reward
table.  Its output is the literal pure-set root.  If the set is nonempty, the
game absorbs at date zero at that coalition; if it is empty, the profile is
Never.  The checked declarations

```text
IsQuittingSureExitSet
isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
```

in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` cover both cases and
quantify against arbitrary unilateral behavioral deviations, including
history-dependent randomization and Never.  The packet does not replace that
semantic statement with a finite watchdog list.

At a pure-set root the exact first-coalition law is either one atom or Never.
For two distinct disjoint target pairs, at most one target atom can have mass
one and the other has mass zero.  This establishes the gadget no-go already at
terminal Nash error zero, including when calibrators are present as additional
vertices of the same influence graph.

## Adapter, consumer, and boundary tests

The actual-data adapter is fully explicit: compute every cross-influence,
check the finite trichotomy and simple-cycle signs, compute SCCs and a
condensation order, switch actions componentwise, and run the finite addition
algorithm.  Its literal coalition feeds the checked sure-exit consumer without
an artificial continuation or candidate strategy law.

Both boundary tests are exact and relevant.

- The acyclic three-player table has no compatible single global polarity but
  is handled by the SCC theorem, so the result strictly extends the earlier
  global-switch architecture.
- The odd directed negative cycle has no sure-exit coalition, showing that the
  positive-cycle condition cannot simply be deleted from this pure theorem.
  The packet correctly does not infer absence of a mixed or non-pure uniform
  payoff.

## Source and novelty audit

`UniformEquilibrium/Quitting/Stationary/TogglePotential.lean` consumes an
already supplied ordinal potential; it does not derive one from signed
influences.  `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` supplies a single
global polarity transform and explicitly leaves the blockwise extension open.
Narrow searches for signed influence, sign-consistency, cycle balance, and SCC
switching found no checked declaration or other export proving the present
componentwise construction.  The new content is therefore the SCC-local sign
switch plus condensation induction, not a restatement of the checked sure-exit
consumer.

## Lean handoff and nonclaims

The proposed formalization boundary is appropriately narrow: define the
finite influence trichotomy and signed graph, prove path-sign switching and
the component solver, then perform condensation induction to obtain an
existing `IsQuittingSureExitSet`.  The packet names exact positive and negative
regressions and does not encode the desired sure-exit coalition as input data.

The scope exclusions are complete.  The theorem neither constructs a positive
clock gadget nor treats sign-changing influences or a fixed-sign table with a
negative directed cycle.  It also does not advertise the odd-cycle boundary
as a counterexample to uniform-equilibrium existence.

With the two prior independent theorem-level falsification reviews and this
separate whole-packet gate, all eight mandatory export criteria are met.
