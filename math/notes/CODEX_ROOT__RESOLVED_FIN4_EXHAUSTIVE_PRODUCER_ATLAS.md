# Historical resolution: exhaustive finite producer atlas for Fin4

## Resolution

The requested first finite producer classification is checked:
`uniformPayoff_or_nonempty_finFourProducerResidual` gives the six-leaf atlas,
clock compression removes singleton diffusion, and the generic
support-at-most-four theorem eliminates both monodromy tags.  Checked
source-faithful constructions subsequently contract the surviving entrances
to the forced-pair/canonical-ray chain.

The downstream completion problem is also now reduced by a finite
source-preserving system with three modes.  Its two terminal components are
uniform escape and minimum return.  What remains open is consumption of those
two components, not construction of another global atlas.  The text below is
retained as the historical recursive-atlas specification that the three-mode
construction satisfies.

The first source-preserving six-leaf atlas and its arbitrary-data coverage
theorem are checked.  Its mathematical obligation graph has since contracted
to one node.  Minimum-law singleton mass enters the strong concentrated-
singleton packet.  The common monodromy producer is checked impossible via a
stronger generic support-cardinality-at-most-four theorem.  Finally, pure
nonsingleton collision screening sends every nonsingleton minimum-law source,
including the former quantitative-tail-escape branch, to the same strong
concentrated-singleton packet without any tail estimate.  A checked self-tail
chain supplies a stronger-provenance fallback.  The sole mathematical atlas
consumer class is therefore the source-attached strong concentrated
singleton; the shorter no-tail pure-row adapter is the only remaining
implementation simplification on the atlas-entrance side.

The question below is retained as the broader recursive-atlas specification.
Its old intermediate node descriptions should now be read as internal
certificates of the uniform-escape or minimum-return packet, not as a request
to enlarge the global mode type.

The canonical maximal-prefix construction consumes the subarm whose debt ray
converges to `D_*` and sends it to the checked three-role transfer/limit-chord
compiler.  More directly, checked normalized-passport minimization applies to
every forced-pair packet before the ray is classified, closes the
source-attached pair passport under every literal prefix, and eliminates
positive-absorption exact roots at a compact debt minimizer.  The live normal
forms are therefore exactly:

1. a minimum-return `ThreeRoleLimitChord`; or
2. an off-minimum normalized-passport point whose exact cap--Nash root is
   uniquely all Continue.

Neither is yet a terminal consumer.  The chord's actual endpoint sequence now
does regenerate a complete minimum-atom source at the exact limiting endpoint
law: lossless routing retains a named positive finite atom and same-point
causalization supplies the new chronology.  What it does not supply is an
orientation of repeated regenerated sources; the old paid edge need not occur
inside the fresh chronology.  A paid `4`/`6`/`8` endpoint cycle now forces a
fixed spectator debt rise and hence a fixed-charge stopping-law atom
alternative before that regeneration, but the fresh chronology need not
retain this oriented edge either.  The inert point loses its fixed actionable
passport after the paid endpoint update.  Another unchanged exact-prefix
iteration or a horizontal cycle without chronology is not a new atlas node.

## Objective

Construct a finite, natural, source-preserving reduction of every hypothetical
four-player quitting-game counterexample into a fixed family of producer
obligations.  The members of the family may still require substantial
analysis.  The point is to make the family exhaustive, so that proving one
member impossible, consuming one member, or proving one entire producer mode
unavailable strictly reduces the remaining problem.

The target is not an enumeration of reward tables or a bounded search through
chronologies.  It is a finite **obstruction atlas**: a directed transition
system whose nodes are mathematically natural classes of actual counterexample
data and whose edges are exhaustive source-matched alternatives.  The graph
need not be acyclic: same-point source regeneration creates genuine return
edges.  Every strongly connected component must therefore be displayed rather
than silently treated as descent.

The final theorem should have one of the following equivalent forms.

1. Every `FinFourQuantitativeFullSupportHardResidual` produces one member of a
   finite inductive family of source-carrying residuals, and every terminal
   member has a stated conjecture-facing consumer obligation.
2. Every failure of a uniform-equilibrium payoff produces one of finitely many
   mutually intelligible normal forms, each retaining enough literal data for
   a proof or refutation to continue without reselecting its source.

An eventual completion of the atlas must consume every unresolved terminal
node and every nonterminal strongly connected component into one of:

\[
\boxed{
\begin{array}{c}
\text{terminal approximate Nash profiles at every positive error},\\
\text{a positive cumulative admissible payoff near-return},\\
\text{a source-regenerated well-founded descent},\\
\text{or an actual all-behavior positive-gap counterexample.}
\end{array}}
\]

## Exact starting point

Work under a terminal exploitability witness on `Fin 4`.  Equivalently, work
under the checked hard-residual reduction and its positive compact minimum
debt `D_* > 0`.  The maintained hard residual includes table-level normality,
punishment normality, a full-support packet, and a hard principal.

At this boundary the minimum-law finite-atom producer is already checked:

- `finFourHardResidual_minimumLaw_causalSuffixAtom` and
  `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean` attach a positive finite
  coalition atom to a supplied hard-residual minimum joint-law point.
- `QuittingMinimumLawCausalSuffixAtom` in
  `TerminalSemanticLawCarrierCausalization.lean` retains the actual source
  subsequence and arbitrarily deep source-matched cap--Nash suffix access.

Thus the Fin4 atlas need not retain a spurious minimum-law pure-Never leaf.
Never mass and escape bubbles may reappear later under regeneration or
compactification, and must then be represented honestly.

## Required notion of an atlas node

An atlas node must contain more than a predicate on a reward table.  It should
package:

- the literal behavioral source profile or a specified realizing sequence;
- the complete stopping or terminal law when the argument uses it;
- the minimum point and the precise minimum-fiber relation being invoked;
- every marked player, coalition, date, pure-time witness, and continuation;
- all quantitative floors needed by its proposed consumer; and
- the exact operation by which a successor node is reached.

Semantic equality, equality of one payoff vector, agreement of labels, or
membership in the same carrier is not a substitute for these source fields.

A node may carry continuous or measure-valued data.  “Finite atlas” means
finitely many natural **types of obligation**, not finitely many instances.

## Candidate reduction axes

The following axes are proposed starting material, not an assertion that the
coverage theorem has already been proved.

### A. Terminal atom type

The positive minimum-law atom is either:

1. a singleton; or
2. a nonsingleton coalition.

On `Fin 4`, the latter has cardinality two, three, or four.  Player relabelling
may reduce the number of distinct cases, but the source coalition itself must
remain in the data.

### B. Causal row account

After moving the suffix atom to an actual reached row, the exact collision or
Green-account inequality should dispatch to:

1. quantitative tail escape from the minimum fiber; or
2. a low-tail literal endpoint transfer.

For a nonsingleton atom, collision anti-diffusion gives a fixed reached stage
mass.  `NonsingletonMinimumLawLinearTransfer.lean` contains the current
Research-level tail-escape/routed-transfer interface.

### C. Low-tail endpoint dynamics

The literal same-stage endpoint reduction now gives:

1. a routed concentrated singleton; or
2. a finite horizontal strict endpoint cycle.

`SameStageEndpointMonodromy.lean`,
`SameStageEndpointPurification.lean`, and
`FinFourSameStageEndpointMonodromy.lean` check this finite reduction in
`Research`.  On Fin4 the cycle has length at most eight and has common-host or
complementary-pair geometry.

For the profitable maximum-defect dynamics, every surviving nonsingleton
cycle has period `4`, `6`, or `8`.  Literal return of the complete profile and
exact own-debt subtraction imply that some frozen spectator gains debt by at
least one third of the edge floor.  The endpoint-rise decoder converts this
into a fixed-charge stopping-law atom alternative.  Compactification then
gives an off-minimum endpoint or regenerates a full minimum-atom source at the
actual endpoint law.  This removes the bare paid-cycle leaf; chronological
orientation of the regenerated source remains open.

The stronger terminal-SCC normalization is also natural.  Under the full
strict membership-toggle graph, every terminal SCC is closed under all
improving toggles.  An elementary cardinality argument shows that every Fin4
terminal SCC contains a pair vertex.  This fact does not itself supply a
chronology.

### D. Exact cap behavior

Whenever an actual paid profile is lifted by exact cap--Nash roots, the
checked `exactTrichotomy` in `PaidCapPortExactTrichotomy.lean` gives:

1. charged near-return;
2. quantitative semantic-debt descent; or
3. inert all-Continue stall.

The charged branch is already consumed under a counterexample witness.  Real
descent is not well-founded without an actual regenerated source, and inert
stall is not a contradiction merely because the suffix law has a positive
atom.

### E. Temporal locality

Every proposed profile-to-profile construction should be normalized by its
first live-history disagreement.

For a single pair of distinct live-root sequences, either there is a least
finite disagreement date or the live-root sequences coincide.  For a sequence
of constructions, after taking a subsequence, the first disagreement dates
are either bounded or tend to infinity.  This gives two fundamental temporal
modes:

1. **tight disagreement:** a fixed finite source-matched row survives;
2. **escape:** every modification moves to infinity and must be represented by
   Never mass, an escaped terminal bubble, or an escaping cap witness.

A proposed atlas should prove the relevant compactness statement rather than
silently treating these two modes as interchangeable.

### F. Finite strategic type

Within a temporal mode, the following are finite natural indices on Fin4:

- marked terminal coalition and its cardinality;
- active positive-debt support;
- pure/interior/boundary status of each product-root coordinate;
- signs and zeros of endpoint complementarity residuals;
- membership-toggle graph and terminal-SCC geometry;
- mover, observer, recipient, and complementary-pair incidence; and
- whether an exact cap root has positive absorption or is uniquely
  all-Continue.

These finite labels do not replace payoff magnitudes or source laws.  They
identify chambers in which one uniform proof may be possible.

### G. The checked tangent-family rank sub-DAG

There is already one complete finite reduction which must appear in the
atlas.  The theorem
`QuittingPositiveMinimumDebtTangentFamily.reducedSupportRankAlternative_of_positiveMinimumDebt`
in `FlatCirculationSupportRankElimination.lean` terminates, by strong
induction on positive-debt-support cardinality, in exactly one of the
following types of exit:

1. a tangent column with positive total slope;
2. flat entry into a previously zero-debt coordinate; or
3. an off-minimum literal full-replacement endpoint carrying an eventually
   paid first-disagreement row.

Minimum-fiber strict support descent is an internal recursive edge, not a
fourth terminal leaf.  The no-entry hypothesis is essential: on the minimum
fiber, debt may move sideways from one active coordinate into a formerly
inactive coordinate without lowering support cardinality.  The abstract
vectors `(1,0,0,0) -> (0,1,0,0) -> (1,0,0,0)` already satisfy the relevant
flat sum and mover-disappearance identities, although this abstract pattern
is not asserted to arise from a quitting-game counterexample.

This checked tangent sub-DAG and the literal endpoint-cycle sub-DAG are
different typed constructions.  The former retains a minimum semantic pair,
a realizing source sequence, vanishing-scale whole-law replacements, and
full-replacement clusters.  The latter retains a literal profile, one reached
date and tail, a routed atom, and a same-stage endpoint word.  Their existence
on the same reward table does not identify their sources.

Consequently the atlas must either keep the two sub-DAGs separate or construct
a genuine dependent coupling, schematically:

```text
EndpointCycleTangentPassport(frontier)
       |
       +-- chronological consumer
       `-- lower-rank frontier + regenerated complete passport
```

Generic support-rank descent regenerates the tangent family only.  It does not
regenerate the atom, marked reached date, endpoint cycle, fixed labels, seams,
floors, or availability estimates.  A claimed edge from horizontal recurrence
to the tangent rank argument is invalid unless it proves this full conjunction.

## A candidate finite transition system

The first atlas should attempt to prove, repair, or refute the following
schematic coverage.  Each arrow must be a theorem on the same actual source
chain.

```text
Fin4 terminal-gap witness
        |
        v
positive minimum + hard residual + positive causal finite atom
        |
        +-- singleton atom
        |      |
        |      +-- terminal approximation / repaired charged return
        |      +-- source or repair debt descent with regeneration
        |      `-- source-matched double inert singleton residual
        |
        `-- nonsingleton atom
               |
               +-- quantitative tail escape
               |      |
               |      +-- positive maximal-cap charge
               |      +-- regenerated descent
               |      `-- inert escaped-tail residual
               |
               `-- low-tail literal transfer
                      |
                      +-- concentrated singleton
                      `-- horizontal recurrence
                              |
                              +-- common-host cycle
                              +-- complementary-pair cycle
                              `-- terminal SCC containing a pair
```

The diagram is deliberately redundant: a terminal SCC may contain several
simple-cycle geometries, and a concentrated singleton may feed the same
singleton node reached directly from the minimum law.  Part of the task is to
replace this sketch by a finite collection of precise nodes and prove which
arrows are exhaustive, which nodes coincide, and which branches are
unnecessary.  Every proved return to an earlier source type must be drawn.
Each edge must be labelled as terminal, a renewable rank decrease, or a
rank-free transition.  SCCs are computed only from proved edges whose output
literally contains the target node's required source fields.

In parallel, every positive minimum enters the checked tangent-family sub-DAG

```text
positive minimum tangent family
        |
        +-- positive total slope
        +-- inactive-support entry
        +-- off-minimum eventually paid row
        `-- lower support rank, then repeat
```

The last arm terminates after finitely many repetitions.  The atlas must not
draw an arrow from the endpoint-cycle diagram to this diagram merely because
both exist on the same reward table.  Producing their source-matched passport
is itself one of the principal atlas edges to prove or refute.

## Required coverage theorem

A satisfactory first result is not required to solve every leaf.  It must,
however, prove a genuine finite coverage statement.  A Lean-facing shape is:

```lean
inductive FinFourProducerResidual (reward : ...) : Type
  | singleton ...
  | tailEscape ...
  | inertTail ...
  | commonHostMonodromy ...
  | complementaryPairMonodromy ...
  | pairTerminalSCC ...
  | escapingDisagreement ...

theorem uniformPayoff_or_finFourProducerResidual
    (reward : ...) :
    Nonempty (QuittingUniformEquilibriumPayoff reward) ∨
      Nonempty (FinFourProducerResidual reward)
```

The actual family may differ.  Constructors should be added only when an
existing exhaustive theorem forces them or when a proved no-go shows that a
coarser constructor must be split.  Every constructor must state its
conjecture-facing completion obligation.

An alternative formulation is a finite list of predicates together with a
coverage theorem and source-carrying structures for each predicate.  An
unstructured disjunction of existential labels is not enough.

## What counts as progress

The atlas is intended to make negative results cumulative.

### Direct conjecture progress

Any of the following strictly reduces the live counterexample space:

- prove that one atlas leaf is impossible under a terminal witness;
- map one leaf into an existing all-behavior compiler;
- map one leaf source-faithfully into another leaf of strictly smaller finite
  rank; or
- merge several leaves by a theorem giving one common consumer.

### Producer-language progress

A no-go for a construction method counts only if:

1. the method is one arm of a proved exhaustive producer normal form; and
2. the no-go eliminates that entire arm, not one chosen parameterization.

For example, a theorem that every local finite first-disagreement producer
must satisfy a stated Bellman identity, followed by an impossibility theorem
for that identity on an inert leaf, removes the complete local arm and forces
the escape arm.  A counterexample to one reset formula does not.

### Insufficient outputs

The following do not by themselves advance the atlas:

- a finer sign split with no coverage or consumer;
- an independently selected stationary profile with matching labels;
- a static coalition cycle presented as a chronology;
- positive terminal-law mass presented as current root absorption;
- real-valued debt decrease without regenerated source data or a uniform step;
- failure of one numerical or bounded-horizon search; or
- a verifier whose hypotheses no atlas node is known to produce.

## Systematic finite work inside a leaf

Once a leaf is established, its finite strategic types may be exhaustively
enumerated up to `S_4` symmetry.  Suitable exact tools include:

- Boolean-cube SCC enumeration for membership toggles;
- support and complementarity-face enumeration for product roots;
- quantifier elimination or exact SMT over the remaining payoff inequalities;
- exact rational witnesses for feasible chambers and exact unsatisfiability
  certificates for empty ones; and
- counterexample-guided enlargement of the node's augmented state when two
  instances with identical recorded data require different consumers.

The temporal adversary must remain unrestricted.  Fixed horizons alone are
not complete.  The checked finite-clock/quantile hierarchy in the
escape-aware certificate lane is the appropriate model for finite exact
approximations that retain Never and escaping clocks.

## Boundary tests for the atlas itself

A proposed atlas is incomplete if any of the following can occur without
entering a constructor:

1. an actual source sequence whose marked data disappear only by escape to
   infinity;
2. a minimum-law atom that remains in a suffix law but never becomes current
   root absorption;
3. an exact cap port with quantitative real descent but no actual regenerated
   source;
4. a unique-all-Continue cap with a persistent paid or curvature mark;
5. a terminal toggle SCC that is a union of differently hosted cycles and has
   neither a common host nor a complementary pair globally;
6. a new positive-debt coordinate entering during a purported support drop;
7. a cap supremum changing its maximizing stopping law under a reset; or
8. two sources with the same semantic pair but different usable laws,
   terminal atoms, or restartability; or
9. a minimum-fiber rank descent that regenerates a tangent family but loses
   the literal atom/cycle passport needed by the proposed consumer.

These are tests of the recorded state, not invitations to create eight new
diagnostic leaves automatically.

## Desired outcome

Produce a finite, proved transition system for the Fin4 hard residual, with
every node carrying literal source data and every outgoing edge recording its
exact completion contract.  Then consume every unresolved terminal node and
every nonterminal SCC, or prove exhaustive no-go theorems that remove edges
and force successively more nonlocal producer modes.

The guiding standard is:

\[
\boxed{
\text{Every successful theorem or genuine no-go removes a node or an edge
from one proved finite atlas.}
}
\]
