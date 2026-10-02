# Packet audit: executable proof architecture and its exact no-go boundaries

Reviewer: `ARCHITECTURE_PACKET_AUDIT`

Targets:

- `meta/EXECUTABLE_COMPACT_STATE.md`;
- `meta/GRAMMAR.md`; and
- `meta/VANISHING_REACH_SUFFIX_NO_GO.md`.

## Verdict

**Mathematical pass, with an export-boundary condition.**  The three records
form one coherent ordinary-mathematics package.  I found no false probability
calculation, strategy-class restriction, hidden use of an attained late clock,
or incompatibility between the elementary reconstruction theorem and the
non-elementary grammar.

The exact positive result is a **supplied-certificate composition theorem**.
It does not construct the required certificates from an arbitrary four-player
table.  The two exact counterexamples delimit particular adapters; neither is
an impossibility theorem for all adapters admitted by the maintained
construction question.

Consequently, the mathematics is ready to be consolidated into one final
packet, but the present combined question
`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md` is not answered in full: its
last clause also asks for the Fin4 instantiation and a terminal, return,
ranked-exit, or positive-gap output.  Before calling the packet a complete
answer to a named question, the question surface should separate:

1. the now-answered generic architecture problem; and
2. the still-open Fin4 adapter-instantiation problem.

This is a scope condition, not a request for more mathematics in the generic
theorem.  If the named question remains conjunctive, the package is a rigorous
partial answer rather than a completed export-gate answer.  No `L`, `A`, or
`C` status is justified until external formalization and a concrete Fin4
adapter exist.

## Exact theorem boundary recommended for the packet

The final theorem should be stated under one standing game model.

Let `I` be a finite nonempty labelled player set.  Let the quitting rewards be
bounded and let the nonabsorption payoff be the standard zero vector.  A
behavioral profile is represented by independent stopping-time laws on

```text
K = natural dates union Never.
```

Against fixed opponents, a complete unilateral behavioral replacement is an
arbitrary stopping-time law on `K`.  Equivalently, its payoff is a convex
combination of the pure finite dates and Never, and its cap is their supremum.
This quantification includes calendar-dependent hazards, Never, arbitrarily
late stopping, and arbitrary fresh behavioral randomization.  It does not add
an external correlating device.

The positive theorem may then be given in two parts.

### A. Trace phase

Consider an increasing family of finite rooted diagrams built from:

- finite prefixing and concatenation;
- complete unilateral replacement;
- fixed-depth suffixing with a displayed positive reach floor;
- a compact recorded witness with a closed legal-operation relation and a
  continuous actual compiler (`ClosedSelect`);
- a uniformly summable finite-macro decoder with fixed-column convergence and
  a closed ancestry theorem (`Decode`);
- a finite closed recorded case split; and
- a uniformly bounded trace-visible rank whose complete tagged terminal and
  successor relations are closed and whose visible child, terminal output,
  and backward maps are themselves trace-safe (`TraceRank`).

Assume one common restriction-compatible sequence of actual executions, not
one independently chosen execution family per diagram depth.  Assume:

- convergence of every finite stopping coordinate and of the Never
  coordinate at each initial and exogenous law port;
- eventual finite-tail tightness at each such persistent port;
- a positive limiting reach floor at each persistent suffix edge;
- compactness or prescribed convergence for every displayed root, witness,
  branch tag, and approximation error;
- closed graph plus comparison transport for moving optimizers; and
- for a triangular decoder, one uniform summable tail bound and convergence
  of every fixed inner column with its displayed witnesses.

Then one subsequence converges to a compatible family of **actual legal
executions** of every finite diagram.  Convergence is in total variation at
every stopping-law port and therefore in terminal law, prescribed payoff,
the full pure-time/Never obstacle, and the cap over all behavioral unilateral
deviations.  With one initial port, all limiting diagrams use the same actual
root controller.

If the prescribed payoffs at that root converge to one fixed vector `v` and
the unrestricted terminal debts tend to zero, the reconstructed root is an
exact terminal Nash profile.  Under the standard zero nonabsorption payoff,
the checked terminal-to-uniform theorem then makes `v` a uniform-equilibrium
payoff.

### B. Control phase

After one actual limiting node has been reconstructed, a pointwise ranked
producer may be run without a continuity assertion.  It must provide at every
node:

- a natural-valued rank;
- either a terminal certificate with a consumer, or an actual selected child
  of strictly smaller rank;
- a legal parent-to-child construction; and
- a backward map from child outcomes to parent outcomes.

Natural-number induction then gives a consumed outcome after at most the
initial rank many nonterminal transitions.  This proves termination only for
the dispatch-selected successor relation.  It does not imply that the child
map commutes with an outer compact limit.  A ranked child visible inside the
trace phase needs the stronger `TraceRank` certificate from Part A.

This is the strongest theorem common to all three records.  It is sufficient,
not necessary, and it is not an arbitrary-game producer.

## Independent mathematical checks

### Stopping-law semantics and unrestricted deviations

Before absorption, the public live history at a date is uniquely the string
of previous all-Continue outcomes.  A player's behavioral hazard sequence
therefore determines one law on finite stopping dates plus Never.  Conversely,
the hazard

```text
mass at t / survival through t
```

executes every such law.  Independent behavioral randomization across players
gives the product of their stopping laws.

For fixed opponents, the expected payoff of any replacement law is linear in
that law.  Thus its value is the convex combination of deterministic-date and
Never values, and the supremum is exactly the supremum over those pure times.
This verifies that the architecture's cap is not merely stationary or
finite-horizon.

The split point `Late` is also necessary and correctly distinguished from
Never.  As a deterministic finite deadline tends to infinity, the deviator
receives its solo reward if all opponents play Never.  A literal Never action
instead receives the nonabsorption payoff.  These coincide only under an
additional reward or opponent-absorption condition.  The compactification
keeps the two points separate and does not claim that `Late` is an executable
stopping date.

### Total-variation estimates

The finite-cylinder estimate follows by splitting the `l1` sum into the
displayed finite coordinates, Never, and the two finite tails.  Product-law
distance is bounded by the sum of marginal distances.  Hence a bounded reward
gives the displayed payoff estimate, and the same estimate uniformly over a
deviator's pure time gives the full obstacle and cap estimates.

Finite prefixing is Lipschitz by common-uniform coupling.  Conditioning a
restriction of mass at least `alpha` has the stated coarse `2/alpha`
Lipschitz bound.  Therefore every fixed finite elementary diagram has a
finite program-dependent modulus.  The order of quantifiers is essential and
is correctly stated: fix the requested finite program first, then choose its
tail cutoffs and reach margins.  No modulus over all future calendar depths
is claimed.

### Tight reconstruction

Finite-coordinate and Never-coordinate convergence alone can lose mass at
late finite dates.  Eventual finite-tail tightness prevents that loss.  The
limiting coordinates then sum to one, and the cylinder estimate upgrades
coordinate convergence to total-variation convergence.  The law-to-hazard
formula provides an actual behavioral compiler.

Topological induction over a finite diagram is valid for prefixing,
replacement, and positive-reach suffixing.  The non-elementary induction in
`GRAMMAR.md` is also valid:

- closed selected edges retain their witness and legality;
- comparison transport retains moving optimality;
- a recorded convergent minimization error retains exactly its limiting
  error;
- summable decoding is Cauchy in total variation, and closed ancestry passes
  to the decoded limit;
- a triangular decoder is identified only after both fixed-column convergence
  and uniform tail summability are imposed;
- a finite case stabilizes a tag and keeps the full closed branch relation;
  and
- trace-visible rank first obtains an actual convergent selected child, then
  applies closedness of the full tagged relation, and recurses only finitely
  many times.

There are only countably many persistent witness occurrences in the union of
the finite diagrams.  Successive extraction and a diagonal subsequence can
therefore stabilize all finite tags and converge all compact witnesses.
Literal restriction compatibility makes the limiting finite executions agree
on shared ports.  This proves the one-controller conclusion.

### Terminal consumer

Total-variation convergence gives convergence of both prescribed payoff and
the complete behavioral cap.  If cap minus payoff tends to zero, its limiting
value is at most zero; it is also at least zero because the prescribed strategy
is an allowed unilateral replacement.  Thus the limit is an exact
all-behavior terminal Nash profile.  The cited checked declaration
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` has exactly the
standard zero-nonabsorption quitting-game semantics needed for the final
uniform-payoff conclusion.

## Exact no-go boundary 1: escaping late mass

The clock/tester table is correct.  The clock receives `-1` exactly when it
quits alone; the tester receives `1` exactly on a simultaneous quit.  If the
clock is uniform on its first `n` dates and the tester plays Never, then:

- the prescribed payoff is `(-1,0)`;
- the clock's cap is `0`, attained by Never;
- the tester's cap is the largest clock atom, `1/n`; and
- every fixed clock coordinate tends to zero while no mass tends to Never.

The compact split trace therefore places all clock mass at `Late`, with
semantic limit payoff `(-1,0)` and cap `(0,0)`.  No actual profile has this
semantic pair.  Clock payoff `-1` would force the clock to stop finitely and
alone almost surely.  Its probability law on the countable finite dates must
then have a positive atom, which the tester can hit by a deterministic quit,
contradicting tester cap zero.

The summable coordinate-budget refinement is exact: if every finite clock
atom is bounded by numbers of total mass `1/2`, the clock stops finitely with
probability at most `1/2`, so its payoff stays at least `-1/2`.  This gives a
fixed discrepancy despite arbitrarily accurate satisfaction of every finite
probe family.

Exact scope:

- compact cylinder compatibility is not executable compactness;
- a tightness or actuality passport cannot be omitted; and
- the example does not obstruct a construction that proves tightness or
  supplies a decoder with enough recovery budget.

The underlying semantic nonattainment phenomenon is already checked in
`PositiveDebtTerminalSemanticNonattainment.lean`.  The split-clock trace and
summable recovery-capacity statement are the new ordinary-mathematics
formulation.  A final packet must not present the entire example as absent
from the Lean corpus.

## Exact no-go boundary 2: vanishing-reach suffixing

With the half-`l1` total-variation convention, conditioning at fixed depth is
`2/rho`-Lipschitz when both source reaches are at least `rho`.  At depth one,
the closure of the legal conditional-suffix graph is exactly

```text
the legal positive-reach graph
union
{delta_0} times all target stopping laws.
```

The arbitrary fibre is obtained by putting mass `1-p` at date zero and a
`p`-scaled, one-date-delayed copy of an arbitrary target law behind it.  If a
limiting source has positive reach, fixed-floor continuity forces the literal
suffix.  If it has zero depth-one reach, it is `delta_0`.  These two arguments
prove both inclusions.

Starting from the protected source `delta_0`, finite prefixing,
concatenation, and legal positive-reach suffixing preserve zero Never mass.
They therefore cannot reconstruct `delta_infinity`; the total-variation
distance remains one.  On the one-player quit-for-one table, this is also a
unit conditional payoff/debt discrepancy.  The closed graph has the literal
self-loop at `delta_infinity`, so no natural rank depending only on the law
can strictly decrease along every edge.

Exact scope:

- this is a conditional suffix-level obstruction;
- the source reach in the approximating profiles tends to zero, so the
  unconditioned semantic effect may vanish;
- it does not rule out a positive reach floor, a finite-precision use, a
  summable ancestry-preserving decoder, richer off-path provenance, or an
  external phase rank.

It therefore does not satisfy the current question's acceptable-negative
clause by itself.

## Exact no-go boundary 3: same-source maximal exact roots

The two-player table in `GRAMMAR.md` has cap vector `(z,0)` on the displayed
source family.  Direct root-complementarity calculation gives:

```text
z > 0:  the exact root set is only all Continue;
z = 0:  the exact root set is [0,1] times {0}.
```

Maximizing one-stage absorption therefore selects all Continue before the
limit and forces player 1 to Quit at the limit.  The prelimit successor traces
converge to all Never, where player 2 has payoff and cap zero.  Every exact
maximal-root successor at the limiting source gives player 2 payoff and cap
one.  The exact same-source maximal-root graph is consequently not closed.

The approximate strengthening is also correct.  At the limiting source, an
exact root that is `epsilon`-maximal for absorption must have first-player quit
probability at least `1-epsilon`; its successor gives player 2 payoff and cap
at least `1-epsilon`.  Thus allowing vanishing optimization error while
retaining exact root equations does not repair the same-source trace.

Exact scope:

- this rules out a universal closed or vanishing-error trace adapter for
  prefixing the same actual source by an absorption-maximal **exact** cap
  root;
- it does not rule out approximate root equations, restricted domains,
  pointwise discontinuous control after reconstruction, a modified source,
  another objective, or a construction-specific ancestry-preserving decoder.

This no-go also does not satisfy the current broad acceptable-negative clause
by itself.

## Consolidation audit

The three files use compatible mathematical objects after one explicit scope
choice: the final packet should impose the standard zero all-Never payoff at
the outset.  `EXECUTABLE_COMPACT_STATE.md` develops some law semantics for an
arbitrary bounded Never payoff, which is harmless, but its terminal-to-uniform
consumer should not be exported at that broader scope.

No proof depends on the contextual absorption-path citation.  The final
packet may omit that citation rather than suggesting reliance on an external
compactification theorem.

The following distinctions must survive consolidation:

1. `Late` is a compact response boundary, not an executable stopping time.
2. The compact trace closure is not the executable state without a passport.
3. A selected output law being actual does not prove that it is the named
   legal operation on the named source.
4. Closed graph preserves feasibility, but moving optimality additionally
   needs comparison transport.
5. Uniform decoder tail summability does not identify an outer limit without
   fixed-column convergence.
6. A pointwise rank is control after reconstruction, not a trace-continuity
   certificate.
7. The suffix no-go is conditional and the maximal-root no-go is
   same-source/exact-root specific.

If these are kept literal, consolidation introduces no hidden dependency.

## Source correspondence

The relevant checked source boundary is:

- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `quittingGame`, whose active-state reward is zero, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`;
- `quittingTerminalPayoff`, whose nonabsorption contribution is zero, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`;
  and
- the clock/tester semantic nonattainment construction and all-behavior
  nonattainment theorem in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean`.

The grammar, split-clock tight-fusion theorem, summable recovery-capacity
formulation, exact suffix-closure calculation, and maximal-root graph
counterexample are ordinary mathematics not yet represented by named checked
declarations.  They should be handed to formalization as new `MathUE` or
`Research` interfaces, not cited as existing Lean results.

The absorption-path paper is only contextual here; none of its results is a
premise of the proofs.

## Boundary tests required in the final packet

The three records already contain strong negative tests.  A consolidated
export should also include one explicit positive nonvacuity test, for example:

- a constant finite-support execution sequence under a fixed finite elementary
  diagram, for which tightness, reach floors, and every trace conclusion are
  immediate; and
- a recorded exact-root prefix whose root witness converges, illustrating
  `ClosedSelect` without asserting a continuous global selector.

These add no new theorem but satisfy the export gate's positive-boundary
requirement and prevent the sufficient grammar from reading as a merely formal
list of hypotheses.

## Lean handoff boundary

A final packet should suggest separate declarations rather than one monolith:

1. stopping-law execution and the pure-time/Never cap formula;
2. elementary operation total-variation estimates and tight-fusion;
3. closed selected-edge and comparison-transport optimization limits;
4. fixed and triangular summable decoders with ancestry;
5. pointwise ranked production and bounded trace-visible rank;
6. the coherent executable diagonal;
7. the terminal-Nash/uniform-payoff corollary;
8. the exact depth-one suffix closure and protected-source no-go; and
9. the same-source maximal-exact-root counterexample.

The adapter structures must contain legal-edge theorems rather than assuming
their own outputs are legal by construction.  The formalizer should not encode
the desired Fin4 adapter as a field: producing that adapter is the remaining
mathematical problem.

## Final recommendation

I give full independent mathematical signoff to the consolidated theorem and
the three narrowly scoped obstruction results.

For export, use one self-contained final document and do not merely concatenate
the three notes.  State the supplied-certificate theorem first, then the three
boundary counterexamples, source correspondence, positive/negative tests,
Lean handoff, and nonclaims.

The clean conjecture-facing split is:

```text
generic executable architecture: complete ordinary mathematics
Fin4 production of its certificates: open
```

If the maintained question is split along that line, the generic packet is a
complete answer to the architecture question and a separate Fin4 question can
ask for the actual residual adapters.  If the question is not split, describe
the packet as a rigorous narrowing result rather than as a completed answer.
