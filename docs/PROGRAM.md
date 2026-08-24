# Uniform-Equilibrium Research and Formalization Method

## Purpose

This document is the stable coordination method for three distinct activities:

- [MATH_RESEARCH_METHOD.md](methods/MATH_RESEARCH_METHOD.md) — how mathematical claims are
  formulated, tested, proved, refuted, and made formalization-ready;
- [LEAN_FORMALIZATION_METHOD.md](methods/LEAN_FORMALIZATION_METHOD.md) — how stable
  mathematics is represented, checked, integrated, and used to expose new
  mathematical obligations;
- [PARALLEL_RESEARCH_METHOD.md](methods/PARALLEL_RESEARCH_METHOD.md) — how independent
  investigations are scoped and promoted when they become relevant.

Current project decisions and process rules are in [`PIPELINE.md`](PIPELINE.md).
The generated declaration index is [`STATUS.md`](STATUS.md), and the curated
mathematical state of knowledge is in [`FRONTIER.md`](FRONTIER.md).
Exact internal claims belong in the integrated, Research, or Literature lanes;
attributed external results belong in [`references/`](references/).
Focused adversarial checks, launch questions, proof-mining notebooks, and
experiments are intake/evidence, never current truth by themselves.

In these method documents, a *consumer* is an internal proof step that turns an
intermediate object into a semantic conclusion. It does not mean an external
library user, and external adoption is never a promotion requirement.

### Source-of-truth hierarchy

1. integrated Lean is machine-checked truth at its exact declaration scope;
2. `STATUS.md` gives the generated headline declaration index;
3. `FRONTIER.md` gives the self-contained current mathematical synthesis;
4. `PIPELINE.md` owns promotion decisions, active gates, and blockers;
5. this `PROGRAM.md` owns stable methodology and update rules;
6. route pages record durable interfaces and exact nonclaims;
7. Research and Literature files carry the scientific working record and
   attribution/scope for material that is not yet integrated;
8. the manuscript is readable derivative exposition; and
9. Discussions, Issues, reviews, proof-mining reports, experiments, and
   archived working notes are evidence/intake only.

## Semantic waist

The stable endpoint of the project is the semantic constructor:

~~~text
there exists a payoff v such that, for every accuracy,
one profile delivers v and caps every unilateral deviation
uniformly over all sufficiently long horizons.
~~~

This is equivalent to existence of a uniform-equilibrium payoff. Analytic,
recursive, potential, occupation, and monitoring arguments are construction
languages for reaching this semantic waist.

No intermediate certificate is presumed universally complete merely because
it is convenient to compose or formalize. Different classes may reach the
semantic waist through different sound consumers.

## Reduction, compiler, and reformulation

The project distinguishes three logically different kinds of interface.

- A **reduction** derives structured data from the original source
  hypotheses, or from the assumption that the target theorem fails. Its
  output remains present in the unresolved regime and is independently
  checkable without assuming the desired conclusion.
- A **compiler or consumer** turns supplied structured data into a later
  object or the semantic conclusion. It records a valid implication, but it
  earns no producer or coverage claim until an actual-data adapter supplies
  its hypotheses.
- A **reformulation** is equivalent to the target at the same quantifier
  scope. This includes an interface whose quantified source type is empty
  whenever the target holds and whose consumer proves the target whenever the
  source is inhabited. Such an equivalence can be an excellent integration
  contract, but proving it is not frontier progress by itself.

For every proposed “missing producer,” record all known reverse implications.
If Lean proves `Interface r ↔ Target r`, documentation must call the interface
a conjecture-level capstone or reformulation. The mathematical work should
then be split at the earliest concrete boundary: for example, one reached-
source block estimate, followed by a separate compatibility and iteration
theorem, followed by the global compiler. A failed construction refutes only
the local statement it actually implements; it refutes an equivalent global
interface only if it supplies a counterexample to the target itself.

The practical audit is:

1. state the forward consumer and every known converse;
2. identify which hypotheses are produced from actual source data;
3. check whether the interface is vacuous in the solved regime;
4. separate finite or one-step output from all-errors or infinite iteration;
5. award frontier progress only to the earliest newly proved nonvacuous arrow.

## Three levels of claim

Every proposed architecture or certificate theorem is classified at three
separate levels:

| Level | Question |
|---|---|
| **Verification** | Does a supplied finite object imply delivery and uniform unilateral-deviation caps? |
| **Bounded synthesis** | For a fixed controller class, size bound, or update skeleton, can such an object be found or refuted? |
| **Strategy-class coverage** | Does every semantic uniform-equilibrium payoff admit an object in that class? |

A theorem at one level receives no automatic credit at either higher level.
In particular, an exact verifier for a fixed finite public architecture is not
an architecture producer, and a bounded-template synthesis theorem is not a
completeness theorem for unrestricted or private-history strategies.

The quantifier over accuracy is also explicit. A uniform-equilibrium payoff
may use a different profile or architecture for each requested accuracy; the
payoff target remains fixed. Architecture size may therefore depend on the
accuracy unless a stronger theorem proves otherwise.

For any proposed finite proof language, separate exact-object existence from
accuracy-indexed density. The root-relevant quantity is the infimum of the
full semantic deviation gap over all permitted object sizes, with every
boundary action such as Never retained. An exact zero, a bounded size, a
nonsingular witness, or convergence inside one fixed parameter space is an
additional theorem, not part of approximate production by default. Likewise,
a strategically convenient contracting subclass must be compared against its
noncontracting boundary before it is advertised as complete.

The strategy and observation class is part of every level. Public finite
state, private randomized finite memory, clock dependence, and unrestricted
behavior are not interchangeable representations without a proved compiler.

## Bidirectional workflow

~~~text
mathematical statement -> proof or exact counterexample
         |                         |
         v                         v
formalization packet         corrected search space
         |
         v
checked kernel -> actual-data adapter -> downstream consumer
         |
         +---- failed quantifier/interface/test ----> math question
~~~

Mathematics determines the statement. Lean tests its exact quantifiers,
dependencies, and composability. Lean may expose a missing theorem or false
interface, but it may not silently weaken a statement until it compiles.

## Mathematics-to-Lean handoff

A result is ready only when it contains:

1. a self-contained statement with the exact strategy and randomness model;
2. a complete proof or finite counterexample;
3. concrete input and output data rather than the desired conclusion hidden
   in a record field;
4. quantitative constants and the relevant expectation, conditioning,
   prefix, shift, restart, and stopping conventions;
5. positive and negative tests;
6. the actual data expected to supply its hypotheses;
7. the downstream theorem expected to consume its output.

For an equivalence or exhaustive alternative, the packet must additionally
identify the exact class over which necessity is claimed and expand every
invoked representation theorem. A standard theorem cited only by name may
justify mathematical confidence, but its hypotheses and multichain,
reachability, or information details must be exposed before Lean is asked to
freeze the converse.

## Lean-to-mathematics handoff

A mathematical blockage is returned as one self-contained question,
preferably with the smallest failed finite model. Definitional inconvenience,
missing library infrastructure, and mathematical gaps are classified
separately.

The formalization may refine a statement by exposing an omitted hypothesis.
It may not treat the refined conditional theorem as a solution of the original
unconditional problem.

## Progress accounting

Use four independent evidence seals:

| Seal | Evidence |
|---|---|
| M | rigorous mathematics or a rigorous counterexample |
| L | checked Lean declaration |
| A | checked adapter from actual source data |
| C | checked consumer producing semantic closure or a valid recursive output |

The record is append-only. Refutations supersede earlier claims without
erasing the knowledge gained. LOC, interface count, and conditional wrappers
do not earn closure credit.

The four seals are recorded at the claim level above. Thus a checked
fixed-architecture verifier can have `M+L+C` while the bounded producer and
strategy-class coverage claims remain open. Status prose must say which level
each seal belongs to.

When a later result refutes a calibration example or premise, correct the
claim at its source and mark downstream live summaries as superseded. A
historical record may retain the failed argument only when it is unmistakably
labelled false and the surviving lesson is stated separately.

## Maintenance protocol

- A theorem or refutation commit updates its owning claim file.
- If the mathematical boundary changes, update `FRONTIER.md` in that stable
  commit or an immediately following documentation commit.
- If priority, route, or a project-control decision changes, add/update a
  stable PC decision and queue row in `PIPELINE.md`.
- `FORMALIZED` requires an exact declaration/path and a successful relevant
  build/check. `PUBLISHED` requires exact attribution, source confidence, and
  an adapter to repository scope.
- Refresh the manuscript periodically from `FRONTIER.md`, not on every theorem.
### Reconciliation is a step, not an accident

A result written before a neighbouring result may not reflect the neighbouring
result's hypotheses or consequences. Reconcile related work before either
result is cited downstream:

- When a commit changes the status of a claim, update the index row and the
  superseded claim's lifecycle card **in that same commit**, not eventually.
  The owning Research or Literature record is the corresponding lifecycle
  record.
- When two results touch the same object within a short window, reconcile them
  before either is cited downstream. The cheap check is: does the later result
  weaken a hypothesis the earlier one carries, or discharge one of its gaps?
- Periodic cross-lane mining is part of the workflow: schedule it to reconcile
  nearby results and expose stronger theorems or surviving obstructions.

A corollary for Research and Literature records: a claim recording "this has
no consumer" or "this hypothesis is undischarged" must be re-checked before it
is used as a current reason not to pursue something.

## Scheduling discipline

Schedule by objective priority, not by the arrival time of an answer or file.
The default ordering criteria are:

1. dependency distance to the semantic waist and the number of downstream
   claims unblocked;
2. risk that a false premise is already being consumed;
3. value of a finite counterexample or regression theorem in protecting the
   interface;
4. mathematical readiness for honest formalization;
5. implementation cost and reversibility.

Recency is only a tie-breaker. A new answer enters the audit queue and may
change priorities when it supplies a load-bearing theorem or refutation, but
it does not automatically preempt an older upstream obligation.

Keep at least one Lean lane continuously assigned to the highest-priority
formalization-ready result while such results remain. When a bounded milestone
is build-clean, integrate and commit it immediately with a path-limited commit;
do not wait to bundle unrelated work or include another worker's staged files.
Formalization priority follows the same objective ordering as mathematics: a
recent representational result is not promoted ahead of an upstream
credibility or root-boundary theorem merely because it arrived last.

## Separation rule

Methodology files change only when the way research or formalization should be
conducted changes. New theorems and counterexamples update their claim files
and, when frontier-changing, `FRONTIER.md`. Current priorities and route
decisions belong in `PIPELINE.md`; neither belongs in a transient status file.
