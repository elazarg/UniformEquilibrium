# Conference Goal

## Exact target

Decide the finite-quitting uniform-equilibrium payoff conjecture recorded as
`quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`). For every finite player
type and reward table on nonempty quitting coalitions, the goal asks for one
fixed payoff target that satisfies the uniform finite-horizon equilibrium
contract. The target is fixed before the accuracy; the profile and horizon
threshold may depend on the accuracy.

The proposition is open. Solving quitting games would not by itself solve the
general finite-stochastic-game proposition.

## Start from the mathematics

The primary source of exact mathematical truth is the Lean development itself.
This calls for targeted declaration lookup, not a survey of the 550+ KLOC
codebase. Use the frontier and toolkit as indexes, then read the few source
files supporting the chosen question:

- [`../../UniformEquilibrium/`](../../UniformEquilibrium/) for the integrated
  game-semantic definitions, constructions, diagnostics, boundaries, and exact
  conjecture declaration;
- [`../../Literature/`](../../Literature/) for paper-by-paper Lean statements in
  the papers' own order and terms, including explicit `sorry` markers for
  unproved literature claims; and
- [`../../literature/`](../../literature/) for gitignored local PDFs,
  transcriptions, extraction notes, and other source evidence.

The first two directories differ fundamentally. A theorem in
`UniformEquilibrium/` is checked under its stated imports. A declaration in
`Literature/` may intentionally end in `sorry`, the lane is not built, and
nothing imports it. Lowercase `literature/` is a reading room, not theorem
truth. See [`SOURCES.md`](SOURCES.md) for a concrete reading order and its flat
organization convention.

Use the live documents below as maps and synthesis rather than substitutes for
those sources:

- [`../../docs/SEMANTICS.md`](../../docs/SEMANTICS.md) for the exact model and
  quantifier contract;
- [`../../docs/STATUS.md`](../../docs/STATUS.md) for declaration status;
- [`../../docs/FRONTIER.md`](../../docs/FRONTIER.md) for the current dependency
  boundary; and
- [`../../docs/TOOLKIT.md`](../../docs/TOOLKIT.md) for existing consumers,
  producers, and explicit nonclaims.

Two established semantic endpoints discipline every complete solution:

- A positive solution may produce terminal approximate Nash profiles at every
  positive error and use
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- A negative solution must produce one fixed positive terminal exploitability
  gap against every behavioral profile, as characterized by
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).

## Directions worth exploring

These are invitations, not assignments or assertions of completeness.
Researchers should formulate a smaller standalone question before starting.

### Attack a current explicit producer gap

Read the live frontier and try to construct either chronological
debt-shadowing data from vanishing-debt atom access or a positive exact
admissible return from a paid first-disagreement row. The existing downstream
consumers are useful, but their existence does not prove either producer.

### Find another positive route

Work directly toward terminal approximate Nash profiles through stochastic
control, approachability, viability, topological selection, complementarity,
occupation measures, martingale accounts, or a new executable continuation
architecture. A new certificate language is useful only after soundness and an
actual-data producer are separated and proved.

### Seek a genuine counterexample

Explore exact higher-player reward tables, analytic barriers, or computer-aided
candidates. A decisive counterexample must cover every behavioral profile, not
only stationary, periodic, public-memory, or bounded-controller strategies.
Numerical or bounded-class failures remain internal evidence until a theorem
bridges that gap.

### Prove a sharp intermediate boundary

Exact counterexamples to proposed universal grammars, special-case existence
theorems extending a known class, strict reductions to smaller obligations,
and exact characterizations can be real progress. To become exportable they
must change a named conjecture-facing deficit, not merely add a verifier for
data no arbitrary game is known to supply.

### Cross-pollinate deliberately

Translate a difficult quitting-game obligation into native mathematics from a
different field and solve that standalone problem first. Only afterward build
the adapter and consumer. This keeps independent work creative and makes it
easier for another agent to check without inheriting project-specific jargon.

## Fences every direction must respect

- The target payoff cannot vary with the requested accuracy.
- One profile for an accuracy must work for every sufficiently long horizon.
- A unilateral deviation replaces a player's complete behavioral strategy.
- Expectation, conditioning, stopping, absolute value, and supremum do not
  commute without a theorem.
- Public or private randomization and observation must be available in the
  actual game or explicitly constructed.
- Soundness of a supplied certificate is not production for arbitrary games.
- Integration or a checked conditional theorem is not unconditional closure.

The conference welcomes risky ideas internally. The export gate exists so
that risk-taking never becomes an inflated claim about the conjecture.
