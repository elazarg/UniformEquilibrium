# Inverse-positive singleton matrices: formalization dependencies

Author: CODEX_ROOT. Bounded implementation audit, 2026-09-08.
The accepted packet `INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`
was read in full. This is a dependency plan, not a Lean coverage seal.

## Mathematical target

For a four-player quitting reward table, form the recipient-row,
quitter-column matrix of singleton reward differences. Negative determinant
and entrywise nonnegative inverse imply existence of a fixed ordinary
uniform-equilibrium payoff. Own singleton and nonsingleton rewards may be
signed. The packet first proves the strictly positive inverse case, then
passes to the nonnegative boundary by perturbing only off-own singleton
entries and transporting full behavioral regret.

## Parallelizable dependency chains

1. Literal discounted Bellman map. Implement its polynomial displacement,
   positive value denominator, endpoint identity, clipping fixed-point
   equivalence, full behavioral-deviation bound, and uniform payoff bound.
   Upper faces and indifferent pure actions remain in the definition.
2. Endpoint-preserving analytic selection. The contrary no-UE source and
   absorbing auxiliary-germ consumer are already named in production.
   The new adapter must retain each specified closure point of the full
   Bellman assignment, not select an unrelated germ. The packet's uniform
   localization quantifies over every small-discount fixed point.
3. Rescaled localization and integer degree. Derive convergence of every
   equilibrium hazard divided by discount, apply the implicit function
   theorem, and compare global degree +1 to the sole local degree -1.
   Parity identifies these signs and cannot replace integer degree.
4. Nonnegative-inverse approximation. For dimension at least three, use
   the matrix geometric series and positivity through the second-order
   coefficient. Preserve the zero diagonal and determinant sign. This
   generic matrix theorem can proceed independently of the game proof.
5. Full-cap reward transport. This branch is integrated in
   `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
   and pushed in `d9c5cd9`, after the full silent build and repository gate.
   It bounds each unrestricted response cap, maximum debt, and global
   infimum under same-profile reward transport. Its explicit reward-closedness
   consumer returns one fixed target from arbitrarily close tables having
   uniform payoffs, without requiring their targets to agree.
6. Exact matrix and game boundaries. Formalize the supplied matrices,
   remote discounted equilibria, second-order necessity, and bounded
   comparisons to named sufficient classes. They are independent checked
   tests, not substitutes for the source theorem.

## Located interfaces and present checks

The packet's declaration names were located in the stated production
files: punishment-normal residual, absorbing auxiliary-germ consumer,
positive-coordinate arc-to-germ constructor, and terminal-all-errors
equivalence. Their packet-specific composition has not been checked.

`UniformEquilibrium/VanishingDiscount/Bellman/CurveGate.lean` explicitly
defines `HasBellmanSignCellCurveSelection` with a specified endpoint and
offers conditional adapters. That definition is not an existence proof.
A bounded search in the current topology and curve interfaces did not
identify the required integer-degree theorem. A library audit must precede
implementation; this record does not claim an exhaustive absence result.

The reward-robustness promotion also serves the membership-stretch source
packet. The Research rational-approximation consumer now imports that
production module; no duplicate Research proof remains.

## Scheduling and nonclaims

The newer `INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`
generalizes the raw sufficient class and directly recovers the whole
nonnegative-inverse case. The shared plan is recorded in
`CODEX_ROOT__INTEGER_LCP_DEGREE_DEPENDENCIES.md`. Prefer that total-degree
route to duplicating strict-interior uniqueness machinery; retain this
packet's independently useful approximation and exact boundary results.

Finish the current algebraic-test, selected-owner, and inverse-stretch
proofs before assigning this new packet's substantial library tasks.
The matrix approximation and payoff-transport branches can run independently
of endpoint curve selection and degree once slots are available.

The theorem is not yet implemented. The supplied ordinary mathematics uses
classical curve selection and integer degree; missing Lean interfaces are
not evidence of a mathematical gap. Matrix hypotheses alone do not localize
every discounted equilibrium. The contrary no-UE assumption is essential
to that step, and no arbitrary-player-count conclusion is asserted here.
