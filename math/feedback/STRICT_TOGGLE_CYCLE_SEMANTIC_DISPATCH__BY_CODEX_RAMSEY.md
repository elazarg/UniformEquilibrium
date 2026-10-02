# Export-gate review of `STRICT_TOGGLE_CYCLE_SEMANTIC_DISPATCH`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  I independently rechecked the assembled export packet against every
item in `exports/README.md`.  I found no unresolved mathematical, semantic,
source-audit, or scope objection.  This is a strict reduction of the updated
selected-cycle obligation, not a compiler for every cycle and not a closure of
the four-player support-two branch.

## Exact statement and proof

The statement quantifies over an arbitrary four-player reward table and one
supplied finite simple strict-toggle cycle.  The bounds `4 <= L <= 16`, even
length, distinct vertices apart from the repeated endpoint, and the literal
reward inequality on each toggled coordinate are all explicit.  The partition

```text
B = intersection S_k,
F = (union S_k) \ B,
O = I \ (B union F)
```

is exhaustive and relabeling-invariant.  A simple hypercube cycle of length at
least four changes at least two coordinates, so `|F| >= 2`; when `B` is
nonempty, `|F| <= 3`.

In the persistent-base case, the induced binary game on `F` has a nonempty
compact Nash set.  The displayed `G` contains exactly the missing initial-row
deviations: outsider join and base-member leave.  For a singleton base, only
the event in which all free players Continue reaches the punishment, so its
coefficient is exactly `mu_x(empty)`.  Thus `G(x) <= 0` gives the stated
all-errors compiler.  Its negation is `G(x) > 0` at every induced Nash point;
continuity and compactness give the strictly positive attained `gamma_(B,F)`.
The `3^|F|` support-status enumeration is a genuine finite semialgebraic
description, with the exact punishment value retained as a supplied scalar.

In the empty-base case, `d_i` is the opponents' absorption probability,
`N_i` the opponents-only absorbing contribution, and `Q_i` the forced-Quit
endpoint.  Since all rates are interior and `|F| >= 2`, `d_i > 0`.  The identity
`H_i = 0` is exactly `N_i = d_i Q_i`; substitution into the stationary payoff
recursion gives `U_i = Q_i`, hence Quit/Continue indifference.  For a passive
player, Continue pays `U_o` and forced Quit pays `J_o`.  Therefore (10) is
exactly the endpoint-Nash system.  Clearing `J_o <= U_o` by the positive
`delta` gives `P_o <= 0`, so `W=0` is equivalent to the complete system.
Compactness of `[rho,1-rho]^F` proves the claimed positive separation and only
the stated conditional boundary escape.

No lemma is deferred inside either argument.

## Behavioral-semantics audit

The packet correctly uses independent behavioral randomization and terminal
absorption at the first nonempty quitter coalition.  There is no hidden public
correlation or post-absorption observation.

- With at least two sure base quitters, any one deviation leaves date-zero
  absorption; with one sure base quitter, only that quitter's leave deviation
  and the free all-Continue event reach the stated unrestricted-cap
  punishment.
- In the empty-base stationary branch, every player has positive opponent
  absorption, so the boundary part of the stationary endpoint theorem is
  vacuous and the theorem controls arbitrary behavioral stopping rules,
  deterministic times, and `Never`.
- Nominal payoffs in the persistent-base all-errors construction are fixed at
  `V(x)` because the prescribed base player quits at date zero.  The exact
  stationary payoff in the empty-base branch is fixed at `U(p)`.  Hence the
  fixed-target terminal-to-uniform consumer applies without a moving-target
  compactness assumption.

This independently confirms the unrestricted-deviation arguments already
checked componentwise by `CODEX_CEDAR`.  Together those are two substantive
reviews of the strategy-class claims, including attempts to break the
endpoint and boundary cases.

## Adapter, consumer, and source audit

The packet's adapter is deliberately conditional on the already checked
strict-toggle branch.  I checked the cited declarations:

- `nonempty_finFourCrossedSupportTwoFiniteResidual` packages the crossed
  support-two finite residual;
- `exists_reachableStrictToggleSimpleCycle_of_lowerSpectatorDefect` and
  `exists_reachableStrictToggleSimpleCycle_of_upperSpectatorDefect` retain the
  anchored positive endpoint toggle and produce the corresponding reachable
  cycle via `exists_reachableStrictToggleSimpleCycle`;
- `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` is the exact
  all-behavior stationary endpoint characterization;
- `exists_punishRow_stationaryUnilateralCap_le` supplies the singleton-base
  near-minmax row; and
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  is the required fixed-target semantic consumer.

The packet does not claim that the finite residual always has a positive
lower/upper defect, nor that equality faces already supply a cycle.  Its new
content begins after a cycle has been supplied and is not a restatement of any
of those declarations.  No paper result is invoked, so no literature
translation remains to audit.

## Boundary and falsification tests

I recomputed all three tables.

- The persistent-base matching-pennies table has the displayed strict
  four-cycle, half-half induced Nash point, and every base-leave excess equal
  to `-1`, so the positive A.1 branch is nonempty.
- The empty-base two-active table has the displayed strict four-cycle and
  `H_s=H_t=0` at rates `1/2`; both passive join inequalities are strict in the
  safe direction, so B.1 is nonempty.
- In the six-cycle negative test, player 1 has `N_1=2d_1` and
  `Q_1=(1-x)(1-y)`, hence `H_1<0` throughout the interior.  This falsifies the
  tempting graph-sign-to-stationary inference.  The separate sure-exit
  equilibrium is correctly recorded, so the example is not misrepresented as
  a quitting-game counterexample.

These tests also prove that A.2 and B.2 are strict residual chambers rather
than vacuous renamings of all supplied cycles.

## Remaining export gates

The packet names the maintained question and makes the exact allowed change:
it replaces the arbitrary selected cycle by a checked semantic endpoint or a
strict face-specific residual.  The Lean handoff proposes definitions and
supplied-object theorem shapes without storing either residual's negation as
an assumed producer field.  The source files are named, and the nonclaims
exclude arbitrary-cycle compilation, chronology, vanishing-defect production,
the equality/strict precursor, and support-three/four cases.  The packet has
no lifecycle/formalization-status header.

Accordingly, the packet satisfies the export gate as written.
