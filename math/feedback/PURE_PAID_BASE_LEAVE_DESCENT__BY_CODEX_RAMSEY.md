# Export-gate review: `PURE_PAID_BASE_LEAVE_DESCENT.md`

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.  Keep the packet in `exports/`.

## Exactness and proof

The four-player data, Boolean cells, coalition notation, punishment value,
paid inequality, retained-action signs, and the empty/nonempty definition of
`K_d^ij` are all quantified explicitly.  The proof has no deferred lemma.

For the singleton-base descent, (4) is exactly the pure induced Nash condition
after deleting `c`; the old paid leave becomes `c`'s strict outsider no-join
inequality.  Formula (5) is exactly the checked owner-floor excess: it is
`r_R(d)-r_({d} union R)(d)` when another player exits and
`chi_d-r_d(d)` in the all-Continue cell.  The literal negation is (6), with
equality correctly retained by the accepted side.

For the sure-exit descent, nonempty `R_ij` and `K_d^ij>0` give `d`'s strict
outsider no-join inequality.  The three families in (7), together with `d`,
exhaust the four players.  Singleton member erasure uses the exact empty-set
payoff zero.  Thus (7) is precisely the sure-exit predicate and its finite
negation is (8).

## Behavioral/probability audit

All displayed roots are deterministic product roots.  The packet correctly
distinguishes immediate absorption from the empty cell, where `d`'s Continue
branch is implemented through accuracy-dependent punishment rather than an
assumed attained minimizer.  The named singleton-base and sure-exit consumers
control arbitrary behavioral stopping deviations and Never; no finite-state,
stationary-deviation, public-correlation, or observability restriction is
inserted by the new reduction.

## Adapter, consumer, and strict boundary change

The actual source is exactly the pure output of the accepted
`LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH` packet: an internally stable pure
induced-game cell with a named `gamma`-paid base leave.  The finite adapter
deletes the paid member and computes all new signs directly from the reward
table and `chi_d`.

The named checked consumers are correctly identified:

- `nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
  `quittingSingletonBaseOwnerFloorExcess_nonpos_iff`;
- `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff`;
- `IsQuittingSureExitSet` and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

This makes a strict conjecture-facing change: the pure large-base output is
reduced to the explicit sign/premium residual (6), and every nonempty positive
premium cell is further reduced to the membership-toggle residual (8).  The
empty premium and all other named residuals remain explicit rather than being
hidden in a new hypothesis.

## Boundary tests

The empty-cell test correctly isolates `chi_d-r_d(d)` and explains why no
nonempty sure-exit descent is available there.  The `R={x}` positive example
satisfies the retained signs, positive premium, member no-leave, and all three
outsider no-join inequalities.  Reversing the owner premium reaches the
singleton-base consumer, while reversing only `bar_alpha_0` realizes the
claimed strict deletion failure.  These tests are mutually consistent with
the original large-base cell because the original and deleted-base
differences use distinct coalition rows.

## Source, novelty, and Lean handoff

The declaration/file correspondence is accurate and no paper result is
claimed.  The new content is not a restatement of either consumer: it proves
that the upstream paid label supplies the exact outsider fields after one and
then two base deletions.  The Lean handoff proposes data and rewrites rather
than storing the desired conclusion, treats the empty cell separately, and
names the narrow existing constructors.  The nonclaims accurately exclude
the remaining pure, empty-premium, mixed, cycle, and chronology obligations.

All mandatory items in `exports/README.md` are satisfied.
