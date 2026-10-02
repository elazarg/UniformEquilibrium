# Post-edit source audit of the Fin4 component questions

Reviewer: `GATE_SOURCE`

## P2 — the generic paid-cap question names the wrong operation

In `questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md`, “the exact
maximal paid-cap dispatch” should be “the exact cap-lifted summable-port
dispatch.”  The displayed trichotomy is supplied by
`QuittingActualProfileTerminalGapPaidCapPort.exactTrichotomy` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
and by `paidFirstDisagreement_capPortTrichotomy` in
`Research/Quitting/PaidRowCapPortDispatch.lean`.  Those constructions choose
exact cap--Nash roots, but do not maximize absorption.  The distinct maximal
one-step construction has a different regeneration/unique-root interface.

The same question's source constraint should also distinguish attached source
provenance from equality of caps.  In the quantitative-descent arm the
descendant is the summable port's terminal-semantic carrier limit, and positive
cap displacement is part of that arm.  It is correct to require the original
actual paid profile, first-disagreement row and its cap comparison to remain
stored as provenance; it would be false to require the descendant cap itself
to equal the original cap.

## P2 — the implementation inequality is cited to the wrong file

In `questions/FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`, the explicit bound

```text
D_* <= 4 eta + sum_i (alpha_i + beta_i)
```

is the Fin4 specialization of the actual-profile implementation theorem in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticImplementationBarrier.lean`.
`PositiveMinimumSeedSeamBarrier.lean` proves the related positive-minimum
small-seed/direct-seam obstruction, but it is not the source of the displayed
payoff/cap-error inequality.  The reference section should cite both files.

No P1 issue was found.  In particular, the edited questions now keep the
generic actual-profile paid-cap stall separate from the independently
constructed paired unique-cap source, state the vanishing-debt atom access in
its actual payoff-difference/response-square form, treat fully screened charge
as an optional shortcut, and use the current density-boundary normal form for
the strict normalized inert arm.
