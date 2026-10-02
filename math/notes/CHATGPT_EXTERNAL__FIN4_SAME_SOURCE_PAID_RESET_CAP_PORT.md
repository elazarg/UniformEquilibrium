# Finite-four same-source paid/reset cap port composite

## Status

Reviewed independently by Codex Cedar, Codex Euler, Codex Ramsey, and Codex
Root: **PASS as an immediate composition of checked declarations**.  The only
missing artifact is a named Lean wrapper retaining all provenance.  This is a
formalized/API integration candidate, not a new mathematical export.  No
discharge of the summable port is claimed.

Reviews:

- `notes/CODEX_CEDAR__FIN4_PAIR_BASE_COMPOSITE_SOURCE_AUDIT.md`;
- `feedback/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT__BY_CODEX_EULER.md`;
- `feedback/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT__BY_CODEX_RAMSEY.md`;
- `feedback/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT__BY_CODEX_ROOT.md`.

## Question

For a reward table on `Fin 4`, assume

```lean
witness : QuittingTerminalExploitabilityWitness reward
```

and choose pairwise distinct `owner baseFirst baseSecond : Fin 4`.  Does the
checked corpus directly compose to produce, from one actual pair-base stationary
profile:

1. a full-gap paid first-disagreement row whose observer is in the forced pair;
2. zero owner debt and unit owner/base incidence on the same terminal law;
3. a fixed-law reset dispatch from an attained positive global debt minimum;
4. a literal cap-Nash prefix chronology starting from that same stationary
   profile;
5. exact total-debt scaling, summable root absorption, a uniform positive lower
   bound on reaching the unchanged paid suffix, uniformly positive shifted paid
   rows, and a terminal-semantic all-Continue limit port?

The intended composition is

```text
terminal exploitability witness
  -> attained positive global semantic-debt minimum
  -> exists_finFour_pairBasePaidResetDispatch
  -> target.paid_row
  -> QuittingPaidCapLiftedSource
  -> QuittingPaidCapLiftedSource.nonempty_summablePort.
```

Writing `D_*` for the minimum debt, `D_n` for the literal prefix-profile debt,
`q_n` for the cap root's joint Continue mass, and `alpha_n = 1-q_n`, the claimed
quantitative output is

\[
D_{n+1}=q_nD_n,
\qquad
D_*\sum_{n<N}\alpha_n\le D_0-D_N\le D_0-D_*,
\]

\[
D_N=D_0\prod_{n<N}q_n,
\qquad
\prod_{n<N}q_n\ge D_*/D_0,
\]

and every finite literal prefix carries the shifted paid row with gain at least
`(D_*/D_0) * witness.terminalGap`.

## Claimed significance

This would bypass the separately selected hard principal and marked lasso for
the source-alignment step.  It would not consume the port or prove a uniform
payoff.  The remaining conjecture-facing implication would still be a
same-source paid-port discharge.

## Checked declarations to audit

- `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
  in `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`;
- `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
  and `FinFourPairBasePaidResetTarget.paid_row` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` and its supporting debt,
  reach, shift, and limit declarations in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`.

## Open audit points

- whether a named composite declaration already exists;
- whether constructing `QuittingPaidCapLiftedSource` from `target.paid_row` needs
  any premise not supplied by the witness/minimum;
- whether the exact finite excess-debt bound is already packaged or merely an
  immediate corollary;
- whether the conclusion is best classified as a missing Lean adapter in the
  formalized packet rather than a new export result.
