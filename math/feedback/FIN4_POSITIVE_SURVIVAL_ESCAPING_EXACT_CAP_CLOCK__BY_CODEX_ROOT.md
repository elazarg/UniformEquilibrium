# Copied-response regret: terminology correction

Author: CODEX_ROOT, with independent read-only Astra verification.
Date: 2026-09-06.

The frozen export's conclusion 2 and the proof following equation (7) call
the displayed residual debt the current-root support-Nash defect. The
formula is correct for ordinary mixed-root coordinate regret, but not for
the regret of every supported pure action.

Write `h` for the owner's Quit probability and `D` for the transported
positive debt. With both actions supported, the raised cap-tail has
`Continue - Quit = D` and prescribed value `Quit + (1-h)*D`.
Consequently:

- ordinary mixed-root regret is `h*D`;
- the supported Quit action's shortfall from the best pure action is `D`;
- its shortfall below the prescribed mixed payoff is `(1-h)*D`;
- the least tolerance in the production row-perfect predicate is
  `max(h,1-h)*D`.

The first quantity, and the copied response's residual debt, are proved by
`quitting_capTail_coordinateDefect_eq_copiedResidual` and
`quitting_copiedCapResponse_debt_eq_quitProbability_mul`
(`UniformEquilibrium/Quitting/Root/CopiedCapResidualDebt.lean`). Their targeted
and full strict silent builds passed; the integrated checkpoint `7e7a4de` is
pushed. The separate supported-action formulas above were checked algebraically,
not yet added as Lean declarations.

The correction is to call the existing quantity the ordinary coordinate Nash
defect. It does not invalidate cap attainment, copied gain, or residual debt.
The frozen export is left unchanged; subsequent coverage must retain this
distinction rather than claim a supported-action bound with the same constant.
