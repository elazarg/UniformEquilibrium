# Export-gate repair for budget-stable compatible packet iteration

Author: `CODEX_EULER`

The packet in
[`revisit/BUDGET_STABLE_COMPATIBLE_PACKET_ITERATION.md`](../revisit/BUDGET_STABLE_COMPATIBLE_PACKET_ITERATION.md)
has been narrowed to the declarations actually represented by
`MathUE/SublinearCostSchedule.lean` and
`Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`.

Exact edits:

1. Removed the file-level formalization/status note; lifecycle is conveyed by
   directory location.
2. Removed every `liminf` formulation and the power-law/harmonic
   specialization, since neither is needed by the compiler declaration.
3. Replaced the broad “necessary-and-sufficient repeated-scale condition” by
   the exact checked statement: operational sublinearity is equivalent to
   existence of a **positive vanishing**, nonsummable scale schedule with
   summable declared cost.  The packet explicitly disclaims necessity for
   nonvanishing iterations and for loose declared cost bounds.
4. Rewrote the recursive proof with the same explicit budgets used by the
   checked theorem:

   ```text
   budget=min(eta,rho(seed)/4),
   cap=rho(seed)/2.
   ```

   This gives `rho(x_k)>=3*rho(seed)/4>h_k` directly, without an optional
   schedule-tail argument.
5. Removed the optional shrinking-radius and superlinear/power-law boundary
   material.  The retained boundary test only explains why vanishing is a
   necessary hypothesis of the stated schedule equivalence.
6. Replaced the prospective Lean tasks by the exact declaration mapping:
   `IsOperationallySublinearCost`,
   `exists_budgetedDivergentCostSchedule`,
   `isOperationallySublinearCost_iff_exists_vanishing_schedule`,
   `QuittingBudgetStablePacketSystem`, and
   `exists_chronologicalDebtShadowingCertificate_of_seed`.

The independent small-debt seed, literal/canonical anchor, one-step
radius-loss hypothesis, fixed actual labels, and absence of any atom/reset
producer remain explicit nonclaims.  No request is made here to move the
packet; the formalizer can recheck the narrowed statement against the named
declarations.
