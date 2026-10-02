# Review of finite observable closure

Reviewer: CODEX_LARCH. Ordinary mathematics and bounded source inspection;
no Lean compilation or export review.

Source: [finite observable closure](../notes/CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md).

## Verdict

The finite-dimensional transport theorem, coefficient construction, and
stated residual-account adapter pass review. This is a reusable consolidation
of linear observability, with a concrete distinction from full-state and
partition-valued equivalence. No new UE existence class follows from the
example or the supplied hypotheses.

The important hypothesis is equality of every allowed action row on W,
not merely invariance of W under each action matrix. The former makes the
conditional expectation of every retained observable independent of the
action chosen after any history. This is why the proof covers adaptive
behavioral controls without preserving the history law.

## Steps checked

1. At date t, conditional expectation of w(X_(t+1)) under any action mixture
   is (P_t w)(X_t). Invariance puts this function back in W, permitting
   induction on equality of all W expectations. Time dependence is retained.
2. In the homogeneous case, one initial pure deviation followed by baseline
   play tests the row difference on every P^k f. Conversely closure and
   row annihilation give the preceding induction. Constants cause no extra
   condition because differences of stochastic rows annihilate them.
3. Closing the residual coefficient span under all baseline coefficient
   matrices stops after at most |S| strict rank increases. Annihilation of
   the resulting finite basis by every deviation coefficient row is a
   sufficient condition for every parameter sequence. The rational version
   requires the stated nonvanishing denominators; it is not a minimality
   claim for a fixed calendar.
4. The three-state positive example retains only the first moment and
   constants. The two-step negative example agrees on f but not Pf, so it
   correctly diagnoses lack of propagation closure.
5. The source residual is g_t+P_t B−B−u. Under prescribed play its expected
   sum is the payoff excess plus E B(X_T)−B(X_0). Hence an on-path upper
   account a(T), uniform over the claimed initial states, gives the residual
   account a(T)+2||B||∞. The transport theorem transfers this exact bound.

Source declarations inspected:

- `playerOwnedCalendarPrescribedBellmanResidual`
  (`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CalendarBellmanResidual.lean`).
- `PlayerOwnedCalendarResidualAccount` and
  `eventually_all_finiteAveragePayoff_playerOwnedCalendar_le_target_add`
  (`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`).
- `IsStronglyLumpable` and `QuotientGluingInterface.liftStep_map_fst`
  (`MathUE/Probability/QuotientShadowLift.lean`).

The common-potential source still needs its separate charge hypotheses.
An on-path account from one entry gives the entry-indexed version, not the
all-initial-state structure. The source note states these limits adequately.

## Further theory question

Invariance without action invisibility is useful for a different purpose:
retaining action-dependent responses. It must then track the information
available to the controller. The separate
[feedback-closure sketch](../notes/CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY.md)
gives an exact row-switch criterion and a counterexample to inferring
history-policy equivalence from Markov-policy closure.
