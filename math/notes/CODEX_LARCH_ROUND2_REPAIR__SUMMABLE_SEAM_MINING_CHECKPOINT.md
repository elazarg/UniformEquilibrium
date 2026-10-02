# Round-two mining: summable child seams are not missing contraction theory

Identity: CODEX_LARCH_ROUND2_REPAIR.

## Result

**Rejected as a new theory candidate.** The initially distant-looking
contraction and tail-average modules do not close the nested-child Nash seam.
The appropriate variable-survival signed recurrence theory, its infinite
series, and a game-specific adapter already exist. The obstruction is a
nonzero terminal displacement that survives the positive infinite survival
product. An exact canonical four-player example below keeps the seam equal
to one even when all prefix hazards and all adjacent displacement increments
are zero.

The only useful weaker condition found was one-sided control of continuation
losses instead of absolute seam summability. That mechanism already appears
in an existing two-block seam note and the integrated action-probability
Nash-defect identity. A short adapter may be worth adding eventually; it is
not evidence for a missing large mathematical theory.

This is a bounded static source/history audit and ordinary mathematics. No
Lean checks, implementation, export, or positive-global-gap counterexample
is claimed.

## 1. The hypothesis mismatch

The initial comparison was among:

- `Math.Probability.error_le_contractionErrorEnvelope` and
  `Math.Probability.sum_error_le_contraction_bound`
  (`MathUE/Probability/ContractionErrorRecurrence.lean`): uniform contraction
  factor 0≤ρ<1 and additive forcing;
- `Math.weightedTailAverage_tendsto_zero`
  (`MathUE/Analysis/SummableTailAverage.lean`): a scalar error tending to zero,
  averaged against positive summable weight tails;
- `summable_nestedChildSeam_quitPayoffDifference`,
  `summable_nestedChildSeam_absorbingContributionDifference`, and
  `summable_nestedChildSeam_survivalDifference_mul_source`
  (`UniformEquilibrium/Quitting/Root/NestedOwnerRootNashSeamSummable.lean`):
  summability of the first, second, and fourth expanded root-seam terms under
  summable owner hazard, with the third payoff-displacement term unresolved.

Write U_n for the source payoff, W_n for its literal owner-forced child's
payoff, and Δ_n=W_n−U_n in one outsider coordinate. The exact source seam is

    child endpoint gap − source endpoint gap = −s_n Δ_n + R_n,

where s_n is opponent Continue mass after the owner is forced to Continue
and R_n is summable. In the intended summable-hazard branch s_n→1, rather
than tending to zero. A theorem requiring ρ<1 uniformly therefore has the
wrong hypothesis, and a theorem requiring Δ_n→0 assumes a conclusion the
source does not supply.

## 2. The more appropriate theory is already connected

Following the actual definitions exposes:

- `terminalChildPayoffDisplacement_next_eq`
  (`UniformEquilibrium/Quitting/Root/ForcedContinuePayoffDisplacement.lean`):
  Δ_(n+1)=a_nΔ_n+c_n, with a_n the forced root's *joint* survival and c_n
  the owner hazard times a bounded correction;
- `summable_abs_terminalChildPayoffDisplacement_increment` and
  `exists_tendsto_terminalChildPayoffDisplacement`
  (`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSequence.lean`):
  finite variation and a limit, not summability of displacement values;
- `exists_terminalCapChildDisplacement_limit_series`
  (`UniformEquilibrium/Quitting/Root/TerminalChildPayoffDisplacementSeries.lean`):
  the full exact weighted infinite-series formula for that limit, imported
  directly from `MathUE/AffineRecurrenceInfiniteUnroll.lean`;
- `quittingNestedCapChild_eventuallyShift_or_negativeHolonomy`
  (`UniformEquilibrium/Quitting/Root/SignedCapChildHolonomyDichotomy.lean`):
  actual coherent cap clocks with the shifted-clock/negative-limit alternative.

The limit formula already displays the missing cancellation:

    Δ_∞=A_RΔ_R+Σ_(n≥R) A_(n+1)c_n,
    A_R=Π_(n≥R) a_n.

In the positive-survival branch A_R>0. Thus the initial boundary mode survives.
Asking for its signed cancellation is a new condition on the supplied laws
and rewards, not another affine unrolling theorem.

The proposed alternate general tools also exist:

- `Math.abs_discrepancy_le_prefix_max_add_terminal`
  (`MathUE/Probability/DiscountedBackwardRecursion.lean`) retains both signed
  prefix-sum control and the terminal survival remainder;
- `sum_survival_mul_coboundary_eq` and
  `sum_survival_mul_difference_eq_coboundary_sub_remainder`
  (`MathUE/Probability/SurvivalCoboundary.lean`) retain the varying-hazard
  telescope and its explicit boundary;
- `MathUE/Probability/OneSidedDebtShadowing.lean` already separates prescribed
  and response recurrences instead of incorrectly comparing their discounts.

These tools correctly preserve the boundary term. Removing it requires
vanishing survival or compatible boundary data, neither automatic here.

## 3. Exact canonical counterexample to the analytic bridge

Let players be {0,1,2,3}, with owner 0. For every nonempty coalition S set

    r_0(S)=2  if S={0,1,2,3};
           1  if S={0} or S={1,2,3};
           0  otherwise;
    r_1(S)=−1 if S={0,1,2,3}, and 0 otherwise;
    r_2(S)=r_3(S)=0.

All-Never pays zero. This is a complete reward table with bound two and
own-singleton vector (1,0,0,0).

At depth n let source player 0 choose Never and players 1,2,3 quit surely
at date n. Let the child replace player 0 by QuitAt n. The source payoff is
(1,0,0,0); the child's is (2,−1,0,0). Prefixing either sequence by one
all-Continue root produces its next member, and forcing the owner to Continue
does not change that root.

Each all-Continue root is exact Nash against the source payoff: the pure
singleton rewards equal its coordinates, so deviating at that root changes
no player's expected payoff. The owner child's full debt is zero: it obtains
two, the largest reward available to it. Its installed QuitAt n response
attains the source's full cap two. Outsider 1 has full cap zero at the child
by Never, and prescribed payoff −1, so its debt is one at every depth.

All root hazards are zero. Both prefix survival coefficients are one. The
outsider displacement is Δ_n=−1, the remainder R_n=0, and the child-minus-source
root endpoint gap is exactly one at every depth. Therefore:

- displacement has zero variation but is not summable and does not vanish;
- the seam is positive and constant, so signed prefix sums grow linearly;
- every normalized average using positive weights is still one;
- the seam cannot equal a bounded ordinary coboundary plus a summable error,
  because summing that identity would bound a quantity growing as N;
- the survival-coboundary formula has survival one and the same obstruction.

The table is solved: the profile with player 0 quitting at date zero and
everybody else Never is exact terminal Nash. Its owner gets one and cannot
improve against Never opponents; every other reward in a reachable singleton
or owner-plus-outsider pair is zero. Thus this example tests the local source
hypotheses and does not refute a theorem using positive global minimum debt
or absence of uniform equilibrium in an essential way.

## 4. A one-sided weakening survives, but is already understood

Let h_n be the outsider's prescribed Quit probability, e_n its old endpoint
gap, and define the exact root-defect function

    f_h(e)=(1−h)e_+ + h(−e)_+.

This is the integrated identity
`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
(`UniformEquilibrium/Quitting/Root/NashDefect.lean`). If the old root is exact,
f_h(e_n)=0. Since the child's gap is e_n−s_nΔ_n+R_n, subadditivity of positive
parts gives the precise useful bound

    child root defect
      ≤ s_n[(1−h_n)(−Δ_n)_+ + h_n(Δ_n)_+] + |R_n|.

Bounded positive displacements are charged only to h_n and therefore have
a summable cost when outsider hazards are summable. Only the negative part
of Δ_n needs additional summability. In particular, an eventually nonnegative
displacement is sufficient for summable root defects, although the absolute
seam may remain order one. No cross-time signed cancellation is being used:
the asymmetry comes from which action carries the mistake probability.

This is not a new theory claim. Section 2 of
[the two-block seam note](CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md)
already derives exactly this polarity for changing a continuation annotation.
The nested owner-forced case adds only the already bounded R_n perturbation.

Even this weaker local conclusion does not directly instantiate
`QuittingSummableResidualNashBellmanSpine`
(`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`):
the child genealogy is a growing reverse prefix, while that consumer requires
an infinite forward chronology with its own bounded values and residuals.
Its uniform-payoff consumer additionally retains persistent marginal labels.
Neither direction conversion nor those source fields follow from summability
of a few root defects. Cap-annotated and prescribed-payoff-annotated spines
must also remain distinct.

## 5. Actual episode and import distance

The history check used `git log --follow` and selected `git show --stat`
calls. The dates below are repository episodes, not claims about when the
mathematics was first invented.

| File or pair | Observed episode | Import relationship |
|---|---|---|
| `ContractionErrorRecurrence.lean` | First visible in the 2026-08-14 migration, `61e9373` | No direct project-module consumer found apart from the umbrella; no directed dependency path from the nested seam module. |
| `SummableTailAverage.lean` and `Research/Quitting/ForwardExactCapTailFirstOrder.lean` | Both added together on 2026-08-28, `02d7505` | The Research file directly imports and consumes the average theorem. This is one coherent episode, not an independent cross-family discovery. |
| `NestedOwnerRootNashSeamSummable.lean` | Added 2026-09-06, `3c6d97a` | No directed dependency path to either proposed generic module. |
| `TerminalChildPayoffDisplacementSequence.lean` | 2026-09-03, `1ef3ed4` | It already carries finite variation and the displacement limit for the same root recurrence. |
| `AffineRecurrenceInfiniteUnroll.lean` and `TerminalChildPayoffDisplacementSeries.lean` | 2026-09-07, `c2789f0` and `766795a` | The latter directly imports the former: the apparently missing analytic adapter is already present. |
| `DiscountedBackwardRecursion.lean` and `SurvivalCoboundary.lean` | 2026-08-22 episodes `62e4871` and `ed50667` | No directed dependency path from the nested seam module; signed/boundary calculus nevertheless already exists. |

Directed paths were checked by parsing project imports in MathUE,
UniformEquilibrium, and Research. Top-level inventory umbrellas were excluded
from the distance calculation so that blanket inventory membership would not
masquerade as a mathematical dependency. External Mathlib internals were not
used to assert a short project path.

## 6. Cost-effective stopping point

The search began from a genuine hypothesis mismatch, then followed only the
recurrence and its actual consumers. It stopped when the exact series adapter,
the prior one-sided seam calculation, and a complete local counterexample
were found. This is a useful negative mining result: the unsummed term is
not evidence that the code lacks signed or damped summation theory.

A meaningful reopening would require a game-specific identity forcing the
surviving boundary functional to have the favorable sign, or an actual
chronological consumer that tolerates its nonzero value. An arbitrary bounded
coboundary assumption would merely rename that missing source theorem.
