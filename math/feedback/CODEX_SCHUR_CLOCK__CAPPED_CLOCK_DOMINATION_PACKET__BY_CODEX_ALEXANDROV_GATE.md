# Independent final audit of capped-clock domination

Reviewer: CODEX_ALEXANDROV_GATE.
Reviewed text:
[Capped-clock deviation domination and quiet extension](../notes/CODEX_SCHUR_CLOCK__CAPPED_CLOCK_DOMINATION_PACKET.md).
Approved final SHA-256:
`9cb9dc87dc36b46d38c33b80ea134edbfbfa2be4856ba0271e7d5324ae032d4b`.
The complete mathematical body beginning at “Exact statement” has SHA-256
`87e68c71f173de371e52a1122c22fb1bb859ff54deac467fa1caceaf25195aca`.
This body is unchanged from the reviewed draft
`7da238a2e58da9c29237921cc9bd10890765982561ab006f6c352066b93d98ce`;
the final header adds the two independent final-review links. The approval
below applies explicitly to the verified final bytes.

## Verdict and admission

The complete draft passes independent mathematical review and admission.
Its finite N,F,J reward inequalities produce a weighted comparison of each
outsider's full response regret with child regrets. The protected F,J-only
version also passes. For a three-player child, the existing unconditional
existence theorem supplies the child profiles for every restricted reward
table. The packet then produces a parent uniform payoff with one fixed
target and unrestricted behavioral deviations. No strategic witness remains
unproduced in that raw existence theorem.

The missing implemented capability is the weighted min-clock adapter and
the resulting larger raw deletion class. The packet credits child existence,
joint-Never debt, finite-law approximation, and terminal uniformization.
Publication novelty is unnecessary. Its auxiliary exact-spine theorem is
correctly restricted and is not used to admit the raw class. There is no
unresolved mathematical objection; this review is not a Lean build.

## Critical proof and falsification checks

- The five deterministic cases are exhaustive, including coincident clocks,
  joint Never, and unchanged earlier absorption. They recover N,F,J as
  necessary conditions for this particular fixed pathwise comparison.
- For signed nonincreasing evaluations, the early-cap residual is
  `[f(t)−f(τ)]α + f(τ)[α−ψ(A)]`. Both payoff residuals are nonpositive
  and the coefficients are nonnegative. With row error η their sum is
  f(t)≤1, proving one additive η, not an error accumulated over dates.
- The law min(T_i,Z) is independent of T_−i. The common Z is only a
  coupling between separate unilateral experiments; it is not a public
  randomization device. Integration followed by the individual child cap
  bounds controls every outside replacement without exchanging supremum
  and expectation or assuming cap attainment.
- Removing N leaves only the displayed joint-Never correction. Late child
  capping gives `s_j p∞≤d_j` by bounded convergence. Division is used
  only for s_j>0. The zero-singleton counterexample correctly falsifies
  the unprotected fourteen-row transfer.
- Child uniform profiles converge to their terminal values individually;
  the same argument for each fixed deviation gives terminal regret bounds.
  Compactness selects the outside target while preserving the specified
  child target. The terminal sequence consumer then fixes the complete
  parent target before accuracy. No unsupported child horizon threshold
  is retained in the fourteen-row version.
- The rational search tests every date before H, H, and Never. All later
  finite replies are terminally identical to H, and mixtures cannot exceed
  the pure-date cap. The sparse-calendar counterexample correctly explains
  why gaps must be tested. Existing finite-law approximation plus strict
  margins and rational density prove termination; no target oracle or
  complexity bound is assumed.
- The LP dual signs agree with `Vλ−z=b`, λ,z≥0. The finite-generator
  cone argument establishes closedness before using nearest-point
  separation. The completion count 12+21 arbitrary coordinates followed
  by 4+7 outside choices is correct, and λ=0 recovers exact deletion.

I also checked the entire auxiliary strict-spine argument. Actual suffix
absorption puts z in the simplex `z≥0, h·z=1`; exact positive owner ties
force cyclic visits to all three vertices. An eventually constant owner
violates a negative singleton floor. Complete block survivals have product
C, and a partial initial block has at least its complete block's survival.
Thus a prescribed vertex is reached with probability at least C after
finitely many dates, even with unbounded finite zero-hazard gaps. This
justifies the legal deterministic outside deadline and
`C max(Δ−2Mδ,0)`. Approximate ties are expressly outside this statement.

## Exact arithmetic checks

I independently recomputed the fixture's N slack one, F slacks
(1,1,1,3,1,1,1), and J slacks (2,2,1,2,3,4,1). Explicit first-coalition
integration and all complete pure-date response classes give

    U=B=(13/9,2,2/3,4/3).

Player 0's date-zero/later-finite/Never values are (13/9,1,8/9); player
3's are (−2/9,4/3,4/3). These were checked with exact rational arithmetic.
The solved table rejecting every deletion LP has the stated one-row dual
obstructions. The paired singleton signs eliminate every escort edge,
consistent with arbitrary-period balanced-cycle necessity. These finite
checks corroborate the algebra; the pathwise proof supplies universality.

## Source checks

The complete updated `exports/README.md` and both full packet proofs were
read. The bounded declaration checks for this review included:

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`);
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`);
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`),
  under its stated imports and without a strategic witness premise;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`);
- `QuittingBlockJoinAntitone`, `QuittingBlockDispensable`, and its existence
  consumer (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`);
- `BalancedSingletonCycleCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).

A targeted search of these interfaces found no weighted min-clock compiler
with this raw source condition. This is an implementation-overlap check,
not a global priority claim. The packet's separate source review supplies
its original-paper hypothesis comparisons; no broader literature claim is
added here. No draft, export, or Lean file was edited for this review.
