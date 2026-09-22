# Capped-clock packet: remaining formalization obligations

The source is
`math/exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
The packet is not fully formalized. The integrated interfaces and source
constructors are described in [the toolkit](../../docs/TOOLKIT.md).

## Checked scope

The deterministic and expected-clock inequalities allow general nonnegative
nonincreasing evaluations. So does the actual full behavioral-cap comparison
at reconstructed quiet parent profiles, by
`outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockEvaluatedFullBehavioralCap.lean`).
Its right side contains survivor debts in the parent game.
`quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile`
(`UniformEquilibrium/Quitting/Classification/PlayerDeletionEvaluatedPayoff.lean`)
preserves survivor debts under the existing Never lift for arbitrary clock
evaluations and arbitrary deleted-player predicates. The final all-evaluation
quiet-extension adapter still needs to combine these results for every actual
child behavioral profile. The terminal adapter already supplies the checked
fixed-target quiet-extension and four-player existence theorems.

The raw reward criterion has exact real and rational LP alternatives. Its
zero-weight case is equivalent to exact singleton block dispensability.
The paired-family constructor preserves arbitrary nonsingleton coordinates
of the three surviving players and supplies a uniform-equilibrium payoff.
Every member fails exact singleton block deletion for every player.
The family and its deletion-3 child admit no balanced singleton cycle of any
period, by `not_nonempty_balancedSingletonCycleCertificate` and
`not_nonempty_balancedSingletonCycleCertificate_deleteThree`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`).

## Work still needed

1. Combine evaluated payoff and full-cap preservation under the actual Never
   lift with the checked evaluated parent-debt comparison, using equality of
   the actual profile's complete stopping laws and those of its reconstruction.
2. Prove the additive-error theorem when every Never, future, and joining row
   may violate its inequality by the same nonnegative tolerance. The current
   slack certificate relaxes only the Never row.
3. Package the expectation-level necessity direction through deterministic
   clock laws. Deterministic necessity and expectation-level sufficiency
   already have proofs.
4. Construct the terminating rational finite-law enumeration: rational
   approximation, exact cap computation on consecutive calendars, and the
   termination argument. Rational LP certificates and real finite-menu
   approximation are not this producer.
5. Seal the additional example conclusions: slack values, terminal Nash laws,
   payoffs and caps, absence of pure terminal Nash equilibria, robustness under
   reward perturbations, and the comparison with the capped-joint hypothesis.
6. Formalize the solved table failing every deletion LP, the missing-Never
   example with zero child singleton, and the sparse-calendar missed response
   with its consecutive-menu repair.
7. Formalize the auxiliary strict inverse-row sharpness theorem: the positive
   inverse classification, forced vertex visits and block survival, the
   continuation-floor equivalence, and the quantitative response-debt bound.
   Its hypotheses concern an exact balanced singleton schedule, not all child
   equilibria or approximate ties.

These are known results supplied by the packet. This record does not assert
that the weighted criterion covers every four-player game, that its weights
are optimal, or that a finite-calendar implementation is complete without
testing the intervening gaps.
