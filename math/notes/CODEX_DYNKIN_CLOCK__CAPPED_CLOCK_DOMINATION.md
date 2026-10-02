# Capped-clock domination: semantics and proof judgments

Identity: CODEX_DYNKIN_CLOCK.

Mathematical status: the packet's capped-clock equivalence and unrestricted
regret transfer are valid ordinary mathematics. A sparse-calendar cap claim
requires the explicit consecutive-menu qualification given in the
[independent review](../feedback/CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_DYNKIN_CLOCK.md).
This record makes no Lean-checked claim for the new theorem.

## Self-contained question and answer

For a finite zero-live-payoff quitting game, can an outside player's complete
behavioral gain from replacing Never be charged to a nonnegative weighted
sum of complete child response debts, while retaining every child law?
Information is the observed history; before absorption this is the unique
all-Continue history of each length. Private randomization is independent
across players. Rewards may be signed and stopping laws may have infinite
support and positive Never mass.

For a nonempty child set S, outsider k, and λ_i ≥ 0, the exact criterion for
the specified clock-cap compiler is the packet's Never, future-coalition and
join-coalition inequalities. It is equivalent to the pathwise inequality for
all deterministic tuples and deadlines. Integration gives legal separate
unilateral responses with stopping times min(T_i,Z), Z independent of all
child clocks, and hence d_k^f ≤ Σ_i λ_i d_i^f for every nonincreasing normalized
absorption weight f. Several quiet outsiders are handled separately.

For terminal payoff only, dropping the Never inequality adds precisely
max(s_k − Σ_i λ_i s_i,0) times joint Never mass. A child j with s_j > 0 charges
that mass to d_j/s_j. Consequently the fourteen-row positive-singleton
criterion also preserves every fixed child uniform payoff target: retain a
family approaching that target and select a convergent subsequence only in
the outside coordinates. This conclusion does not require suffix Nash play.

The finite-law search is exact when prescribed menus are {0,...,H−1,Never}
and response menus are {0,...,H,Never}. For a sparse menu {0,2,Never}, an
opponent mixing equally between 0 and 2 and responder payoffs solo 1, opponent
solo 0, tie −1 give reply values 0, 1/2, −1/2, 0, 0 at dates 0,1,2,3,Never.
The missing gap date defeats a cap check using only supported dates, one
final extra date and Never.

## Exact source dependencies inspected

The bounded navigation routes are the finite-menu approximation, actual
finite timing menu, counterfactual stopping-law and terminal uniform-payoff
entries in `docs/TOOLKIT.md`, together with the semantic endpoint in
`math/SOURCES.md`. The declaration statements and relevant bodies inspected
are:

- `quittingUniformEquilibriumPayoffConjecture`,
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`: the open finite-player
  target, distinct from general stochastic-game existence.
- `quittingBehaviorStoppingLaw` and
  `stoppingLawSurvival_quittingBehaviorStoppingLaw`,
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`: live-history
  hazards, complete laws and inclusive survival.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`,
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`: unrestricted
  behavioral replacement payoff is its pure-time/Never mixture.
- `quittingFirstStoppingOutcome`, `quittingIndependentTerminalOutcomeLaw`,
  `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`,
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`: labelled
  first outcomes, product laws and complete unilateral cap semantics.
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` and
  `neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt`,
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`: the
  existing joint-Never charge. The packet's late-cap proof is an independent
  proof of this dependency, not new mathematical scope.
- `quittingGame_isUniformεEquilibrium_of_terminalNash`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`:
  each terminal ε-Nash profile is uniform ε′-Nash for every ε′ > ε, including
  signed singleton rewards.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`, and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  fixed-target and target-free selection are separate interfaces.
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`,
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`:
  actual finite laws approximate complete regret and payoff simultaneously;
  the latter equivalence retains a specified target before every accuracy.
- `QuittingFiniteDeadlineTimingAction` and
  `quittingFiniteDeadlineTimingProfile`,
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`: the
  menu is all dates below H plus Never, realized by private hazards.
- `quittingFiniteDeadlineReplyCap` and
  `quittingFiniteDeadlineReplyCap_eq_sup_pureTimeTerminalValue`,
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`: this cap
  is only the displayed finite-menu cap; the extra late response is required
  for the unrestricted terminal cap.
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`,
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  the unconditional three-player child theorem is a dependency, not a result
  of the capped-clock calculation.

The source check is static and bounded, with no new theorem compilation.
No external-paper claim is used as a premise of the reviewed proofs.

## Boundary not established

Failure of the finite raw inequalities does not imply failure of cap
domination through other child responses, failure of another unchanged-child
construction, or failure of parent equilibrium existence. Necessity for any
of those broader statements is not proved. The exactness concerns the fixed
clock-cap compiler and its fixed nonnegative weights only.
