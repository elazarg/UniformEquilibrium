# Deadline withdrawal security: checked chain and remaining producers

Scope: Section 5 of `math/exports/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`.
The security LP, actual restart law, all-evaluation nonpositive floor, mixed
atom-restart response, and full behavioral-debt comparison are checked. The
remaining Fin4 dependency is a raw reward-table certificate for each selected
outsider and a fixed child uniform-equilibrium target. A positive terminal
security value requires a separate error-to-zero cap argument: the checked
all-evaluation theorem uses only `min(gamma,0)`. LP attainment must not be
reported as attainment of the terminal security guarantee by a stopping law.

## Finite optimization and actual clocks

`exists_deadlineWithdrawalSecurity_optimizer`,
`deadlineWithdrawalSecurityValue_spec`, and
`exists_deadlineWithdrawalSecurity_positive_approximation`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`)
construct the exact two-variable LP optimum from the literal reward table and
positive-hazard feasible values arbitrarily close to it. The optimizer can be
zero. The indexing type includes the singleton row even when there are no
opponent coalitions. No reward-bound premise or supplied strategy is needed.

`deadlineWithdrawalSecurityRestartLaw` and
`exists_deadlineWithdrawalSecurityRestartLaw`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityRestart.lean`)
use the existing `geometricFiniteStoppingLaw`
(`MathUE/ProbabilityMassFunction/GeometricPivotStoppingLaw.lean`) beginning at
deadline plus one. Their geometric masses, zero Never mass, and zero mass at
or before the deadline are explicit. The atom-only kernel reads the owner's
original clock and its private outsider replica, never opponent clocks.
These declarations construct actual probability laws. Their terminal security
guarantee is supplied by the separate payoff module below.

## Terminal and evaluated payoff bridges

Fix a finite child player set, its literal parent reward table, a child i,
a finite deadline t, and deterministic opponent clocks T_j strictly later
than t for every j other than i. Let 0 < h ≤ 1 and let v satisfy the LP rows:
v ≤ s_i and v ≤ (1-h) r_i(B) + h r_i(B union {i}) for every nonempty
opponent coalition B. Independently replace i's clock by the geometric law
starting at t+1. Keep the outside player at Never.

The terminal conclusion is now proved in Lean: the expectation over this actual
replacement law of i's actual pure-clock payoff is at least v.
`deadlineWithdrawalSecurityRestartLaw_terminal_floor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityPayoff.lean`)
selects the first date and coalition from every deterministic future opponent
tuple, with the owner's unused coordinate normalized to Never. Its finite-date
case is `deadlineWithdrawalSecurityRestartLaw_finiteOpponent_floor` in the
same file. The actual opponent-Never equality is
`deadlineWithdrawalSecurityRestartLaw_terminalPayoff_opponentsNever`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityRestart.lean`).

If the first opponent date is L = t+1+n with coalition B, the checked
`deadlineWithdrawalSecurity_geometric_threeBranch_expect` and
`deadlineWithdrawalSecurity_terminalPayoff_threeBranch`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityPayoff.lean`)
identify its actual payoff with

    [1-(1-h)^n] s_i
      + (1-h)^n [(1-h) r_i(B) + h r_i(B union {i})].

Both coefficients are nonnegative and sum to one. On opponent Never, the
payoff equals s_i because the geometric law has total finite mass one.
The argument includes h=1 and n=0; no division by 1-h is valid at h=1.

For an evaluation f nonnegative and antitone, the corresponding finite-L
formula is formalized in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityEvaluated.lean`:

    sum_(m<n) h(1-h)^m f(t+1+m) s_i
      + (1-h)^n f(L) [(1-h) r_i(B) + h r_i(B union {i})].

If v ≤ 0, it is at least f(t)v. On opponent Never the analogous infinite
sum obeys the same estimate. The same-date Continue/Quit branches are paired
before using the floor: their individual rewards need not each exceed v.
`exists_deadlineWithdrawalSecurityEvaluatedPlan`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityEvaluatedPlan.lean`)
selects one law independently of the evaluation and opponent tuple.

These are pointwise-in-opponent-tuples estimates averaged over the fresh own
clock. They do not require conditioning on a positive-probability survival
event, and avoid introducing unnecessary assumptions on conditional laws.

## Exact nonpositive-floor selection

Let l be the minimum of zero and all passive opponent rewards, let V be the
LP value, and let gamma=max(l,V). The all-evaluation floor is min(gamma,0).
Its witness uses the following explicit case split, now checked as
`deadlineWithdrawalSecurity_nonpositive_witness`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`):

- If gamma=l, Never guarantees it.
- If an optimal h is positive, its LP guarantee supplies min(gamma,0)
  whenever V dominates l.
- If an optimal h=0 and V≤0, the zero-hazard rows imply V≤l, returning to
  the Never branch.
- If an optimal h=0 and V>0, all passive rewards are positive and Never
  guarantees zero. This includes the empty opponent-coalition family.

For the terminal floor gamma, use Never when l dominates V and a positive
hazard with feasible value at least V-error otherwise. The hazard may depend
on the requested error, but never on hidden opponent clocks.

## Mixed restart and full behavioral debt

The existing `DeadlineWithdrawalRewardCertificate`,
`deadlineWithdrawalGainFloor`, and `deadlineMixedPrivateClockLaw` hard-code
the passive floor and withdrawal to Never. Merely substituting gamma into a
certificate cannot reuse their proof unchanged.

On source clocks later than the finite outsider deadline, keep the existing
advance coin with probability a/max(a,b). On the exact deadline atom use a
fresh restart with probability b/max(a,b). Otherwise keep the source clock.
Treat max(a,b)=0 separately. A Never outsider deadline is the identity.
This preserves the one-site gain identity and maximum coefficient because
the two source-clock events remain disjoint. The withdrawal gain now includes
expectation over the restart law, so deterministic pathwise domination is
replaced by domination averaged over that fresh law.

`deadlineSecurityMixedPrivateClockLaw_gain_identity`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedLaw.lean`)
implements the exact one-site gain. The actual private replacement and product
marginal are in `DeadlineWithdrawalSecurityMixedBehavioral.lean` and
`DeadlineWithdrawalSecurityMixedMarginal.lean`. The improved literal N/F/J
rows are `DeadlineSecurityRewardCertificate`
(`DeadlineWithdrawalSecurityMixedRaw.lean`); their pointwise and averaged
domination are in `DeadlineWithdrawalSecurityMixedPointwise.lean`,
`DeadlineWithdrawalSecurityMixedDomination.lean`, and
`DeadlineWithdrawalSecurityMixedExpectation.lean`. These file names are
relative to `UniformEquilibrium/Quitting/Classification/QuietExtension/`.

`deadlineSecurity_quietLift_outsideBehaviorDebt_le_weighted_childDebt` and
`deadlineSecurity_quietLift_totalBehaviorDebt_le_weighted_childDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedFullBehavioralDebt.lean`)
apply the full behavioral deviation cap to the actual quiet lift for every
nonnegative antitone evaluation. Their coefficients are `max(a_i,b_i)` and
`1+max(a_i,b_i)`. No selected security law, gain identity, expectation bound,
or desired debt inequality is a hypothesis of these results.

For terminal gamma, each positive error yields an actual response and an
error at most error times the sum of withdrawal weights. Bound each actual
response by its full cap first, then let error decrease to zero. For the
all-evaluation min(gamma,0) floor, the selected law attains the necessary
nonpositive floor, so no terminal-limit argument is needed. Both retain the
original Never and future rows and coefficient max(a,b).

The fixed-target consumer already exists for the ordinary deadline certificate
(`exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineWithdrawalFamily` in
`DeadlineWithdrawalFixedTarget.lean`). Applying the security-enhanced rows to
Fin4 still requires literal raw-table certificates and child UE targets, or
an explicitly checked adapter to that consumer. The security chain itself
does not produce those inputs. For positive terminal `gamma`, the response
hazard may depend on an error; proving a cap bound before sending that error
to zero is a separate, stronger bridge.
