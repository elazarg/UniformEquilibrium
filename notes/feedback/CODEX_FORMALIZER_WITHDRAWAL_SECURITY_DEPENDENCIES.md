# Deadline withdrawal stationary security: exact remaining dependencies

Scope: Section 5 of `math/exports/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md`.
The mathematical argument supplies the obligations below; this audit found no
mathematical counterexample or missing strategic premise. The remaining gap is
formalization of evaluated payoffs and composition with the existing
deadline mixed-response chain. LP attainment must not be reported as attainment
of the terminal security guarantee by a stopping law.

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
guarantee is supplied by the separate payoff module below. The modules are
reachable through the production umbrella and passed a silent full build and
the project trust and import-graph checks.

## Terminal payoff bridge and remaining evaluated lemma

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
formula remains to be formalized:

    sum_(m<n) h(1-h)^m f(t+1+m) s_i
      + (1-h)^n f(L) [(1-h) r_i(B) + h r_i(B union {i})].

If v ≤ 0, it is at least f(t)v. On opponent Never the analogous infinite
sum obeys the same estimate. Pair the same-date Continue/Quit branches before
using the floor: their individual rewards need not each exceed v. Bounded
payoffs justify the series and expectation interchanges. No evaluation
normalization beyond nonnegativity and antitonicity is needed; f(0) bounds
all finite weights, and actual Never payoff is zero.

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

## Composition with the existing deadline chain

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

`pmfPi_bind_privateClockKernel`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalProductLaw.lean`)
is the reusable product-marginal theorem. The downstream existing full-debt
theorem is `deadlineWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalFullBehavioralDebt.lean`).
Its literal law and gain identities must be replaced by the restart versions
before applying the behavioral cap; no cap bound or desired debt inequality
should become a supplied-data premise.

For terminal gamma, each positive error yields an actual response and an
error at most error times the sum of withdrawal weights. Bound each actual
response by its full cap first, then let error decrease to zero. For the
all-evaluation min(gamma,0) floor, the selected law attains the necessary
nonpositive floor, so no terminal-limit argument is needed. Both retain the
original Never and future rows and coefficient max(a,b).

Concrete next task: prove the nonpositive evaluated lower bound for the actual
geometric law, retaining the grouping of same-date joint/passive branches,
then generalize the atom-restart mixture and full behavioral debt consumer.
No security-enhanced D certificate, full behavioral debt bound, or fixed-target
uniform-equilibrium consumer has been derived from these security modules.
