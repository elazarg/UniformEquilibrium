# Bidirectional deadline deviations: independent response review

## Verdict and required narrow repair

PASS for the main complete all-evaluation domination theorem, the
max(a,b) coefficient, Never relaxation, specified-target extension,
stationary-security floor strengthening, and the explicit strict class
and reward neighborhood.

The rational-enumeration sentence in Section 4 requires one correction.
Scanning only a finite law's displayed support dates, one date after its
last atom, and Never does not always give the complete response cap.
Use consecutive calendars and scan every date 0,...,N plus Never, or
include a representative of every nonempty calendar gap. This changes no
raw inequality or main strategic theorem, and repairs the algorithmic
claim completely.

The reviewed manuscript is
[`BIDIRECTIONAL_DEADLINE_DEVIATION_DOMINATION.md`](../gpt/BIDIRECTIONAL_DEADLINE_DEVIATION_DOMINATION.md).
The existing comparison is
[`CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`](../exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md).
These conclusions are ordinary mathematics, not new Lean theorems.

## Complete pathwise comparison and independent agency

The cap C_t changes only clocks strictly later than t. Atom withdrawal
R_t changes only clocks equal to t. Both depend only on the player's
old clock and the proposed outsider deadline. At deadline Never both
operations are the identity, as required.

If the child first quits before t, all gains vanish. If t is strictly
before child absorption, R_t has no effect and the original capped-clock
N/F decomposition applies, including signed rewards. At equality,
nonmembers join under C_t and members leave under R_t. A singleton
withdrawer's possible later opponent coalition or Never gives the floor
ell_i=min(0,passive child rewards). Because this floor is nonpositive,
every later evaluated payoff is bounded below by f(t)ell_i.
The J row therefore proves the desired inequality for every monotone f.

The pointwise necessity witnesses recover N, F and J at terminal
evaluation with the same fixed weights. The singleton witness chooses a
later coalition or Never attaining the floor. This is exactness for the
specified maps, not a characterization of all quiet extensions or UE.

For c=max(a,b), use advancing probability a/c on the event T_i>t and
withdrawing probability b/c on T_i=t. These events are disjoint. After
conditioning on the old tuple, c times this single response's expected
gain equals aG_i^C+bG_i^R. It is not necessary that (a+b)/c<=1: the
two randomization probabilities apply on different events. This proves
the maximum coefficient without cancellation of nonnegative regrets.

For a randomized outsider deadline, use an independent private replica.
The resulting child response stays independent of every original child
opponent. Summands are separate unilateral experiments, not one jointly
correlated profile. Bounding each constructed gain by the full response
cap and then taking the outsider supremum proves the complete behavioral
claim. There is no expectation/supremum interchange.

## Security-floor enhancement

The finite LP maximizes

    v <= s_i,
    v <= (1-h)r_i(B)+h r_i(B union {i}),   0<=h<=1,

over nonempty opponent coalitions B. A finite reward bound makes it a
compact feasible optimization without changing its value V_i.
For h>0, the geometric own clock guarantees v against every independent
opponent plan. Conditional on a deterministic first opponent date, every
earlier own stop pays at least v, and the conditional mixture at that
opponent date has mean at least v. On opponent Never the own stop occurs
almost surely. Averaging preserves the guarantee.

If an optimum uses h=0, positive hazards tending to zero have guaranteed
values tending to V_i by the finite minimum of the affine expressions.
This correctly treats positive nonattained security values without
assigning them to Never. The alternative floor ell_i is actually guaranteed
by Never, so gamma_i=max(ell_i,V_i) is arbitrarily closely guaranteed.

Restarting only when T_i=t preserves disjointness from advancing. A member
of a nonsingleton first coalition still leaves its surviving members at t.
For a singleton, fresh own randomization after t gives the chosen guarantee
against the conditional future opponents. Those conditional laws remain
independent; equivalently, the guarantee already holds for each fixed
opponent clock tuple. The eta error is at most eta times the sum of
withdrawal weights. Letting eta tend to zero after the complete-cap bound
gives the exact terminal numerical inequality.

The all-evaluation floor gamma_i^-=min(gamma_i,0) is also correct. A
nonpositive LP optimum attained at h=0 is no better than ell_i. A positive
optimum attained only at h=0 has all passive rewards positive, so Never
guarantees zero. Otherwise an optimal positive hazard guarantees the needed
nonpositive level. For such a level v, multiplying a branch payoff or a
same-date mixture by a later, smaller nonnegative evaluation weight keeps
it above f(t)v. This proves the evaluated restart bound; no positive
terminal floor is silently used at a finite horizon.

For a strict improvement example, let s_i=0 and let the only opponent's
solo and joint rewards to i be -1 and 1. Then ell_i=-1, while h=1/2
gives V_i=0, improving the terminal and all-evaluation floor to zero.
For a nonattainment boundary, s_i=1 with passive reward 1 and joint reward
0 gives V_i=1 only at h=0; positive hazards guarantee 1-h, and Never pays
zero on opponent Never. This verifies the need for the limiting argument.

## Fixed targets, Never, and the finite-calendar correction

Late cap responses give s_h p_infinity<=d_h by bounded convergence,
so the omitted N row has precisely the stated terminal correction.
Its absorption into regret requires a strictly positive singleton.
No evaluation-by-evaluation claim is made for that relaxation.

The specified child UE target is retained: use the target-preserving
entrance declaration below, quiet lift the actual terminal approximants,
and choose a convergent subsequence only for the bounded outside payoff
coordinates. The full terminal vectors then converge to one fixed v
extending v_S while full regrets vanish. The named terminal-target
consumer provides UE at v. This is not merely existential payoff selection.

Here is the exact sparse-calendar falsifier to Section 4's scan.
Child a prescribes Never; b quits at date 0 or 2 equally. Let

    r_a({a})=1,   r_a({b})=0,   r_a({a,b})=-1,

and make b's payoffs zero. The complete pure reply values for a are

| Date | 0 | 1 | 2 | 3 | Never |
|---|---:|---:|---:|---:|---:|
| Payoff | 0 | 1/2 | -1/2 | 0 | 0 |

The claimed support/post-final/Never scan reports zero and misses date 1.
The repair is to enumerate laws on consecutive calendars
{0,...,N-1,Never} and test all dates 0,...,N and Never, including
zero-mass dates. Every later finite date is outcome-equivalent to N.
For any fixed calendar the finite pure-response maximum is continuous in
the product probabilities. Full-cap finite-law approximation and rational
density therefore prove termination with the corrected scan. This producer
is target-free unless target approximation data are additionally supplied.

## Exact fixture, neighborhood, and claimed increment

Independent exact arithmetic reproduces every stated N,F,J slack, the
factor three, the centered singleton matrix, the half-hazard residual
vector, every nonempty pure-coalition improvement, and all complete reply
values at q=(1/2,1/3,1,0), followed by Never:

    U=B=(2/3,-9/16,-11/48,23/16).

The sure owner's Never and strictly late values differ, as stated:
-17/24 versus -35/48. This distinction is retained in the scan.

The radius-1/512 coefficient estimates preserve the certificate and the
old-test obstruction rows. Children omitting the positive pivot fail the
old N row because all remaining own singletons stay negative. The two
remaining F blockers and five full-child J blockers are exact algebraic
obstructions, not numerical LP failures. The inverse perturbation estimate
preserves strict positivity and positive determinant, hence R0 and degree
+1. Pairwise distinct half-hazard residuals exclude every nondiscrete
response-invariant partition, throughout the stated neighborhood.

The 33-free-child-recipient completion argument is valid: singleton F
and N rows remain fixed; choose the four outside passive collision
coordinates above their F lower bounds, then choose the seven outside
joining coordinates below their separate J upper bounds. There are no
conflicting coordinates. The analogous 33-versus-11 completion mechanism
already exists for the old capped-clock class; its reuse is not itself
a new freedom-count principle. The new content is the distinct raw
withdrawal cone, its maximum regret coefficient, security floors, and
the strict separation from every old proper-child test.

## Comparison and proposed consolidated package

Future withdrawal and deadline-only withdrawal are incomparable raw cones
for a fixed child. The former adds a withdrawal term to F and J, while
the latter adds it only to J and exploits disjoint private-clock events.
Exact separating tables and proofs are recorded in
[`the independent patient-reset review`](FUTURE_WITHDRAWAL_AND_PATIENT_RESET_QUIET_EXTENSION__BY_CODEX_RESPONSE_REVIEW.md).
The one-child separator remains outside the bidirectional cone even with
its security enhancement, because that enhancement does not change F.

A single self-contained package should retain these as separate criteria,
share the clock model, old capped-clock specialization, Never lemma,
target-preserving entrance/exit and corrected finite-law producer, and
include the fully justified stationary-security improvement. It should not
claim either criterion subsumes the other, nor remove unrelated existing
inverse-row sharpness mathematics.

## Exact source correspondence

The following declaration statements and their actual imports were inspected;
all named repository paths are Git-tracked. No Lean source was changed and
no new theorem is described as already Lean-checked.

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`
  identify literal coordinate replacement, its actual payoff expectation,
  and equality of full behavioral and pure-time caps.
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`
  is the signed all-Never mass inequality used before division by a
  strictly positive own singleton.
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  gives actual terminal ε-Nash profiles within ε of one specified child
  UE target. In the same file,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  consumes vanishing terminal errors and convergence to one fixed full
  target. This is a target-preserving entrance and exit, not merely an
  existential all-errors equivalence.
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  in
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`
  preserve actual payoff and unrestricted-regret control on finite menus,
  without sign, normality, or early-absorption hypotheses.
- `quittingGame_exists_uniformEquilibriumPayoff_onePlayer` in
  `UniformEquilibrium/Quitting/Classification/OnePlayer/Existence.lean`
  covers an arbitrary Unique player type.
  `quittingGame_exists_uniformEquilibriumPayoff_twoPlayer` in
  `UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`
  covers Bool.
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`
  covers Fin 3. Relabeling histories, rewards, independent laws, and
  unilateral replacements supplies every nonempty proper child of Fin4.

## Strongest survivor and next check

The strongest survivor is the raw all-evaluation domination theorem with
maximum coefficients, the terminal and nonpositive evaluated security-floor
enhancements, the fixed-target and signed Fin4 consumers, and the strict
robust class. The rational enumeration becomes valid with the precise
consecutive-calendar repair above. A self-contained consolidated version
should receive a second independent review before export.

