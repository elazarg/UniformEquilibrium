# Independent review of bidirectional deadline domination

## Verdict and exact scope

PASS for the main all-evaluation complete-deviation inequality, its maximum
coefficient, terminal Never relaxation, fixed-target extension, security-LP
refinement, exact example, and strict open raw class. One statement in the
original rational enumeration is false: supported dates alone do not suffice
for the pure-reply scan. The explicit consecutive-calendar repair below is
correct and sufficient. Thus the mathematical result passes with that narrow
algorithmic repair; the unrepaired original enumeration should not be exported.

I read all of `gpt/BIDIRECTIONAL_DEADLINE_DEVIATION_DOMINATION.md`, SHA-256
`f341303aa7c25e9078e1b1327d638ea235ae6665cbd8456cf6d7cf41fccae37b`.
This review is ordinary mathematics, not a Lean check. The claim checked is a
raw reward-table producer of full behavioral regret control for every actual
independent child profile, and consequently of signed Fin4 UE via an actual
low-cardinality child equilibrium. No supplied good continuation or root is
accepted as a substitute for produced data.

## Pathwise proof and the maximum coefficient

At a finite outsider deadline t, advancing changes only T_i>t; withdrawing
the atom changes only T_i=t. Both use only that child's sampled private clock
and the independently replicated outsider deadline. They do not observe any
opponent's hidden clock. At t=Never both are the identity.

The deterministic proof exhausts the possibilities. If the child absorbs
before t, all gains vanish. If the outsider moves strictly before the first
child coalition, withdrawal does nothing and the evaluated residual is

    [f(t)−f(τ)](s_k−Σ a_i s_i)
      + f(τ)[s_k−r_k(A)−Σ a_i(s_i−r_i(A))],

which is nonpositive by N and F. This calculation, rather than separate
unsigned estimates, handles arbitrary signed rewards. Joint child Never is
exactly the N row.

At a tied first date, advancing joins nonmembers and withdrawal removes
members. A nonsingleton withdrawal leaves the other members at the same
date. A singleton withdrawal reveals either a later opponent coalition or
Never. Since the raw floor is nonpositive and bounds every such reward,
its evaluated payoff is at least f(t) times that floor. The J row therefore
gives the pathwise inequality for every nonincreasing evaluation. Hidden
later coalitions and the actual zero Never payoff are both retained.

Necessity is correctly limited to this particular fixed-weight pathwise
compiler. Joint Never gives N, first A at date 1 with deadline 0 gives F,
and first A at date 0 gives J. For a singleton J witness one chooses the
later coalition or Never attaining its finite floor.

For c=max(a_i,b_i)>0, use probability a_i/c only on T_i>t and probability
b_i/c only on T_i=t. These disjoint private-clock events allow both
probabilities to be at most one without requiring their sum to be at most
one. Conditional on the original tuple, c times the resulting single
replacement gain equals a_i times the advance gain plus b_i times the
withdrawal gain. The c=0 case is the identity.

A common outsider replica is only a coupling of separate unilateral
experiments; no correlated prescribed profile is constructed. Each child
replacement is independent of its unchanged opponents. Integrating the
pathwise comparison bounds each such replacement by the corresponding full
child cap; the outsider supremum is taken last. This proves the exact
max-coefficient bound over all complete behavioral responses, not merely
finite deadlines or stationary deviations.

## Stationary-security floors

The two-variable LP correctly computes a sufficient security value. Adding
the reward box −M≤v≤M does not alter the optimum, because v=−M is feasible
and all relevant rewards lie in that box. Hence an optimum exists.

For h>0, condition on the first opponent date and its coalition. Any earlier
own quit pays s_i≥v; at that opponent date the conditional mean is precisely
(1−h)r_i(B)+h r_i(B∪{i})≥v. On opponent Never the geometric own clock quits
almost surely. Thus the same private stationary strategy guarantees v
against arbitrary opponent laws. At an optimum h=0, small positive hazards
give guaranteed values converging to the LP optimum by continuity of the
finite list of affine constraints. This does not assign the limiting
positive value to Never.

The maximum with the original Never floor is therefore arbitrarily closely
guaranteed. Restart that plan at t+1 only on the atom-withdrawal event. A
nonsingleton first coalition still absorbs at t, while a singleton restart
faces only the conditional future opponents, against which the security
bound is universal. Advancing and restarting still act on disjoint private
events, so the maximum coefficient survives. Let the security error tend
to zero AFTER bounding each actual replacement gain by its full cap. This
justifies an exact numerical inequality without attainment of a cap or of
the optimal security value.

The all-evaluation refinement must use min(γ_i,0), as stated. Its attained
guarantee follows from the cases in the manuscript: an h=0 nonpositive
optimum is no better than the Never floor; an h=0 positive optimum gives
nonnegative passive rewards, so Never supplies zero; otherwise an optimal
positive hazard works. For a nonpositive target bound, multiplying any
later conditional payoff by the smaller future weight cannot push it below
the current weight times that bound. This proves the evaluated restart
claim. The untruncated positive γ_i is only asserted for terminal evaluation.

## Never correction and preservation of a specified target

Omitting N leaves only the stated positive residual on joint child Never.
Late deterministic capping converges pointwise to a singleton payoff gain
s_h p_Never, giving s_h p_Never≤d_h by bounded convergence. Division is
used only when s_h>0. There is no unwarranted finite-horizon version of this
terminal relaxation.

For a specified child UE target, pass each fixed profile and each fixed
deviation to the terminal limit, then quantify over deviations. The lifted
profiles preserve child payoffs and caps exactly. A subsequence of the
bounded outsider payoff vectors gives one full target extending the child
target, chosen before the final requested error.

The tracked declaration
`quittingGame_isUniformεEquilibrium_of_terminalNash` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
keeps the SAME prescribed profile and supplies uniform regret at every
strictly larger error. Its statement and proof were read directly. Thus the
quiet outsiders remain Never, including under the terminal-only relaxation
or security refinement. Bounded convergence for the prescribed payoff then
gives target delivery for all sufficiently large horizons. This is stronger
and more precise than invoking a payoff-only existence consumer and silently
assuming that it preserves the quiet strategies.

## Required finite-scan repair

Let one player have solo reward 1, passive reward 0 against its opponent,
and joint reward −1. The opponent quits at dates 0 and 2 with probabilities
one half each. The player's pure reply values at dates 0,1,2,3,Never are

    0, 1/2, −1/2, 0, 0.

The omitted interior gap date 1 strictly beats every supported date, the
post-final date, and Never. This directly refutes the original Section 4
scan; the issue is not an unattained supremum.

Repair: enumerate rational product laws on the consecutive calendar
{0,…,N−1,Never}, including zero-probability dates, and scan every finite
reply 0,…,N plus Never. Every finite date beyond N−1 is terminally equivalent
to N: either some opponent already absorbed by N−1, or all opponents are
Never and the deviator quits alone. Never stays a separate action. Every
random law is a mixture of these pure terminal responses, so the resulting
finite maximum is exactly the complete cap. Alternatively, include one
representative from every nonempty gap in a sparse calendar.

The tracked `exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`
provides actual payoff approximation and full exploitability control without
singleton-sign assumptions. On each finite calendar the finitely many
payoffs and cap maximum are continuous in the product law. Rational density
and a strict acceptance tolerance therefore prove termination of the
corrected enumeration. This is target-free accuracy search, not a complexity
bound or computation of an arbitrary named real target.

## Exact fixtures and genuine scope

I independently recomputed the literal translated example from its raw
fifteen reward vectors using exact rational arithmetic. Its own singletons,
N slack 1/16, both seven-entry F/J lists, stated immediate/Never/late reply
triples, and actual equilibrium payoff all match. The sure owner's late
and Never replies differ and were checked separately. The half-hazard
residual vector and all fifteen stated strict membership-toggle gains also
match exactly.

The old-test obstructions are algebraic: a child omitting the positive pivot
has an impossible Never inequality with strictly negative child singletons;
two pivot-containing children have a nonpositive future row against a
positive outsider gap; the others have a positive outsider join gain at a
full-child coalition, where every old child coefficient is structurally
zero. These facts persist under the stated radius 1/512 perturbation.

The floor Lipschitz bounds give the stated N/F/J perturbation budgets. The
Neumann estimate preserves strictly positive inverse and determinant sign,
hence R₀ and degree +1. Pairwise distinct residuals at the common half point
reject every nondiscrete response partition, robustly. The escort signs,
negative triple inverse entry, attainable small-hazard singleton surplus,
and strict pure toggles establish the limited additional comparisons claimed.
They do not exclude all other sufficient classes or all stationary verifiers.

The 33-versus-11 collision-coordinate completion is consistent: singleton
rows stay fixed; choose four outsider passive collision coordinates above
their F lower bounds, then seven distinct outsider joining coordinates
below their J upper bounds. No coordinate receives conflicting demands.

The bidirectional and patient cones are NOT nested. The two explicit small
separators in my patient-reset review below were independently checked.
The advance-only cone is contained in each by zero withdrawal weights, but
their union should not be presented as one of them alone.

## Named source checks and surviving result

I read the exact tracked one-, two-, and three-player existence statements:
`quittingGame_exists_uniformEquilibriumPayoff_onePlayer` in
`UniformEquilibrium/Quitting/Classification/OnePlayer/Existence.lean`,
`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer` in
`UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`, and
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`.
Their player types are respectively arbitrary Unique, Bool, and Fin 3;
finite relabeling supplies the actual child. The three-player declaration
alone should not be cited as an at-most-three statement.

I also read the tracked update, expectation, and pure-time cap statements
`quittingBehaviorStoppingLaws_update`,
`quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
`quittingBehaviorDeviationPayoffCap_eq_pureTime` in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`, and the
target-sequence consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
All referenced paths were checked with git ls-files.

The strongest surviving result is the manuscript's universal all-evaluation
compiler and security refinements, with actual fixed-target and signed Fin4
consumers. The corrected exhaustive finite scan is the only required repair.
No extra strategic hypothesis or unresolved main proof objection remains.
