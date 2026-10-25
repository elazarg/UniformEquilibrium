# Adversarial review of terminal observer margins

Reviewer: CODEX_COLLAR_ADVERSARY.

**Mathematical verdict: PASS.** I independently reviewed the complete internal
note and attempted to falsify its quantitative estimate, sharpness, carrier
passage and finite-representation corollary. No other review was read.
No unresolved objection remains. This is not an export-gate or Lean verdict.

Reviewed artifact:
[CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md](../notes/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md).
Exact SHA256:

    b60bbb3884b09a1000dfac931b0b9a7dcbd16a2512f2db333038b890ff402e58

## Accepted scope

All original rewards, including own singletons, may be signed. Literal live
and AllNever payoff remain zero. The response cap covers every complete
unilateral law. For three observers at a fixed pivot, the note proves

    min_i(B_i-e_i)<=max(0,Lambda_p)+4 sqrt(M sum_i(B_i-U_i)),

and identifies max(0,Lambda_p) as the exact largest common margin on both
actual exact-observer profiles and their augmented semantic closures. Actual
absorbing profiles attain the maximum. Two strict observers suffice for a
finite-calendar realization of an actual exact-observer tuple (U,B,e).

No arbitrary-counterexample source is shown to satisfy Lambda_p<=0.
The note does not infer prescribed Never mass, realization of an abstract
carrier point, debt descent, or a new uniform-equilibrium class.

## Final-date and quantitative arguments

A proper opponent makes every sufficiently late deadline outcome-equivalent
to Never under a pathwise coupling, so bounded convergence gives V_i(t)->e_i.
This uses original signed rewards directly. Each proper observer has another
proper observer; absorption of the prescribed profile alone would not imply
this needed property. A uniform positive gap on used deadlines therefore
bounds each observer's support. Distinct last support dates are impossible,
since the earlier observer would already have stopped before the later used
date. Independence gives the positive survival product at the common last
date and the same pivot conditional probability x for all comparisons.

I checked the sign-sensitive step in (6): the terminal comparisons are
positive, so all L_i(x)>0. Multiplying them by positive factors at most one
then gives the claimed upper bound on their minimum. No analogous assertion
for arbitrary signed comparisons is needed. Exact optimality implies that
every used response attains B_i and that positive Never margin excludes
prescribed Never mass. Supremum attainment is not assumed separately.

The approximate argument is valid even for nonabsorbing original profiles.
Outside the delta-near-best set, the nonnegative offer loss implies
rho_i<=d_i/delta. In the nontrivial branch g>K, bounded rewards give
D/delta<1/2, so conditioning is defined and excludes Never. Conditioning
each law separately preserves independence. A maximal coupling changes
any response payoff by at most 2M times the sum of opponent mismatch
probabilities; applying this also to Never gives the displayed 4M D/delta
loss. This estimate is uniform over the entire response menu.

Thus the conditioned profile satisfies the final-date lemma without being
observer-Nash. The argument retains the original B_i and e_i throughout;
no cap from the conditioned profile replaces them. The trivial and strict
branches give the bound for every delta>0. Minimization at
delta=2 sqrt(MD), and the separate D=0 limit, give exactly the claimed
constant 4. No support-size or properness assumption on the original laws
is hidden in this passage.

## Sharpness, finite tests and closure

When Lambda_p>0, the simultaneous date-zero observer collision realizes
the maximizing x. Each observer faces exactly two response offers, and
all complete mixtures are bounded by their maximum. Their gaps are exactly
L_i(x), so the positive bound is attained by an absorbing profile.
When Lambda_p<=0, a sure date-zero pivot reduces observer responses to a
finite binary game. An independent mixed Nash equilibrium of that game is
an actual absorbing exact-observer profile, so zero is attained as well.

The piecewise-affine computation uses the two endpoints and at most three
pair intersections; parallel and coincident lines do not add candidates.
The two-action minimax identity gives the displayed nonnegative dual
certificate. The at-most-two-row reduction is sound: the strict positivity
sets are intervals, and finite one-dimensional Helly applies even with open
endpoints. Minimax on the failing one- or two-row subsystem supplies the
claimed small-support witness.

All coordinates U,B,e are bounded, so their closures are compact. Debt,
minimum margin and the quantitative upper bound are continuous in these
coordinates. This proves the estimate on both carriers without assigning
them actual profiles. Appending bounded Never offers to a realizing sequence
and taking a subsequence preserves its original (U,B) limit. Every such
lift with zero observer debts obeys the same conclusion when Lambda_p<=0;
the binding observer may depend on the lift.

## Two strict observers and semantic correspondence

With two strict exact observers, each is proper and faces the other as a
proper opponent. Both supports are therefore bounded. Moving every player's
mass after a common bound T to Never leaves those two clocks unchanged.
Under any one unilateral replacement, at least one unchanged observer still
stops by T. Consequently every prescribed and replacement outcome is
unchanged pathwise under the natural coupling. This preserves the entire
tuple (U,B,e), not merely its prescribed payoff. The contrapositive for
three observers correctly requires at least two Never-active observers in
any actual exact-observer tuple without a finite-calendar realization.
No bounded-calendar assertion is transferred to nonrealized closure points.

I statically inspected `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
in `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`,
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
They concern full behavioral caps and actual profile splicing, consistently
with this note. The new quantitative and sharp-margin results are ordinary
mathematics. No Lean command ran.
