# Review: single-pivot secant collars and strict pivot pressure

## Verdict and claim checked

**PASS as an ordinary mathematical counterexample-source reduction. No unresolved
mathematical objection was found.** This is not a uniform-equilibrium existence
proof, a counterexample, or a renewable debt-descent theorem.

Reviewed in full: `gpt/SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE.md`,
SHA-256 `204af9eb77b2d6f3639021be30a7ac2d1954f3ab20107600f581e08df3143ca1`.

The claim is conditional only on existence of some real four-player counterexample.
From that premise it produces a rational frozen 56-coordinate table, rational
positive entrance level and scale, and one fixed table with singleton vector
`(xi,0,0,0)`. Every near-minimizer at the selected table has a fixed positive
pivot-singleton mass. One sequence of actual independent finite profiles has
vanishing exploitability excess, vanishing weighted inactivity, uniformly
vanishing enlarged-calendar directional error, positive tester weight for every
owner, and strictly negative pivot pressure. The same source supplies a finite
almost-best pivot deadline and a legal private delay-only replacement losing a
fixed amount of pivot-singleton mass while losing arbitrarily little pivot payoff.

The review independently checked the secant, parameter selection, modified calendar
argument, response extraction, and delay identities. The optional generic
screened-root condition is a supplied, previously established compatibility
result, not an input to the new collar or pressure proof.

## 1. Full behavioral secant and endpoint checks

Only the pivot-recipient entry at coalition {0} changes. For one fixed product
profile and Delta=x-y>0, its prescribed pivot payoff increases by Delta*z.
Every complete pivot response payoff increases by Delta times that response's
singleton-0 mass, a number in [0,1]. Suprema therefore obey

    B_0^y <= B_0^x <= B_0^y+Delta.

Every other recipient's payoff and complete cap are unchanged, including after
that recipient's own unilateral replacement. Taking the maximum of all coordinate
debts gives both sides of equation (1). This is a full-cap statement, not a
comparison against a displayed menu. Taking infima gives the asserted
one-Lipschitz estimate for e.

In particular, for every actual profile at the final table,

    e(t) <= E_(r^t)(p) <= E_(r^xi)(p)+(xi-t)z(p).

This proves (S) without a support, attainment, or opponent-absorption premise.
At fixed r^xi, both E and the retained singleton-law coordinate are continuous
functions of the joint semantic/outcome-law carrier coordinates, so the same
inequality extends to that carrier. No full-pair realization of its limit is used.

The endpoint e(0)=0 is literal: at all-Never, every possible sole-quitter reward
is zero. At x=1, the pivot's full cap is at most one. The supplied proof of the
positive MAX-minimum moat is correct: an auxiliary exact Nash prefix with shift
0<=h<m has every new debt at most c*m+(1-c)h, so any positive absorption
contradicts maximum-debt minimality. The all-Continue inequalities then imply
B_i-s_i>=m. The pivot cap upper bound contradicts this at x=1.

The argument does not confuse maximum regret with total debt and does not require
an actual minimizing strategy.

## 2. Rational entrance and fixed descending-window selection

The tracked single-pivot equivalence really supplies a no-UE table with one unit
own singleton and three zero own singletons. A sufficiently small common positive
scaling puts every entry strictly inside the unit cube while leaving a positive
pivot singleton t<1. Reward continuity then allows rational perturbation inside
this same 57-dimensional affine slice while preserving the positive gap. The three
zero coordinates need not move.

The last alpha-level point a exists by continuity and compactness. Its maximality
implies e(x)<alpha for every a<x<=1, since a subsequent value at least alpha would
force another alpha-level crossing before the zero endpoint. For c=alpha/4, an
outer maximizer of e(x)+cx on [a,1] cannot be 1 and satisfies

    3alpha/4 <= e(xi) <= alpha.

The finite-calendar maximizers converge along one subsequence to such a xi.
Thus the fixed table, fixed positive m=e(xi), and fixed constants precede every
accuracy and depth request.

The universal collar follows uniformly on the whole descending interval:

    (x-t)z > 2alpha-alpha-alpha/4 = 3alpha/4.

Since 0<x-t<1, the advertised weaker lower bound follows. For E=m the secant is
stronger; for z=0 it gives E>=e(t)>2alpha>=2m. None of these statements uses the
generic screened-root reconstruction.

Optional rational nonvanishing of the screened polynomial is compatible with the
open positive-gap entrance. The associated screened gap is a property of the
whole frozen-coordinate fiber. The final singleton vector need not maximize that
fiber, and the note correctly disclaims that stronger assertion.

## 3. Same-calendar scalar pressure selection

The common tester pool is complete on every domain used in the proof. For a
profile on X_N, its finite opponents stop before N. All response dates at least N
are therefore equivalent to the late finite response; Never is a separate action.
The common pool through L=2k+1 covers X_L and all enlarged competitor domains
after the last two calendars are discarded.

The uniform finite approximation supplies

    e(x) <= min_(X_N) E_x <= e(x)+rho_k

for all N>=k, uniformly in x. The soft maximum lies between E and
E+tau*log|J|. Consequently all minimizers of all the calendar objectives are
uniformly near the same positive limiting maximum-regret value. This statement
is about actual laws and complete exploitability, not payoff-only compression.

The right directional envelope formula has the correct minimum sign:

    f_N'(x;+1)=min_(old inner minimizers p) partial_x F(x,p).

The reverse inequality follows from compactness of new minimizers and uniform
differentiability. Because the selected outer maximum is below 1, the right
direction is feasible even if the maximizer is the left endpoint a. Thus the
average of these minimum derivatives is at most -c.

For each N, selecting one minimizer attaining this scalar minimum simultaneously
gives an actual tuple with average pivot pressure at most -c. No convex combination
of tuples is needed in one dimension. The direction differentiates only the
pivot's own-singleton coordinate, so its derivative is exactly P_0. It yields no
sign for total pressure and no optimality condition in other reward coordinates.

The law-direction curvature estimates are valid: the gains are differences of
bounded expectations multilinear in at most four marginal laws. Bounds 16 and 96
for first and second chord derivatives are conservative. The log-sum-exp Hessian
adds a variance bounded by 256/tau. A negative derivative -b, followed for b/H,
is a legal chord step and forces the comparison with the next calendar minimum.
The common-table, common-pool telescope gives the stated vanishing averaged
directional error.

## 4. Silence and retention of the same weights

The near-minimum moat is uniform over all chosen inner minimizers. A violating
sequence, evaluated at the fixed limiting table, would give a semantic-carrier
MAX-minimum with B_i-s_i<m, contradicting the tracked moat. This uses compactness
of finite-dimensional semantic coordinates, not compactness or realization of
limiting strategies.

Shifting every finite clock by one preserves the prescribed outcome law. Its only
additional pure-response opportunity is Quit0, worth s_i; hence the new full cap
is max(B_i,s_i)=B_i under the moat.

The partition-sum comparison correctly retains the late-label multiplicities:

- Old finite labels below L transport to their successors.
- One last finite label per owner is removed, with combined normalized weight
  at most 1/d_N because there are d_N identical late labels for each owner.
- The four new initial labels have combined relative partition weight at most
  4 exp(-m/(2tau)).
- Never and zero transport unchanged.

For a transported observable bounded by one, comparing the numerator and
denominator gives the asserted 4(1/d_N+a_k) bound. Pivot pressure is such an
observable. The bound is not an assertion that every individual softmax weight
changes little.

The shifted objective bound and the three-step calendar telescope yield (9) with
the recomputed weights of that same shifted profile. Removing two calendars and
then the vanishing fraction with large directional error perturbs the bounded
pressure average only by o(1). One remaining profile therefore has both small
directional error and pressure at most -c+o(1). This is deterministic selection
from a finite family, not public correlation.

The owner-weight calculation is also sound. In its test direction, only owner i's
law changes to Quit0 and the three other prescribed laws stay unchanged. At the
endpoint, every other owner's noninitial response gain is zero. The exceptional
initial joining gains have absolute value at most two and total weight O(a_k).
Writing W=sum lambda*g and W_i for its owner-i portion gives exactly

    derivative = theta_i(U_i-s_i)-W+W_i+initial joining terms.

Using W>=E-eps_k and W_i<=theta_i(B_i-U_i) gives (11). The unit reward bound then
implies theta_i>=m/4 eventually for every owner.

Finally the laws are evaluated at r^xi while the already selected weights are
retained. Uniform reward bounds control gains, exploitability, and marginal-chord
derivatives independently of calendar size. No continuity of softmax weights as
tau tends to zero is assumed. Pressure and singleton probabilities are independent
of the changed reward parameter. All fields therefore hold on the same fixed-table
profiles and weights.

## 5. Finite response, Never conversion, and delay-only move

The inactivity bound makes the total bad-tester weight at most alpha/64. Removing
those testers from a pivot singleton-loss average at least alpha/8 leaves at least
7alpha/64. Since total remaining weight is at most one, some good pivot tester has
loss at least alpha/16 and gain at least E-epsilon_1. This also puts its payoff
within epsilon_1 of the full pivot cap, whether or not its weight is large.

If that tester is Never, its payoff is W, not generally zero. Against the finite
opponents, Quit_(N+1) has payoff W+xi*Z and singleton probability Z. Since both
are complete response values and W is nearly best, xi*Z<=epsilon_1.
The all-Never profile shows xi>=m>=3alpha/4. With the requested smaller internal
error, the universal source collar dominates Z and gives the claimed finite
response with even more singleton loss. All source accuracy requirements can be
met together by passing sufficiently far down the selected sequence.

For finite T, both indicator identities were independently checked including
the all-Never tuple. The latter belongs to the negative term
{T<O<=T_0}; this is essential and is correctly retained. Consequently positive
net singleton loss supplies the positive waiting event {T_0<O<=T}.

The map T_0 -> max(T_0,T) uses only the pivot's private clock and a deterministic
deadline selected from the laws. It does not inspect any opponent's realization.
Its singleton loss is exactly that positive waiting-event probability. By affinity
in the own marginal, its payoff change is

    sum_(u<T) p_0(u)(F_0(T)-F_0(u)) >= -epsilon*Pr(T_0<T).

The full pivot cap is unchanged because all opponents are unchanged. The pivot
debt conclusion follows, with no statement about outsiders' debts. The seven
opponent coalitions and the two timing alternatives give alpha/112 and
alpha/224 on a subsequence by finite pigeonhole selection. Neither the deadline
nor an eventwise favorable reward sign is fixed by this argument.

## 6. Tracked declarations and exact source meanings

The following declarations and their relevant hypotheses or definitions were read;
their source paths were verified with `git ls-files`.

- `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`:
  the exact existential no-UE normalization, not an unproved affine invariance.
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`:
  the 2-Lipschitz reward-table estimate used only for entrance and transport.
- `minimumTerminalSemantic_exploitabilitySingletonMargin`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  a positive global minimum of maximum semantic debt implies the margin for
  every player. It is not the total-debt minimum theorem.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `exists_finiteClockSemanticPair_exploitability_eq_upper`, and
  `quantileClockSupport_fin4`
  in `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`:
  the upper value is attained by an actual finite-clock semantic pair; its
  gap above the unrestricted infimum is at most 24/j and its clock bound is
  8j+1. Thus j=floor((k-1)/8) provides the claimed rho_k.
- `hasEscapeAwareQuantileClockCompression_of_normalized`
  in `Research/Quitting/EscapeAwareQuantileClockTransport.lean` and
  `quittingFiniteClockSemanticReachable`
  in `Research/Quitting/FiniteClockTerminalSemantics.lean`:
  normalized rewards produce the needed compression without a further supplied
  strategic hypothesis, and the reachable object retains unrestricted caps.
- The standard terminal all-errors and positive-gap endpoints are
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  and `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

For the conference dependency, the common-calendar comparison was against
Sections 7.3–7.4 of
`exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`.
Its shorter namesake in `gpt/` does not contain those subsections. The current
note reproduces the relevant argument, and its scalar tilted modification was
checked directly rather than accepted by analogy.

This is a source-and-mathematics review. No Lean compilation or axiom audit was
run, and no new claim is described as Lean-checked on the strength of this review.

## 7. Falsification checks and scope boundary

Independent exact arithmetic checks used twenty finite product profiles with
clock support {0,1,2,Never}, positive integer marginal weights, frozen rewards in
{−5/7,...,5/7}, three zero own singletons, and pivot levels 2/7 and 5/7.
Full caps were evaluated over all supported dates, a post-support finite date,
and Never. Both complete-cap secant inequalities and the delay payoff/cap bounds
held in every case. These are local-identity checks, not numerical evidence for
a counterexample or for the hard-branch existence premise.

Both waiting-flux and delay-loss indicator identities also held exactly on all
768 configurations obtained from four clocks in {0,1,2,Never} and deadlines
T in {0,1,3}. In particular, ties at the deadline and joint Never did not falsify
the formulas.

The main attempted failure modes were: replacing full caps by finite-menu caps;
losing the right derivative at the left endpoint; choosing different profiles for
pressure and stationarity; dropping late-label multiplicity; recomputing
potentially unstable softmax weights at the limiting reward; treating Never as
zero payoff; observing an opponent's future clock in the delay operation; and
turning singleton mass loss into a monotone debt rank. None is used in the proof.

Two optional clarity improvements remain, neither a mathematical objection:

1. In the owner-weight direction, explicitly say that the other three marginal
   laws stay unchanged.
2. Identify the active export when citing its Sections 7.3–7.4, to distinguish it
   from the shorter temporary namesake.

The source is narrower and more specific than the former total-singleton collar:
it retains a single positive pivot and controls that pivot's singleton mass with
a strict pressure sign. It does not retain the former total-pressure condition,
full-fiber maximizing property, or membership-stretch ancestry. The fixed final
pivot singleton need not be rational.

The next mathematical question is exactly the stated consumer problem: control
the three changed outsider caps, or produce a renewable return/descent that
retains the singleton loss. The source and delay move do not already solve it.
