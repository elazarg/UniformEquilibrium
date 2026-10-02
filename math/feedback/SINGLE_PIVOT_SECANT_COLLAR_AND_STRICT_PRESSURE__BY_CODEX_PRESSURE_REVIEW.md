# Single-pivot secant collar: independent pressure and calendar review

## Verdict

PASS within the reviewed mathematical scope. No correction is required in
Sections 6.1--6.4 or in their matching to the stated finite-response and
delay conclusions. The full statement and proof were read; this review
concentrates on the scalar envelope, common-calendar error estimates,
same-profile weight transport, and simultaneous strict-pressure selection.

The source uses a maximum-regret minimum of one fixed selected table.
It does not import a total-debt minimum, maximality over all four own
singletons, a sign for total singleton pressure, or a played mixture of
different profiles. No conjecture resolution or export admission is asserted.

## 1. The scalar outer maximum supplies the correct sign

The one-coordinate full-cap sandwich is valid for arbitrary actual
behavioral profiles. Only the pivot's prescribed payoff and cap change;
the prescribed change is exactly (x-y)z(p), and every pivot response
changes by a number in [0,x-y]. Consequently e is 1-Lipschitz and the
secant inequality is about the pivot singleton itself.

The two endpoint arguments give e(0)=e(1)=0. The latter uses the
positive maximum-regret minimum moat on the compact semantic carrier;
it does not require an actual minimizing strategy. The last alpha-level
a lies strictly between t and 1. On [a,1], e <= alpha, while every
maximizer xi of e(x)+cx, c=alpha/4, satisfies

    xi < 1,       3 alpha/4 <= e(xi) <= alpha.

For each calendar window the uniform finite-clock approximation and the
softmax error imply H_k -> H uniformly. Any selected convergent
subsequence of maximizers therefore has the stated fixed limiting xi.
The strict gap between H(a) and H(1) excludes x_k=1 eventually.
Rightward motion remains feasible when x_k=a, which is the constrained
boundary case needed by the proof.

For fixed k,N, the inner domain is compact and F is uniformly
differentiable in its scalar reward parameter. Its right envelope
derivative is the minimum of partial_x F over the old minimizers.
The proof with new minimizers gives the matching lower derivative bound,
not just an upper bound. Finite sums of these right derivatives can be
differentiated term by term. Choosing one derivative-minimizing old
minimizer for each N yields

    average_N P_0(p_(k,N),lambda_(k,N)) <= -c.

No convexification of tuples is needed for this single feasible scalar
direction. Conversely, this argument provides no reward-gradient condition
in the other own-singleton directions or the other 56 coordinates.

## 2. The common calendar controls every enlarged direction

All f_N, all Delta_N, and all relevant softmax functions within a window
use exactly the same x_k, temperature, and labelled tester pool. Thus

    Delta_N >= 0,
    sum_(N=k)^(2k) Delta_N <= 2+eps_k.

The derivative bounds are uniform in the number of dates: they arise
from four independent marginal chords and bounded terminal rewards,
not from a coordinatewise norm whose dimension grows with the calendar.
The log-sum-exp second derivative is at most
H_k = 96+256/tau. A negative derivative -b has b <= 16, so the trial
step b/H_k is within the chord. This proves the directional estimate
simultaneously for all competitors in the next calendar.

After shifting a source in X_N, it lies in X_(N+1). Dropping the last
two calendars gives N+3 <= L, so both that source and every competitor
in X_(N+3) remain in the domain where J represents full regret. The
three successive differences, rather than only Delta_N, correctly pay
for this enlarged comparison:

    R_N^2 = 2 H_k (Delta_N+Delta_(N+1)+Delta_(N+2)+tau a_k).

For the unnormalized average over the retained calendars, one explicit
upper bound is

    b_k = sqrt(2 H_k [3(2+eps_k)/(k+1)+tau a_k]) -> 0.

Here H_k is O(sqrt(k)), eps_k is O(log(k)/sqrt(k)), and
a_k = 4 exp(-m sqrt(k)/2). Thus the curvature growth does not defeat
the telescoping error. Every Delta is charged at most three times.

## 3. Silence transports the actual pressure rows

Uniform near-minimality holds for every inner minimizer in the window,
not only the minimizer ultimately selected. Re-evaluating any alleged
violating sequence at r^xi and taking a compact semantic limit yields a
MAX minimum there. Its moat gives B_i-s_i >= m, so eventually every
inner source has B_i-s_i >= m/2 for every owner.

The silent shift preserves the prescribed coalition law and changes the
full cap to max(s_i,B_i)=B_i. Old finite tester u<L is transported to
u+1, while Never and zero remain separate. These transports preserve
singleton-indicator differences as well as numerical gains.

With d_N=L-N+1 identical old late labels per owner, removing the last
finite label costs normalized weight at most 1/d_N. The initial tests
have total added weight, measured relative to the old partition sum,
at most a_k. The exact partition-sum ratio is

    Z_hat/Z = 1-ell_N+a_N.

It proves both F(p_hat) <= f_N+tau a_k and the stated
4(1/d_N+a_k) transport bound for any scalar row observable bounded by
one. In particular it applies to P_0. Recomputing softmax after the
shift is necessary and is explicitly done; the proof does not pretend
that the original numerical weights remain softmax weights there.

The average shift error is bounded by

    V_k = 4/(k+1) sum_(N=k)^(2k-2) (1/d_N+a_k) -> 0.

This harmonic average is small even though a few individual late-label
removal bounds need not be small.

## 4. One source retains strict pressure and all error bounds

Let q_k=2/(k+1) be the deleted final-calendar mass. The retained,
unnormalized pressure average is at most -c+q_k+V_k. Delete also
calendars with R_N>sqrt(b_k). Their mass is at most sqrt(b_k), by the
bound in Section 2. Since P_0 is between -1 and 1, the remaining
unnormalized pressure average is at most

    -c+q_k+V_k+sqrt(b_k) = -c+o(1).

The remaining calendar mass tends to one. For large k the displayed
upper bound is negative; normalization cannot spoil its limiting
strict sign. Some remaining actual shifted source therefore has
P_0 <= -c+o(1), while every remaining source has
R_N <= sqrt(b_k). Inactivity is already at most eps_k at each source.
Thus all three conditions hold on one profile with its own recomputed
weights. No interchange of a profilewise minimum and an unrelated
pressure average is being made.

The all-owner estimate uses the legal one-marginal direction replacing
owner i by Quit0 and keeping the other prescribed laws silent. The
weighted derivative is

    theta_i(U_i-s_i)-W+W_i + initial joining terms.

At that endpoint every noninitial tester of another owner has zero
gain. The total new initial mass is at most 2a_k, so its contribution
is bounded in absolute value by 4a_k. With W >= E-eps_k and
W_i <= theta_i(B_i-U_i), the exact derivative bound gives

    theta_i(B_i-s_i) >= E-eps_k-R_N-4a_k.

Since B_i-s_i <= 2 and E -> m, theta_i >= m/4 eventually. This
calculation requires neither other-coordinate outer normality nor
nonpositive total pressure.

Finally the selected laws are evaluated at the one fixed table r^xi,
and the selected weights are retained rather than recomputed again.
Reward continuity changes regret and inactivity by o(1). The same
four-marginal bound makes directional transport uniform over the whole
enlarged competitor domain, despite its growing number of dates.
Pressure, singleton masses, and owner weights are unchanged.

Aggregating tester labels later than N+3 at N+3 is valid on the entire
X_(N+3), whose finite dates end at N+2. Their gain functions, their
directional derivatives along these chords, and their singleton
observables agree there. Aggregation preserves owner weights and
inactivity. Never is not identified with these late finite tests.

## 5. Matching the collar and the extracted response

The fixed-table sources satisfy E -> m, so the universal secant collar
applies eventually to those same laws. The strict pressure limit gives
P_0 <= -alpha/8 eventually. Requesting arbitrarily small inactivity
then supplies a good pivot tester with gain at least E-epsilon_1 and
singleton loss at least alpha/16. The good-tester argument uses the
nonnegative deficits E-g_A of the full response pool.

If this tester is Never, the finite after-support reply has value
W+xi Z, not W and not zero. Near-optimality of Never implies
xi Z <= epsilon_1; xi >= m >= 3 alpha/4 and the collar give the
stated stronger singleton loss for T=N+1. No opponent-absorption
assumption or cap attainment is introduced. The final finite reply
and all original source fields can therefore be requested together.

The waiting-flux identity includes equal infinite clocks correctly.
The private map T_0 -> max(T_0,T) removes exactly the probability of
T_0<O<=T. Its payoff comparison uses independence of T_0 and the
opponents and the near-cap property of the fixed deadline T. It does
not condition the chosen deadline on a realized private clock.

The unchanged pivot cap does not bound any changed outsider cap.
Neither a renewed near-minimum source nor a decreasing global-regret
rank follows. The manuscript explicitly retains this consumer boundary.

## Source checks and status boundary

The full manuscript and the needed common-calendar proof in
`exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`,
Sections 7.3--7.4, were read and compared. The latter's four-coordinate
normal-cone selection and total-pressure conclusion are not imported.

The narrow tracked checks included:

- `exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`:
  an actual counterexample entrance, without preservation of an old minimum.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  the MAX-minimum moat on the semantic carrier, with no full-fiber maximum
  premise and no total-debt substitution.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `exists_finiteClockSemanticPair_exploitability_eq_upper`, and
  `quantileClockSupport_fin4` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`:
  the normalized complete-semantic approximation is unconditional and its
  upper value is attained by an actual finite-clock profile.
- `quittingFiniteClockSemanticReachable` in
  `Research/Quitting/FiniteClockTerminalSemantics.lean`:
  its cap coordinate remains the supremum over all behavioral deviations,
  and the laws retain Never atoms.

No additional checker or numerical experiment was used for this focused
review. The conclusions above follow from the displayed identities,
inequalities, compactness arguments, and exact named source statements.
There is no unresolved mathematical objection in this scope. The result
remains a counterexample-source reduction awaiting its downstream consumer,
not an arbitrary-table equilibrium producer or a Lean implementation.
