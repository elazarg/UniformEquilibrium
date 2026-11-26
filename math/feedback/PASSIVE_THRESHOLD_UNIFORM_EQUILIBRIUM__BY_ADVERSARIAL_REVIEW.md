# Final adversarial mathematical review: passive-payoff threshold

Reviewer: NASH_ITERATION. Ordinary mathematics, not Lean checked.
Reviewed complete artifact, intended retained path:
`math/exports/PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md`.
SHA256: `0c1c9e0471f76faff1d5eb6780f866a20f5d0effd24142d5426e92ecb7045da5`.

**Verdict: PASS on the entire mathematical statement and proof, Sections1–11.**
There is no unresolved mathematical objection and no unproduced strategic
input. I explicitly checked the virtual-seed localization, recursive compact
fibers, complete-deviation cap accounting, weak boundary, both complementary
profiles, all15 old global-invariance selectors, and the eleven-support
polynomial equivalence. The separate final BENCHMARK_NUMERIC coverage review,
pinned to this same artifact, audits the wider previously accepted producer
families. Together these establish the export coverage increment; the result
is not merely a supplied-object verifier or another construction on an already
covered benchmark. Neither review claims Lean verification or full Fin4 closure.

## Raw guards and localization

Strict(R2) makes V>H>=0 and cV+aGamma02<0 exactly. No denominator can vanish,
since a,c>0. Active owner0 has Q0<=0. The three two-owner subsets of123 have
the stated nonpositive supported Quit offer. In the full123 case, Q1>0 forces
q2>a/(a+c), independently of the continuation annotation and of q1. Each
row0 corner is affine in q2 and nonpositive at both ends of the threshold
interval. Bilinear interpolation supplies the output inequality for every
root, including boundaries; no selected stationary root is substituted for
this universal argument.

The open domain u0<V is genuinely produced and prefix-invariant. Every
actual row0 payoff and full cap is at most H, since every terminal or Never
payoff is at most H. A finite prefix from a fixed virtual seed has row0
payoff and cap bounded above by max(seed0,H)<V. The same strict bound survives
closure. Thus neither taking compact minima nor using nested local inductions
can reach the boundary of the domain on which NI was proved.

## Local escape and actual-law minimum

I rechecked the complete induction, including its possible circularity points.
In the kernel case the singleton drift cancels in every core row; the
remaining O(epsilon^2) per-date passive contribution and O(epsilon) immediate
Quit offers give O(epsilon) full debt over O(1/epsilon) dates. Positive
outsiders retain strict Continue preference through every intermediate prefix.

When no nonnegative kernel exists, separation of the compact column simplex
from zero produces the signed row w. The small-hazard remainder is uniformly
bounded by max(q)sum(q), giving the stated positive drift. For |S|>=2, signed
seeds with w z>0 and one negative coordinate exist arbitrarily close to zero;
|S|=1 was already covered by the kernel case. They can be chosen inside the
open invariant domain.

Unique AllContinue plus closedness of finite-game Nash conditions and
compactness of the entire root cube supplies uniformly small nearby roots.
Outsiders' strictly positive continuation values force their hazards to zero.
The minimum fiber contains the empty word. A nonzero Nash prefix preserves
B=U, the nonpositive minimum, the ORIGINAL separator inequality, and strict
survival-budget slack. Its decrease of survival is strict. If only Continue
remains, the zero set is a proper nonempty subset: all coordinates are
nonnegative, at least one is zero, and the original signed inequality makes
the core vector nonzero. The smaller-zero-set induction stays in the same
ambient domain. Its words preserve the original separator inequality even
though they need not be Nash at intermediate annotations. Strict slack puts
the resulting limit back into the SAME original fiber. The inner positive
absorption amount need not be uniform in the minimizer. Finally, transferring
identical words from virtual seeds to v uses payoff and full-cap Lipschitz
bounds independent of word length. No virtual seed is asserted realizable.

The global carrier is the closure of actual bounded finite-dimensional
semantic data, not a claimed continuous payoff image of weak stopping laws.
Prefix continuity is the explicit root recurrence. Moving the smallest
original marginal Never mass changes four prescribed payoffs and three full
caps by at most2M times that mass, while the chosen owner's cap is unchanged.
This verifies14M in(4.1). The least Never-product minimum on the zero-debt,
nonpositive-payoff fiber is positive under A_Z>0. A sure-quitter prefix
contradicts(4.1); a nonzero proper root contradicts minimality; and the unique
Continue case is contradicted by the local escape. All reductions use the
original Never masses, not a conditional-tail replacement. Hence A_Z=0.

## Consumer and weak boundaries

For nonnegative own offsets, every absorbing prescribed law receives its
full own shift, whereas every deviating law receives at most that shift.
Thus original full terminal debt is bounded by native debt. The stated
terminal-to-uniform endpoint supplies the fixed payoff target. Negative own
offsets are correctly excluded from this consumer.

At equality in(R2), Gamma02<=0. Decreasing that one reward leaves H and every
other raw guard unchanged and makes(R2) strict. Uniform reward perturbations
change each full deviation debt by at most2epsilon, even after taking its
supremum over all behavioral replacements. The same absorbing profiles give
A_Z=0 on the boundary, with total-debt error at most8epsilon. This is a valid
closure argument, with no assumed perturbation radius or moving target.

## Exact corollaries and negative controls

I independently reconstructed the literal coalition expectation formulas in
exact fraction arithmetic. This verifies every Bellman equation and both
action comparisons of the five-date profile at K=0,t=t0, including its quiet1
margin43187916/204490445. Increasing K only helps that comparison, while
lowering t helps quiet3. R and p do not occur in its prescribed payoffs or
one-player deviation offers. Positive opponents-only absorption in every
period proves its full behavioral and arbitrary-own-shift consumer.

For the two-date profile, R>=-33/100,t>=t0 gives0<x<1/10 and0<z<1/20. The
player0 and player3 indifferences are exact. The quiet1 lower margin9/40
and player2 lower margin33/4 follow from the displayed bounds. Player2's
continuation cap is exactly-10 against sure01, not its prescribed continuation
value. Every deviator absorbs by date2. Together with the localized region,
these profiles cover the entire(R,t) plane for K>=0, arbitrary p and
nonnegative own levels, including all stated equality boundaries.

The exact fraction reconstruction also verifies both global-NI counterexample
roots and the modified-table negative control. Independent enumeration of the
safe predecessor graph leaves exactly{2} and{2,3} as proper nonempty closed
sets. Their explicit root and the all-four root therefore exclude all15 old
global marked-cone selectors. The static ordered-participant rejection holds
for every marked set, block order and positive weight choice. The negative
control satisfies(R1), strict(R2), and the unaffected(R3) guards, while its
fully positive root output refutes the invariant when the passive23 guards
are omitted. None of these controls is mislabeled as a no-UE game.

## Eleven-support criterion

For every proper root H_i>0. An active owner's indifference uniquely fixes
v_i=(Q_i-P_i)/H_i and its output is Q_i, so(A1) is exact. An inactive owner's
output ranges over an open interval with upper endpoint P_j+u_jH_j. The
existence of a positive output at least Q_j is exactly the two strict upper
inequalities(A2). An inactive anchor with v_j<=0 exists exactly when P_j>0
and Q_j<=P_j: necessity follows from its output being at most P_j, and
sufficiency uses v_j=0, which is interior to the raw box. Active anchors are
exactly Q_i-P_i<=0. These choices are independent across inactive coordinates.
Thus(A1)–(A3) are equivalent to a proper cone-crossing Nash root in the box.

Zero support cannot cross the cone, and a single active owner has output0.
The remaining support counts are6+4+1=11, each with at most four anchor
alternatives. All hazard polynomials have degree at most3. The raw open box
contains every actual annotation and every sufficiently small signed seed;
all fixed-seed prefix closures lie in a smaller closed interior box. Hence
Sections3–4 apply exactly, proving the sufficient criterion and its stated
necessary condition for a counterexample with nonnegative own levels.
Failure of the test correctly makes no claim of UE failure.

No unproduced continuation, selected equilibrium root, recurrence hypothesis,
or strategy-class completeness assumption remains. The finite reformulation
is correctly treated as an additional description of the mechanism, not
counted as a second reward-coverage gain. No Lean command was run.
