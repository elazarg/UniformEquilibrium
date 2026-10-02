# The unresolved uniform exactification step for positive bonuses

Author: CODEX_RENY.

Ordinary mathematical supporting calculation. The scalar minimization
below is proved; the all-menu source conversion is not. This note does
not claim a counterexample to the positive-bonus selector, a uniform
modulus, or a new equilibrium class.

## 1. The actual target

Consider arbitrary canonical four-player quitting rewards, with own
singletons (1,0,0,0), |r_i(S)|≤M, independent stopping laws, and zero
Never reward. Full exploitability E uses every complete unilateral
behavioral replacement, equivalently all pure stopping dates and Never.

The intended source conversion would start with an ACTUAL finite product
profile of small ORIGINAL E. It could enlarge the finite menu arbitrarily
and select entirely new laws. Its output would have to satisfy the
[compensated correspondence](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md):
the pivot globally minimizes the original full repair LP, and all three
nonpivots are exact best responses for compensation plus a planned-Never
bonus β_j∈[0,η]. Here η>0 is prescribed before the output is chosen.

One quantitative target is a function ω_(M,η)(ε)→0 as ε↓0 such that
every input table and actual finite profile with E≤ε yields such a
point, at some enlarged menu, with original value L≤ω_(M,η)(ε).
A table-dependent modulus would be a weaker meaningful target. Neither
is proved here. A zero-bonus obstruction does not falsify them: η remains
positive, and output menu size is unrestricted.

## 2. Exact optimization over the one allowed scalar bonus

Fix finite nonpivot laws and one global pivot LP minimizer with L≤ε.
For a nonpivot j write

    z=p_j(Never),
    H=max_(t<N) π_t,
    T=max(W,C)=W+Δ,
    G=Σ_(t<N) p_j(t)(H−π_t)≥0.

Here π_t are original finite pure-response payoffs, W the Never payoff,
C the first late endpoint, and Δ=[C−W]₊ the compensation. All are held
fixed in the player's replacement problem, including closed LP boundary
points. The prescribed compensated payoff with extra bonus β is

    Σ_(t<N)p_j(t)π_t+z(T+β),

and its largest pure payoff is max(H,T+β). Consequently its ordinary
auxiliary regret is exactly

    R(β)=G+(1−z)[T+β−H]₊+z[H−T−β]₊.                 (1)

The minimum on 0≤β≤η is attained by

    β*=min(η,[H−T]₊),

and its exact value is

    min R = G+(1−z)[T−H]₊+z[H−T−η]₊.                 (2)

Proof: subtract the finite contribution (1−z)H−G and split at the
single kink T+β=H. Before the kink the slope is −z; afterwards it is
1−z. Clamping the kink to [0,η] gives (2). This includes z=0 and z=1,
with no division by a vanishing support or survival probability.

Thus exactification at the SAME source by the permitted scalar bonus is
possible precisely when all three nonnegative terms in (2) vanish.
For 0<z<1 this says that every positively supported finite time has
payoff H and that 0≤H−T≤η; then β=H−T is forced. If z=0, finite
support still must attain H, and T≤H suffices with β=0. If z=1,
one only needs H−T≤η.

## 3. What the supplied small full value does and does not control

At β=0, exact source identities give

    R(0)=d_j−zΔ≤L≤ε.

Using (1), this implies

    G≤ε,
    (1−z)[T−H]₊≤ε,
    z[H−T]₊≤ε.                                       (3)

These are weighted estimates, not the exact vanishing conditions in
(2). In particular β cannot change G at all. Bounds on average regret
do not force equality of every positively supported finite-time payoff.
When H>T, the required bonus is bounded by ε/z only if z>0; this is
not a uniform unweighted estimate as z vanishes.

This identifies the failure of a particular proof step, not failure of
the global source implication. Optimizing the three scalar bonuses while
holding the actual finite laws and original pivot minimizer fixed cannot
by itself prove exact outer equations from (3). Changing the laws is
allowed in the target and might remove these terms simultaneously.

Pruning low-payoff support can convert average errors into approximate
support errors with length-free bounds. That is already available in the
earlier [approximate finite-Nash note](CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md).
It does not make (2) exactly zero. Pruning opponents also changes the
original inner optimization; selecting a new global pivot minimizer can
change every finite-time payoff appearing in (1). No uniform stability
or favorable value orientation for this joint operation has been proved.

## 4. The exact stopping point

Finite-dimensional compactness proves equality of the zero sets at each
fixed deadline, as recorded in the
[expressiveness test](CODEX_HILBERT__COMPENSATED_SELECTOR_EXPRESSIVENESS_TEST.md).
It supplies no modulus uniform over increasing deadlines. The existing
geometric LP identification and actual finite approximation yield small
L and hence (3), but no exact outer best-response selection.

The narrow sources used are
`exists_objective_minimizer_eq_behavioral_infimum` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`
and `HasQuittingSmallPivotRepairValue` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean`,
together with the exact compensated-source equations above. They do not
assert the desired approximate-to-exact conversion. No Lean build was
performed for this supporting calculation.

The first unresolved implication remains genuinely JOINT: from actual
laws with small L and the weighted errors (3), produce a new finite
profile, a global original pivot optimizer, and β≤η for which every
term in (2) is exactly zero and the new L still tends to zero. Allowing
an enlarged menu does not itself prove that implication. Conversely,
nothing here excludes a successful reselected profile at that enlarged
menu. No new all-menu obstruction to the strictly-positive-bonus class
has been established.

## 5. Relaxed fixed-table target and two joint mechanisms

The weaker question fixes ONE canonical table and one η>0. It assumes
arbitrarily good actual finite-profile approximants and asks only

    inf_(N≥1) c_N(η)=0,

where c_N(η) minimizes original L over all bonuses up to η and all
compensated fixed points. It requires no uniform modulus, preservation
of a supplied profile, bounded enlargement, or nearby equilibrium.
The calculation above does not settle this weaker implication either.

Two joint mechanisms were tested without yielding the required value
control. Neither is presented as a counterexample to the implication.

First, the small-L set is separately convex in each prescribed marginal:
each deviation gain is affine or a supremum of affine functions of that
marginal, with its prescribed payoff affine. This suggests searching for
a fixed point within a low-value constraint set. But constrained best
responses are not the unrestricted auxiliary best responses in the
selector. No invariance of that set under joint responses, or removal
of the active value constraints, follows from separate convexity. Exact
best responses to nearly indifferent opponents can move a large amount
of probability even in a static finite game. Thus a standard fixed-point
argument on the constrained set does not establish the claimed source.

Second, one can represent the outer equations by a finite auxiliary
continuation game. Write w=λ+ν and assume wD_j>0. Against the fixed
pivot head, prescribe a terminal vector τ after all players survive the
finite head. Replacing the original late contribution by this terminal
payoff agrees, for every unilateral nonpivot replacement, with the
compensated objective exactly when

    β_j=D_j[wτ_j−max(a_jλ,b_jα)]∈[0,η].

Indeed the original late Never contribution is D_j a_jλ, the new
continuation contribution is D_jwτ_j, and their difference must be
Δ_j+β_j. This is a payoff identity with the opponents held fixed, not
a source of an acceptable τ or an equilibrium tail. It is the same
target-matching constraint already exposed in the
[tail-matching obstruction](CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md).
Finite auxiliary-game Nash existence does not also impose original
global pivot optimality or small L. Conversely reoptimizing that pivot
can change the continuation constraints. Assuming a favorable tail
or a joint value-preserving re-equilibration would assume the missing
step rather than prove it.

The relaxed fixed-table positive-bonus implication remains unresolved.
These two mechanisms supply neither a small-value sequence nor an
all-menu counterexample to that class. No strengthened exactness
restriction is substituted for the intended positive-bonus question.
