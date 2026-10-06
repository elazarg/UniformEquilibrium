# Independent review: larger-eigenvalue four-clock producer

Reviewer: CODEX_BROUWER.

## Verdict and exact scope

**PASS.** I independently checked the final section **Larger-eigenvalue
four-clock branch**, equations (119) through the end of
[`CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`](../notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md),
at whole-note SHA256
`4d1786293fc5ec9aecf07528a4fca8f83031ec5f0dfa4b03fa5bab52618da40d`.
No other review was read. There is no unresolved mathematical or strategic
input in the stated raw-table-to-fixed-uniform-payoff theorem.

This is ordinary mathematical review and static inspection of the cited
production declarations, supported by exact rational/symbolic calculations.
I did not run Lean, modify Lean, or claim the new raw producer is already
implemented. I did not edit or export the candidate.

The precise input is an actual Fin4 reward table, up to cyclic relabeling,
with successor comparisons −b_i<0, predecessor comparisons h_i>0,
opposite comparisons g_0,g_2<0<g_1,g_3, D>1, and det Γ>0.
Own singleton levels and every nonsingleton coordinate are arbitrary
signed reals. No strategy, root, value, or cap is supplied. The output
is one fixed payoff, with actual independent profiles and unrestricted
behavioral deviation control at every accuracy and all sufficiently long
horizons. The unrefined cycle is not asserted Nash.

## Raw algebra and all sixteen floors

I expanded the determinant independently, including an exact symbolic
check of

    det Γ=−(∏b_i)[(1−U)(1−D)−VL].

From D>1 and d_2>0, D_0>0. The sign pattern gives L<0 and V>0.
Since χ(1)<0 while −VL>0 and 1−D<0, necessarily U<1. Thus χ
has two distinct real roots straddling1, and its larger root λ satisfies
λ>1>U. The proposed w_0=V and w_1=λ−U are strictly positive.

The eigenvector equations are exactly

    Uw_0+Vw_1=λw_0,       Lw_0+Dw_1=λw_1.

Substituting the definitions of w_2,w_3 gives all four recurrences (123),
not just two of them. In particular

    D_0w_3=w_1−A a_0d_1w_0>0,

so w_3>0 and then w_2=A d_1w_0+a_1w_3>0. There is no assumed
positive eigenvector or unverified choice of branch here. The upper
eigenvalue is essential in this sign configuration.

The β_j and T_j give four proper hazards and period survival exactly A.
The numerator in V^j has total coefficient T_j(1−A), so these are
actual convex combinations of singleton rewards, even for signed tables.
Direct subtraction proves all four vector Bellman equations. The four
weighted comparison balances give V^{i+1}_i=s_i, and then V^i_i=s_i.
The other two entries in each coordinate are exactly

    V^{i+2}_i−s_i=q_{i+1}b_i/(1−q_{i+1}),
    V^{i+3}_i−s_i=q_{i+3}h_i.

Both are strictly positive. This checks every one of the sixteen floors,
including cyclic wraparound; the opposite comparison does not need a
separate floor argument. The target is precisely the displayed singleton
lottery with weights w_i/W, independent of refinement accuracy.

## Full behavioral, Never, and uniform-horizon seam

The microphase value lies on the segment between its TWO coarse values,
not necessarily between two singleton-floor-safe singleton endpoints.
This distinction is handled correctly. For the owner, both coarse endpoint
values equal its singleton. Consequently every microphase has exact policy
evaluation AND exact forced-Continue transport for every player.

For a passive player i, only the singleton {i} and pair {i,j} can occur
under a first deviation at a solo-j date. Hence its Quit endpoint is at
most s_i+C p_{j,K}, where C is the maximum positive pair premium.
The floor then bounds it by current value plus e_K. Triple and grand
rewards are not identified with singleton rewards: they are literally
unreachable under prescribed solo rows and one unilateral deviation.
They may therefore be arbitrary finite signed numbers.

Adding ONE e_K to every continuation coordinate is a supersolution:
under Continue its extra contribution is c_{−i}e_K≤e_K. There is no
sum of per-date errors. Against any history-dependent behavioral response,
the remaining bounded continuation error after complete periods is
multiplied by κ_i^n, where κ_i=∏_{j≠i}(1−q_j)<1. This proves the
full cap bound, including arbitrarily late stopping and Never. Negative
singleton values do not create a hidden terminal-floor assumption because
the OTHER three players absorb almost surely against every deviation.

For the horizon seam, let T be the first opponent quitting date, counted
from zero. Pathwise the N-date average differs from the terminal reward
by at most M min((T+1)/N,1). Geometric period domination gives
E(T+1)≤4K/(1−κ_i), uniformly over the deviator. The same estimate holds
for the prescribed profile. Thus one may use, for example, regret bound

    e_K+2M [max_i 4K/(1−κ_i)]/N.

The candidate's more conservative estimate also suffices. First select K,
then one common horizon threshold; u never changes. The initial live zero
is included by T+1. No terminal-payoff statement is being substituted for
an exact finite-horizon delivery statement.

### Literal production consumer inspected

In `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`
I checked the fields of `BalancedSingletonCycleCertificate`, its finite
collision-bound construction, and
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`,
`BalancedSingletonCycleCertificate.isHorizonNash_and_delivers`, and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.
None requires nonnegative singleton rewards. The four distinct owners
and positive hazards supply its actual `opponentDivergence` premise.

In `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean` I checked
`quittingSoloReward_le_quittingSingletonArcCycleValue_of_coarse`,
`quittingSingletonArcCycle_phase_certificate`,
`singletonArcCycle_isTerminalNash_and_hasValue`, and
`singletonArcCycle_isUniformEquilibriumPayoff` at the fields needed here.
These consume the exact equations and all floors just produced; they do
not supply a missing selector. The nearby all-solo-calendar obstruction
`Schedule.one_over_sixtyEight_lt_literal_exploitability` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`
is for its specific Solan–Vieille boundary table, not all solo cycles.
No universal architecture completeness is claimed here.

## Exact stress tests and fixture verification

For the full rule (128), direct enumeration yields exactly the singleton
matrix (127), determinant25, traps01,23,I, weights and hazards in the
candidate, and its four rational value vectors. All sixteen Bellman
coordinates and all floors were checked exactly. The initial player1
Quit excess is indeed1/23, so refinement is strategically necessary.

For a signed stress test, add the same vector (−8,3,−5,−11) to EVERY
singleton reward vector of (128), but replace every nonsingleton vector
by the completely unrelated rule

    r_i(S)=(−1)^(sum_(j∈S)j+i)(37+11i),       |S|≥2.

The singleton matrix, rates and balance equations remain unchanged.
The new own singleton vector is (−7,3,−5,−11), and the target is
(−7,3,−107/23,−250/23). Every coarse value is the old value plus
that shift, so all sixteen floors and Bellman equations still hold.
The pair bound C is finite and the same full supersolution proof applies.
This explicitly tests the claimed signed and arbitrary-collision scope,
rather than relying on a nonnegative fixture alone.

The exact stationary exclusion in (129) is valid. I derived each of the
four indifference equations directly from the full two-pair completion.
The cases of a missing pair, a zero individual hazard, and any sure
hazard are exhausted before division. The displayed bounds give
α≤11β/12 and β≤36α/35, hence α≤33α/35 with α>0, a contradiction.
This part proves absence of EXACT stationary equilibria. It alone would
not justify absence of arbitrarily accurate stationary profiles; a separate
proof of the latter is given below, not silently inserted into (129).

All twelve pure child witnesses check. For child012 the full Quit and
optimal-Continue endpoints on its active coordinates are

    Q=(3/2,1/6,0),       C=(3/2,1/6,−7/6).

For child023 they are

    Q=(1,4/5,1/3),       C=(−1/5,4/5,1/3).

The last Continue value for the sure owner0 includes its later solo Quit
after the other two fail to stop; using a zero suffix there would be wrong.
The omitted players' gains are respectively6 and5. In all fourteen cases
the child profile is exact terminal Nash and joint Never is zero. Therefore
the claimed universal fixed nonnegative weighted-debt-plus-Never bound is
impossible for SOME outsider of EACH proper child. This does not exclude
every possible quiet equilibrium of any particular child.

## Bounded coverage and significance

I checked `SignedFourCycleSingletonData.StrictTests` and its weighted
balances in `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
the definitions and eigenvector algebra in `MathUE/SignedFourCycleAlgebra.lean`,
and `SignedFourCycleSingletonData.certificate` and
`SignedFourCycleSingletonData.targetValue_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`.
The existing raw producer really selects the SMALLER root and requires
its upper-right coefficient to be negative. The generic balanced compiler
does not already produce the new raw input.

For (127), among all six cyclic orders starting at0 only (0,3,2,1) has
the required negative successor and positive predecessor signs. Its four
rotations all have characteristic polynomial

    (2λ−3)(8λ−3)/16.

Thus their smaller root is3/8, and no relabeling passes the implemented
smaller-root test. Positive row rescaling and row translation preserve
these comparison-ratio tests. This is a real source-input distinction.

Exact support enumeration at (3,−2,−7,5) gives only the stated full LCP
solution. I independently checked all principal determinants, the stated
negative inverse entries, and all fourteen partition block-row inequalities.
The R₀ argument is sound: support of size at least two would give a kernel
of an invertible principal matrix, and singleton support is defeated by a
negative entry in its column. The unique regular full root gives degree+1,
so this is not a zero-degree exit. The principal02 obstruction is an R₀,
non-Q two-by-two matrix, not merely a negative entry in a larger inverse.
I also checked the actual `StandardLCPSolution` convention in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.

The full core, opposite-sign pair gaps, lack of a weak full-trap leaver,
and positive sure-grand premiums exclude the listed core, leaver, boxed,
mixed-trap and product-low classes. The three aggregate-leave inequalities
force even nonnegative weights to vanish, so they genuinely exclude the
weighted-floor packet's weaker weak-leave test. The proper-child witnesses
exclude the universal debt bounds used by the accepted finite quiet-lift
packet. The singleton child obtained by deleting the only positive-own-
singleton player has an all-positive passive row, excluding the prescribed
cyclic-child raw sources under relabeling.

The accepted `TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD.md` explicitly shrinks
its neighborhood so that one pair trap has no weak leaver; both pair traps
here have strict leavers. Its neighborhood therefore does not contain this
fixture. These checks concern actual accepted raw criteria, not unproduced
inputs to arbitrary supplied-object consumers.

**Independent significance verdict:** this is a new original-table UE
producer with an explicit complete table outside the applicable implemented
and accepted raw existence gates checked above. It genuinely shrinks the
surviving counterexample class. It is not a new refinement compiler, a
claim that all four-clock sign patterns work, or an unrestricted strategy-
class completeness theorem. No unresolved strategic witness is hidden.

## Separate strengthening: the fixture also excludes approximate stationary families

This paragraph is ordinary mathematics supplied by this review, not needed
to validate the author's exact stationary claim or the new UE class.
Suppose stationary profiles q^n had full terminal exploitability ε_n→0.
Pass to q^n→q*. All singleton rewards of the fixture are nonnegative.

If q*≠0, prescribed stationary payoffs are continuous at q*. For any player
with positive limiting opponent absorption, its full stationary cap is the
continuous maximum of Quit and Never endpoints. If limiting opponent
absorption is zero, only this player can have a positive limiting hazard;
its cap at q* is s_i≥0, and the Quit endpoints along q^n tend to s_i.
Thus the cap is lower semicontinuous there as well. Since prescribed
payoffs converge and regrets vanish, q* is an exact stationary equilibrium,
contrary to the complete support argument (129).

It remains that q^n→0. Terms with q^n=0 are impossible for small ε_n because
s_0=1. Put H_n=∑q_i^n>0 and select q^n/H_n→p in the simplex. The stationary
first-coalition probability of singleton i tends to p_i, while total
multiquitter probability tends to zero. Hence u^n→u=∑p_j r({j}). Forced
Quit values tend to s, so u≥s and Γp≥0.

For p_i>0 and positive opponent absorption a_{−i}^n, write Q_i^n and N_i^n
for the full stationary Quit and Never endpoints. The prescribed value is

    u_i^n=θ_i^n Q_i^n+(1−θ_i^n)N_i^n,
    θ_i^n=q_i^n/[q_i^n+(1−q_i^n)a_{−i}^n] → p_i>0.

The actual cap bounds N_i^n−u_i^n≤ε_n. Therefore
θ_i^n(u_i^n−Q_i^n)≤ε_n, and u_i≤s_i in the limit. If opponent absorption
is zero on a subsequence, the player is the only positive stationary
quitter there, and u_i^n=Q_i^n=s_i directly. Together with u≥s this proves
p_i(Γp)_i=0 for every i. Thus p is a nonzero homogeneous complementary
solution, contradicting the checked R₀ property. Every support limit,
including a direction concentrated on one player, is covered.

Consequently the infimum of FULL stationary terminal regret for this one
fixture is positive. No numerical lower bound or game-level gap is asserted;
the nonstationary refined profiles already prove its UE.

## Potential structural extension, not an acceptance condition

The proof suggests one useful unified raw selector rather than further
constant variants: retain b_i,h_i>0, allow arbitrary opposite comparisons,
test BOTH real eigenvalues, and accept either λ>1 for which one of the two
orientations of (V,λ−U), reconstructed as in (122), has all four weights
positive. These are finite scalar reward tests, not supplied strategies.
The same four balances, sixteen floors and compiler then work. Choosing
the negative orientation on the smaller root recovers the implemented
branch; the positive orientation on the larger root recovers this one.
I have not claimed that either test always succeeds, or that this exhausts
all eigenvector degeneracies. The stated strict new branch is already
complete and does not depend on this possible packaging extension.
