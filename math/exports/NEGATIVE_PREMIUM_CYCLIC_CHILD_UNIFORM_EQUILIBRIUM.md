# Negative joint premiums with a cyclic three-player child

## Complete raw statement

This is ordinary mathematics. It is a producer from a finite reward table,
not an equilibrium verifier and not a solution of arbitrary Fin4 games.
There are four players with private independent live-date Quit/Continue
coins and public past actions. The first nonempty quitting coalition
absorbs at its specified finite reward vector. The initial and selecting
live dates pay zero, later absorbed dates pay that vector, and Never pays
zero. All unilateral deviations below are full behavioral replacements.

Choose a parameter 0<ε≤1. Define a canonical table u by prescribing only
the four singleton vectors and one scheduled joint vector:

    u(0)  = (1,0,0,0),
    u(1)  = (2,1,4,0),
    u(2)  = (2,0,1,4),
    u(3)  = (0,4,0,1),
    u(03) = (1−ε,3,−1,1−ε).                         (N1)

Require the following twelve weak raw caps, and no others:

    u₁(01)≤1−ε,   u₁(13)≤1+ε,   u₁(013)≤1,
    u₂(02)≤1−ε,   u₂(23)≤1,     u₂(023)≤1−ε,
    u₀(01)≤1+ε,   u₃(13)≤1,     u₂(12)≤1+ε,
    u₀(02)≤1,     u₃(23)≤1+ε,   u₁(12)≤1.          (N2)

All other nonsingleton coordinates are arbitrary finite reals, including
all four grand-coalition coordinates. Thus (N1) fixes twenty coordinates,
(N2) bounds twelve different coordinates, and twenty-eight coordinates
are unrestricted. The parameter ε is raw data, not a supplied hazard.

The original signed-row version allows ANY own levels s_i∈ℝ and positive
row scales k_i>0. Its finite conditions are that

    u_i(S)=1+(r_i(S)−s_i)/k_i

satisfies (N1)–(N2). These are equalities and inequalities on the original
sixty rewards. Never is still zero in the original game; no affine
invariance of general quitting games is being assumed.

**Theorem.** Every such raw table has one exact terminal Nash profile and
one fixed original-game uniform-equilibrium payoff, against all full
behavioral deviations. The same profile works at every accuracy. For
0<ε<15/26 all four players have a proper scheduled hazard. At ε≥15/26
pivot0 always Continues (its stopping law is Never), and the three children
have proper solo hazards.
The conclusion is a raw completion-family theorem, not presently a
full sixty-coordinate open-neighborhood theorem.

## Conjecture-facing change and strategic inputs

The missing producer is a cyclic three-child construction with both
scheduled joint-participant premiums negative and no nonnegative
triple-joining row in the child. The existing positive-joint-premium raw
adapter requires a nonnegative child increment; that premise is not
available here. Conditions (N1)–(N2) instead produce all hazards and
actual continuation vectors. The complete rational table below separates
this family from the compared implemented and accepted raw criteria,
including their whole persistent-base and child-carrier selection sets.
This is an additional raw completion family, not a completeness theorem
for the three-row architecture.

The only inputs are a finite reward table, ε, and, for the signed version,
four positive row scales and the four own singleton levels. The scalar
root, four hazards, three product roots, phase values, realized target,
opponent survival bounds and accuracy-to-horizon bound are all produced
below. No finite Nash witness, stationary solution, positive-gap source,
punishment strategy, correlated randomization, deleted-game strategy,
local root or continuation value is assumed. The chosen profile uses only
private independent coins and the public date modulo3; deviations may
use every public history and arbitrary behavioral randomization. There
is no recursive strategy-selection step.

## Produce the root on the negative-premium interval

Assume 0<ε<15/26. The repeated three rows will be

    A: joint0,3 with hazards p,y;
    B: solo1 with hazard z;
    C: solo2 with hazard w.                            (N3)

For 2/5≤y≤2/3 put

    p_bar(y)=(3−4y)/(4−3y),
    z=(p+y)/[3(1−p)(1−y)],
    d=1+3y−p,          w=(3y−p)/d.                  (N4)

The boundary p=p_bar makes z=1. On 0≤p≤p_bar one has p≤1/2,
3y−p≥7/10, d>0 and w∈(0,1); before the cap z∈(0,1).
The child balance is

    f(p,y)=p(1−ε)/(1−p)+z
                       −(1−z)[3w−εp(1−w)]=0.       (N5)

Multiplication by the positive denominator 3(1−p)(1−y)d gives

    F(p,y)=−αp²+βp−γ,
    α=16+ε−12y>0,
    β=(9ε−36)y²+(32−10ε)y+13,
    γ=13y(2−3y)≥0.                                (N6)

For y<2/3, F(0,y)<0. At the cap there is the exact identity

    F(p_bar,y)=3(y−1)(9y²−13y−1)
                   [4−3y−ε(3−4y)]/(3y−4)² >0.      (N7)

Every factor's sign is explicit on this interval: y−1 and
9y²−13y−1 are negative, while
4−3y−ε(3−4y)≥1+y>0 because 0≤ε≤1.
A strictly concave quadratic negative at0 and positive at its cap has
exactly one crossing in that cap interval. Its derivative at that crossing
is positive. At y=2/3 its selected crossing is0, its derivative is
(55−8ε)/3>0, and the other root lies beyond the cap. Consequently
there is one continuous selection

    p(y)=2γ/[β+√(β²−4αγ)] ∈[0,p_bar(y)),             (N8)

with p(y)>0 for y<2/3 and p(2/3)=0. The discriminant and denominator
in (N8) are positive by the preceding crossing argument; no unproved
choice continuity is used.

The pivot balance along this already produced child branch is

    g(p,y)=(1−εy)/(1−y)−2+(1−z)(1+εy)/d=0.         (N9)

Its positive-denominator numerator is

    G(p,y)=(6y−3−3εy)p²
        +(12εy²+2εy−18y²+2)p
        +(18−13ε)y²−7y.                            (N10)

At y=2/5, F(1/5,2/5)=−3(23ε+25)/125<0, so the selected
p lies in (1/5,1/2). At this endpoint

    G=−3p²/5−22p/25+2/25
                +ε(−6p²/5+68p/25−52/25)<−3/25.

The first part is≤−3/25 for p≥1/5, and the coefficient of ε
is≤34/25−52/25<0 for p≤1/2. Thus g has a negative left
endpoint. At y=2/3 its selected p=0 and z=w=2/3 give

    g=(30−52ε)/27>0.                               (N11)

The intermediate value theorem produces y∈(2/5,2/3) with g=0.
Choose one such y once, independent of accuracy. Its selected
p∈(0,p_bar), z,w are all proper. This is an exact global scalar
crossing for the whole interval 0<ε<15/26, not a numerical root or
an isolated implicit-function neighborhood.

## All eight active and sixteen passive action tests

For clarity normalize child coordinates by subtracting their own1;
retain pivot0's canonical own1. This is algebraic notation for phase
values, not a transformation of Never. In original order0,1,2,3 the
three displayed vectors in these partly centered coordinates are

    V_A=(1−εy, 3y−p, 0, −εp),
    V_B=((1−εy)/(1−y), 0, 3z, p(1−ε)/(1−p)),
    V_C=(2w+(1−w)(1−εy), 0, 0,
                              3w−εp(1−w)).        (N12)

Restore canonical actual values by adding1 to coordinates1,2,3.

At A, pivot0's forced Quit value is1−εy. Its Continue value is
(1−y)V_B,0, since u₀(3)=0, and these are equal by (N12).
Player3's centered Quit value is−εp; its Continue value is
−p+(1−p)V_B,3=−εp. Thus BOTH active joint participants are
indifferent even though both participant increments are negative.

At B, active child1's centered Quit and Continue values are both0:
the former is its singleton, the latter is V_C,1. At C, active
child2's centered Quit and Continue values are both0, because
V_A,2=0. The other policy equalities at the solo rows are exactly
the affine recursions in (N12). In particular

    V_B,3=−z+(1−z)V_C,3

is (N5), while

    V_B,0=2z+(1−z)V_C,0

is (N9). At A, the passive child1's Continue value is
3y−p because the scheduled joint reward is3 and hence the centered
joint reward is2. Child2's Continue value is0 because

    −p−y+3z(1−p)(1−y)=0.

These are precisely (N4). Therefore every prescribed Continue endpoint
and every prescribed policy value has been checked, not just four active
indifferences.

It remains to check all passive Quit endpoints from the actual raw table.
At A, (N2) implies the centered child1 Quit bound

    Q₁≤−εp(1−y)+ε(1−p)y=ε(y−p),

including the nontrivial simultaneous outcome013. Its Continue margin is

    V_A,1−Q₁≥(3−ε)y−(1−ε)p>0.                    (N13)

Indeed y>2/5, p<1/2 and ε≤1 imply (3−ε)y−p>3/10.
At A, centered child2 Quit is≤−εp, including outcome023, hence
at most its Continue value0.

Put H=(3−ε)y−p>0. Then

    V_C,0−1=H/d>0,
    V_C,3−εw=3H/d>0.                              (N14)

At C the pivot's Quit cap is1 and child3's centered Quit cap isεw,
so these are the exact needed margins. The other passive player1 has
centered Quit cap0 and Continue value0.

At B, the pivot's Quit cap is1+εz. Its actual Continue value is
2z+(1−z)V_C,0≥1+z≥1+εz. Child2's centered Quit cap isεz≤3z,
and child3's centered Quit cap is0≤p(1−ε)/(1−p).
This exhausts both actions of every player at all three rows. A passive
comparison was never replaced by an own-singleton floor at the negative
joint phase.

## The large-ε child-only exit

For 15/26≤ε≤1 take p=0 and y=z=w=2/3. Thus A is solo3,
followed by solo1, solo2. The actual canonical phase vectors are

    V_A=(8/13,3,1,1),
    V_B=(24/13,1,3,1),
    V_C=(20/13,1,1,3).                             (N15)

Every active child is indifferent at its own singleton1. In particular
player3 at A has Quit1=Continue V_B,3; at B its passive Continue value
is (2/3)u₃(1)+(1/3)V_C,3=1. The nine passive tests are

    A: Q₀≤1−2ε/3≤8/13,  Q₁≤1+2ε/3≤3,  Q₂≤1=V_A,2;
    B: Q₀≤1+2ε/3<24/13, Q₂≤1+2ε/3≤3,  Q₃≤1=V_B,3;
    C: Q₀≤1<20/13,      Q₁≤1=V_C,1,   Q₃≤1+2ε/3≤3.

The three active child Continue endpoints are respectively V_B,3,
V_C,1 and V_A,2, all1; their Quit endpoints are their own singleton1.
The pivot's A Quit bound is1−2ε/3≤8/13 exactly when ε≥15/26.
At B its bound1+2ε/3≤5/3<24/13, and at C its bound1≤20/13.
This proves the same full endpoint inequalities for the child-only exit.
The ε=15/26 boundary is included directly, not by an assertion that
exact proper four-player profiles persist to that boundary.

## Actual realization, complete behavioral replies and fixed horizons

In either branch each child has one proper hazard per three-row period.
In the low branch the pivot also has a proper hazard. The displayed
Bellman recursions are a contraction over a whole period, with survival
factor ρ=(1−p)(1−y)(1−z)(1−w)<1. Their unique bounded solution
is therefore the actual vector of eventual absorption rewards: iteration
leaves a remaining annotation multiplied by ρⁿ→0. In particular these
are realized payoffs, not only consistent annotations.

Deleting ANY player still leaves at least two proper opponent hazards
per period. Let

    ρ₀=(1−y)(1−z)(1−w),
    ρ₁=(1−p)(1−y)(1−w),
    ρ₂=(1−p)(1−y)(1−z),
    ρ₃=(1−p)(1−z)(1−w).                             (N16)

All four numbers are strictly below1, including p=0 in the high branch.
The opponents' calendar is fixed conditional on the unique live history.
No change of the deviator's behavior changes their conditional private
coins. Therefore the probability that opponents alone are quiet through
n complete periods is ρ_iⁿ, uniformly over EVERY history-dependent
behavioral replacement. Actual absorption can only occur sooner.

Each action's one-step reward-plus-continuation endpoint is≤the current
displayed value. Iterating that inequality for n periods bounds any
deviation by its initial phase coordinate plus an error≤2Mρ_iⁿ,
where M bounds all finite rewards and phase values. Letting n→∞
proves exact terminal Nash. It includes Never and unbounded delayed
stopping. On path equality and the contraction identify the displayed
initial target, so the comparison is to an actual payoff.

For arbitrary signed original own levels and row scales, define actual
phase values s_i+k_i(V_i−1), where V is a canonical actual phase vector.
All Bellman/action comparisons retain their direction and equality because
all current reward and continuation masses sum to1. Opponent contraction
also implies absorption almost surely under every unilateral deviation.
Thus the terminal constant shift contributes exactly s_i−k_i to every
response, not a variable Never mass. This is why the signed-row extension
is valid here; it is not a general affine invariance claim.

Now let M=max_{S,i}|r_i(S)| for the original finite table. The actual
values, already realized, also have absolute value≤M. If T is the
absorbing-action date numbered from0, then the first N state payoffs
contain (N−T−1)⁺ copies of r(S). Consequently

    |terminal−N-average|≤M min(T+1,N)/N.

For any unilateral replacement, summing the opponent-only survival tail
over three-date blocks gives E[T+1]≤3/(1−ρ_i). Set

    C=3M max_i 1/(1−ρ_i).

The same bound works on path because ρ≤ρ_i. The profile's N-average
payoff differs from its one fixed initial target by at most C/N; every
unilateral N-average payoff is at most that player's target+C/N.
Hence actual N-average Nash error is≤2C/N for every N≥1. One fixed
profile and one target supply every requested accuracy at all sufficiently
large horizons. No exact finite-horizon Nash assertion is made.

The directly inspected strategic consumers with this semantics are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. The proof
above supplies all their mathematical ingredients without assuming the
certificate or running Lean here.

## Signed-own and negative-target test

Apply the original row extension to the complete rational table with

    s=(−3,−5,−1,−4),          k=(1,2,3,4).

The selected low-ε target is exactly

    (−3−εy, −5+2(3y−p), −1, −4−4εp).

Every coordinate is negative: in particular 3y−p<2, so the second
coordinate is<−1. The complete transformed table still satisfies all
literal raw conditions. Never is zero but does not evade the negative
target: the other players' two or three proper hazards force absorption
almost surely after ANY unilateral replacement, with the same geometric
bound. Thus the exact terminal Nash and uniform target are valid in the
original signed game. This is a direct instance of the produced policy,
not a normalization argument which forgets a positive Never probability.

At the other raw boundary, ε=1, set every capped coordinate to its (N2)
upper bound and every unrestricted coordinate to37. The child-only
vectors (N15) and all displayed endpoint inequalities remain valid: no
unrestricted reward coordinate enters the deviating player's payoff
under one unilateral replacement of the produced schedule. For example
the signed extension s=(−5,2,−7,0), k=(2,1/3,5,7/2) has initial target
(−75/13,8/3,−7,0). This directly tests binding caps, zero target, mixed
own signs and arbitrarily large unused rewards. The ε=15/26 endpoint
has a binding pivot-A comparison, covered by the same child-only proof.

## Complete finite-screen survivor and bounded major-source comparison

Take ε=100/729, P=629/729, E=829/729, all own levels1 and scales1.
The full sixty-coordinate table is

| S | u(S), in order0,1,2,3 |
|---|---|
| 0 | (1,0,0,0) |
| 1 | (2,1,4,0) |
| 2 | (2,0,1,4) |
| 3 | (0,4,0,1) |
| 01 | (E,P,3,−1) |
| 02 | (1,−1,P,3) |
| 03 | (P,3,−1,P) |
| 12 | (3,1,E,3) |
| 13 | (1,E,3,1) |
| 23 | (1,3,1,E) |
| 012 | (E,P,1,2) |
| 013 | (1,1,2,P) |
| 023 | (P,2,P,1) |
| 123 | (2,E,E,E) |
| I | (1,1,1,1) |

Formula (N1) and all twelve literal caps are verified directly from the
complete table. Equivalently, put f=(1,3,1,2), a=(3,0,0,0) and use
(N17): a participant's reward is1+ε(1_{f(i)∈S}−1_{a(i)∈S}); a
nonparticipant's reward is1+∑[j∈S]Γ_ij. The strategy proof uses no
assertion that a positive global semantic minimum exists at this table.

Its singleton comparison matrix is

    Γ=((0,1,1,−1), (−1,0,−1,3),
       (−1,3,0,−1), (−1,−1,3,0)).                 (N17)

The pair principal determinants in order01,02,03,12,13,23 are
(1,1,−1,3,3,3); triple determinants012,013,023,123 are
(−2,−4,4,26), and full determinant13. Each column has a negative
off-diagonal entry. Thus every nonzero homogeneous complementary support
is impossible and Γ is R0. At offset−1 all pair active solutions have
a negative coordinate, the first three triple solutions are respectively
(−5/2,−1/2,3/2), (−7/4,3/4,−1/4), (−1/4,1/4,−3/4), and the
123 solution(1/2,1/2,1/2) has omitted residual−1/2. The sole root is
the full vector1, with determinant13>0, giving degree1 rather than a
degree-not-one source exit. The exact implemented root-sum interface is
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`.

Its inverse is

    Γ⁻¹=((2,5/13,−11/13,−7/13),
          (1,4/13,−1/13,−3/13),
          (1,3/13,−4/13,1/13),
          (1,7/13,−5/13,−2/13)).                  (N18)

Column3 has mixed signs, so no column sign changes make the full inverse
positive. This defeats the signed-column producer and the positive-inverse
producer under every permutation and positive row scaling. The favorite
graph also is not a bijective matching: row0 has TWO positive comparisons,
while the other rows have one each. It fails both the strict and weak
matching favorite graphs in `PairedCycle.CrossedMatching.RawSource` and
`WeakRawSource`, and hence the actual implemented raw producers
`exists_uniformEquilibriumPayoff` and
`exists_uniformEquilibriumPayoff_of_weak` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.

The only pair with BOTH nonnegative joining coefficients is03:
its two coefficients are1−ε>0. Every other pair has one strictly
positive and one strictly negative coefficient. In particular no pair
partition has four nonnegative joining coefficients, and no pair has
two negative coefficients. This defeats every relabeling of the accepted
two-pair weak-joining producer, below-floor two-pair producer and
opposite-sign matching producer. It also defeats every triple–singleton
collision-box choice, which needs all six within-triple pair joins positive.

The proper premium trap is123 and the greatest premium core isI: the
trap123 together with player0's positive premium at01 makesI a trap.
There are no pair traps and no other proper triple trap. Inside the
cyclic child123 each directed favorite comparison has joining ε−3<0, the
reverse comparison has joining1>0, and all three two-opponent joining
coefficients are ε−2<0. This is precisely a no-good triple-join child,
not the two-good-row collision-box geometry.
Both accepted triple-core criteria already fail because the greatest core
has size4. Their within-child tests fail separately: joining-attractive
joining is false, and the mixed-sign
triple-core criterion needs one mutually nonnegative pair and two mutually
nonpositive pairs, plus two zero two-opponent joining coefficients; it
fails every relabeling here. Each player has a negative participant premium
at its adverse pair, so the protected set required by common/support-
specific leaver criteria is empty. The boxed and mixed-trap charge tests
fail since, for example, the trap123 has positive singleton premium sum
P_{123}({1})=ε>0 instead of a strictly negative sum. The weighted-floor
criterion also fails at the global background S={0}: every child has
participant premium−ε there, so EVERY positive child weight has strictly
negative weighted forced-Quit excess.

The smaller- and larger-eigenvalue signed four-clock producers also
fail under every cyclic ordering. Their raw prerequisite is a positive
predecessor comparison Γ_i,i−1 for every row. But column0 has NO
positive off-diagonal entry, so no predecessor cycle can pass through0.
The inspected literal interface is `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
no spectral computation is needed after this prerequisite fails.

The earlier paired-cycle raw region fails too: each child has two
singleton rewards strictly below its own singleton. The source lemma
`PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` forces
every such quitter to equal the unique scheduled partner. Two distinct
below-own quitters make that impossible. This also excludes its positive
row-affine transports, which preserve both strict comparisons.

For the actual cyclic-child singleton exits, the only column whose three
off-diagonal entries are negative is column0. Therefore any raw cyclic-
child table with positive three pivot harms must use pivot0. Order its
children as3,1,2. The positive cycle parameters are a=b=c=3, all
three harms1, and exterior singleton parameters(u,v,R)=(0,2,2).
Its resonance is1, not2. Its passive inverse numerators are(7,−5,11),
so the high passive exit fails. The low-degree exit requires R<1 and
fails. Under either other cyclic ordering the inverse weights are merely
permuted, and R−resonance stays1; those exits fail there too.
The other child deletions do not have nonnegative inverses: using the
original player labels, the inverse after deleting1 has its
entry(0,2)=−3/4, after deleting2 its entry(0,0)=−3/4, and after deleting3
its entry(0,0)=−3/2. Together with the negative outside weight after
deleting0, these exhaust the four three-child passive-inverse source tests.

The exact inspected declarations are `CyclicChildSingleton.RawRows`,
`exists_uniformPayoff_of_resonance` and `resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`;
`exists_uniformPayoff_of_passiveNumerators`,
`exists_uniformPayoff_of_passiveThreshold` and `outsideInverseWeight_eq`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`;
and `exists_uniformPayoff_of_below_resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildLowDegreeExit.lean`.

Every child i has u_i(0i)−s_i=−ε<0. Consequently ALL choices of
the pivot's scheduled partner fail the nonnegative η hypothesis of
`Math.CyclicChildJointPhase.JointPhaseData` in
`MathUE/CyclicChildJointPhasePivot.lean`. The partner3 used here also
has negative pivot premium ξ=−ε and positive passive collision reward2.
The literal implemented raw one-joint and all-pivot producers are
`CyclicChildJointPhase.exists_uniformPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean` and
`exists_uniformPayoff_all_pivots` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSingletonExits.lean`.
Their ξ>0/η≥0/q₂≤0 hypotheses are not satisfied. The accepted positive-
premium two-joint and zero-premium/repeated-solo-buffer classes likewise
cannot use any pivot partner, because all three child pivot premiums are
strictly negative. This is failure of their finite raw producer hypotheses,
not a statement that no other three- or four-phase policy exists.

The actual punishment value at the complete table is P for every player:
all participant rewards are at leastP, so Quit immediately guaranteesP;
its adverse player quitting surely yields passive reward0 and joiningP,
so the full response cap isP. The finite-game proof below shows every root
at continuation(P,P,P,P) is fully proper, with unique hazards
(1/10,1/10,1/10,1/10). A sure-base extension of ANY
complementary finite Nash law with admissible member/punishment floors
would instead give a root with a sure coordinate. Hence ALL fifteen full-
carrier concrete persistent-base criteria fail at this table, not merely
some manually chosen induced profile. Their actual named interfaces are
`exists_uniformPayoff_or_singletonBase_pos_gap` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
This concrete screen exclusion distinguishes the producer from the
singleton punishment-tail construction.

## Actual response-quotient source screens

The quotient comparison does not assert that all coarse response
invariance fails. In fact the relevant finite necessary singleton row
identities retain two coarse partitions as well as the discrete one.

For any partition into nonempty blocks, response invariance requires equal
singleton row sums over EACH block for every two recipients in the same
block. The exact prerequisite is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
It suffices to test those necessary identities, even allowing arbitrary
positive playerwise row scaling DΓ. Since every row of Γ sums to1,
summing the required identities over all blocks forces the row scales
equal within every block. Thus scaling cannot add partitions here.

No pair block except03 has equal self-block row sums: its two reciprocal
entries have opposite signs. Block03 can agree on its two outside columns
only if1,2 are in the same block, since their separate column values are
(1,−1) and(1,3); but block12 has unequal self sums−1,3. Among triples
containing0, the self sums in increasing player order are respectively
(2,−2,2), (0,2,−2), (0,−2,2), and cannot agree. This excludes every
nontrivial partition containing0 in a proper nonsingleton block. With0
singleton, every child pair again has opposite-sign self sums. The only
remaining partitions are therefore

    discrete,               {0}|{1,2,3},               indiscrete.

Their quotient matrices, up to positive row scaling, are respectively

    Γ,                      [[0,1],[−1,2]],             [1].

The full Γ is R0 of degree1 by the exact census above. For the middle
matrix Q, a nonzero homogeneous solution would force x₁>0 and
x₀=2x₁>0, contradicting the active first row x₁=0; hence Q is R0.
At offset−1 its first residual is x₁−1, so every solution has x₁≥1.
The second active equation gives x₀=2x₁−1>0, the first then gives
x₁=1, and x₀=1. The sole regular root has determinant1, so its degree
is1. The matrix[1] is likewise R0 with unique offset−1 root1 and
degree1. Positive row scaling preserves the homogeneous complementary
zero set and its isolation; a positive diagonal homotopy therefore preserves
each degree. All three determinants are positive after any such scaling.
The middle inverse is[[2,−1],[1,0]], with a negative entry; the full
inverse has the mixed signs already displayed.

Consequently no candidate partition passes either the quotient-degree-
not-one producer or the negative-determinant/nonnegative-inverse producer.
The exact inspected declarations are
`exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`
(it requires quotient R0 degree≠1), and
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
(it requires a negative determinant and nonnegative inverse).
An interface consuming an independently supplied NONZERO quotient fixed
point is different and is not excluded by this finite raw-source test.

## Exact all-base screen, not a selected-law test

Write h,x,y,z for the singleton-clock hazards of players0,1,2,3;
these symbols in this paragraph are NOT the selected phase rates above.
Set A=1−ε and B=3−ε. At continuation(P,P,P,P), the literal child
Quit-minus-Continue gaps are the cyclic rotations of

    g₁=ε(1−h)(1−y)(1−z)+Ah+y−Bz.                 (N19)

The pivot gap is

    g₀=−Ax−y+Az+ε(1−x)(1−y)(1−z).                 (N20)

Here the fixed ε=100/729 is strictly below1/2, so A>ε>0 and B>2.
For any fixed h∈[0,1], no child can be quiet: if x=0, its Nash
condition g₁≤0 forces z>0, since the expression at z=0 is strictly
positive. Positive z requires g₃≥0 and hence

    By≤ε(1−h)(1−y)+Ah≤max(ε,A)<1.

But g₂=ε(1−h)(1−z)+Ah+z>0 then forces y=1, a contradiction.
Rotate this argument for either other quiet child. No child can be sure
either: x=1 makes g₂=Ah+z−B≤−1, contradicting positive y. Thus all
three child gaps equal0 and every child hazard is proper.

With C=ε(1−h), each child equation solves one hazard as the same map

    φ_h(r)=[C(1−r)+Ah+r]/[B+C(1−r)].              (N21)

Its derivative is positive: it equals
[1−C(1−φ_h(r))]/[B+C(1−r)]. A strictly increasing real function
has no nonconstant three-cycle, so x=y=z=r(h). The unique r(h)∈(0,1)
satisfies

    ε(1−h)(1−r)²+Ah−(B−1)r=0.                    (N22)

The left side strictly decreases in r and has opposite endpoint signs.
It strictly increases in h, because A−ε(1−r)²≥1−2ε>0, so r(h)
is strictly increasing and continuous. The choice
ε=(1/10)/(9/10)³ makes r(1/10)=1/10 and makes the pivot gap zero.
Indeed at the common child hazard it is exactly
g₀=ε(1−r(h))³−r(h), strictly decreasing in h.
Its values at h=0 and h=1 are therefore respectively positive and
negative, excluding both boundary pivot hazards. This proves the unique
full cube root and, importantly, the absence of ANY sure-coordinate root.

For |E|≥2, a complementary product Nash point whose expected joining
gap is nonnegative for every member would extend to a cube Nash root
with all E coordinates sure; a remaining member supplies certain opponent
absorption, so the continuation annotation is irrelevant. For E={i}, the
actual owner Continue value at annotationP is its nonempty passive
expectation plus the quiet event multiplied byP. Nonpositive singleton
floor excess is exactly its Nash inequality when it is sure. Complementary
players already optimize in their induced finite game. Thus this extension
too would be a sure-coordinate root, contradicted above. This checks EVERY
induced Nash law at EVERY base, not a specific law chosen for convenience.
Compactness of each finite Nash set gives a strictly positive minimum gap.
The same contradiction also covers every partial free carrier: a nonpositive
concrete excess includes the missing outsiders' Continue optimality, so it
again extends to a FULL sure-coordinate cube root atP. Thus no disjoint
base/free choice is accepted, not only the fifteen full-complement screens.

## Conditional range, influence and all child-carrier screens

The literal conditional reward-range adapter fails without a search over
hazard boxes. Each child has a passive singleton reward4, so any allowed
Continue-upper bound is≥4. Every participant reward of that child in the
complete table is≤1+ε<4. Every lower blocker mixture is therefore≤1+ε,
because its mixture probability lies in[0,1]. The required strict lower
face comparison Continue-upper<lower-Quit-mixture is impossible for ANY
blocker and ANY lower/upper box. The inspected source definition is
`IsQuittingConditionalFaceGapRange` and its raw producer is
`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`, both in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
This excludes that coarse raw range adapter, not the broader supplied-face
certificate interface.

The fixed-sign influence source fails literally. Let Δ₁(T) be player1's
membership joining gain, with empty background reward0. Its influence
from player0 is

    Δ₁({0})−Δ₁(∅)=−ε<0,
    Δ₁({0,2})−Δ₁({2})=1−ε>0.                       (N23)

The two backgrounds both omit players0,1. Thus
`SignConsistentQuittingInfluence` is false, under all relabelings. Its
definition, `quittingPairInfluence`, and the producer
`exists_isQuittingSureExitSet_of_cycleBalancedSignConsistentInfluence`
were inspected in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`.
The affine membership-gain prerequisite of the componentwise weighted-
potential source also fails: its bias would be1, its coefficients from
players0,2 would be−ε,0, predicting Δ₁({0,2})=1−ε rather than the
actual2−ε. The exact prerequisite is `IsAffineQuittingMembershipGain`
in `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

There is a stronger intrinsic exclusion of all raw universal child quiet-
lift certificates. For EACH nonempty proper child carrier C, the following
table gives an exact full-behavior terminal Nash profile in the deleted
child game, with zero joint Never mass. Its indicated outside player has
a strictly positive full-game deviation gain after the quiet lift.

| Child C | Exact child profile | Outside player | Positive outside gain |
|---|---|---|---|
| 0 | sure0 | 1 | 1−ε |
| 1 | sure1 | 3 | 1 |
| 2 | sure2 | 1 | 1 |
| 3 | sure3 | 2 | 1 |
| 01 | sure1 | 3 | 1 |
| 02 | sure2 | 1 | 1 |
| 03 | sure0,3 | 2 | 2−ε |
| 12 | sure1 | 3 | 1 |
| 13 | sure3 | 2 | 1 |
| 23 | sure2 | 1 | 1 |
| 012 | sure1 | 3 | 1 |
| 013 | sure0,3 | 2 | 2−ε |
| 023 | sure2 | 1 | 1 |
| 123 | solo3,1,2 cyclic, each hazard2/3 | 0 | (15−26ε)/39 |

For every sure-singleton row, the child's nonsure members have joining
gap either ε−1,−1 or ε−3, all negative, and the sure child's own1
dominates Never0 and all delayed own1 responses. For a sure03 row,
both owners have joining gap1−ε>0; the possible remaining child1
has joining gap1−3=−2. Thus each displayed pure child profile is exact
terminal Nash against all behavioral replies. In child123 the cyclic
profile is the child part of (N15). Its passive Quit centered values are
0 or2ε/3≤2, its active children are indifferent at1, and every deleted-
player cycle contracts. It is therefore exact full-behavior terminal Nash
too, even when ε<15/26 and the pivot would spoil the quiet lift.

For the cyclic child, the outside pivot's initial quiet payoff is8/13;
Quit immediately gives1−2ε/3, hence the stated positive gap. All other
rows use the indicated positive joining gap at date0. In every row the
child debt vector is zero and the child joint Never probability is zero.

The exact common consumer is
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
It bounds this literal outside full-behavior debt by a nonnegative weighted
sum of ALL child debts plus Never-excess times the actual child joint
Never probability, for ANY supplied child profile. Therefore the fourteen
displayed profiles contradict the consumer for every source kind:
patient, deadline, evaluated security, terminal security and cancellation.
The kinds and their literal finite F/J certificates are
`WithdrawalFutureJoinKind` and `WithdrawalFutureJoinRewardCertificate`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
Advancing-only capped-clock certificates are their zero-withdrawal subcase;
the independent advancing-only theorem inspected was
`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`.
Consequently no such certificate family can cover ANY child carrier at
this complete table. This is a source-hypothesis exclusion, not merely
failure to find weights numerically.

For a finite-row cross-check at child123, write λ₁,λ₂,λ₃≥0 for its
advancing weights. The three singleton future rows are

    F(1): −1≤−3λ₂+λ₃,
    F(2): −1≤λ₁−3λ₃,
    F(3):  1≤−3λ₁+λ₂.

Combining F(2)+3F(1)+9F(3) gives5≤−26λ₁, impossible. At child023
the sole future row T={2} gives1≤−λ₀−3λ₃; at child012 the sole
row T={1} gives1≤−λ₀−3λ₂. At child013 the joining row T={0,3}
gives2−ε≤−2λ₁. These agree with the intrinsic zero-debt witnesses.
The broader withdrawal exclusion uses the common actual debt consumer,
not an unsupported claim that withdrawal and advancing weights coincide.

## Actual-data adapter, source correspondence and Lean handoff

The actual-data adapter consists solely of checking (N1)–(N2), selecting
the low-ε scalar root or the high-ε explicit child rates, and substituting
the displayed phase values. The reward table is retained literally;
unused rewards are neither replaced nor bounded. The signed adapter
applies the explicitly proved action-level row transformation, with
opponent-only absorption ensuring that Never contributes no exceptional
mass. No no-UE normalization is needed.

For implementation, a raw-data proposition should contain only the five
reward-row equalities and twelve caps, together with 0<ε≤1. A separate
mathematical theorem should produce p,y,z,w and their interval bounds,
the two balance equalities, and the three actual value vectors; these
must not be assumed as fields of the raw-data proposition. The low
branch can first formalize the strictly concave quadratic crossing and
its continuous selected root, then the single-variable intermediate
value argument (N7)–(N11). The high branch is rational arithmetic.

Use `GameTheory.PairedCycle.root` for the joint03 product root and
`rootSuccessor_eq_bellman` in
`UniformEquilibrium/Quitting/Root/PairedProductRoot.lean` for its policy
equation. Use `quittingSoloStationaryRoot` and the owner/nonowner
endpoint formulas in
`UniformEquilibrium/Quitting/Root/SingletonRootEndpoints.lean` for the
two solo roots. The exact pure-endpoint-to-root-Nash bridge is
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, at error0.

The adapter's output must prove three policy-recursion equalities,
three exact root-Nash statements and four opponent-cycle contractions.
These are precisely the hypotheses of the two named `PeriodicCompiler`
consumers above, with K=3 and initial phase A. They yield exact terminal
behavioral Nash and `IsUniformEquilibriumPayoff none` for the produced
original-game target. Neither consumer supplies the scalar root or any
raw reward-table hypothesis. The explicit C/N and 2C/N bounds strengthen
the qualitative uniform conclusion without changing its target or
strategy quantifiers. A likely final declaration is a raw-table
existence theorem for a uniform payoff, with an additional statement
that this same cyclic profile witnesses every requested accuracy.
The new scalar producer and raw adapter are ordinary mathematics here;
the cited endpoint and periodic consumers are existing Lean declarations.

## Scope and nonclaims

The raw existence theorem (N1)–(N2), its signed
row extension, the all-sign realization and full-deviation proof, and one
fixed-profile/all-large-horizon conclusion are proved above. The complete
center lies outside the compared implemented and accepted raw producers,
including all fifteen concrete-base screens and all fourteen child-carrier
universal quiet-lift systems. This demonstrates that the whole completion
family is NOT subsumed by those producers. It does not assert
that every completion violates every other producer. No blanket exclusion
of unspecified IFT neighborhoods, all stationary equilibria or arbitrary
supplied-strategy verifiers is claimed. The producer does not classify
arbitrary nonlinear escape faces or settle all four-player quitting games.
All new mathematics here is ordinary mathematics, not a Lean verification.
