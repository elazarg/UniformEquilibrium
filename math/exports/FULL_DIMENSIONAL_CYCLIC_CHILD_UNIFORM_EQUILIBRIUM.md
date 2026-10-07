# Full-dimensional cyclic-child uniform equilibrium near a rational table

## Exact raw statement

There are four players I={0,1,2,3}. A reward table r assigns an arbitrary
finite real vector r(S) to each nonempty S⊆I, so the raw reward space is
ℝ⁶⁰. Live players choose Quit or Continue with independent private coins
and observe the public past. The first nonempty quitting coalition
absorbs. The initial and absorption-selecting date pay zero; subsequent
absorbed dates pay r(S). Never pays zero. A unilateral deviation is a
complete, unrestricted behavioral replacement.

Put e=100/729, P=629/729 and E=829/729. For each η≥0 define the
following complete raw table R^η, in player order0,1,2,3:

| S | R^η(S) |
|---|---|
| 0 | (1,0,0,0) |
| 1 | (2,1,4,0) |
| 2 | (2,0,1,4) |
| 3 | (0,4,0,1) |
| 01 | (E,P,3,−1) |
| 02 | (1,−1,P,3) |
| 03 | (P,3,−1,P) |
| 12 | (3,1−η,E,3) |
| 13 | (1,E,3,1−η) |
| 23 | (1,3,1−η,E) |
| 012 | (E,P,1,2) |
| 013 | (1,1,2,P) |
| 023 | (P,2,P,1) |
| 123 | (2,E,E,E) |
| I | (1,1,1,1) |

The sup norm of a reward difference is the maximum of its sixty absolute
coordinate differences.

**Theorem.** For every η>0 there is d_η>0 such that EVERY finite
reward table r with ‖r−R^η‖∞<d_η has an exact terminal Nash profile
repeating these three rows:

    A: joint0,3 with proper hazards p,y;
    B: solo1 with proper hazard z;
    C: solo2 with proper hazard w.

All four hazards, three actual phase vectors and the initial target
are produced from r. They can be selected smoothly throughout a smaller
reward ball. The same selected profile witnesses this one target at
every requested positive accuracy, over all sufficiently large finite
horizons and against all complete behavioral deviations. No equality or
cap on a perturbed table is assumed beyond membership in the reward ball.

The radius is qualitative: ∀η>0 ∃d_η>0 ∀r in that ball, with the
existential choices of profile and target made separately for each r.
There is no common target for distinct games, and no uniform positive
radius as η→0 is asserted.

Moreover, for every 0<η<e there is a smaller radius
b_η∈(0,d_η) such that the compared concrete persistent-base, universal
quiet-lift and finite raw phase/core criteria fail throughout that
smaller ball. Choosing a sufficiently small nonzero perturbation of
player0's singleton1 coordinate also removes the fixed-row cyclic-child
criterion;
an open subball then consists entirely of new tables relative to all
the explicitly compared raw criteria. In particular η=e/2=50/729
is one completely specified rational center for this comparison.

## Conjecture-facing change and strategic inputs

The construction removes every fixed-row equality: arbitrary perturbations
of all sixty reward coordinates are admitted simultaneously. This is a
raw open-region existence theorem, not a verifier for a supplied root
and not a generic claim about every finite four-player table.

Leaving a fixed-row surface alone would not establish new coverage.
The whole-source comparison below excludes every base/free carrier
choice and all fourteen deleted-child quiet-lift families, as well as
the other stated finite raw criteria, on a nonempty open region.
It includes both implemented producers and the explicit hypotheses of
the compared unimplemented phase/core criteria.

Inputs are only η and the raw reward table in its produced ball.
The base root, local hazard selection, phase values, terminal target,
deleted-player survival bounds and accuracy-to-horizon bound are all
produced below. No stationary root, deleted-game equilibrium, finite
Nash law, punishment profile, continuation annotation, correlated
randomization or global positive-gap witness is assumed. The produced
policy uses independent private coins and date modulo3. There is no
recursive strategy-selection step.

## Exact algebraic base root

Use the rational polynomials

    F=−(16+e−12y)p²
       +[(9e−36)y²+(32−10e)y+13]p−13y(2−3y),
    G=(6y−3−3ey)p²+(12ey²+2ey−18y²+2)p
                                      +(18−13e)y²−7y.

On the rectangle 19/100≤p≤21/100, 47/100≤y≤12/25,
termwise rational interval bounds give

    F_p>14,      F_y>9,      G_p<−1,      G_y>5.     (O2)

For explicit checks, the corresponding enclosing derivative intervals are

    F_p ∈[13441769/911250, 7430767/455625],
    F_y ∈[18049781/1822500,7406657/607500],
    G_p ∈[−3464381/1822500,−605173/405000],
    G_y ∈[18956381/3645000,7230857/1215000].

These follow by expanding each derivative as a polynomial and taking
the monomial minimum/maximum at the rectangle's positive endpoints,
with endpoints reversed for negative coefficients. There is no
floating-point inference. Moreover

    F(19/100,12/25)=−23257/182250<0,
    F(21/100,47/100)=220067/3037500>0.

Together with(O2) these give one continuous p(y) in the rectangle
solving F=0. The crossing is unique in this rectangle because F_p>0.
At the left endpoint

    F(41/200,47/100)=−352051/81000000<0,
    G(41/200,47/100)=−4464901/162000000<0,

so p(47/100)>41/200 and G at that selected p is strictly negative.
At the right endpoint

    F(199/1000,12/25)=60523229/4556250000>0,
    G(199/1000,12/25)=231741911/6075000000>0,

so p(12/25)<199/1000 and G there is strictly positive.
The intermediate value theorem gives a root in the rectangle's interior.
It is unique there because

    D=F_p G_y−F_y G_p>79,
    dG(p(y),y)/dy=D/F_p>0.                         (O3)

This determines an exact algebraic root, not a numerical or assumed
equilibrium point. Define

    z=(p+y)/[3(1−p)(1−y)],
    d=1+3y−p,             w=(3y−p)/d.

The rectangle gives 0<p,y<1, 3y−p>0 and w∈(0,1).
Also z≤(21/100+12/25)/[3(79/100)(13/25)]<1 and z>0.
Thus every scheduled hazard is proper. These depend only on the
displayed rational table, not on an externally supplied equilibrium.

## Four actual active equations and nonsingular Jacobian

For arbitrary nearby proper (p,y,z,w), let actual phase values be the
unique Bellman-policy solution. They are smooth in all hazards and all
sixty rewards: the full-period survival ρ=(1−p)(1−y)(1−z)(1−w)
is strictly below1, so each player's three linear policy equations have
an invertible coefficient matrix. Let K_i be that player's actual
forced Quit minus Continue at its scheduled active row.

At R^η, introduce

    H₁=3(1−p)(1−y)z−p−y,
    H₂=(1+3y−p)w−3y+p,
    f=p(1−e)/(1−p)+z−(1−z)[3w−ep(1−w)],
    k=(1−ey)/(1−y)−2z
                         −(1−z)[2w+(1−w)(1−ey)].

There is an EXACT identity, not merely an equivalence of zero sets,

    (K₀,K₁,K₂,K₃)
        =((1−y)k, H₂, −H₁, (1−p)f)/(1−ρ).        (O4)

To derive it, annotate each player's own active-phase value by its
forced-Quit endpoint, then propagate the other two policy rows once.
The active Quit-minus-Continue discrepancy of this annotation is,
respectively, (1−y)k,H₂,−H₁,(1−p)f. Correcting the annotation to
the actual policy value divides the discrepancy by1−ρ. This follows
directly from the scalar cycle equation V=A+ρV, and holds for every
proper hazard vector, not just at the root.

The z derivative of H₁ is u=3(1−p)(1−y)>0 and the w derivative
of H₂ is d=1+3y−p>0. After eliminating H₁,H₂, the remaining
f,k equations are F/N,G/N with N=ud. At their root the reduced
Jacobian determinant is D/N². Block elimination gives
det ∂(H₁,H₂,f,k)/∂(p,y,z,w)=D/N. Thus(O4) gives

    det ∂K/∂(p,y,z,w)
       =−(1−p)(1−y)D/[N(1−ρ)⁴]≠0.               (O5)

The three η-dependent coordinates do not affect this Jacobian or any
policy equation: they enter only the passive Quit tests, not active K
or policy values. The implicit function theorem therefore produces a smooth
proper hazard vector solving the four ACTUAL active equations for
every table in an unconditional full-dimensional reward neighborhood.

## All center policy equations and twenty-four action tests

For the complete center R^η the following twelve inequalities are direct
entries of its table; they are NOT hypotheses on nearby raw tables:

    R₁(01)≤1−e,   R₁(13)≤1+e,   R₁(013)≤1,
    R₂(02)≤1−e,   R₂(23)≤1,     R₂(023)≤1−e,
    R₀(01)≤1+e,   R₃(13)≤1,     R₂(12)≤1+e,
    R₀(02)≤1,     R₃(23)≤1+e,   R₁(12)≤1.

Write u=R^η for the original center rewards. For clarity normalize
child coordinates by subtracting their own1;
retain pivot0's canonical own1. This is algebraic notation for phase
values, not a transformation of Never. In original order0,1,2,3 the
three displayed vectors in these partly centered coordinates are

    V_A=(1−ey, 3y−p, 0, −ep),
    V_B=((1−ey)/(1−y), 0, 3z, p(1−e)/(1−p)),
    V_C=(2w+(1−w)(1−ey), 0, 0,
                              3w−ep(1−w)).        (N12)

Restore canonical actual values by adding1 to coordinates1,2,3.

At A, pivot0's forced Quit value is1−ey. Its Continue value is
(1−y)V_B,0, since u₀(3)=0, and these are equal by (N12).
Player3's centered Quit value is−ep; its Continue value is
−p+(1−p)V_B,3=−ep. Thus BOTH active joint participants are
indifferent even though both participant increments are negative.

At B, active child1's centered Quit and Continue values are both0:
the former is its singleton, the latter is V_C,1. At C, active
child2's centered Quit and Continue values are both0, because
V_A,2=0. The other policy equalities at the solo rows are exactly
the affine recursions in (N12). In particular

    V_B,3=−z+(1−z)V_C,3

is f=0, while

    V_B,0=2z+(1−z)V_C,0

is k=0. At A, the passive child1's Continue value is
3y−p because the scheduled joint reward is3 and hence the centered
joint reward is2. Child2's Continue value is0 because

    −p−y+3z(1−p)(1−y)=0.

The latter equality is H₁=0. At C, the passive child1 policy recursion is
V_C,1=−w+(1−w)(3y−p)=0, exactly H₂=0.
Therefore every prescribed Continue endpoint
and every prescribed policy value has been checked, not just four active
indifferences.

It remains to check all passive Quit endpoints from the actual raw table.
At A, the displayed center caps imply the centered child1 Quit bound

    Q₁≤−ep(1−y)+e(1−p)y=e(y−p),

including the nontrivial simultaneous outcome013. Its Continue margin is

    V_A,1−Q₁≥(3−e)y−(1−e)p>0.                    (N13)

Indeed y>2/5, p<1/2 and e≤1 imply (3−e)y−p>3/10.
At A, centered child2 Quit is≤−ep, including outcome023, hence
at most its Continue value0.

Put H=(3−e)y−p>0. Then

    V_C,0−1=H/d>0,
    V_C,3−ew=3H/d>0.                              (N14)

At C the pivot's Quit cap is1 and child3's centered Quit cap isew,
so these are the exact needed margins. The other passive player1 has
centered Quit cap0 and Continue value0.

At B, the pivot's Quit cap is1+ez. Its actual Continue value is
2z+(1−z)V_C,0≥1+z≥1+ez. Child2's centered Quit cap isez≤3z,
and child3's centered Quit cap is0≤p(1−e)/(1−p).
This exhausts both actions of every player at all three rows. A passive
comparison was never replaced by an own-singleton floor at the negative
joint phase.

## Persistence of every passive test

At R^η all eight passive comparisons are STRICT. The A1 comparison has
the positive margin in(N13); A2 has at least ep>0. At B, pivot0's
actual value is strictly above1+z, child2 has margin(3−e)z>0,
and child3's Continue increment p(1−e)/(1−p)>0 while Quit is at
most0. At C, pivot0 and child3 have the strict margins in(N14).
The remaining C1 comparison has exact margin ηw>0, since
R₁(12)=1−η while its actual Continue value is1.

Thus the smooth hazard and actual-value selection produced by the
implicit function theorem continues to satisfy all passive inequalities
on a sufficiently small FULL sixty-dimensional reward ball. Active
gaps vanish by construction. The policy equalities are those of actual
values, not imposed annotations. This proves all24 action tests for
every nearby original reward table, whose singleton and collision rows
may all vary freely.

## Actual realization, complete behavioral replies and fixed horizons

Each player has a proper scheduled hazard per three-row period. The displayed
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

All four numbers are strictly below1.
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
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The proof supplies all their mathematical hypotheses; the raw local
producer is new ordinary mathematics, not assumed certificate data.

## Complete whole-source comparison at R^0

For these calculations set η=0 in the displayed complete table and write
ε=e. Equivalently, put f=(1,3,1,2), a=(3,0,0,0).
A participant's reward is1+ε(1_{f(i)∈S}−1_{a(i)∈S}); a
nonparticipant's reward is1+∑[j∈S]Γ_ij, with Γ below.
No positive global semantic minimum is asserted at this table.
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
at its adverse pair, so the protected set (players with every participant premium nonnegative)
required by common/support-specific leaver criteria is empty. The boxed and mixed-trap charge tests
fail since, for example, the trap123 has positive singleton premium sum
P_{123}({1})=ε>0 instead of a strictly negative sum, where
P_C(T)=∑[i∈C](r_i(T∪{i})−r_i({i})). The weighted-floor
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

The actual punishment value at the table R^0 is P for every player:
all participant rewards are at leastP, so Quit immediately guaranteesP;
its adverse player quitting surely yields passive reward0 and joiningP,
so the full response cap isP. The finite-game proof below shows every root
at continuation(P,P,P,P) is fully proper, with unique hazards
(1/10,1/10,1/10,1/10). A sure-base extension of ANY
complementary finite Nash law with admissible member/punishment floors
would instead give a root with a sure coordinate. Hence ALL fifteen full-
carrier concrete persistent-base criteria fail at R^0, not merely
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

## Exact all-base exclusion for every 0≤η<e

The following proof is for R^η itself, not just R^0. Every participant
reward is at leastP when0≤η<e, and each player's adverse sure opponent
still caps its complete response atP. Thus the actual punishment values
are exactlyP. In particular this is true at the rational center
η=e/2=50/729, where the three lowered entries are679/729.

Write h,x,y,z for singleton-clock hazards of players0,1,2,3; these
are NOT the selected cyclic-profile rates. Put A=1−e, B=3−e and H=1−h.
At continuation(P,P,P,P), the child Quit-minus-Continue gaps are cyclic
rotations of the exact polynomial

    g₁^η=eH(1−y)(1−z)+Ah+y−Bz−ηH y(1−z).          (Q1)

The last term is precisely the single lowered participant reward1−η
on coalition12, occurring when0 and3 Continue. The pivot's gap is
unchanged:

    g₀=−Ax−y+Az+e(1−x)(1−y)(1−z).                (Q2)

Since e<1/2 and η<e, one has A>e, B>2 and e+η<1.
No child can be quiet. For example x=0 and g₁^η≤0 force z>0:
at z=0 the gap is eH(1−y)+Ah+(1−ηH)y>0.
Positive z requires g₃^η≥0, and its η term vanishes when x=0.
Consequently By≤eH(1−y)+Ah≤max(e,A)<1.
But g₂^η=eH(1−z)+Ah+(1−ηH)z>0 forces y=1, contradiction.
Rotate this argument for the other two children.
No child can be sure either: x=1 makes g₂^η=Ah+z−B≤−1,
contradicting positive y. Therefore every child is proper and has zero gap.

Each child equation solves its successor hazard as the same map

    φ_h^η(r)=[eH(1−r)+Ah+(1−ηH)r]
                          /[B+eH(1−r)−ηH r].                   (Q3)

Its denominator is positive and φ∈(0,1) on[0,1]. Indeed the denominator
minus the numerator is B−Ah−r≥B−A−1=1.
Differentiation gives

    dφ/dr=[1−(e+η)H+(e+η)H φ]/[B+eH(1−r)−ηH r]>0.

A strictly increasing real map has no nonconstant three-cycle, so
x=y=z=r(h). The fixed-point equation is

    eH(1−r)²+Ah−(B−1)r−ηH r(1−r)=0.              (Q4)

The left side is strictly decreasing in r: its derivative is at most
−(B−1)+η<0. Its endpoint signs are positive at0 and negative at1.
Its h derivative is A−e(1−r)²+ηr(1−r)≥1−2e>0.
Thus its unique r(h) is continuous and strictly increasing.

At equal child hazards, g₀=e(1−r(h))³−r(h), strictly decreasing in h.
It vanishes exactly at r=1/10 because e=(1/10)/(9/10)³.
Substituting r=1/10 in(Q4) gives the unique pivot hazard

    h_η=(274/3645+9η/100)/(548/729+9η/100)∈(0,1).   (Q5)

The numerator is positive and smaller than the denominator, and the
strict increase of r(h) excludes the boundary pivot hazards.
Hence the ONLY Nash root of the full punishment-priced cube is

    (h_η,1/10,1/10,1/10),

with every coordinate proper. At η=e/2 it is exactly
(593/5525,1/10,1/10,1/10). No sure coordinate exists.

For any base of size≥2, an induced complementary Nash point with all
member expected joining gaps nonnegative would extend to a cube Nash
root whose base coordinates are sure. Another sure member eliminates
the owner's empty-opponent event, so continuation pricing is irrelevant.
For a singleton base, its actual owner-floor inequality is precisely
the owner's Continue inequality with empty event priced at the trueP.
The free Nash inequalities hold already. An omitted outsider's concrete
component is its missing Continue inequality. Therefore ANY accepted
point at ANY full or partial free carrier would extend to a FULL
sure-coordinate cube root, contradicted above.

This checks every induced Nash law, every nonempty base and every
disjoint free carrier. Each compact Nash set has a strictly positive
attained excess minimum. The exact implemented source declarations are
`exists_uniformPayoff_or_singletonBase_pos_gap` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
No selected-law or stationary-Never surrogate is used.

## Conditional range, influence and all child-carrier screens

The literal conditional reward-range adapter fails without a search over
hazard boxes. Each child has a passive singleton reward4, so any allowed
Continue-upper bound is≥4. Every participant reward of that child in the
table R^0 is≤1+ε<4. Every lower blocker mixture is therefore≤1+ε,
because its mixture probability lies in[0,1]. The required strict lower
face comparison Continue-upper<lower-Quit-mixture is impossible for ANY
blocker and ANY lower/upper box. The inspected source definition is
`IsQuittingConditionalFaceGapRange` and its raw producer is
`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`, both in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
This excludes that coarse raw range adapter, not the broader supplied-face
certificate interface.

The literal odd-interval blocker-core adapter fails as well. An embedded
odd core in four players with size at least3 has size3 and contains a
child i∈{1,2,3}. Its literal continuation maximum C_i⁺ is at least4,
from that child's passive singleton. Its blocker-absent Quit minimum
H_i⁻ is at most its own singleton1, since the defining background set
includes the empty set. Thus the required strict inequality C_i⁺<H_i⁻
is impossible for every embedding and cyclic blocker choice. This
persists under arbitrary small reward perturbations, with margin at least3
at the center. The exact inspected definitions are
`finiteOddCoreContinuationUpper`, `finiteOddCoreBlockerAbsentQuitLower`
and `IsLiteralStrictFiniteOddIntervalBlockerCore`; its consumer is
`isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore`,
all in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`.
This is an exclusion of its literal finite row-extrema producer, not of
every supplied stationary face certificate.

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
terminal Nash against all behavioral replies. For child123, the cyclic solo3/solo1/solo2 profile has actual full-game
quiet-lift values

    V_A=(8/13,3,1,1),
    V_B=(24/13,1,3,1),
    V_C=(20/13,1,1,3).

These follow by substituting the three solo hazards2/3 in each policy
recursion. The three active child Continue endpoints equal their own1.
Its passive Quit centered values are0 or2ε/3≤2, and every deleted-
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
this table R^0. This is a source-hypothesis exclusion, not merely
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

## Whole-source stability and a nonempty new open class

The preceding calculations and the exact all-base argument imply every
stated source failure at EACH R^η with0<η<e, not at one selected
equilibrium law. We now give the stability argument needed for a
full-coordinate region around any such center.

For each nonempty base B and disjoint free carrier F, the induced finite
product-Nash set is compact and has a closed graph as a function of reward
data. Indeed every mixed point belongs to a fixed compact product simplex,
and its finitely many unilateral endpoint inequalities are continuous
polynomials in rewards and probabilities. A convergent sequence of
induced Nash points is therefore Nash at the limit table.

The actual punishment value is1-Lipschitz in the sup reward norm:
for any fixed opponent strategy and complete response, terminal payoff
changes by at most the reward perturbation, since its absorption weights
are nonnegative and sum to at most1, with Never reward0 unchanged.
Taking the supremum over responses and then the infimum over opponents
preserves this bound. These are the literal minmax quantifiers of
`quittingPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
Hence every singleton owner-floor and large-base component screen is
continuous jointly in rewards and mixed points.

At R^η every actual induced-Nash point at every carrier has strictly
positive excess by the sure-coordinate contradiction already proved.
Compactness gives a positive attained minimum for each fixed carrier.
There are65 disjoint choices (B,F) with B nonempty, including every
partial free carrier. If tables converged to R^η with an accepted point
at any carrier, pass to one carrier and a convergent subsequence of its
Nash points. Closedness and screen continuity would give an accepted
point at R^η, a contradiction. Thus a whole reward neighborhood of R^η
excludes ALL persistent-base choices and all their Nash laws.
No stationary-Never floor is substituted for the real punishment value.

The pure deleted-child profiles in the table above persist as EXACT
terminal Nash under small arbitrary reward perturbations. Their nonsure
members have strict negative joining gaps; the sure singleton owner has
positive own reward, and both sure03 owners have strictly positive joining
gaps. An owner deviating cannot avoid another sure owner except in a
sure-singleton profile, where Never0 and all late own-singleton exits
are weakly worse than the earliest positive own payoff.
Their indicated outside gains are strictly positive and continuous.
Child debts remain zero and joint Never probabilities remain zero.

For the only mixed child, C={1,2,3}, use solo3/solo1/solo2.
Writing z,w,y for its own hazards and annotating each active coordinate by
its singleton, the three active-gap numerators at R^0 are

    L₁=1−(1−w)(1+3y),
    L₂=1−(1−y)(1+3z),
    L₃=1−(1−z)(1+3w).

At z=w=y=2/3 their Jacobian is

    [[0,3,−1],[−1,0,3],[3,−1,0]],       determinant26.

The actual gaps divide these numerators by the positive cycle factor
1−(1−z)(1−w)(1−y); the actual Jacobian is consequently nonsingular.
The implicit function theorem produces an exact proper child root under
arbitrary nearby reward changes. At R^η the same hazards and values
remain: the three η-dependent pair entries affect only passive Quit.
Their formerly binding low-value passive margins become2η/3>0,
while all three high-value passive margins are strictly positive already.
Thus for every fixed η>0 all six passive child tests remain strict nearby.
The full behavioral contraction proof supplies an exact terminal child
Nash profile, not only a local active root. Its quiet-lift pivot gain
(15−26e)/39 remains strictly positive nearby. Every child-carrier witness
therefore persists, and the universal debt/Never consumer still excludes
ALL five withdrawal kinds and advancing-only capped clocks, regardless
of their weights, floors or choice of carrier.

Every other stated finite source failure has a strict sign or nonzero
finite identity defect at R^η whenever0<η<e. The three modified
coordinates leave all singleton data unchanged. Within the child they
replace reverse joining1 by1−η>0, leave adverse/favorite joining
unchanged, and make the relevant low passive Quit tests strictly easier.
Consequently all these failures persist under sufficiently small arbitrary
reward changes. In particular:

- The singleton sign pattern, mixed inverse column and nonzero principal
  determinants persist. Γ stays R0 of degree1 under the small homotopy.
- Each pair except03 keeps one positive and one negative joining
  coefficient, while03 keeps both positive. This excludes all compared
  two-pair joining and below-floor/opposite-sign choices and every
  six-positive-pair-join triple choice.
- All child-to-pivot joint premiums remain negative; the passive inverse
  defect and resonance gap remain strict. The only possible raw cyclic
  pivot is still0. The positive-joint and zero-joint source premises
  continue to fail for every pivot partner.
- Every row still has an adverse negative participant premium, the full
  premium core remainsI, and the trap charge at singleton1 stays
  e−η>0. The negative weighted-floor background persists.
- The conditional-range and literal odd-interval separations between
  passive4 and participant
  upper bound1+e persist. The influence signs are now−e and1−e+η,
  while the affine-gain identity defect is1+η, all still nonzero.

For the response quotient, continuity includes arbitrary positive row
scaling, not only bounded or fixed scales. Let g_i be the total singleton
row sum of a nearby table; each g_i stays positive. If factors c_i>0
make the necessary identities true, summing them over all target blocks
forces c_i g_i to be common within each recipient block. Rescale that
block by this common positive number. Its normalized factors are then
EXACTLY c_i=1/g_i, independent of the partition. These converge to1
at every R^η. The remaining normalized partition identities form a
FINITE collection of continuous equalities, so a partition whose
identities fail at the center cannot become valid arbitrarily close.
The only possible three quotient matrices stay close, after this positive
row normalization, to Γ, [[0,1],[−1,2]] and[1]. R0 is open (minimize the
homogeneous complementary residual on the compact nonnegative unit sphere),
its degree is invariant along this small R0 homotopy, and all determinants
stay positive. Hence neither raw quotient exit can appear nearby.
No assertion that response invariance itself fails is used.

Finally compare the fixed-row cyclic-child criterion itself. Its
canonical singleton rows require exactly one recipient with two positive
singleton comparisons, those TWO positive comparisons EQUAL. Its other
three recipients have one positive comparison each. This necessary
equality survives any positive recipient-row affine transformation and
any relabeling: the unique two-positive row identifies its pivot.

Choose any0<η<e, for example η=50/729, and a source-exclusion radius
b_η<d_η. Modify only
player0's coordinate at singleton1 from2 to2+ζ, where
0<|ζ|<b_η/4. Call this complete table R^{η,ζ}; all its other fifty-nine
entries are those in the displayed R^η table. The new open producer
applies, but its pivot's two positive comparisons are1+ζ and1, unequal.
Therefore no such fixed-row raw criterion or positive row-affine
relabeling admits it. A full sup-norm ball about R^{η,ζ} of radius

    0<t<min(b_η/2, |ζ|/4)

retains unequal comparisons, lies within the produced UE and source-
exclusion ball, and excludes every compared criterion simultaneously.
This is a nonempty FULL-dimensional new region, not merely points leaving
one fixed-row surface. Its existence and the inequalities defining it
are qualitative; no unproved numerical value of b_η or t is asserted.

## Exact boundary and attempted-falsifier tests

At η=0 the full-game C1 passive margin is zero and the child123
low-value passive margins are zero. The implicit function theorem
alone cannot preserve those weak inequalities under every reward
perturbation. The theorem deliberately requires η>0 and makes no
full-dimensional radius assertion at η=0.

The active hazard and phase-value solution is independent of η at the
center. Thus even η arbitrarily large, making all three displayed
collision rewards negative, does not affect the base profile: those
entries enter only the deviator's passive Quit tests and improve them.
Nearby values remain actual absorbing-game values bounded by the new
reward maximum. No unknown continuation annotation is used.

The exact rational rectangle and determinant estimate above rule out
wrong selected quadratic roots and singular active crossings at this
center. All four scheduled hazards and all four opponent-only survival
factors are strict; no conclusion is extended to their zero/sure
boundaries by continuity. All simultaneous unilateral outcomes, including
013 and023 at the joint row, appear in the twelve center cap tests.

## Actual-data adapter, source correspondence and Lean handoff

The raw input is a full sixty-coordinate reward vector near the complete
table R^η. The new mathematical work produces its hazards via the exact
algebraic base root and the nonsingular ACTUAL active-gap map, then proves
every passive test and every Bellman recursion. The reward table is
retained literally. No row identity, supplied continuation or Nash
certificate is a field of the raw input.

A likely formalization separates a finite polynomial root lemma with
the rational rectangle and derivative bounds from the actual policy
map. The latter is defined by the invertible three-row Bellman system,
with four active endpoint gaps. Prove the exact identity(O4), not merely
equivalence of zero sets; then derive(O5) and apply a local implicit
function theorem in four hazards and sixty reward coordinates.
The statement should quantify ∀η>0 ∃d>0 ∀r in the sup ball,
producing three product roots and actual phase values.

Use `GameTheory.PairedCycle.root` and `rootSuccessor_eq_bellman` in
`UniformEquilibrium/Quitting/Root/PairedProductRoot.lean` for joint03;
use `quittingSoloStationaryRoot` and the pure endpoint formulas in
`UniformEquilibrium/Quitting/Root/SingletonRootEndpoints.lean` for
solo1 and solo2. The pure-to-all-mixed root bridge is
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, at error0.

The output proves three policy equalities, three exact root-Nash
statements and four opponent-cycle contractions. These are exactly the
inputs of the two named `PeriodicCompiler` consumers above, with K=3.
They yield exact terminal behavioral Nash and
`IsUniformEquilibriumPayoff none` for the one produced target.
They do NOT produce the new local raw source or its root.
All new mathematical assertions here are ordinary mathematics, not
Lean verification. No implementation reorganization is required.

## Scope and nonclaims

Every table in a produced full sixty-coordinate ball has one fixed
terminal Nash profile and one fixed uniform target, against arbitrary
behavioral deviations and over all sufficiently large horizons.
A smaller nonempty open region lies outside all explicitly compared
raw producers, including their full carrier and Nash-law selection sets.

The theorem is local in reward space. It does not classify all stationary
equilibria, show completeness of this three-row architecture, exclude
arbitrary supplied-strategy verifiers, blanket-exclude unspecified
neighborhoods of other implicit-function results, or settle arbitrary
four-player quitting games. The neighborhood radius and the new-region
separation thresholds are qualitative, not numerically optimized.
