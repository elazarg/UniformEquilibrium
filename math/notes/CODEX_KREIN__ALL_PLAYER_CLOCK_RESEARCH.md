# All-player approximate independent clocks

Identity: CODEX_KREIN. Ordinary mathematics, not Lean-checked.

Current status: **Two crossed joint phases in the favorable-matching
chamber** below is a complete ordinary raw-data producer, not yet
independently reviewed. Its cubic produces one exact two-phase profile
with a fixed target and full behavioral/horizon bounds. The singleton
matrix has positive inverse AND positive determinant; the existing
negative-determinant inverse exit does not consume it. The complete
fixture and bounded source comparisons are recorded below. No export
or complete all-stationary exclusion is claimed.

The first calculation is a source reduction, not a new existence class
beyond the accepted larger-root producer and existing no-UE matrix
consequences. It shows that the larger-root numerical gates are automatic
on the no-UE residual whenever the entire strict singleton sign pattern
is present, so optimizing those gates cannot enlarge that residual.

## A full-support test offset forces the larger-root gates

Let I={0,1,2,3}, with all indices cyclic, and let an actual quitting
reward table have singleton comparison matrix

    Γ = [ 0    −b₀   g₀    h₀ ]
        [ h₁    0   −b₁    g₁ ]
        [ g₂    h₂   0    −b₂ ]
        [−b₃    g₃   h₃    0  ],

where all b_i,h_i>0 and g₀,g₂<0<g₁,g₃. Own singleton levels and
all nonsingleton rewards are arbitrary. Put

    D=h₂(h₀b₁+g₀g₁)/(b₀b₁b₂).

**Claim.** If this Γ is R₀ with degree one, then D>1 and det Γ>0.
In particular a hypothetical Fin4 no-UE table with this sign pattern
automatically satisfies both numerical assumptions of the larger-root
four-clock producer.

### Exact original-data source

The inspected declaration
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
supplies full R₀ and degree one from nonexistence of an original-game
uniform payoff, with no singleton-sign or punishment-normality input.
The definition `quittingSingletonMatrix`, in
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`,
is exactly Γ_ij=r_i({j})−r_i({i}).

The declaration `isStandardQ_of_r0Degree_ne_zero`, in
`MathUE/LinearProgramming/R0Degree.lean`, makes such a matrix standard Q.
Equivalently, the separate direct source
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`, in
`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
supplies the same Q fact. The definition of `quittingProjectiveLCPMatrix`
in `UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` is the same
receiver-row singleton difference; no transpose or reward normalization
is involved. Only the first, degree-based route is needed below.

### Every solution of one test problem has full support

Use standard LCP convention z≥0, w=q+Γz≥0, z_iw_i=0, and the fixed
offset q=(−1,0,−1,0). Standard Q supplies at least one solution.
The inequalities w₀≥0 and w₂≥0 imply respectively z₃>0 and z₁>0,
because their rows have no other positive coefficient. Hence w₁=w₃=0.
The two resulting equations are

    b₁z₂=h₁z₀+g₁z₃,
    b₃z₀=g₃z₁+h₃z₂.

Their strictly positive coefficients imply z₂>0 and z₀>0. Thus every
solution is fully supported and Γz=(1,0,1,0).

The matrix is nonsingular. Otherwise take a nonzero kernel vector v.
Starting from the positive solution z, move along the line z+t v until
the first coordinate reaches zero, keeping all coordinates nonnegative.
This is possible in one of the two directions because v≠0 and I is
finite. The residual remains identically zero, so the boundary vector
is another LCP solution. That contradicts the just-proved full-support
property. Consequently the test problem has exactly one solution and
its full principal determinant is nonzero.

The degree formula
`exists_finset_r0Degree_eq_sum_sign_det`, in
`MathUE/LinearProgramming/R0DegreeSum.lean`, applies: its inactive strict
residual condition is vacuous and its active nonsingularity condition is
the determinant conclusion above. Therefore

    1=degree Γ=sign(det Γ),

and det Γ>0. This uses the actual full ambient support, not a chosen
subcollection of auxiliary roots.

### The same root forces D>1

Substitute z₂=(h₁z₀+g₁z₃)/b₁ in the zeroth equation Γz=(1,0,1,0):

    −b₀z₁+(h₀+g₀g₁/b₁)z₃+(g₀h₁/b₁)z₀=1.

Multiply this equality by h₂ and add b₀ times the second-coordinate
equation g₂z₀+h₂z₁−b₂z₃=1. The result is

    [h₂(h₀+g₀g₁/b₁)−b₀b₂]z₃
       +[h₂g₀h₁/b₁+b₀g₂]z₀=h₂+b₀.

The second bracket is strictly negative, while z₀,z₃>0 and the right
side is positive. The first bracket is therefore strictly positive.
Dividing by b₀b₂>0 gives D>1, as claimed.

## Consequence and its precise coverage status

The strict sign pattern alone implies original-game UE: if no UE existed,
the source just described would give R₀ and degree one; the claim would
give D>1 and det Γ>0; then the complete larger-root producer would
construct an original-game uniform payoff, a contradiction. Its fixed
target and unrestricted behavioral proof are preserved in
[`LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md`](../exports/LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md).

This conclusion has no missing strategic input. Nevertheless it does not
establish coverage beyond the union of the accepted producer and the
existing matrix exit criteria: its numerical complement is already
excluded by those criteria. It is retained here as a source-conditioned
classification and a reason not to optimize the larger-root gates.
No new export is proposed for this algebraic consolidation.

The proof also gives an exact falsifier of the speculation that the
larger-root D condition could fail on the degree-one/Q part of this sign
chamber: the actual test root forces the strict inequality. No numerical
root selection is being used to claim that implication.

For a negative boundary check before the degree-one restriction, take
all b_i=h_i=1 and (g₀,g₁,g₂,g₃)=(−1,1,−1,1). Here D=0.
The same test offset has no solution: full support would give
z₂=z₀+z₃, and then its zeroth equation would read −z₁−z₀=1.
Thus the strict sign chamber by itself does not force the spectral gates;
the actual no-UE/Q source is essential in the implication proved above.

## Next independent-law question

A universal construction cannot use deterministic at-most-one-owner
calendars, even with infinitely many dates and accuracy-dependent hazards.
The inspected
`SolanVieilleBoundary.SoloHazardLedger.Schedule.one_over_sixtyEight_lt_literal_exploitability`,
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`,
gives that obstruction for its exact boundary table. The reward definition
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`
has each own singleton 1, partner singleton 4, and the two opposite-pair
singletons 0. In particular every comparison row has two negative and
one positive off-diagonal entries, unlike the mixed row counts in the
sign pattern above. Its no-solo result does not prohibit genuine
simultaneous phases or approximate independent laws in general.

The live question is to combine retained joint phases with refinable
solo arcs on the remaining sign configurations, selecting all four
players' laws together and controlling each player's deleted-opponent
tail on those same laws. A proposed complete mechanism must retain the
actual nonsingleton rewards in its joint-phase Quit caps and produce a
target before the accuracy parameter. No such general producer is
asserted in this note.

## Two crossed joint phases in the favorable-matching chamber

### Exact raw reward class

Let I={0,1,2,3}. Define the favorable partner f by f=(01)(23), and
partition the players into active pairs A={0,2} and B={1,3}. The other
member of a player's active pair is denoted a(i); the remaining player
is o(i). Thus f(i) and o(i) constitute the opposite active pair.

Choose arbitrary own singleton levels s_i∈ℝ and positive scales b_i>0.
The shared finite raw parameters satisfy

    H>2,             Π>−1,             K∈ℝ.                    (17)

Require the literal singleton entries

    r_i({i})=s_i,
    r_i({f(i)})=s_i+H b_i,
    r_i({a(i)})=r_i({o(i)})=s_i−b_i.                            (18)

For each of the two scheduled pairs T=A,B, require

    r_i(T)=s_i+Π b_i   if i∈T,
    r_i(T)=s_i+K b_i   if i∉T.                                 (19)

There are exactly twelve collision caps:

    r_i({i,j})≤s_i      for j∈{f(i),o(i)},
    r_i({i,f(i),o(i)})≤s_i,        for every i∈I.                (20)

All other nonsingleton coordinates are unrestricted, including every
grand-coalition coordinate. The parameters in (17)–(19) are raw reward
equalities and inequalities, not strategic witnesses. The class permits
four own levels, four positive row scales, H,Π,K, and thirty-six other
nonsingleton coordinates, twelve of the latter bounded as in (20).
It is an equality stratum, not an asserted open sixty-coordinate class.

**Ordinary theorem.** Every such reward table has one explicitly produced
period-two profile that is exact terminal Nash against unrestricted
behavioral deviations at both live suffixes, and whose actual initial
payoff is a fixed uniform-equilibrium payoff of the original game.
Live play and Never pay zero. No public correlation is used. The phases
activate A and B alternately, with both active players using one common
proper hazard determined below. None of the players is first fixed at a
child equilibrium.

### The exact cubic selector

Define

    P(t)=Πt³+(H−1−K)t²+Kt−(Π+1).                               (21)

At the endpoints P(0)=−(Π+1)<0 and P(1)=H−2>0. By continuity
there exists t∈(0,1) with P(t)=0. Select one such t once and for all,
before accuracy or horizon; for example take the smallest root in (0,1).
This choice exists because the nonzero polynomial has finitely many
roots and neither endpoint is a root. Put q=1−t∈(0,1).

At its active phase player i will have value

    U_i=s_i+qΠ b_i,

and at the passive phase it will have value

    W_i=s_i+q(Π+1)b_i/t>s_i.                                   (22)

The inequality holds even when Π<0; no claim that U_i≥s_i is needed.
At the A phase the vector has U entries on A and W entries on B; at
the B phase these roles reverse.

### All action endpoints, not just policy equations

At i's active phase only a(i) can quit if i Continues. Its forced
Quit value is

    t s_i+q(s_i+Πb_i)=U_i.

Its forced Continue value, with the actual next-phase value W_i, is

    q(s_i−b_i)+tW_i=U_i.

Thus both supported actions are exactly indifferent for all four
players, with arbitrary signed s_i. At i's passive phase the two
opponents are f(i),o(i). Its forced Continue value is

    s_i+b_i[q t(H−1)+q²K+t²qΠ].                                (23)

Equation (21) is exactly the assertion that (23) equals W_i: after
dividing by q>0 and multiplying by t, it reads

    Π+1=t²(H−1)+t(1−t)K+t³Π.

Its forced Quit is an average of s_i and the three rewards appearing
in (20), so is at most s_i<W_i. Hence every passive player strictly
prefers Continue. This verifies all eight policy coordinates and all
sixteen action endpoints of the two-phase cycle. It retains all actual
simultaneous outcomes under one unilateral deviation; triple rewards in
(20) are not replaced by singleton rewards.

### Full behavioral and fixed-target horizon consumer

Joint survival per period is t⁴<1. The two bounded Bellman vectors are
therefore the actual terminal continuation values, by iterating their
identities and letting the surviving remainder vanish. Removing any one
player leaves three opponent hazard occurrences per period, with product
survival t³<1. At every date the current value bounds both unilateral
action endpoints with the following prescribed continuation. Backward
iteration thus bounds any behavioral deviation, leaving a bounded
remainder multiplied by at most t^(3n) after n full periods. This
vanishes, including on every delayed-Quit or Never response. The profile
is exact terminal Nash at both phases.

Let M=max_{S,i}|r_i(S)|. Under any unilateral deviation, absorption is
no later than the first opponent Quit, whose expectation is at most
1+2/(1−t³), including the initial live-zero convention. The expected
terminal-to-N-date-average difference is at most

    2M[1+2/(1−t³)]/N.

The same estimate holds on path. Thus the one profile delivers its fixed
initial target with vanishing finite-horizon error, and every deviation
has gain at most twice that error for all sufficiently long horizons.
No accuracy-dependent target selection, finite-memory restriction, or
joint-survival-only replacement for the opponent tail is used.

The inspected checked consumers
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
are in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The actual raw producer here supplies their two roots, both values,
Bellman/Nash identities, and opponent contraction. It is not a new
conditional compiler.

### Why the nonnegative-inverse exit does not consume this chamber

Before positive row scaling, the literal singleton comparison matrix is

    Γ_H = [ 0   H  −1  −1 ]
          [ H   0  −1  −1 ]
          [−1  −1   0   H ]
          [−1  −1   H   0 ].                                  (24)

Its eigenvalues are H−2,H+2,−H,−H. Consequently

    det Γ_H=H²(H²−4)>0.

Its inverse has diagonal d, favorable-partner entry a, and the other
two entries c in every row, where

    d=2/[H(H²−4)],
    a=(H²−2)/[H(H²−4)],
    c=1/(H²−4).

All are strictly positive. For row scales b_i, the actual matrix is
diag(b_i)Γ_H, whose determinant has the same positive sign and whose
inverse is Γ_H⁻¹diag(1/b_i). Thus the negative determinant premise of
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`, in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`,
fails throughout the class. The positive entries form two matched
transpositions, not a positive Hamiltonian cycle; confusing those two
permutation signs would reverse this conclusion.

Every principal of size at least two is nonsingular: pair determinants
are −H² or −1, each triple determinant is 2H, and the full determinant
is as above. Every column has a negative entry, so Γ_H is R₀. Its
positive inverse gives degree +1, not an exit, using
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.
Every triple inverse has a negative diagonal entry −1/(2H), excluding
the raw three-child nonnegative-inverse producers. Any harmful pair is
[[0,−1],[−1,0]], which is neither standard Q nor homogeneous-feasible,
excluding the all-principal projective-Q criterion.

No cyclic order can put a positive predecessor in each row: the unique
positive predecessor map is f, two disjoint transpositions, whereas the
predecessor of a four-cycle is one four-cycle. Thus both the existing
smaller-eigenvalue and the accepted larger-eigenvalue four-clock raw
sign conditions fail under every relabeling.

### A fully specified rational fixture

Take s_i=b_i=1 for every player, and

    H=53/8,          Π=5,          K=−1,          t=4/5.

Equation (21) holds exactly. The singleton rewards are 1 to the owner,
61/8 to its favorable partner, and 0 to the others. Complete all rows
as follows:

| S | r(S) |
|---|---|
| 0 | (1,61/8,0,0) |
| 1 | (61/8,1,0,0) |
| 2 | (0,0,1,61/8) |
| 3 | (0,0,61/8,1) |
| 01 | (−1,−1,0,0) |
| 02 | (6,0,6,0) |
| 03 | (−1,0,0,−1) |
| 12 | (0,−1,−1,0) |
| 13 | (0,6,0,6) |
| 23 | (0,0,−1,−1) |
| 012 | (−10,1,−10,0) |
| 013 | (1,−10,0,−10) |
| 023 | (−10,0,−10,1) |
| 123 | (0,−10,1,−10) |
| 0123 | (−11,−12,−13,−14) |

The two roots are (1/5,0,1/5,0) and (0,1/5,0,1/5).
Their values are

    V_A=(2,5/2,2,5/2),       V_B=(5/2,2,5/2,2).

At either phase each active player's two endpoints are both 2. Every
passive player's Continue endpoint is 5/2 and Quit endpoint is
9/25, so the strict outsider margin is 107/50. These are exact original
reward computations, not a limiting or numerical root fit.

Only 02,13,I are premium traps. In particular the greatest core is
full. Both pair traps have joining gap 6 in both directions. There is
no pure exit: a singleton's active partner gains by joining; an active
pair's outsider gains 1 by joining; any other pair member can leave
its reward −1 for a nonnegative singleton reward; an active-pair member
of any triple can leave −10 for 0; and each grand-coalition member can
leave its negative reward for 0. All-Never is defeated by an own Quit
paying 1.

Every proper child has an exact terminal equilibrium with zero joint
Never and a profitable omitted player. If the child cuts either active
pair, let j belong to the child with a(j) outside. Pure initial Quit by
j is a child equilibrium: every other child player gets 0 or 61/8 by
waiting, while joining j pays −1; j gets 1 and cannot improve by
delaying against Never. The omitted player a(j) gains 6 by joining.
The only proper nonempty children that cut neither active pair are 02
and 13; their pure joint exit is a child equilibrium, and either outsider
gains 1 by joining. This exhausts all fourteen children. Hence every
proper child fails a universal fixed nonnegative weighted-child-debt
plus finite joint-Never lift for some omitted player.

### No proper three-player stationary mixing root

This is a bounded architecture exclusion, not an assertion that full
four-player stationary equilibria are impossible. The rows of size at
most three are invariant under the Klein group generated by f and a,
which acts transitively on deleted players. It therefore suffices to
exclude a stationary root with support012 and all three hazards proper.
Write these hazards (a,x,c), with player3 inactive, and let F=61/8.

Player2 receives zero at every absorption not containing it. Its Never
payoff is zero. Interior optimality therefore forces its Quit payoff
to zero:

    1+5a−2x−14ax=0.

For 0<a<1 this implies

    3/8<x<1/2,       a=(1−2x)/(14x−5).

Player0's Quit payoff, using the same equation, is

    Q₀=(14x−5)(a−c).

Its Never payoff is

    N₀=F x(1−c)/(x+c−xc)>0.

An interior root requires Q₀=N₀. Hence c<a<1, and so

    Q₀<(14x−5)(1−c),       N₀≥F x(1−c).

But F x>14x−5 whenever x<1/2, because F>4. This is a contradiction.
All four deleted-player versions follow by the stated permutations.
In particular no relabeling of the implemented three-active proper
stationary branch in
`PairedCubicStationaryExample.exists_local_stationary_branch`,
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`,
can consume this fixture.

### Bounded comparisons still relevant to the fixture

At the all-sure hazard vector the literal displacement for player i is
r_i(I)−r_i(I∖{i}), hence is respectively −11,−12,−13,−14. These
are distinct, so no nondiscrete partition can satisfy
`QuittingResponseInvariantOnUnitCube` from
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`:
the all-sure vector belongs to every block-constant cube. This excludes
response quotients, centered-pair classes, and subgroup-orbit consumers,
despite the singleton matrix's symmetry.

Product-low fails at the sure active pair: both participants get 6>1.
The supportwise weighted nonpositive-premium criterion fails there too.
Greatest-core≤2 and both triple-core classes fail by the full core.
Every player has a negative grand-coalition premium, so there is no
protected player at all. The weighted-floor test also fails at S=I,
since every nonzero nonnegative weight vector has a strictly negative
weighted grand-coalition premium. Boxed-charge classes exclude pair
traps. The mixed-trap larger-support test fails because

    P_I({j})=5−2−2=1>0

for every singleton j, not the required strictly negative bound.
These failures retain signed premiums; none is inferred just from the
presence of a negative entry.

The raw paired-cycle region permits only one below-own singleton entry
in each row (`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`); this
fixture has two in every row. The integral-tournament singleton fibres
require opposite signs on each unordered pair, while here every pair
has equal signs in both directions. The visible overlapping period-three
affine cylinder has favorable/harmful singleton-difference ratio near 3,
and certainly less than 4 in its radius-1/50000000 box. Here the ratio is
53/8>4 in every row, invariant under positive playerwise affine changes.

Deleting any player leaves its favorable partner with two strictly
negative comparisons in the remaining triple. Thus every deletion fails
the literal cyclic-child predicate requiring opposite strict signs in
each child's off-diagonal row, independently of singleton normalization.

The four-phase architecture joint-pair, solo-a, solo-b, joint-pair,
with the same joint pair at both ends, has a useful intrinsic necessary
sign test when its certified floors satisfy

    V_B,a=V_C,a=s_a,       V_C,b=V_D,b=s_b,
    V_D,a>s_a,            V_B,b>s_b.

Its proper solo rates z,w and exact Continue identities imply

    s_a=w r_a({b})+(1−w)V_D,a,
    V_B,b=z r_b({a})+(1−z)s_b.

Therefore Γ_ab<0<Γ_ba. The accepted full-table two-joint neighborhood
retains precisely these identities and strict floors, independently
of its unspecified neighborhood radius. Here every unordered singleton
pair has the same strict sign in both directions, so no relabeling
satisfies this necessary raw property. This is a comparison with that
certified branch, not with every possible two-joint architecture.

All ordered-pair crossed-response lower guards fail on explicit pure
outsider faces. Given recipient i and selected partner j, first suppose
j≠f(i). Put the favorite f(i) surely Quit, every other opponent Continue,
and the selected partner at zero. The literal zero-discount displacement
is

    r_i({i,f(i)})−r_i({f(i)})=−1−61/8=−69/8<0.

If instead j=f(i), let o(i) surely Quit and the other opponents Continue.
The displacement is r_i({i,o(i)})−r_i({o(i)})=−1<0. Both are actual
root evaluations; no infinitesimal or stationary approximation is used.
Consequently the fixture fails even the weak polynomial lower-face
guard, and hence all stronger lower-ranking versions, for every ordered
choice. The inspected declarations are
`QuittingCrossedStrictLowerRanking` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawTests.lean`,
`QuittingHalfWeakRawGuards` and
`exists_uniformEquilibriumPayoff_of_weakHalfRaw` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryProducer.lean`,
and `QuittingOneSidedWeakUnitGuards`,
`QuittingOneSidedWeakUnitRawGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The broader `QuittingHalfWeakPolynomialGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
tests these same closed-square lower faces. It therefore fails too,
excluding the producer
`exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`.
The matrix-free polynomial consumer
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in the one-sided file
likewise requires the failed lower-face inequality.
The strict unit, strict half, weak half, and one-sided matrix-free raw
producers all require one of these failed guards. So do the guard-derived
full-reward neighborhoods
`halfCeiling_fullRewardBall_source` and
`unitCeiling_fullRewardBall_source`, in
`UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFullRewardNeighborhood.lean`.
Positive playerwise scaling and row translation preserve the strict
negative displacement witnesses, so do not repair these failures.

The separate literal owner-risky family `sharpReward`, with consumer
`sharpReward_exists_uniformEquilibriumPayoff`, in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`,
has Γ_03=0 for every value of its two parameters. Every off-diagonal
entry of (24) is nonzero. Thus no relabeling or positive playerwise
affine copy of that literal family equals this fixture. Its source
explicitly does not assert a full-reward robustness neighborhood.

The boxed full-core and proper-triple raw neighborhoods also require
absence of pair traps, which the two strict pair traps violate. The
remaining generic rational-box, stationary-face, and periodic compilers
verify supplied strategic certificates rather than automatically
consume arbitrary reward tables. The comparisons here do not exclude
arbitrary supplied stationary certificates, nor every full-support
stationary equilibrium. The actual new raw producer is (17)–(20),
with the complete original-game consumer above; the fixture establishes
strict coverage beyond the specified existing raw families, not a
universal architecture-completeness claim.
