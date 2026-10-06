# Global joint phases with opposite participant signs

Identity: CODEX_NOETHER. Ordinary mathematics, not Lean-checked and not
independently reviewed. Internal complete proof candidate; no export.

Status: a whole raw completion family is produced by one global high branch
and a scalar crossing. No rates or strategic witnesses are inputs. The
complete table below separates the family from the accepted positive and
below-floor matching producers and the compared actual raw sources. The
next required step is independent adversarial review of the full mechanism
and actual coverage, not another local root calculation.

## 1. Finite data and exact theorem

There are four players I={0,1,2,3}, one live state with zero reward,
independent private Continue/Quit actions at simultaneous dates, and public
histories. A nonempty quitting coalition S absorbs at a finite signed reward
vector r(S). The absorption-selection date still pays the live zero reward;
subsequent dates pay r(S). Never pays zero. Unilateral deviations are arbitrary
full behavioral replacements. Every conclusion is in expectation.

Let f=(01)(23), a=(02)(13), o=f∘a, A=02 and B=13. Choose arbitrary
signed s_i, positive b_i, and real parameters

    H>2,       Π_A<−1,       Π_B>−1,       k>0.

Put h=H−1, β=−Π_A>1, γ=β−1>0 and c_B=Π_B+1>0. Require the actual
singleton entries

    r_i({i})=s_i,
    r_i({f(i)})=s_i+H b_i,
    r_i({a(i)})=r_i({o(i)})=s_i−b_i.

For either scheduled pair T impose participant increments Π_A b_i on
players in A and Π_B b_i on players in B. Impose passive increments
−k b_i for players in A and K_B b_i for players in B. Thus the table's
four scheduled-pair participant and four passive coordinates are fixed by
these raw parameters; all other nonsingleton coordinates are subject only
to the twelve caps below.

The following scalar choices are computed from raw data, not from a
strategy. Choose

    y_L>max(h/k,β/(h+2k)),

for example y_L=1+max(h/k,β/(h+2k)). Set

    D_L=(1+y_L)²,       C_L=h y_L−k y_L²<0,
    x_L=[β−γD_L−C_L+√((γD_L−β+C_L)²−4γD_L C_L)]/(2γD_L).

Assume the finite raw threshold

    K_B>[c_B y_L(1+x_L)²−h x_L−Π_B y_L/(1+y_L)]/x_L².    (T)

Define m=y_L(k y_L−h)/[γ(1+y_L)²]>0. Choose a raw upper bound

    Y>max(y_L,[K_B+h/m+max(Π_B,0)/m²]/c_B),

for example one plus the displayed maximum. Define

    δ=(1/2)min(k,[(2k+h)y_L−β]/[Y(Y+2)])>0,
    C_A=k−δ,                0<C_A<k.

The twelve literal collision caps are, for ∅≠T⊆{f(i),o(i)},

    i∈A: r_i({i}∪T)≤s_i−C_A b_i,
    i∈B: r_i({i}∪T)≤s_i.                                (C)

Claim: every original reward table satisfying this finite raw data has one
exact proper period-two terminal Nash profile and one fixed UE target. The
same profile witnesses every accuracy and all sufficiently large horizons.
All unused reward coordinates, including the entire grand reward, are
arbitrary. This is a raw producer, not a supplied-certificate verifier.

## 2. A unique global high branch

For y≥y_L, put D(y)=(1+y)² and C(y)=h y−k y²<0. Consider

    −γxD(y)+βx/(1+x)=C(y).                              (A)

Multiplying by1+x gives

    γD(y)x²+[γD(y)−β+C(y)]x+C(y)=0.

Its leading coefficient is positive and its constant term negative. It
therefore has exactly one positive root x(y), explicitly the same quadratic
formula as x_L with y replacing y_L. This branch is continuous on[y_L,∞).
No other branch, implicit-function certificate or root selection is supplied.

Equation (A) implies

    γD(y)x=βx/(1+x)+k y²−h y>k y²−h y.

The ratio y(ky−h)/[γ(1+y)²] increases on[y_L,∞): its derivative is
[(2k+h)y−h]/[γ(1+y)³]>0. Consequently x(y)>m throughout that interval.
The upper bound x(y)<k/γ also follows, because

    βx/(1+x)−h y<β−h y<2ky,
    γD(y)x<ky²+2ky<kD(y).

The second strict inequality uses (2k+h)y≥(2k+h)y_L>β.

## 3. A raw scalar crossing produces the other rate

Define

    R_B(y)=c_B y(1+x(y))²−h x(y)−K_Bx(y)²−Π_B y/(1+y).

Condition (T) gives R_B(y_L)<0. The lower bound x(y)>m gives

    R_B(y)/x(y)²
      ≥c_B y−K_B−h/m−max(Π_B,0)/m².

Thus R_B(Y)>0. The intermediate value theorem produces one y∈(y_L,Y)
with R_B(y)=0. Fix this root once and put x=x(y)>0. The two equations are

    −γx(1+y)²=h y−k y²−βx/(1+x),
    c_B y(1+x)²=h x+K_Bx²+Π_B y/(1+y).                   (E)

These are exactly the original four passive Continue equations, duplicated
only by the normalized equality of the two rows within each scheduled pair.
There is no strategic root among the hypotheses.

## 4. The collision estimate does not force a pure exit

For the selected root y∈(y_L,Y), (A) gives

    γx/[1−(1+y)⁻²]
      =[βx/(1+x)−hy+ky²]/[y(y+2)]
      ≤k−[(2k+h)y−β]/[y(y+2)]
      ≤k−[(2k+h)y_L−β]/[Y(Y+2)]
      ≤k−2δ<C_A.                                       (F)

The cap C_A<k is load-bearing for coverage. At a pure B exit, an A-player's
passive reward is s_i−k b_i, while a permitted triple join can be strictly
higher, up to s_i−C_A b_i. Therefore (C) does not already protect that pure
exit. A crude cap at or below s_i−k b_i would destroy this distinction.

## 5. Exact behavioral equilibrium and one uniform target

Let the A rates be q_A=x/(1+x) and the B rates q_B=y/(1+y). Alternate
the two independent joint rows; no player ever quits at its passive phase.
Define

    i∈A: U_i=s_i−β b_i x/(1+x),   W_i=s_i−γ b_i x;
    i∈B: U_i=s_i+Π_B b_i y/(1+y), W_i=s_i+c_B b_i y.

At an active phase, forced Quit has value U_i, and forced Continue has
the same value by q_a(s_i−b_i)+(1−q_a)W_i=U_i. At a passive phase,
Continue equals W_i by (E). For i∈A, passive Quit is at most
s_i−C_A b_i[1−(1+y)⁻²], strictly below W_i by (F). For i∈B it is
at most s_i<W_i. All sixteen pure endpoints and all policy values are
therefore checked, including every possible simultaneous unilateral triple.
The grand coalition is unreachable under one deviation.

Joint period survival is (1−q_A)²(1−q_B)²<1. Iterating the bounded policy
identities realizes these signed phase vectors as actual terminal payoffs.
For each deviator i, deleted-opponent period survival is the product of its
three opponents' factors, strictly less than1. Iterating the endpoint upper
bounds through arbitrary behavioral deviations leaves a bounded remainder
times this product's n-th power. It vanishes uniformly, including Never and
arbitrarily late stopping. Thus this is exact terminal Nash.

For M=max|r_i(S)| and ρ_i the deleted period survival, set
C_time=max_i[1+2/(1−ρ_i)]. The expected absorption date-plus-one is at
most C_time, uniformly over all deviations. Terminal-to-average error is
at most2M C_time/N, and unilateral regret at most4M C_time/N. The phase-A
vector is fixed before accuracy and this same profile works for every large
horizon. The game has not been translated or correlated.

The exact consumers inspected are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Every input is
produced above. The new raw theorem is ordinary mathematics only.

## 6. A complete previously surviving table

Take s_i=b_i=1, H=3, Π_A=−11/10, Π_B=1, k=68/25, K_B=10.
Choose y_L=59/34 and Y=6. Here m=272816/43245>6. At the lower endpoint

    R_B(y_L)/x_L²<2y_L(7/6)²−10=−3229/612<0;

at the upper endpoint the lower bound is

    R_B(6)/x(6)²>12−10−1/3−1/36=59/36>0.

Thus these exact endpoint tests imply (T) and the upper-bound condition.
The computed δ=10039/81600. Put

    ζ=1−k+δ/2=−54133/32640.

Its cap slack and its pure-B joining gain are both δ/2=10039/163200>0.
The full sixty-coordinate table is

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (ζ,1/2,0,0) |
| 02 | (−1/10,11,−1/10,11) |
| 03 | (ζ,0,0,1/2) |
| 12 | (0,1/2,ζ,0) |
| 13 | (−43/25,2,−43/25,2) |
| 23 | (0,0,ζ,1/2) |
| 012 | (−100,1/2,−100,0) |
| 013 | (ζ,100,0,100) |
| 023 | (−100,0,−100,1/2) |
| 123 | (0,100,ζ,100) |
| 0123 | (1000,−101,1001,−102) |

The two rates are genuinely produced by the crossing, not stipulated. The
proof puts6<x<136/5 and59/34<y<6. A numerical experiment gives
y≈4.471486 and x≈15.524067; these approximations are not proof inputs.

The argument covers every raw completion of Sections 1–5, not just this
table or a local neighborhood. The table is separate new-coverage evidence.

## 7. Raw overlap and pure/child tests

The accepted `exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md` cannot use
scheduled02/13 because its A participant comparison is−1/10<0. Favorite
signs force f. The other harmful matching03/12 has A participant comparison
ζ<0 as well. Thus every relabeling fails that weak matching criterion.
Every partition fails the additional Π≥0 inverse criterion, since each
perfect matching has at least one negative A participant premium.

The scalar raw family in `exports/BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md`
requires every normalized Π<−1. Here the B scheduled participant increment
is+1, and its other harmful pair increment−1/2>−1. This fails under either
harmful matching. The local below-floor producer retains the same two-pair
word and all phase values below their own levels: a B active increment+1
forces U_B>1 on02/13, and a B participant comparison+1/2 forces W_B>1
on03/12. It therefore cannot produce that below-floor architecture here.

There is no pure equilibrium. A sole A quitter is profitably joined by its
o-partner in B for1/2 instead of0; a sole B quitter is profitably joined
by its B mate for2 instead of0. At A a participant withdraws from−1/10
to0; at B an A outsider joins for gainδ/2. Every other pair has its A
participant withdraw from ζ<0 to0 or4. At an A-containing triple an A
participant withdraws from−100 to0. At a B-containing triple the omitted
A player joins for1000 or1001 instead of0. At I a B player withdraws
from its negative grand payoff to0. All Never loses to own Quit1.

Every proper child has an exact terminal Nash, zero-Never counterprofile
to universal debt lifts. Singletons use sure own Quit. A uses a sure solo
member, B its sure joint exit, and every cross pair its sole B member.
A triple omitting B uses its sole B member; a triple omitting A uses its
full sure triple. The waiting/joining comparisons are exactly those above:
B joint participants obtain2 instead of0, the A member of a B triple
obtains ζ rather than−43/25, and B triple participants obtain100 instead
of0. Omitted players profit by1/2,2,δ/2, or1000/1001 respectively.

The actual nonnegative quiet F/J criterion also fails every child already
at J. For an A-only child use a singleton and its omitted B o-partner;
for a B singleton or any cross child use its B singleton and omitted B mate.
Each omitted joining gain is positive and every child joining gain there
is nonpositive. For child B use the full B coalition and an A outsider's
gainδ/2, all child joining gains zero. A triple omitting A uses its full
coalition and positive grand joining gain, again all child joining gains
zero. These exhaust the fourteen children. This tests the actual raw
family in `exports/NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md`, not just
arbitrary supplied child profiles.

## 8. No proper-three stationary support

The table's rows of size at most three are invariant under a=(02)(13).
A support consisting of full B plus one A leaves a B player whose favorite
is omitted. That player's Never payoff is zero, while all its forced-Quit
outcomes are1,2,1/2,100. It cannot mix properly.

For support012, write its proper hazards(a,x,c) for0,1,2. Player2's Never
payoff is zero. Put C₀=1−ζ>0 and D(x)=11/10+(999/10−C₀)x>0.
Its indifference is

    1−C₀x−D(x)a=0.

Player0's forced Quit is D(x)(a−c), and its Never payoff is
4x(1−c)/(x+c−xc)>0. Its indifference therefore forces c<a. But player1's
Never payoff is

    N₁=a[4(1−c)+11c]/(a+c−ac)
       >(4+7c)/(2−c)≥2,

while all its forced-Quit outcomes are1 or1/2, so Q₁≤1. Contradiction.
The other full-A support follows by the permutation a. All four
proper-three supports are excluded, not all stationary profiles.
This excludes the actual proper-three branch named
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.

## 9. Other bounded exact-source comparisons

The only premium traps are B and I: A players have positive participant
premiums only at I, and B players witness their premiums at B. Thus the
greatest core is full, excluding proper pair/triple core criteria. Sure B
violates product-low and supportwise premium balance. At sure A every
forced-Quit premium is negative (−11/10 on A,−1/2 on B), excluding every
nonzero nonnegative weighted global floor. At full trap I and subset B,
the actual aggregate joining charge isδ>0, violating the intermediate L
inequality in `exports/MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md` and
`exports/BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md`. No player is protected:
each has a negative participant premium at some cross pair.

The singleton matrix is the H=3 matrix with determinant45, positive inverse,
R₀ degree+1, harmful principal pairs not Q or homogeneous admissible, and
triple inverse diagonals−1/6. These fail the actual negative-determinant,
degree-not-one and child-inverse exit hypotheses in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`,
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`, and
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The row sums are1, so singleton terminal tests Γᵀλ≤0 force λ=0,
excluding `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.

At all-sure the displacements are1000,−101,1001,−102, all different.
The block-row-sum identity forces equal positive scales within any affine
response block, so no nondiscrete response quotient exists even after
positive affine row transports. The exact necessary identity is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

The positive graph is two transpositions; every row has two negative
singleton comparisons and reciprocal signs agree. These exclude the
favorable-four-cycle, cyclic-child, unique-negative paired and integral
tournament raw patterns. All participant pair gap ratios have absolute
value at least1/2, whereas the visible affine period-three cylinder's
center has zero participant pair gaps and radius1/50000000. Its exact
center and visibility definitions are in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
and `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.

Every crossed lower polynomial guard fails. If selected partner≠favorite,
the favorite surely quits, giving ζ−4<0 on A or1/2−4<0 on B. If it
is the favorite, an A owner's scheduled mate surely quits, giving−1/10;
a B owner's two A outsiders both surely quit, giving1/2−11<0. This
excludes `QuittingHalfWeakPolynomialGuards` and
`QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The owner-risky literal family has an off-diagonal zero; this matrix has none.

For every conditional range blocker, ContinueUpper≥4. QuitWithoutLower≤1.
On A, the empty-background pair gives QuitWithLower≤max(ζ,−1/10)<0;
on B, the maximal background gives the negative grand payoff. Thus its
strict lower-face range inequality fails. The actual definition is
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.

Influence1→0 is ζ−5<0 at∅, but k−1=43/25>0 at{3}. Consequently
`SignConsistentQuittingInfluence` and `IsAffineQuittingMembershipGain` fail
in `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

These are bounded actual-source comparisons, not nonexistence claims for
all stationary, quiet-child or periodic strategies. The producer actually
adds the opposite-sign normalized participant family with arbitrary raw
completions; it does not settle unrestricted Fin4 or assert a new Lean seal.
