# A larger-eigenvalue four-clock uniform-equilibrium producer

## Exact statement

Let I={0,1,2,3}. For every nonempty S⊆I let r(S)∈ℝ⁴ be the
terminal reward when exactly S quits first. The initial and every live
state pay zero; after absorption the reward is r(S) at every subsequent
date. Never absorbing pays zero in the terminal evaluation. Players use
private independent randomization. A unilateral deviation may be any
behavioral strategy, with arbitrary dependence on the observed history.

Put s_i=r_i({i}), Γ_ii=0, and Γ_ij=r_i({j})−s_i for i≠j. Suppose
that, after some relabeling of I in cyclic order, the following strict
raw-table conditions hold, with indices read modulo four:

    Γ_i,i+1=−b_i,     b_i>0,
    Γ_i,i+3=h_i,      h_i>0,
    Γ_i,i+2=g_i,      g₀,g₂<0<g₁,g₃.

Define the eight ratios and six auxiliary scalars

    a_i=g_i/b_i,                   d_i=h_i/b_i,
    D₀=a₀a₁+d₀,                  L=a₀d₁+D₀a₂,
    D=D₀d₂,                      U=a₃L+d₃(d₁+a₁a₂),
    V=a₃D+d₃a₁d₂.

Assume also

    D>1,                         det Γ>0.                         (1)

Equivalently, the first inequality in (1) is
h₂(h₀b₁+g₀g₁)>b₀b₁b₂. There is no restriction on own singleton
rewards or on any nonsingleton reward.

**Theorem.** These conditions produce a fixed vector u∈ℝ⁴ which is a
uniform-equilibrium payoff of the original quitting game. More precisely,
for every ε>0 there are one behavioral profile σ and N₀ such that, for
every N≥N₀, its N-date average payoff is within ε of u in each
coordinate and no unilateral behavioral deviation improves that average
payoff by more than ε. The same profile is an approximate terminal Nash
profile against every full behavioral deviation, including late quitting
and Never. The target u is selected from the reward table before ε.

The assumptions are strict inequalities in continuous functions of the
sixty reward coordinates. Their union over the finite set of relabelings
is an open raw-table class. All strategic data used below are produced;
none is a hypothesis.

## Conjecture-facing change and strategic inputs

The existing signed four-cycle raw adapter uses the smaller eigenvalue
of a two-dimensional transfer matrix and requires that eigenvalue to
exceed one. Here the two eigenvalues straddle one, and the larger one
produces positive weights and a valid survival probability. Both branches
are kept distinct. Failure of the smaller-root test is not failure of the
four-clock strategy architecture.

The theorem produces, in order, a positive eigenvector, a period survival
factor, four proper solo hazards, four exact continuation vectors, one
fixed target, and a family of increasingly fine four-phase profiles.
There are no supplied equilibrium, root, timing law, floor vector, or
recursive child witnesses. Nonsingleton rewards enter a finite collision
bound, not an assumption that discards simultaneous quitting.

The full rational table below lies outside the compared raw existence
criteria, including all admissible relabelings of the smaller-root
adapter. Its coarse cycle is not Nash, so the all-player refinement is
essential. The theorem does not solve arbitrary four-player tables.

## Source correspondence

The following are existing tracked sources, distinct from the ordinary
mathematics proved here.

- `SignedFourCycleSingletonData` and its `StrictTests`, in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
  read the literal singleton comparisons. `StrictTests` requires positive
  discriminant, smaller eigenvalue greater than one, negative upper-right
  entry, and three positive reconstructed weights.
- `Math.SignedFourCycleCoefficients`, in
  `MathUE/SignedFourCycleAlgebra.lean`, defines the transfer entries
  `lowerLeft`, `lowerRight`, `upperLeft`, and `upperRight`. They are
  respectively L,D,U,V above. Its existing `smallerEigenvalue` and
  `periodSurvival` refer to the smaller branch, not the branch below.
- `SignedFourCycleSingletonData.certificate` and
  `SignedFourCycleSingletonData.targetValue_isUniformEquilibriumPayoff`,
  in `UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`,
  construct and consume the smaller-branch certificate.
- `BalancedSingletonCycleCertificate` and
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`, in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`,
  require proper nonnegative hazards, Bellman arcs, owner indifference,
  all singleton floors, and a positive opponent hazard for every player.
  They impose no sign restriction on the own singletons. These are the
  existing certificate and fixed-target consumer used by the new adapter.

The additional source comparisons below use named declarations with their
literal hypotheses; no existence conclusion is inferred merely from a
failed test of some other criterion.

## Proof

### 1. The larger eigenvalue gives positive weights

For χ(t)=(t−U)(t−D)−VL, direct determinant expansion gives

    det Γ=−b₀b₁b₂b₃ χ(1).                                      (2)

Since d₂>0, (1) implies D₀>0. The signs of a₀,a₂ are negative and
those of a₁,a₃,d_i are positive. Consequently L<0 and V>0. By (2),
χ(1)<0. Because D>1 and −VL>0, the inequality
(1−U)(1−D)−VL<0 forces U<1.

A monic real quadratic negative at 1 has two distinct real roots on
opposite sides of 1. Thus its discriminant is positive and

    λ₋<1<λ₊,
    λ=λ₊=(U+D+√((U−D)²+4VL))/2,
    A=1/λ∈(0,1).                                                (3)

Define

    w₀=V,                       w₁=λ−U,
    w₃=A(a₂w₀+d₂w₁),           w₂=A d₁w₀+a₁w₃.                 (4)

The first two weights are positive. The characteristic equation and (4)
give both eigenvector equations

    Uw₀+Vw₁=λw₀,              Lw₀+Dw₁=λw₁.

Substitution yields the four balance identities

    w₁=a₀w₂+d₀w₃,             w₂=A d₁w₀+a₁w₃,
    w₃=A(a₂w₀+d₂w₁),          w₀=a₃w₁+d₃w₂.                   (5)

For example, substituting w₂,w₃ into the first equality gives the
second eigenvector equation multiplied by A. Substituting them into the
last equality gives the first eigenvector equation multiplied by A.
The first two equalities in (5) imply

    D₀w₃=w₁−A a₀d₁w₀>0.

Hence w₃>0; the formula for w₂ then gives w₂>0. This proves positivity
from the raw signs, rather than assuming a positive eigenvector.

### 2. Four exact coarse phases and the fixed target

Let W=Σ_i w_i, β_i=(1−A)w_i/W, and

    T_j=1−Σ_{i<j}β_i     (0≤j≤4),
    q_j=β_j/T_j          (0≤j<4).

Then T₀=1, T₄=A, and T_j>T_{j+1}>0. Therefore 0<q_j<1 and
∏_j(1−q_j)=A. At phase j only player j uses hazard q_j; all others
Continue. Repeat the four phases forever.

Its continuation vectors, with V⁴=V⁰, are

    Vʲ=[A Σ_{i<j}β_i r({i})+Σ_{i≥j}β_i r({i})]
         /[T_j(1−A)].                                           (6)

The coefficients in (6) are nonnegative and sum to one. Direct
substitution proves the four Bellman equations

    Vʲ=q_j r({j})+(1−q_j)Vʲ⁺¹.                                 (7)

Multiplying (5) by the b_i gives precisely

    −b₀w₁+g₀w₂+h₀w₃=0,
    A h₁w₀−b₁w₂+g₁w₃=0,
    A(g₂w₀+h₂w₁)−b₂w₃=0,
    −b₃w₀+g₃w₁+h₃w₂=0.                                       (8)

These are the singleton-comparison balances in (6). They imply
Vⁱ⁺¹_i=s_i, and (7) then also gives Vⁱ_i=s_i. Applying (7) at the
two remaining cyclic positions gives

    Vⁱ⁺²_i−s_i=q_{i+1}b_i/(1−q_{i+1})>0,
    Vⁱ⁺³_i−s_i=q_{i+3}h_i>0.                                  (9)

Thus all sixteen singleton-floor inequalities hold. The prescribed
terminal payoff at phase zero is the fixed vector

    u=V⁰=Σ_i (w_i/W)r({i}).                                    (10)

### 3. Refining all four phases

For each positive integer K replace phase j by K consecutive solo
microdates with common hazard

    p_{j,K}=1−(1−q_j)^(1/K).

The product survival of that block is still 1−q_j. Thus all coarse
values and the actual target (10) remain exactly unchanged. With ℓ
microdates remaining, the value is

    r({j})+(1−p_{j,K})^ℓ (Vʲ⁺¹−r({j})),   0≤ℓ≤K.              (11)

It lies on the line segment from Vʲ to Vʲ⁺¹, so the floors persist
at every microdate. This uses the two coarse endpoint floors, not a
floor at r({j}); that singleton endpoint can lie below a passive
player's floor. The owner's value in (11) is always s_j.

Let

    C=max_{i≠j} max(r_i({i,j})−s_i,0),
    e_K=C max_j p_{j,K}.

The finite constant C controls every possible simultaneous outcome under
one unilateral deviation: at most the owner and the deviator can quit.
Since max_j p_{j,K}→0, e_K→0. At a microdate owned by j, a passive
player i's forced Quit payoff is

    (1−p_{j,K})s_i+p_{j,K}r_i({i,j})≤s_i+e_K.

This is at most its current prescribed value plus e_K. For the owner,
forced Quit equals its current value exactly. For every player, forced
Continue followed by the prescribed suffix equals the current value:
this is the Bellman equality for passive players and exact indifference
for the owner.

Add the same constant e_K to each successive prescribed value. If the
deviator Continues, the added constant is multiplied by the probability
that all opponents Continue, hence is at most e_K. If the deviator
Quits, the preceding inequality applies. Therefore these shifted values
form a supersolution for both actions, and for every mixture of them.
There is one error e_K, not one new error at each date.

For player i the opponent-survival factor in each complete refined
period is

    κ_i=∏_{j≠i}(1−q_j)<1.                                     (12)

This bound is independent of its behavioral deviation. Iterating the
supersolution to any finite time bounds every deviation by u_i+e_K,
apart from a bounded remainder multiplied by opponent survival. By (12)
that remainder tends to zero. This proves the full terminal cap bound,
including arbitrary delayed stopping, random stopping and Never.

Before absorption the only public history is an all-Continue history.
The same induction is valid conditionally on any private randomization
of the deviator. No restriction to Markov, stationary, bounded-memory,
or finite-calendar deviations was used. Every opponent's coins remain
independent; there is no public mixture selecting a cycle.

### 4. Uniform finite-horizon evaluation

Let M=max_{S,i}|r_i(S)|. Under every unilateral deviation by player i,
the actual absorption time is no later than the first opponent Quit.
The expected latter time is bounded by

    B_i=1+4K/(1−κ_i).                                         (13)

The extra 1 safely accounts for the initial live state. On a realized
path with absorption time τ, the N-date average differs from its terminal
reward by at most 2M min(τ/N,1). Thus the expected difference is at
most 2M B_i/N. The same bound holds for the prescribed profile, using
any of its opponent bounds.

Fix ε>0. First choose K with e_K<ε/3. Then choose a common N₀ with
4M max_i B_i/N₀<2ε/3 and 2M max_i B_i/N₀<ε. For every N≥N₀,
the on-path average is within ε of the same target u, and the finite
average gain of every deviation is at most

    e_K+4M max_i B_i/N<ε.

The initial stage payoff is zero; no claim of exact finite-horizon
delivery at an immediate exit was used. Signed singleton and terminal
rewards cause no difficulty because (12) controls the deviator's actual
Never event. This completes the original-game uniform-payoff proof.

## Exact full-table example and boundary tests

Use original player labels with s=(1,0,0,0) and comparison matrix

    Γ = [ 0   3  −2  −2 ]
        [−4   0   1   1 ]
        [−2  −2   0   5 ]
        [ 3   3  −5   0 ].                                   (14)

The full sixty-coordinate reward table is

| S | r₀(S) | r₁(S) | r₂(S) | r₃(S) |
|---|---:|---:|---:|---:|
| 0 | 1 | −4 | −2 | 3 |
| 1 | 4 | 0 | −2 | 3 |
| 2 | −1 | 1 | 0 | −5 |
| 3 | −1 | 1 | 5 | 0 |
| 01 | 2 | 1 | −2 | 3 |
| 02 | 1 | −4 | 0 | −5 |
| 03 | 1 | −4 | 5 | 0 |
| 12 | 4 | 0 | 0 | −5 |
| 13 | 4 | 0 | 5 | 0 |
| 23 | −1 | 1 | 2 | 1 |
| 012 | 2 | 1 | 0 | −5 |
| 013 | 2 | 1 | 5 | 0 |
| 023 | 1 | −4 | 2 | 1 |
| 123 | 4 | 0 | 2 | 1 |
| 0123 | 2 | 1 | 2 | 1 |

Here and below a digit string denotes its set of players. Equivalently,
the first two rewards depend only on S∩01 and the last two only on S∩23.
For local intersection ∅, first singleton, second singleton, and pair,
the local reward pairs are respectively

    pair01: (−1,1), (1,−4), (4,0), (2,1);
    pair23: (−2,3), (0,−5), (5,0), (2,1).

In cyclic order (0,3,2,1) the raw data are

    b=(2,5,2,4),     g=(−2,3,−2,1),     h=(3,3,5,1),
    (L,D,U,V)=(−3/2,9/4,−3/8,15/16),    det Γ=25.

The eigenvalues are 3/8 and 3/2. The balance determinant in survival
variable A is −5(3A−8)(3A−2). Thus the smaller eigenvalue would give
A=8/3, which is not a probability. The larger eigenvalue gives A=2/3,
weights proportional to (3/8,3/4,3/4,1), and phase hazards

    (1/23,1/11,1/10,4/27).

In original player coordinates the four exact continuation vectors are

    V⁰=(1,0,8/23,3/23),     V¹=(1,2/11,5/11,0),
    V²=(6/5,1/10,0,0),      V³=(13/9,0,0,5/9).                 (15)

They verify all sixteen Bellman identities and floors directly. The
unrefined profile is not Nash: at its initial solo0 date player1's
prescribed payoff is zero but immediate Quit gives 1/23. After
subdivision the same first-date gain is p_{0,K}→0. This is a test that
local owner indifference alone does not prove equilibrium.

Among all twenty-four labelings, the only orders with negative successor
and positive predecessor in every row are the four rotations below.
Indeed, an order starting with 0 must end with 1, its unique positive
predecessor. The alternative order (0,2,3,1) fails because Γ₂₃=5>0.
Their transfer matrices, with rows (U,V) and (L,D), are

| Cyclic order | Transfer matrix |
|---|---|
| (0,3,2,1) | [[−3/8,15/16],[−3/2,9/4]] |
| (1,0,3,2) | [[15/8,−3/2],[3/8,0]] |
| (2,1,0,3) | [[−3/2,9/4],[−5/2,27/8]] |
| (3,2,1,0) | [[15/8,−3/8],[3/2,0]] |

Every matrix has eigenvalues 3/8 and 3/2. Hence no admissible relabeling
satisfies the implemented smaller-eigenvalue test. Positive playerwise
affine changes multiply each Γ row by a positive scalar, preserving all
ratios and balances. This also excludes those affine transports of the
smaller-branch class.

For an explicit signed-singleton and arbitrary-collision stress test,
add (−8,3,−5,−11) to every singleton vector of the displayed table,
but replace all its nonsingleton rewards by the unrelated rule

    r_i(S)=(−1)^(Σ_{j∈S}j+i)(37+11i),     |S|≥2.

The comparison matrix, rates, and all balances are unchanged. The new
own-singleton vector is (−7,3,−5,−11), the target is
(−7,3,−107/23,−250/23), and every coarse vector is (15) plus the
same shift. All sixteen floors persist. This is a new reward table
checked directly by the theorem, not an appeal to translating the
Never payoff: Never still pays zero, and (12) still controls it.

## Bounded coverage comparisons

### 1. Premium, trap, and signed-core criteria

For a nonempty S call r_i(S)−s_i the participant premium, for i∈S.
A premium trap is a set T with |T|≥2 such that every player of T has
a strictly positive premium at some coalition contained in T and
containing that player. A weak leaver p of T satisfies
r_p(S∪{p})≤r_p(S) for every nonempty S⊆T∖{p}.

All participant premiums in the example are nonnegative. Its traps are
exactly 01,23,I: a player in either pair has positive premium precisely
when that pair is contained in the quitting coalition. Thus the greatest
premium core is full. Criteria requiring greatest core at most two or
three do not apply, including the signed pair and both signed/attractive
triple-core cases.

On pair01 the two joining gaps are −2 and 5; on pair23 they are −3
and 6. Both pairs have opposite-sign joining, excluding the mixed-trap
same-sign-pair criterion. The pair traps exclude boxed-charge criteria
that require no pair trap.

The full trap has no weak leaver: players 0,1,2,3 have positive joining
gaps respectively against singleton 2,0,0,2. Hence no common-leaver or
protected-set support-specific-leaver hypothesis holds, even though all
participant premiums are nonnegative.

Even the weak aggregate-leave condition on the full trap has no nonzero
nonnegative weights λ_i. Its inequalities for opponent sets 02,01,23
would include, respectively,

    5λ₁+6λ₃≤0,       2λ₂−3λ₃≤0,       2λ₀−λ₁≤0.

The first forces λ₁=λ₃=0, and the others force λ₂=λ₀=0. Thus
weighted-floor aggregate-leave criteria fail as well.

At the sure grand-coalition root all four premiums are strictly
positive. This violates `HasProductLowQuittingPremium`, used by
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
It also rules out the stronger supportwise nonpositive weighted-premium
condition, which implies product-low.

### 2. No exact stationary Nash profile

Write the stationary hazards as (h,x,y,z), and put
α=h+x−hx, β=y+z−yz. Equilibrium requires α,β>0. If α=0<β,
player0 receives −1 and can Quit for 1. If β=0<α, player2 receives
−2 and can Quit for 0. If both vanish, player0 can Quit for 1.

If h=0 and x>0, player1 prefers Never's payoff 1 to Quit's payoff 0.
If x=0, player0 prefers Quit's 1 to Never's −1, forcing h=1;
then player1's strict joining gain forces x=1, a contradiction. Thus
h,x>0. Similarly y=0 would force z=0, because player3 otherwise
prefers Never's 3 to Quit's 0. If z=0, player2 must Quit surely,
which forces z=1 by player3's strict joining gain. Thus y,z>0.

If h=1, then x=1, but player0 can leave for 4 instead of 2. If
x=1, player0 strictly prefers h=0. If y=1, then z=1, but player2
can leave for 5 instead of 2. If z=1, player2 strictly prefers y=0.
Consequently a stationary equilibrium would have all four hazards
strictly between zero and one.

The four interior indifferences, obtained from the table, are

    β=x(3−x)/[(1−x)(2+x)],      β=h(h+4)/(1−h)²,
    α=z(5−2z)/[2(1−z²)],       α=y(y+5)/[(1−y)(3−y)].           (16)

The first two imply x≤2β/3 and h≤β/4, hence α≤11β/12.
The third implies z≤3α/7 because
3(5−2z)−14(1−z²)=1−6z+14z²>0. The fourth implies y≤3α/5
because 3(y+5)−5(1−y)(3−y)=23y−5y²>0. Therefore
β≤36α/35, and α≤33α/35, a contradiction.

This includes every support and sure-hazard boundary, and in particular
excludes all pure absorbing equilibria. It excludes exact stationary
Nash producers and their relabelings. It does not assert that an
accuracy-dependent stationary approximation family is impossible.

### 3. Other implemented periodic raw regions

The paired-cycle `RawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` requires a
player's partner singleton to be below its own singleton, but both
nonpartner singletons to be above it. The exact necessary statement is
`RawRegion.eq_partner_of_singleton_lt`: only one quitter can give a
receiver a below-own singleton reward. Rows0 and2 of (14) each have
two below-own entries. Thus every paired schedule, every relabeling,
and every positive playerwise affine transport of that region fails.
This comparison concerns the raw source for
`exists_exact_allSuffix_uniformPayoff_of_rawRegion`, not its conditional
certificate consumer.

The overlapping period-three affine cylinder in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`
uses `exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`.
Its center has own singletons all 1 and, in every row, one other-player
singleton equal to 4 and two equal to 0. All singleton coordinates are
visible; the permitted coordinate error is at most 1/50000000.
Consequently every row still has exactly one above-own singleton.
Rows1 and3 of (14) have two. This excludes that entire affine cylinder
under every relabeling, not merely its center.

The integral-tournament singleton fibres in
`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`
require opposite signs in both directions of each pair, through
`normalizedSoloMatrix_eq_tournamentSkewMatrix_iff`. Pair02 of (14)
is negative in both directions, so this source and its positive row
scalings do not apply.

Two further literal raw predicates fail. First, consider the predicate
that there exists p with s_p>0 and s_j=0 for j≠p, and that for every
i∈I∖{p}, the two numbers Γ_ij with j∈I∖{p,i} have opposite strict
signs. The singleton levels force p=0, but the two remaining entries
in row1 are Γ₁₂=Γ₁₃=1. Thus this canonical cyclic-child sign predicate
fails under every relabeling. Any criterion requiring it is excluded.

Second, consider the predicate that some two-player premium trap has
no weak leaver, using the definitions above. The only pair traps here
are 01 and 23. Player0 is a strict leaver of 01 because
r₀(01)−r₀(1)=−2, and player2 is a strict leaver of 23 because
r₂(23)−r₂(3)=−3. Thus this predicate also fails under every
relabeling. These are direct reward-table comparisons, not appeals to
another neighborhood theorem or claims that all periodic architectures
have been exhausted.

### 4. Singleton-matrix and response-quotient criteria

Every principal minor of size at least two is nonzero. In increasing
support order the determinants are

    pairs:   12, −4, 6, 2, −3, 25;
    triples: −22, 33, −50, 25;
    full:    25.

Moreover every column has a negative off-diagonal entry. Thus Γ is R₀:
a nonzero homogeneous LCP solution with at least two positive entries
would force a singular active principal matrix, while singleton support
would require a nonnegative off-diagonal column.

For the convention z≥0, w=b+Γz≥0, z_iw_i=0, take
b=(3,−2,−7,5). The unique solution has full support and is

    z=(11/5,31/5,151/25,119/25).

Indeed empty support fails b≥0, and every singleton support fails
because its active offset coordinate is nonzero. Pair supports
01,02,03,12,13 have, respectively, the negative active coordinate
z₀=−1/2,−7/2,−5/3 and z₁=−7/2,−5/3; support23 has inactive
residual w₀=−9/5. Triple supports012,013,023 have z₀ equal to
−23/22,−6/11,−9/10, and support123 has z₁=−2/5. This accounts
for every proper support. The unique full solution has determinant
25, so the R₀ degree is +1 by the support-degree formula
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. Hence the hypothesis of
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`, in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
fails.

The full inverse has entry(0,1)=−1. The four triple inverses have
negative entries(0,0)=−1/11,−1/11,−1/2 and (0,1)=−1/5 in their
inherited orders. Thus neither a nonnegative full inverse nor
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
applies. Principal02=[[0,−2],[−2,0]] is R₀ but not Q: at offset
(−1,−1) every residual coordinate is negative for every z≥0. This
rules out the all-principal projective-Q assumption used by
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.

For a response-invariant partition, receivers in one block must have
equal Γ-row sums on every column block, by
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
All fourteen nondiscrete partitions fail this necessary condition:

| Partition | Receivers | Column block | Unequal sums |
|---|---|---|---|
| 01/2/3 | 0,1 | 01 | 3,−4 |
| 02/1/3 | 0,2 | 1 | 3,−2 |
| 03/1/2 | 0,3 | 2 | −2,−5 |
| 0/12/3 | 1,2 | 0 | −4,−2 |
| 0/13/2 | 1,3 | 0 | −4,3 |
| 0/1/23 | 2,3 | 0 | −2,3 |
| 012/3 | 0,1 | 012 | 1,−3 |
| 013/2 | 0,1 | 2 | −2,1 |
| 023/1 | 0,2 | 1 | 3,−2 |
| 0/123 | 1,2 | 0 | −4,−2 |
| 01/23 | 0,1 | 01 | 3,−4 |
| 02/13 | 0,2 | 13 | 1,3 |
| 03/12 | 1,2 | 12 | 1,−2 |
| 0123 | 0,1 | 0123 | −1,−2 |

### 5. Every proper child fails a universal debt/escape lift

For a child profile, define each child player's terminal debt as its
best full unilateral response payoff minus its prescribed payoff. A
universal weighted child-debt-plus-Never inequality would bound an
omitted player's profitable quiet extension by a fixed nonnegative
linear combination of these child debts plus a finite coefficient times
the child's joint-Never probability.

Every proper nonempty child here has an exact full-behavior terminal
equilibrium with joint-Never probability zero and a profitable omitted
player. Twelve witnesses are pure initial exits, followed by Never if
that date survives:

| Child | Initial exit | Omitted joiner | Gain |
|---|---|---:|---:|
| 0 | 0 | 1 | 5 |
| 1 | 1 | 2 | 2 |
| 2 | 2 | 3 | 6 |
| 3 | 3 | 0 | 2 |
| 01 | 1 | 2 | 2 |
| 02 | 02 | 1 | 5 |
| 03 | 0 | 1 | 5 |
| 12 | 2 | 3 | 6 |
| 13 | 1 | 2 | 2 |
| 23 | 3 | 0 | 2 |
| 013 | 1 | 2 | 2 |
| 123 | 3 | 0 | 2 |

To verify exactness, at these exits every continuing child player weakly
prefers its quiet reward to joining, and every quitting child player
weakly prefers its prescribed reward to leaving. If its unilateral
refusal could prevent absorption entirely, its later best reward is at
most max(s_i,0), which is no larger than its prescribed reward.

For child012 use first-date hazards (1/6,1/2,1), then Never. Players0
and1 have equal Quit/Continue endpoints 3/2 and 1/6. Player2's Quit
payoff is 0; its initial Continue endpoint is −7/6, and the best
continuation on the event that no opponent quits is 0. Thus its full
Continue plan cannot improve. The quiet omitted player3 receives −5
and can Quit for 1, gaining 6.

For child023 use first-date hazards (1,1/3,2/5), then Never. Players2
and3 have equal endpoints 4/5 and 1/3. Player0's Quit payoff is 1;
Continue followed by its optimal late Quit gives −1/5. The quiet
omitted player1 receives −4 and can Quit for 1, gaining 5.

Thus for each of the fourteen children there exists an omitted player
for whom no universal inequality of the stated kind holds: the entire
right side vanishes at the displayed equilibrium and the left side is
strictly positive. This does not exclude all equilibria of any child,
nor every possible quiet-extension construction.

## Adapter, consumer, and Lean handoff

The new raw predicate should record the sign pattern and (1), using the
literal `quittingSingletonMatrix`. The needed new algebra consists of
(2), the larger-root characteristic and reconstruction identities, and
the positivity argument (3)–(5). It should not redefine the existing
smaller-root `StrictTests` to mean the larger branch.

From those scalars construct q and V by (6). Equations (7)–(9) give
the `arc`, `active`, and `soloFloor` fields of
`BalancedSingletonCycleCertificate` with four distinct cyclic owners.
Every q_j is positive and less than one, so its `opponentDivergence`
field is immediate. The existing
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` then
consumes the produced certificate at the target (10).

A narrow theorem shape is: for every raw reward table satisfying the
larger-branch predicate, its explicitly reconstructed target is an
`IsUniformEquilibriumPayoff none`. A relabeling wrapper transports the
four cyclic indices. No new general mesh compiler or strategy-space
compactness theorem is needed. The rational table, both eigenvalues,
all sixteen coarse identities, and its positive unrefined regret are
useful finite regression tests.

The larger-branch producer and the calculations in this manuscript are
ordinary mathematics; the separately named certificate consumers and
source tests are existing Lean declarations. No Lean-checked status for
the new producer is asserted here.

## Scope and nonclaims

The theorem is an actual-data producer on a strict full-dimensional raw
class, with arbitrary signed own singletons and unrestricted nonsingleton
rewards. The target is fixed before accuracy, while the refinement and
horizon threshold may depend on accuracy. Its complete deviation bound
uses every player's own deleted-opponent survival, not merely the joint
absorption tail.

There is no assertion at D=1 or det Γ=0, no general openness principle
for UE, and no claim of completeness of four-clock constructions. The
fixture's source comparisons distinguish failure of explicit raw
criteria from failure of all conditional interfaces. Its absence of
exact stationary Nash does not assert absence of uniform equilibrium:
the theorem supplies such an equilibrium payoff directly.
