# Complementary odds for two scheduled pairs

## 1. Statement and counterexample restriction

Consider a four-player quitting game. At each live date the players
independently choose Continue or Quit, with full observation of past
actions. The first nonempty quitting coalition S absorbs forever at
the arbitrary real reward vector r(S). Live rewards and the payoff on
joint Never are zero. Deviations are unrestricted behavioral strategies.
Write s_i=r_i({i}); these own rewards may have either sign.

Choose a partition into pairs A and B. Let a(i) be i's mate and O(i)
the opposite pair. Assume

    r_i({i,a(i)})≥r_i({a(i)})                    for every i,       (1)
    r_i({i}∪T)≤s_i                for every i and ∅≠T⊆O(i).       (2)

Then the ORIGINAL game has one uniform-equilibrium payoff: a fixed target
v such that for every ε>0 some behavioral profile delivers v within ε
and bounds every unilateral behavioral gain by ε at every sufficiently
large finite horizon. The target is chosen before ε.

Under strict (1) there is a stronger constructive conclusion when the
singleton matrix Γ, with Γ_ii=0 and Γ_ij=r_i({j})−s_i for j≠i,
is R₀ with nonzero minimum-map degree. The proof then produces one
exact period-two terminal Nash profile, and the same profile witnesses
one fixed uniform target. Inactive players are allowed. R₀ means that
x≥0, Γx≥0 and x_i(Γx)_i=0 imply x=0.

The raw Fin4 theorem does NOT assume this matrix property. The existing
original no-equilibrium source supplies R₀ and degree1 in the
contradictory branch. Weak equality in (1) uses reward closure; no exact
periodic profile is asserted on that boundary or on a matrix-source exit.

Consequently every Fin4 counterexample must satisfy, for EACH of its
three pair partitions, at least one of the following finite alternatives:

- Some player strictly prefers remaining outside its scheduled pair:
  r_i({i,a(i)})<r_i({a(i)}).
- Some opposite-pair joining reward exceeds its own singleton:
  r_i({i}∪T)>s_i for some player i and ∅≠T⊆O(i).

There is no supplied root, strategy, cone, continuation value or child
equilibrium in this restriction. It applies under every relabeling and
with arbitrary signed rewards. This proof is ordinary mathematics, not
a new Lean verification or an arbitrary-game completeness assertion.

## 2. Global nonlinear root production

Put

    Π_i=r_i({i,a(i)})−s_i,       K_i=r_i(O(i))−s_i,
    c_i=Π_i−Γ_i,a(i)=r_i({i,a(i)})−r_i({a(i)}.

For now c_i>0. The signs of Π and K remain arbitrary. If O(i)={j,k},
define on the nonnegative orthant

    N_i(X)=c_iX_a(i)(X_j+X_k+X_jX_k)
             +Π_iX_a(i)²/(1+X_a(i))−K_iX_jX_k.            (3)

We produce a NONZERO nonlinear complementarity solution

    X≥0,       e=ΓX−N(X)≥0,       X_i e_i=0 for every i.    (4)

The origin always solves (4); existence of some root is not enough.
Neither N≥0 nor positivity of Γ⁻¹ is assumed.

### Compactness of all feasible points

The closed set E={X≥0:ΓX≥N(X)} is bounded. This uses c>0 and Γ_ii=0,
but no R₀ or degree hypothesis. Suppose instead Xⁿ∈E and
t_n=ΣXⁿ_i→∞. Pass to a subsequence with Xⁿ/t_n→u≥0 and Σu_i=1.
Choose u_j>0 and i=a(j). Writing O(i)={k,l}, factor (3) as

    N_i=c_iX_j(X_k+X_l)+(c_iX_j−K_i)X_kX_l
              +Π_iX_j²/(1+X_j).                          (5)

Since Xⁿ_j→∞, the second coefficient is eventually nonnegative.
The final term has absolute value at most |Π_i|Xⁿ_j=O(t_n).
If u_k>0 or u_l>0, the first term has a positive order-t_n² lower
bound, contradicting (ΓXⁿ)_i=O(t_n)≥N_i(Xⁿ). Hence u is supported
on {i,j}. Drop the first two nonnegative terms, divide by t_n and
take limits. The zero diagonal gives Γ_ij u_j≥Π_i u_j, impossible
because Γ_ij=Π_i−c_i<Π_i and u_j>0. Thus E is compact.
Singleton normalized supports and mixed signs of Π,K are included.

### Total degree zero versus local degree nonzero

For λ≥0 define a continuous map on ℝ⁴ by

    H_λ(x)=min(x,Γx−N(x⁺)−λ1),                           (6)

with coordinatewise minimum and positive part. A zero has x≥0,
nonnegative residual, and complementary coordinates. Every zero for
EVERY λ≥0 therefore lies in E. Boundedness of ΓX−N(X) on E
gives a finite Λ>0 for which H_Λ has no zero. A large ball containing
E has no boundary zero throughout λ∈[0,Λ], so the total degree
of H₀ there is zero.

Under R₀, h(x)=min(x,Γx) has its sole zero at0. Homogeneity and
compactness of the unit sphere give ‖h(x)‖≥a‖x‖ for some a>0.
Equation (3) gives N(x⁺)=O(‖x‖²). Since minimum is Lipschitz in
its second argument, min(x,Γx−θN(x⁺)), 0≤θ≤1, has no zero
on a sufficiently small sphere. Its local degree at0 is therefore the
nonzero homogeneous minimum-map degree. Excision contradicts total
degree zero if0 were the only zero. This produces X≠0 in (4),
without a regularity assumption, finite root count or Jacobian sign.

The argument works inside ONE scalar chart, avoiding an additional
ambient-degree identification. Choose R>0 with E⊂(−R,R)⁴ and pull
the negative fields H_λ back to [−2R,2R]⁴ as cube gain fields.
On the central region corresponding to (−R,R)⁴, including its closure,
cube solutions are exactly field zeros. Its degree is zero by the
λ-homotopy. Let V be a sufficiently small ball's preimage in the SAME
chart. The θ-homotopy preserves its degree. For h, solution-set
excision equates the degree on V with its central degree, which equals
the canonical R₀ integer by scalar-radius invariance. If H₀ had only
the zero root, excision for H₀ would contradict these two degrees.
No arbitrary-chart comparison is required.

### Singleton supports are impossible

Suppose only X_j>0. All N_l vanish except possibly at i=a(j).
Feasibility forces Γ_lj≥0 outside that row, and in the mate row

    Γ_ij≥Π_i X_j/(1+X_j).                                (7)

For Π_i<0 this is impossible: Γ_ij=Π_i−c_i<Π_i, whereas the
right side exceeds Π_i. For Π_i≥0 it forces Γ_ij≥0 too.
Thus a feasible singleton support would make column j nonnegative,
giving a nonzero homogeneous LCP root at the jth unit vector, contrary
to R₀. The produced root has at least two positive coordinates.

## 3. Actual strategies and unrestricted deviations

Set q_i=X_i/(1+X_i). At even live dates schedule A with its hazards,
while B Continues; at odd dates schedule B. All draws are independent.
No extra observation or public lottery is used. Inactive q_i=0 are
allowed. Each player has a positive-hazard opponent, so its opponents'
survival probability over one whole period is

    ρ_i=∏_{j≠i}(1−q_j)<1.                               (8)

The scheduled-phase and passive-phase templates are

    U_i=s_i+Π_iq_a(i),             W_i=s_i+c_iX_a(i).      (9)

At the scheduled phase, forced Quit pays U_i. Continue, using W_i
when the mate also continues, pays exactly

    q_a(i)(s_i+Γ_i,a(i))+(1−q_a(i))W_i=U_i.              (10)

At the passive phase let D_i=(1+X_j)(1+X_k). Continue, using U_i
when both opponents continue, pays

    [U_i+X_jr_i({j})+X_kr_i({k})+X_jX_kr_i({j,k})]/D_i
        =W_i+e_i/D_i.                                   (11)

All simultaneous exits are included. Passive forced Quit is a convex
combination of s_i and the three rewards in (2), so is at most s_i≤W_i.

If X_i>0 then e_i=0. Equations (10)–(11) are the prescribed-policy
recursions, with both scheduled actions equal U_i. Opponent contraction
in (8) makes the templates the unique bounded actual values.

If X_i=0, the player Continues in BOTH phases. The templates must be
corrected. Put p=q_a(i), d=1/D_i. Solving the two policy equations gives

    ΔW_i=(e_i/D_i)/(1−d(1−p))≥0,
    ΔU_i=(1−p)ΔW_i≥0,
    W_i^act=W_i+ΔW_i,       U_i^act=U_i+ΔU_i.             (12)

The denominator is positive by (8). These are actual finite values
because opponent stopping has a geometric tail. Scheduled forced Quit
still pays U_i≤U_i^act; Continue pays U_i^act. Passive forced Quit
is at most s_i≤W_i≤W_i^act; Continue pays W_i^act. Thus every
policy equation and every endpoint inequality holds for inactive players
as well. Negative template or actual values cause no problem.

Iterate the inequalities under any unilateral behavioral strategy.
Conditional on still being live, all previous actions were Continue;
the next random action simply mixes the two endpoints. After m periods
the absolute terminal remainder is bounded by a finite constant times
ρ_i^m, which tends to zero, including under Never. Thus the profile
is exact terminal Nash against all behavioral deviations.

For a direct uniform bound set M=max_{S,i}|r_i(S)| and ρ=max_iρ_i<1.
Under any unilateral deviation absorption occurs no later than the first
opponent quit; its expected number of live dates, including the initial
date, is at most C=2/(1−ρ). The same bound holds under the prescribed
profile. Pathwise the N-date average differs from the terminal reward
by at most M times the number of initial live dates divided by N.
Thus target error is≤MC/N and every finite-horizon gain is≤2MC/N.
The target is the ACTUAL phase-A vector from (9)–(12), fixed once X
is chosen. The initial live reward remains zero; no exact finite-N
equality with the terminal target is asserted.

## 4. Original-game source and weak closure

Suppose a raw strict table has no uniform payoff. The literal theorem
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
supplies R₀ and degree1 for THIS singleton matrix, with no sign,
normality or auxiliary-no-equilibrium inputs. Its R₀ dependency is
`finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`.
Sections2–3 produce an original-game uniform payoff, a contradiction.

For weak (1), increase only the four scheduled-pair PARTICIPANT entries
by δ>0. Singletons and every entry in (2) are unchanged; all c_i
become c_i+δ>0. The tables differ by at most δ in every coordinate.
Apply the strict result at every δ and
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
It selects one fixed target for the original table, allowing approximating
targets to vary. This proves the weak theorem and Section1's restriction.

All strategic inputs are produced. The original source supplies the
matrix property in the contradictory branch; degree supplies nonzero
odds; support exclusion supplies absorption; (9)–(12) give actual values;
endpoint iteration gives complete behavioral caps; geometric absorption
gives uniform horizons. Weak closure needs no exact limiting profile.

## 5. Exact signed and inactive boundary test

Take

    Γ=[[0,1,−2,−1],[1,0,−1,−2],
       [3/2,−1,0,−1/2],[−1,3/2,−1/2,0]],

schedule01/23, own vector s=(1,1,1,1), and

    Π=(2,2,−1/4,−1/4), K=(7,7,0,0), X=(1,1,0,0).

Then c=(1,1,1/4,1/4)>0 and e=(0,0,1/2,1/2). The templates
are U=W=(2,2,1,1), but the actual values at BOTH phases are
(2,2,7/6,7/6). The inactive correction is (1/8)/(3/4)=1/6.
All cross-pair participant and relevant triple cap entries can equal1;
all unused coordinates are arbitrary. This is a complete-table-compatible
stress test, not new-coverage evidence.

The six principal pair determinants are−1,3,−1,−1,3,−1/4;
the four triple determinants are1/2,1/2,−1/4,−1/4; the full
determinant is2. Every column has a negative entry, so Γ is R₀.
At offset−1 its sole root is (5/2,5/2,1/2,1/2), with positive
determinant2, giving degree1. These matrix checks are not needed to
verify the displayed root but show compatibility with the actual source.

Replacing every nonempty reward of player i by that reward plus s_i−1
allows any signed own vector with the same gaps and root. In particular
s=(−3,2,−1,4) gives target (−2,3,−5/6,25/6). This applies the
theorem directly to a new table, not a terminal-translation rule for
profiles with positive Never mass.

## 6. Complete new-coverage table

Set D=52104052 and

    K=(−4711507/97125,−41341/22950,36491/10300,−94597/7650).

These are all fifteen coalition vectors:

| S | r(S) |
|---|---|
| 0 | (1,0,4,4) |
| 1 | (4,1,0,0) |
| 2 | (0,4,1,0) |
| 3 | (0,0,0,1) |
| 01 | (1/2,1/2,0,0) |
| 02 | (1/2,0,−D,0) |
| 03 | (2,1+K₁,1+K₂,5) |
| 12 | (1+K₀,5,1,1+K₃) |
| 13 | (0,1/2,0,1/2) |
| 23 | (0,0,−D,1/2) |
| 012 | (1/2,−10,100,0) |
| 013 | (−10,1/2,0,−10) |
| 023 | (−10,0,−D,−10) |
| 123 | (0,−10,100,1/2) |
| 0123 | (1000,1001,1002,−104) |

On schedule03/12, c=(2,1,1,1)>0 and all twelve caps are strictly
below1. Thus an open full-table neighborhood also satisfies the strict
criterion, with no equality-stratum restriction. The displayed table,
not a guessed neighborhood radius, is used for the comparisons below.

The singleton data are

    Γ=[[0,3,−1,−1],[−1,0,3,−1],[3,−1,0,−1],[3,−1,−1,0]],
    Γ⁻¹=(1/13)[[2,5,−7,13],[5,6,−11,13],
                [1,9,−10,13],[1,9,−23,26]].             (13)

Pair determinants in order01,02,03,12,13,23 are(3,3,3,3,−1,−1);
triple determinants in order012,013,023,123 are(26,−10,6,2);
det Γ=13. Each column has a negative entry. Hence no nonzero
homogeneous LCP root has singleton support, and no larger support is
possible because its principal submatrix is nonsingular: Γ is R₀.
At offset−1 the positive singleton entries force z₀,z₁,z₂>0.
If z₃=0 their equalities give all three1/2, leaving fourth residual
−1/2. Otherwise the unique root is (1,1,1,1), with positive determinant.
The finite-root formula gives degree1, hence standard Q. The declarations
are `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

Only child012 has positive inverse; the other three have respectively
diagonal entries−3/10,−1/6,−1/2. Its outside inverse row is
(−1,−9,23)/26, defeating passive inverse factorization.
The negative full inverse column excludes nonnegative-inverse criteria,
even after positive affine playerwise transport. A signed-column criterion
Γ⁻¹diag(σ)>0 uniquely forces σ=(1,1,−1,1). On03/12 it fails
σ₂c₂>0; on01/23 and02/13, K₂=−1 and it fails σ₂K₂≤0.
Thus all schedules fail that raw criterion. The favorable graph
0→1→2→0,3→0 has unequal indegrees and is neither a matching
nor a four-cycle. Every row has two below-own singleton entries and
pair13 is negative in both directions. These exact signs exclude
matching chambers, transitive Klein-four forms and tournament signs.

## 7. Child and withdrawal sources

For a child S and omitted player k, elementary nonnegative join rows
require, for every nonempty T⊆S,

    r_k(T+k)−r_k(T)≤Σ_{i∈S}λ_i[r_i(T+i)−r_i(T)], λ_i≥0.  (14)

Thirteen children fail a single row. The vectors list child joining
gains in increasing child order. Put d_i=−1/2−K_i.

| S | T | k | Child joining gains | Omitted gain |
|---|---|---|---|---|
| 0 | 0 | 1 | (0) | 1/2 |
| 1 | 1 | 3 | (0) | 1/2 |
| 2 | 2 | 0 | (0) | 1/2 |
| 3 | 3 | 0 | (0) | 2 |
| 01 | 1 | 3 | (−7/2,0) | 1/2 |
| 02 | 0 | 1 | (0,−D−4) | 1/2 |
| 12 | 12 | 0 | (0,0) | d₀ |
| 23 | 3 | 0 | (−D,0) | 2 |
| 03 | 03 | 1 | (0,0) | d₁ |
| 13 | 13 | 2 | (0,0) | 100 |
| 013 | 13 | 2 | (−10,0,0) | 100 |
| 023 | 03 | 1 | (0,−D−1−K₂,0) | d₁ |
| 123 | 123 | 0 | (0,0,0) | 1000 |

Here d₀>40,d₁>1. For012, omitted3, the J rows at0 and02 give
1≤λ₁/2−(D+4)λ₂ and −10≤−10λ₁, which are inconsistent.
The literal elementary source is `CappedClockParentFutureJoinCertificate`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`.

For every displayed child except123, prescribing T as a sure coalition
is exact child terminal Nash. Its members do not gain by withdrawing:
solos have positive own rewards; pair03 gives2,5 versus0,4; pair13
gives1/2,1/2 versus0,0; pair12 gives5,1 versus4,0. Nonmembers'
joining gains are nonpositive. The profile has zero child debt and
zero Never but positive omitted gain. Thus no universal omitted-gain
bound by a fixed nonnegative weighted sum of child debts and Never
can hold for these children.

For123 use q₁=D/(D+100), q₂=1/21, q₃=1. Players1,2 have
both endpoint values0. Player3's Quit value is
1/2+(1−q₁)(1−q₂)/2>0; its Never payoff is negative, since only
opponent pair12 contributes, with reward1+K₃<0. This is exact child
terminal Nash with zero Never. Omitted0 has Never value0 and immediate
Quit gain5210405575/136773399>0, defeating the same universal bound.

For012 we instead exclude the five actual RAW withdrawal variants;
we make no universal child-profile assertion. Their singleton withdrawal
gains are nonpositive. The patient floor is≤max(s_i,0)=1; deadline's
floor is≤0; security's LP has its own-singleton row, giving value≤1,
and its maximum with the deadline floor is still≤1. For nonsingleton
T a member's withdrawal gain is exactly r_i(T\{i})−r_i(T).

Let λ,μ≥0 be arbitrary advance and withdrawal weights. In J(T0),
F(T1), and F(T12), every withdrawal contribution is nonpositive.
At12 both nonzero withdrawal gains are−1: 4−5 for1 and0−1 for2.
The necessary rows therefore give

    1≤λ₁/2−(D+4)λ₂,
    1≤−3λ₀+λ₂,
    −K₃≤−K₀λ₀−4λ₁.                                    (15)

The first two force λ₁≥2+2(D+4)(1+3λ₀). The final right side
is at most−8−8(D+4)+[−K₀−24(D+4)]λ₀<0, whereas−K₃>0.
For patient/cancellation the nonpositive withdrawal contributions were
dropped from F; for deadline and both security variants they are absent.
Thus all five raw withdrawal F/J certificates fail for012 as well.

The exact definitions and bounds are `WithdrawalFutureJoinKind.gain`,
`WithdrawalFutureJoinKind.futureWeight` and
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
`patientWithdrawalFloor_le_ownNeverAlternative` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`,
`deadlineWithdrawalZeroFloor_le_zero` and `deadlineWithdrawalGainFloor`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
and `deadlineWithdrawalSecurityValue_le_singleton` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`.
The universal bound used for the other children is the conclusion of
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
These are failures of literal raw deletion sources, not of every possible
specially selected safe child equilibrium.

## 8. Other finite source comparisons

### Premium traps, weights and aggregate charges

A premium trap is a nonempty E such that each i∈E has some coalition
T⊆E containing i with r_i(T)>s_i. Exactly03 andI are traps here.
No player has globally nonnegative participant premiums: use01 for0,1,
02 for2, and13 for3. Greatest-core≤3 and protected-player criteria fail.

A global forced-Quit floor weight λ≥0 must obey
Σ_iλ_i[r_i(T+i)−s_i]≥0 on EVERY nonempty T. AtT1 the coefficient
vector is(−1/2,0,0,−1/2), forcing support⊆{1,2}; atT3 the remaining
coefficients are−1/2 and−D−1, forcing λ=0. Separately r(013)<s
coordinatewise, so no nonzero nonnegative weight has a floor on every
actual reward row either. These are different tests. The implemented
weighted consumer is `exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`.

At trapI, intermediate coalition13, the sum of nonparticipants' participant
premiums is88 and their joining differences sum to90. Both are positive,
violating the nonpositive larger-trap charge tests, including combinations
with separate pair traps. At q₀=q₃=1/2,q₁=q₂=0 both active
forced-Quit values3/2 and3 exceed own1. Thus the predicate
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
fails, and so does its supportwise-balance sufficient condition
`hasProductLowQuittingPremium_of_supportwiseBalance` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumProductLow.lean`.

### Quotients and temporal raw forms

All Γ row sums are1. Thus a nonnegative weight with Γᵀλ≤0 vanishes.
These sums also exclude all fourteen nondiscrete response-invariant
partitions after positive affine playerwise transport. Differentiating
response equality at zero block hazards equates all blockwise singleton
row sums for two recipients in one block. Summing over source blocks
forces their positive row scales equal. At all-sure hazards the four
original response displacements1000,1001,1002,−104 are distinct,
incompatible with equal row scales. Translations cancel. The exact
necessity is `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

No proper two-pair profile with EVERY phase value below its own level
can produce this table. On03/12 players0,1,3 have positive active
premiums. On01/23 player1 has c₁=1/2>0; on02/13 player0 has
c₀=1/2>0. Equation (9) forces an above-own active or passive value
in each case. These are all pair partitions and relabelings; the argument
excludes that output form without guessing a local neighborhood's radius.

Only012 has the directed favorable child three-cycle, so a cyclic-child
pivot must be3. The outside inverse row fails as above; resonance and
contrary-degree exits fail at degree1. The only pivot pair with both
participant premiums positive is03, whose passive child2 increment
K₂>0 violates the nonpositive joint-outsider requirement. Pairs13 and23
have negative pivot premiums; none has zero pivot premium. A source
requiring two nonnegative pivot singleton gaps also fails, since pivot3
has only one. These are intrinsic raw nonmembership tests. Their named
sources include `RawRows` and `exists_uniformPayoff_of_resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`,
`outsideInverseWeight_eq` and `exists_uniformPayoff_of_passiveNumerators`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`,
and `CyclicChildJointPhase.RawTable` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`.

### Polynomial guards, conditional ranges and anchors

For every ordered owner/passive pair, a pure-face weak-unit guard fails.
A lower witness T avoids both players and has negative owner joining
gain. An upper witness contains the owner, omits the passive player,
and has positive passive joining gain.

| owner, passive | Face | T | Difference |
|---|---|---|---|
| 0,1 | lower | 23 | −10 |
| 0,2 | lower | 1 | −7/2 |
| 0,3 | lower | 1 | −7/2 |
| 1,0 | lower | 23 | −10 |
| 1,2 | upper | 01 | 100 |
| 1,3 | lower | 02 | −10 |
| 2,0 | lower | 3 | −D |
| 2,1 | lower | 0 | −D−4 |
| 2,3 | lower | 0 | −D−4 |
| 3,0 | upper | 3 | 2 |
| 3,1 | lower | 02 | −10 |
| 3,2 | lower | 01 | −10 |

The predicates `QuittingOneSidedWeakUnitGuards` and
`QuittingOneSidedWeakUnitRawGuards`, and consumer
`exists_uniformPayoff_of_oneSidedWeakUnitGuards`, are in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
Every singleton also has a profitable join by Section7, excluding the
instant-no-join alternative. For `IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`,
player2 has Continue upper at least4, while both Quit lower bounds are
at most1 for every blocker. The empty background gives the first bound,
and pairs02,12,23 give the second. No required convex combination
can strictly exceed the Continue upper bound.

Membership influence changes sign: adding1 changes player0's joining
gain by−9/2 at empty background and by−1−K₀>0 at background2.
This excludes `SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

Every player has a negative joining comparison: use backgrounds1,23,0,02
for players0,1,2,3, giving−7/2,−10,−D−4,−10 respectively.
Thus no player satisfies the raw one-shot anchor condition of a
nonnegative own reward and nonnegative joining gaps on every nonempty
opponent coalition. The stronger comparison with all sure-quitter
stationary profiles is established next.

## 9. No sure-quitter stationary producer for the table

Fix a proposed stationary sure quitter j. The other three players must
play Nash in the finite two-action game with j present. Additionally
j must prefer its immediate Quit payoff to Never against those stationary
opponents. The following endpoints completely specify the other players'
multiaffine Quit-minus-Continue differences. Each quadruple corresponds
to the two listed hazards at (0,0),(1,0),(0,1),(1,1).

| j | Recipient i | Other variables | Difference endpoints |
|---|---|---|---|
| 0 | 1 | (q₂,q₃) | (1/2,−10,d₁,1001) |
| 0 | 2 | (q₁,q₃) | (−D−4,100,−D−1−K₂,1002) |
| 0 | 3 | (q₁,q₂) | (1,−10,−10,−104) |
| 1 | 0 | (q₂,q₃) | (−7/2,d₀,−10,1000) |
| 1 | 2 | (q₀,q₃) | (1,100,100,1002) |
| 1 | 3 | (q₀,q₂) | (1/2,−10,d₃,−104) |
| 2 | 0 | (q₁,q₃) | (1/2,d₀,−10,1000) |
| 2 | 1 | (q₀,q₃) | (1,−10,−10,1001) |
| 2 | 3 | (q₀,q₁) | (1/2,−10,d₃,−104) |
| 3 | 0 | (q₁,q₂) | (2,−10,−10,1000) |
| 3 | 1 | (q₀,q₂) | (1/2,d₁,−10,1001) |
| 3 | 2 | (q₀,q₁) | (−D,−D−1−K₂,100,1002) |

For j=0 write (x,y,z)=(q₁,q₂,q₃). If z>0, its nonnegative
difference1−11x−11y−83xy gives x,y≤1/11. Player2's difference
is at most−D(1−x)+1002x≤(−10D+1002)/11<0, forcing y=0.
Then both endpoints for player1 are positive, forcing x=1, impossible.
Thus z=0. The other differences are1/2−21y/2 and
−D−4+(D+104)x. Their unique equilibrium is
x=(D+4)/(D+104), y=1/21, where player3's difference is negative.

For j=1, player2's four endpoints are all positive. Hence q₂=1;
player0 is forced sure and player3 forced inactive. The only profile
is therefore (1,1,1,0).

For j=2 write (x,y,z)=(q₀,q₁,q₃). At z=0 player0 is sure,
then y=0. At z=1 the other differences are−10+1010y and
−10+1011x. Their equilibria are (0,0),(1,1), and
(10/1011,1/101); (1,1) fails player3's sure condition.
If 0<z<1, x cannot be0 or1 by player3's difference, so x is mixed.
If y=0, mixed x,z equal1/21, where player1's difference1001/441
is positive. If y=1, player0 is forced sure. At an all-proper point
player3's equation forces x>1/21. Player1's equation
1−11x−11z+1022xz=0 then forces x>1/11 and z<11/1022<1/21.
Player0's difference is at least1/2−21z/2>0, a contradiction.

For j=3 write (x,y,z)=(q₀,q₁,q₂). If z=0, player1 is sure,
then player0 inactive, and player2 has positive difference100.
Thus z>0; its nonnegative difference gives y≥D/(D+1002)>1/2.
If y<1, player1's nonpositive difference gives z≥1/21. On that
rectangle player0's difference2−12y−12z+1022yz is positive:
both derivatives are positive and its lower-corner value is−4+499/21>0.
Thus x=1, making player1's difference d₁(1−z)+1001z>0,
a contradiction. Hence y=1, then z=1 and x=1.

The resulting complete census and the sure player's failures are:

| j | Full hazards | Failure |
|---|---|---|
| 0 | (1,(D+4)/(D+104),1/21,0) | Q₀−Never₀<0 |
| 1 | (1,1,1,0) | Q₁−Never₁=−10 |
| 2 | (0,0,1,1) | Q₂−Never₂=−D |
| 2 | (1,0,1,0) | Q₂−Never₂=−D−4 |
| 2 | (10/1011,1/101,1,1) | Q₂<0<Never₂ |
| 3 | (1,1,1,1) | Q₃−Never₃=−104 |

At j=0, with x=(D+4)/(D+104), y=1/21, the actual values are

    Q₀=1/2+(1−x)(1−y)/2,
    Never₀=[4x(1−y)+(1+K₀)xy]/(x+y−xy).

Their difference is−724795040468913623231/692156460057385664250.
At the mixed j=2 point, Q₂≤(−100D+1002)/101<0, while
Never₂=(1+K₂)(10/1011)(100/101)>0. All other comparisons are
literal pure coalition rewards. Every opponent stopping law used here
absorbs surely or geometrically. Thus the census excludes every stationary
terminal equilibrium with a sure quitter, including every pure exit.

No absence of all-proper stationary equilibria is claimed. An existential
local theorem at a different center does not certify this table's
membership without an actual radius or another usable predicate. For
example `PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
is a local theorem, not a blanket producer from (1)–(2). These comparisons
are bounded evidence against literal raw tests and specified output forms,
not a statement that every possible equilibrium architecture is absent.

## 10. Implementation handoff and semantic boundary

A raw finite predicate should store only a pair partition, the four
comparisons (1), and the twelve comparisons (2). It must not store odds,
phase values, an equilibrium or a matrix-degree assumption. The strict
R₀/nonzero-degree lemma first bounds E and then uses the two homotopies
in one chart to obtain (4). It must retain the support-size bound and
the actual inactive corrections (12) needed by the strategy compiler.

The exact degree interfaces are `r0Degree` and
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`,
`BoxComplementarityProblem.ofAmbientMap` and
`isSolution_ofAmbientMap_iff_of_coordinateInterior` in
`MathUE/Topology/BoxComplementarityAmbientMapAdapter.lean`,
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq` in
`MathUE/Topology/BoxComplementarityStabilizedLocalDegree.lean`,
`BoxComplementarityProblem.localDegree_eq_of_solutionsIn_eq` in
`MathUE/Topology/BoxComplementaritySolutionExcision.lean`, and
`BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero`
in `MathUE/Topology/BoxComplementarityLocalDegreeConsequences.lean`.
The last declaration contrapositively gives zero degree on an empty
isolating region. The whole-cube degree-one statement is not applied
to the selected central region.

Define phase0 to schedule A and phase1 to schedule B. Sections2–3
produce exact policy recursion, both pure endpoint inequalities and
playerwise opponent contraction. These are precisely the hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The root endpoints and mixture identity are defined in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
Compose with the literal original no-UE source and weak reward closure
from Section4. This is a raw producer, not a supplied-certificate
interface. No new Lean seal, public-randomization capability, unrestricted
positive-gap example or resolution of arbitrary Fin4 is claimed.
