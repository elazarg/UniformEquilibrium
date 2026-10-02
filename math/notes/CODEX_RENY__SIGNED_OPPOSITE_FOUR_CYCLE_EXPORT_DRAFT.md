# A signed singleton-comparison class with uniform equilibrium

Author: `CODEX_RENY`.
Source: [complete signed-cycle proof](../notes/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md).
Independent whole-source reviews: [CODEX_SKEPTIC](../feedback/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER__BY_CODEX_SKEPTIC.md),
[CODEX_FRECHET_CYCLE](../feedback/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER__BY_CODEX_FRECHET_CYCLE.md),
both PASS with no unresolved mathematical objection.
Final assembled-surface confirmations: CODEX_FRECHET_CYCLE (Section 9 of the
review above) and [CODEX_HILBERT](../feedback/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_EXPORT_DRAFT__BY_CODEX_HILBERT.md),
both PASS with no unresolved mathematical objection.

## Exact statement

Let I={0,1,2,3}, with indices on players and phases interpreted modulo four.
A quitting reward table assigns a real vector r(S)∈ℝ⁴ to every nonempty
coalition S⊆I. Infinite all-Continue pays zero. Write

    sᵢ=rᵢ({i}),                 Γᵢⱼ=rᵢ({j})−sᵢ.

Suppose its twelve off-diagonal singleton comparisons satisfy

    Γᵢ,ᵢ₊₁=−bᵢ<0,      Γᵢ,ᵢ₊₂=gᵢ∈ℝ,      Γᵢ,ᵢ₊₃=hᵢ>0.       (1)

Define aᵢ=gᵢ/bᵢ, dᵢ=hᵢ/bᵢ, and calculate the following real quantities
from the table:

    X=a₀d₁+(a₀a₁+d₀)a₂,             Y=(a₀a₁+d₀)d₂,

    K = [ a₃X+d₃(d₁+a₁a₂)    a₃Y+d₃a₁d₂ ]
        [ X                   Y             ],

    Δ=(K₀₀−K₁₁)²+4K₀₁K₁₀,
    λ=(K₀₀+K₁₁−√Δ)/2.                                      (2)

Require, in order,

    Δ>0,       λ>1,       K₀₁<0,       K₀₀−λ>0;

    A=1/λ,     W₀=−K₀₁,              W₁=K₀₀−λ,
    W₃=A(a₂W₀+d₂W₁)>0,
    W₂=A d₁W₀+a₁W₃>0.                                      (3)

The square root and divisions are therefore well-defined. The smaller
eigenvalue in (2) is intentional: K need not be nonnegative, and no Perron
theorem is assumed.

Theorem. For every reward table satisfying (1)–(3), set

    wᵢ=(1−A)Wᵢ/ΣⱼWⱼ,
    v⁰=Σⱼwⱼr({j})/(1−A).                                   (4)

Then v⁰ is a uniform-equilibrium payoff against all unilateral behavioral
deviations. Explicitly, for every ε>0 there are one behavioral product
profile σ and a horizon threshold n₀ such that, for every n≥n₀, σ is
ε-Nash for the n-stage average payoff and that payoff is within ε of v⁰
in every coordinate. The same σ is used at every n≥n₀.

There is also a direct finite-clock conclusion. For every e>0, integer
H≥1, ρ>0, and integer N₀≥0, the construction gives an integer
N≥max(H,N₀) and a product stopping law p on {0,…,N−1,Never} such that

    E_r(p)<e,                     R_p(N−H)<ρ.                (5)

Here E_r is unrestricted terminal exploitability, not merely finite-menu
regret. Consequently p is e-Nash in its actual finite timing menu.

All four own singleton levels sᵢ and all forty-four nonsingleton reward
coordinates are arbitrary real numbers. No punishment normality, positive
own singleton, supplied equilibrium, balanced cycle, or continuation value
is an assumption.

## Conjecture-facing change

This is a sufficient raw-data existence theorem on an explicitly tested
heterogeneous singleton-comparison class. The algebra in (1)–(3) produces
the cycle needed by the existing balanced-singleton semantic compiler.
It is not another verifier of a supplied cycle.

The exact heterogeneous examples below have full standard-Q singleton
matrix, no homogeneous simplex solution, and a non-projective-Q proper
principal. These properties, the strict producer conditions, and genuine
heterogeneity persist on an open comparison neighborhood. Thus the producer
adds collision-unrestricted heterogeneous input coverage beyond the named
cyclic raw producers and the ordinary non-Q, homogeneous, and full
projective-Q-bar matrix branches.

This is a bounded comparison with the relevant checked sources, not a
claim that each individual nonsingleton completion was previously unsolved.
Some completions can also satisfy other sufficient conditions. The
circulant base example is already covered by an existing cyclic criterion
and is not counted as new coverage. Arbitrary Fin4 existence and the
general early-absorption source question remain open.

## Definitions and assumptions

At each integer date every surviving player chooses Continue or Quit.
Choices use independent private randomization. The first nonempty quitting
coalition absorbs; its vector r(S) is the terminal payoff and the subsequent
absorbing reward. Before absorption the stage reward is zero. All histories
are perfectly observed, but the only unabsorbed public history at a given
date consists entirely of Continue actions. There are no public signals,
correlated recommendations, hidden state, or deviation detection.

A complete unilateral behavioral deviation may change the player's actions
at every history and date, with no time or memory bound. On the unique
unabsorbed history it determines a distribution over its first Quit date
in ℕ∪{Never}. Conversely every such distribution is implementable by its
conditional hazards. Independent player laws therefore give exactly the
relevant product stopping-law representation. Actions after absorption do
not change payoffs.

For a product law p, let Uᵢ(p) be its expected terminal payoff. Against p₋ᵢ,
write fᵢ(t;p₋ᵢ) for the payoff of the pure first-Quit date t, including
t=Never, and define

    Cᵢ(p)=sup[t∈ℕ∪{Never}] fᵢ(t;p₋ᵢ),
    E_r(p)=maxᵢ(Cᵢ(p)−Uᵢ(p)),
    R_p(t)=Pr_p(no player quits before date t).

The pure-date supremum equals the full behavioral cap by the mixture
representation just described. Payoffs are bounded because the table is
finite; fix any M>0 with |rᵢ(S)|≤M for all i,S. Never zero satisfies the
same bound. For a finite law on F_N={0,…,N−1,Never}, menu e-Nash means
fᵢ(t;p₋ᵢ)≤Uᵢ(p)+e for every i and t∈F_N. No finite-menu approximation
is silently treated as an unrestricted one.

## Source correspondence

All paths in this section are repository-relative. The new mathematics is
the raw signed reconstruction into the existing balanced-cycle interface;
no existing semantic compiler is claimed as new.

1. `quittingSingletonMatrix` in
   `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`
   is exactly Γᵢⱼ=rᵢ({j})−rᵢ({i}). `Normalization.lean` identifies the
   normalized singleton/projective matrices in this convention. The
   standard and projective LCP definitions used below are those of
   `MatrixClasses.lean`, not an opposite-sign convention.

2. `BalancedSingletonCycleCertificate` and its method
   `isUniformEquilibriumPayoff` in
   `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`
   are the intended supplied-object interface and checked consumer.
   Its fields are `owner`, `hazard`, `coarse`, `initial`,
   `hazard_nonneg`, `hazard_lt_one`, `arc`, `active`, `soloFloor`, and
   `opponentDivergence`. All are constructed below. The consumer derives
   the finite collision bound internally and preserves the fixed target
   against unrestricted behavioral deviations. The uniform quantifiers
   agree with `Game.IsUniformEquilibriumPayoff` in
   `GameTheory/GameTheory/Stochastic/Uniform.lean`.

3. `hasQuittingCanonicalEqualHazardTailData_iff` in
   `UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`
   already accepts a cyclic comparison matrix, a scalar survival in (0,1),
   polynomial balance, and nonnegative canonical tails. The circulant
   fixture Γ* below satisfies that criterion. The later
   `QuittingCyclicSingletonOpenSignData` is narrower: only its first forward
   offset may be negative. Neither interface supplies the heterogeneous
   class here. `CyclicSingletonTailData` in `CyclicSingletonTailProducer.lean`
   has one scalar survival and one tail depending only on relative cyclic
   offset; its recurrence forces Γ itself to be cyclically invariant.

4. `BalancedSingletonCycleCertificate.exists_escortCycle` in
   `CyclicSingletonEscort.lean` is a necessary graph consequence of supplied
   certificate data, not a heterogeneous raw producer.
   `isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate` in
   `CyclicKofNPlayerPhaseHazards.lean` consumes supplied phase hazards and
   exact root-Nash conditions. Arbitrary collisions do not give those exact
   coarse conditions, as the boundary test below demonstrates.

5. `exists_certificate_of_unitOutneighbor` and
   `FinFourIntegralTournamentBalancedSingleton.target_isUniformEquilibriumPayoff`
   in `UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`
   require a tournament-skew singleton matrix. A mutually negative pair
   excludes that class. The matrix calculations below also exclude the
   source hypotheses of the ordinary non-Q and homogeneous branches in
   `OrdinaryNonQClosure.lean` and `HomogeneousProducer.lean`, and the full
   projective-Q-bar source consumed by
   `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
   `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.

6. The inverse calculation uses the checked all-right-hand-side theorem
   `isStandardQMatrix_of_copositive_of_isR0Matrix` in
   `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`.
   The transfer through matrix inversion is proved explicitly below.
   `NormalCore.lean` defines the separate recursive algebraic normal core;
   it is not identified with punishment normality.

7. The bounded stationary comparison also inspected
   `QuittingPureSingletonChamber` and `QuittingPurePairChamber` in
   `Quitting/Classification/Existence/SureExitChambers.lean`,
   `QuittingInducedOwnerChamber` in
   `Diagnostics/Quitting/InducedOwnerChambers.lean`,
   `IsQuittingConditionalFaceGapRange` in
   `Quitting/Classification/Existence/ConditionalFaceGapRange.lean`, and
   `IsStrictFiniteOddBlockerCore` in
   `Quitting/Classification/Existence/FiniteOddBlockerCore.lean`, all below
   `UniformEquilibrium/`. Their respective collision signs, supplied induced
   Nash/owner-floor data, conditional face bounds, or passive-payoff identity
   are not produced merely by (1)–(3) with all nonsingleton coordinates free.
   This comparison does not assert disjointness for every reward completion.

8. The finite censor estimate is proved directly by coupling below. Relevant
   checked tools include `abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV`
   in `MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean` for arbitrary
   discrete laws, and `Math.PMFProduct.pmfTV_pmfPi_le_sum` and
   `abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV` in
   `MathUE/PMFProduct/TotalVariation.lean` for finite state spaces. The latter
   finite-state declarations are not silently applied to an infinite clock.

The construction is a direct algebraic argument, not an invocation of an
unverified paper theorem. No original-paper priority or literature-wide
nonduplication claim is made. Its semantic translation rests on the named
checked definitions and consumer; the two independent reviews additionally
reconstructed the behavioral proof and attempted to falsify the source
coverage. No Lean implementation of this new raw producer is claimed here.

## Proof

### 1. The signed reconstruction produces four positive hazards

The characteristic equation of K and the definition of λ give

    K(W₀,W₁)ᵀ=λ(W₀,W₁)ᵀ.

Indeed the first eigenvector equation cancels identically, and the second
is det(K−λI)=0. Positivity of W₀,W₁ follows from (3); positivity of W₂,W₃
is separately tested there. Also 0<A<1.

The definitions of W₂,W₃ imply

    W₂=A[(d₁+a₁a₂)W₀+a₁d₂W₁].

Consequently a₀W₂+d₀W₃=A(XW₀+YW₁)=W₁, using the second row of
AK(W₀,W₁)ᵀ=(W₀,W₁)ᵀ. Substitution in a₃W₁+d₃W₂ gives its first
row. Thus all four identities hold:

    W₁=a₀W₂+d₀W₃,          W₀=a₃W₁+d₃W₂,
    W₂=A d₁W₀+a₁W₃,        W₃=A(a₂W₀+d₂W₁).                 (6)

For k=0,…,4 define t_k=1−Σ[j<k]wⱼ, and for k=0,…,3 put

    q_k=w_k/t_k,             c_k=t_(k+1)/t_k=1−q_k.          (7)

Every wᵢ is positive and Σwᵢ=1−A. Thus t_k=A+Σ[j≥k]wⱼ,
t₀=1, t₄=A, and 0<q_k,c_k<1. The survival product telescopes:
∏c_k=A. Repeating the four roots, with only player k active at phase k
and hazard q_k, gives first-absorption weights w_k during one period.

Multiplying (6) by the appropriate positive bᵢ, and using (1), gives

    Σ[j>i]wⱼΓᵢⱼ+AΣ[j<i]wⱼΓᵢⱼ=0                 for every i. (8)

For i=3, its displayed identity in (6) results after canceling the common
factor A in (8). This is valid because A>0. No zero-survival case or
nonnegative-matrix eigenvector selection has been used.

### 2. Actual terminal values satisfy all sixteen phase floors

Let vᵏ be the actual terminal value of the infinite coarse cycle starting
at phase k. Absorption is almost sure because the period survival is A<1.
The values are bounded by M and satisfy the literal Bellman equations

    vᵏ=q_k r({k})+c_k v^(k+1),
    v⁰=Σⱼwⱼr({j})/(1−A).                                    (9)

Starting just after phase i, the first-period absorption weight of player j
is wⱼ/t_(i+1) if j>i, and Awⱼ/t_(i+1) if j≤i. These weights sum to
1−A. The case i=3 uses t₄=A and returns to phase zero. Subtracting sᵢ
from the geometric-resolvent value and using (8) gives

    v^(i+1)_i=sᵢ,                 vⁱ_i=sᵢ,                    (10)

where the second equality follows from Bellman at the owner's phase.

There are exactly two remaining phases for player i. Bellman at i+1 and
at i+3, respectively, gives

    0=−q_(i+1)bᵢ+c_(i+1)(v^(i+2)_i−sᵢ),
    v^(i+3)_i−sᵢ=q_(i+3)hᵢ+c_(i+3)(vⁱ_i−sᵢ).

Hence

    v^(i+2)_i−sᵢ=q_(i+1)bᵢ/c_(i+1)>0,
    v^(i+3)_i−sᵢ=q_(i+3)hᵢ>0.                              (11)

Together (10)–(11) prove every player's singleton floor at every phase.
The sign of gᵢ was never restricted. Every player also faces positive
hazards from three distinct opponents. With owner(k)=k and initial phase
zero, (7), (9), (10), and (11) therefore supply every field of
`BalancedSingletonCycleCertificate` for the actual table.

### 3. Fine cycles control all behavioral deviations

Fix an integer L≥1. Replace coarse phase i by L consecutive dates on
which only i has hazard

    θᵢ=1−cᵢ^(1/L).

The new period has 4L dates and the same survival cᵢ over phase i.
Its coarse values remain vᵏ. With m dates left in phase i, including the
current date, the actual value is

    (1−cᵢ^(m/L))r({i})+cᵢ^(m/L)v^(i+1),       0≤m≤L.

It is the convex combination of vⁱ and v^(i+1) with coefficient
(1−cᵢ^(m/L))/(1−cᵢ) on vⁱ. Thus every fine value retains every singleton
floor. The active owner's value is exactly sᵢ throughout its own phase.

For a passive player j≠i at an i-owned date, Quit gives

    Qⱼ=(1−θᵢ)sⱼ+θᵢrⱼ({i,j})≤sⱼ+2Mθᵢ.

Continue gives the prescribed value at that date and is at least sⱼ.
At a j-owned date, both Quit and Continue give sⱼ. At every date,
therefore, choosing Continue and then restoring the prescription has exactly
the prescribed value for j. Backward substitution shows that forcing j to
Continue through any finite prefix and then restoring the prescription
preserves Uⱼ=v⁰ⱼ exactly.

Fix a finite date t. Change this restored choice at t to Quit. The only
additional gain is the endpoint gain at t, multiplied by the probability
that no opponent quit earlier. This deleted-opponent reach is at most one.
The resulting pure-date response therefore satisfies

    fⱼ(t)−v⁰ⱼ≤η_L,              η_L=2M maxᵢθᵢ.               (12)

There is no sum of local errors over the preceding dates.

Never requires a separate limit. Under that response, opponents survive K
complete periods with probability βⱼᴷ, where

    βⱼ=∏[i≠j]cᵢ<1.

Never and forced Continue for those periods followed by restoration differ
in payoff by at most 2Mβⱼᴷ. The latter profile has payoff v⁰ⱼ, so Never
has exactly v⁰ⱼ as K→∞. This holds also when sⱼ or v⁰ⱼ is negative.
The stopping-law mixture representation now extends (12) to every complete
behavioral response. For the infinite fine profile σ_L,

    U(σ_L)=v⁰,                    E_r(σ_L)≤η_L→0.            (13)

This also proves the fixed uniform-payoff conclusion directly. For fixed L,
put β=maxⱼβⱼ<1. Under any unilateral response, survival after K periods
is at most βᴷ, uniformly in that response. The expected absorption date
plus one is consequently bounded by a finite constant depending only on
L and β, for example 4L/(1−β)+1. Since rewards are bounded, every n-stage
average payoff differs from its terminal payoff by a bound tending to zero
as n→∞, uniformly over all those responses. One may use
2M(4L/(1−β)+1)/n.

Given ε>0, first fix L with η_L<ε/2. Then choose n₀ so the last bound is
less than ε/4 for n≥n₀. Terminal regret plus the two average/terminal errors
is below ε, while prescribed average payoff is within ε/4 of v⁰. This is
one profile σ_L for all sufficiently large n, with the target independent
of L. Equivalently it is precisely the existing balanced-cycle uniform
consumer, not merely a horizon-dependent Nash sequence.

### 4. Actual finite laws satisfy every early-absorption quantifier

Given e>0, H≥1, ρ>0, and N₀≥0, first choose L so η_L<e/2. Since every
cᵢ lies in (0,1), choose an integer K≥1 with

    4MΣᵢcᵢᴷ<e/2,                       Aᴷ<ρ.                 (14)

Set T=4LK. For each player's independent stopping law in σ_L, map every
finite date at or after T to Never. The original marginal has no Never
mass and has remaining mass cᵢᴷ at T. Denote the product of censored laws
by p, and let δ=Σᵢcᵢᴷ.

Couple the original clocks and their literal censored images. Some clock
changes with probability at most δ, so each prescribed payoff changes by
at most 2Mδ. For a fixed unilateral pure-date or Never response, couple only
its opponents. Its payoff changes by at most
2MΣ[i≠j]cᵢᴷ≤2Mδ, uniformly over the response date, including every date
after T. Taking the supremum preserves that bound. Therefore

    E_r(p)≤η_L+4Mδ<e.                                       (15)

The joint Never mass of p is exactly ∏cᵢᴷ=Aᴷ, and every finite atom is
strictly before T. Choose N=max(T+H,N₀). Then N≥max(H,N₀), p is a law on
its actual finite menu F_N, and

    R_p(N−H)=Aᴷ<ρ.

Full regret was bounded before enlarging the finite menu. Thus this step
does not pad a finite-menu approximate equilibrium while ignoring the new
deviations. It proves (5) and completes the existence theorem.

## Boundary tests

### 1. A previously covered circulant test

Let all sᵢ=1 and let the comparison matrix be

    Γ* = [ 0  −1  −1   6 ]
         [ 6   0  −1  −1 ]
         [−1   6   0  −1 ]
         [−1  −1   6   0 ].

Then aᵢ=−1, dᵢ=6, and K=[55 −78; −13 42] has eigenvalues 16 and 81.
The selected λ=16 yields

    W=(78,39,39/2,39/4),          A=1/16,
    w=(1/2,1/4,1/8,1/16),        q=(1/2,1/2,1/2,1/2),

    v⁰=(1,4,2,1),       v¹=(1,1,4,2),
    v²=(2,1,1,4),       v³=(4,2,1,1).

Every identity follows by direct substitution. This is a positive check of
the formula, not new table coverage: the existing canonical equal-hazard
criterion accepts this cyclic table at survival 1/2, with closed tail
(0,0,2,6).

### 2. Exact heterogeneous tests

Change two entries in the first row to obtain

    Γ† = [ 0  −1  −9/10  29/5 ]
         [ 6   0  −1     −1   ]
         [−1   6   0     −1   ]
         [−1  −1   6      0   ].

Here

    K=[541/10 −381/5; −121/10 201/5],
    eigenvalues 16 and 783/10,
    W=(381/5,381/10,381/20,381/40).

Again A=1/16 and all hazards are 1/2. The first three displayed coarse
values for Γ* remain unchanged, and v³=(39/10,2,1,1). The ratios of the
two negative magnitudes in row zero and in the other rows are 10/9 and 1,
respectively. These ratios are unchanged by positive playerwise rescaling
or by column permutation. Thus no relabeling, even combined with positive
playerwise rescaling, makes Γ† cyclically invariant.

A second heterogeneous test genuinely uses unequal hazards:

    Γ‡ = [ 0 −1 −1  6 ]
         [ 9  0 −1 −1 ]
         [−1  4  0 −1 ]
         [−1 −1  4  0 ].

Now K=[56 −44; −16 28] has eigenvalues 12 and 72, and

    W=(44,44,22,11),             A=1/12,
    w=(1/3,1/3,1/6,1/12),       q=(1/3,1/2,1/2,1/2),

    v⁰=(1,4,2,1),       v¹=(1,1,3,3/2),
    v²=(2,1,1,3),       v³=(4,2,1,1).

All four balances, all sixteen Bellman entries, all owner equalities, and
all floors hold exactly for both examples. Their nonsingleton coordinates
are still arbitrary. Both independent reviews separately recomputed these
finite identities in exact rational arithmetic.

### 3. Exact placement outside the three large matrix branches

For a real matrix Γ, standard Q means that for every ξ∈ℝ⁴ there is z≥0
with w=ξ+Γz≥0 and zᵢwᵢ=0 for all i. A homogeneous simplex solution has
ξ=0 and Σzᵢ=1. A projective solution instead has α≥0, z≥0,
α+Σzᵢ=1, residual w=αξ+Γz≥0, and zᵢwᵢ=0. Projective Q-bar requires
projective solutions for every ξ on every nonempty principal submatrix.

All three fixture matrices have strictly positive inverses. The inverse
of Γ* is 1/1200 times

    [ 37 209  13  41 ]
    [ 41  37 209  13 ]
    [ 13  41  37 209 ]
    [209  13  41  37 ].

The other two exact inverses are

    (Γ†)⁻¹ = (1/11595) [ 370 2019  127  392 ]
                       [ 410  357 2021  121 ]
                       [ 130  396  358 2018 ]
                       [2090  123  404  334 ],

    (Γ‡)⁻¹ = (1/781) [ 17 91  11  27 ]
                     [ 39 25 209  16 ]
                     [ 14 29  55 206 ]
                     [139  9  44  37 ].

The determinants are −1200, −2319/2, and −781, respectively. Multiplication
on either side verifies each inverse exactly.

Put B=Γ⁻¹ for any fixture. For every nonzero x≥0, xᵀBx>0: every term
is nonnegative and a positive diagonal term is strictly positive. Hence B
is copositive and R₀, since a nonzero homogeneous complementary pair would
give xᵀBx=0. The checked copositive-R₀ theorem gives standard Q for B.
To transfer this through inversion, fix any ξ and solve the B-LCP at −Bξ.
Writing its variable as w and its residual as z gives

    w≥0,        z=B(w−ξ)≥0,        wᵢzᵢ=0.

Multiplication by Γ gives w=ξ+Γz, so z solves the Γ-LCP at ξ. This is
an all-right-hand-side argument, not a finite direction screen.

If Γ had a nonzero homogeneous complementary pair w=Γz≥0, z≥0, then
z=Bw and 0=zᵀw=wᵀBw. Strict copositivity forces w=z=0, a contradiction.
Thus Γ has no homogeneous simplex solution.

The principal matrix on {0,2} is [0 −u; −v 0] with u,v>0: u=v=1 for
Γ* and Γ‡, and u=9/10,v=1 for Γ†. At ξ=(−1,−1), projective residuals
are −α−uy and −α−vx. Their nonnegativity forces α=x=y=0, contrary to
α+x+y=1. Thus these full matrices are not projective Q-bar, including
its zero-cemetery alternative. Their algebraic normal core is all four
players: every player has its distinct negative successor at every recursive
normal-layer step.

This places the examples in the full-normal-core, standard-Q,
nonhomogeneous, non-projective-Q-bar matrix regime. It does not assert
that these UE games carry an actual positive terminal-gap or paid-port
counterexample source.

All inequalities in (1)–(3) are strict at the heterogeneous fixtures.
The chosen simple eigenvalue, the reconstructed coordinates, and matrix
inversion are continuous in a neighborhood of each fixture. Strict inverse
positivity and one mutually negative opposite pair persist there. Thus the
producer covers an open neighborhood in twelve comparison coordinates in
the same matrix regime. Near Γ†, also keep the row-zero negative-magnitude
ratio separated from those in the other rows; this ensures genuine
noncyclicity even after relabeling and positive row scaling throughout a
smaller open neighborhood. The four own levels and forty-four nonsingleton
coordinates remain free.

### 4. Rejected strengthenings and boundary cases

Using the larger eigenvalue at Γ* would give W₁=55−81=−26 instead of a
positive coordinate. The small root and each positivity test in (3) are
essential to this sufficient construction. At λ=1, A=1 and the
normalization has no positive absorption mass. Δ=0 and zero-coordinate
boundaries are not covered; no claim of UE failure is made outside the
strict class.

The coarse cycle need not be exact Nash. At Γ† with sᵢ=1, choose the
allowed collision reward r₀({0,1})=3. Player zero can Continue at date zero
and Quit at date one. Since player one quits at date one with probability
1/2, this response pays 2 instead of v⁰₀=1. On the fine mesh, the same
endpoint gain is 2θ₁ and tends to zero. This checks both the necessity of
collision control and the false scope of an exact-coarse-Nash replacement.

Negative own levels do not break the proof: all phase comparisons are
relative to sᵢ, and the Never equality uses opponent absorption, not a
nonnegativity assumption. Likewise no rationality of λ or the fine hazards
is claimed for arbitrary real reward data.

## Adapter and consumer

The actual-data adapter is the finite calculation (1)–(7), followed by the
actual resolvent values (9). It creates a period-four
`BalancedSingletonCycleCertificate` for the same reward table with initial
phase zero. The existing `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
then gives the fixed payoff (4). This checked consumer is reused, not
reproved as a new repository theorem. Sections 3–4 of the proof also make
the unrestricted deviation bound and the finite early-absorption producer
explicit as ordinary mathematics.

In particular, for every requested e>0, H≥1, ρ>0, and N₀≥0, the output
is an actual finite-menu e-Nash product law p at some N≥max(H,N₀),
with R_p(N−H)<ρ. It even has small unrestricted terminal
regret before the menu is enlarged. This is a direct sufficient class, not
a hypothesis that such a family exists and not a producer for all Fin4
tables. No positive-minimum source, concentration family, or chronological
return certificate is inferred from the cycle.

## Lean handoff

The narrow formalization target is a new raw-data producer, not a refactor
of the balanced-cycle compiler. Proposed names below are suggestions, not
existing checked declarations.

1. Define `SignedFourCycleSingletonData` from the actual Fin4 reward table,
   with bᵢ>0,hᵢ>0, real gᵢ, the literal Γ identities, definitions (2), and
   the strict tests (3). Do not put a cycle, Nash profile, or UE conclusion
   in a source field.
2. Prove the 2×2 characteristic/eigenvector identities and (6). Normalize
   the four positive coordinates and establish (7)–(8), retaining A>0 at
   the last-row cancellation. The selected root is the smaller one; a
   Perron library is neither necessary nor applicable to signed K.
3. Define coarse values by the finite geometric resolvent, prove (9), the
   rotated balance/owner identities (10), and the two signed floor identities
   (11). Construct `BalancedSingletonCycleCertificate (L := 4) reward` and
   call its existing `isUniformEquilibriumPayoff` method.
4. If the explicit finite-EA corollary is formalized, reuse the stopping-law
   representation and a general discrete-law bounded-expectation estimate,
   or formalize the literal coupling in the proof. Its response estimate
   must be uniform over every omitted later date and Never before menu
   enlargement. Preserve the order ∀e,H,ρ,N₀, ∃L,K,N,p.
5. Keep the three rational fixtures as separate exact tests. The matrix
   placement can be proved by inverse multiplication, the checked
   copositive-R₀ bridge, the explicit inversion argument, and the two-player
   projective obstruction. Openness is a continuity corollary; it is not
   needed to construct a certificate for one supplied table.

The new raw-data construction and its direct finite output remain ordinary
mathematics until implemented and checked under the repository's trust
policy. Independent review does not give the packet an L, A, or C seal.

## Scope and nonclaims

The theorem covers the precise strict signed singleton class (1)–(3),
including a heterogeneous open neighborhood with arbitrary signed own
levels and arbitrary nonsingleton rewards. It provides actual behavioral
profiles, one fixed uniform payoff, and arbitrarily accurate finite-clock
sources with the exact early-absorption quantifiers.

It does not settle arbitrary Fin4, characterize every balanced cycle or UE
payoff, give an exact coarse equilibrium for arbitrary collisions, preserve
a separately selected exploitability minimum, or supply a rational decision
procedure. The circulant fixture is already covered. The narrower new
contribution is the explicit heterogeneous signed raw-data producer beyond
the named cyclic inputs and matrix branches, not a new semantic compiler
or a literature-priority claim.
