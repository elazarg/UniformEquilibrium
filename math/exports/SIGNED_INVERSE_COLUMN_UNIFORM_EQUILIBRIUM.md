# Signed inverse columns and two-phase quitting equilibria

## 1. Raw data and conclusion

Let I={0,1,2,3}. At each live date the players independently choose
Continue or Quit. The first nonempty coalition S of quitters absorbs at
the given reward vector r(S), received thereafter. Live stages, including
the initial live stage, and perpetual continuation pay zero. All sixty
reward coordinates are arbitrary real numbers unless restricted below.
Strategies and deviations are arbitrary behavioral strategies using the
game's public history and independent private randomization. No public
correlation device or restriction on unilateral memory is introduced.

Write s_i=r_i({i}). Let Γ be the singleton comparison matrix

    Γ_ii=0,                    Γ_ij=r_i({j})−s_i  for i≠j.

Choose a partition I=A⊔B into two pairs. Write a(i) for the other member
of i's pair and O(i) for the opposite pair. Suppose Γ is invertible and
there are signs σ_i∈{−1,1} such that

    G=Γ⁻¹diag(σ) > 0 entrywise.                              (1)

Define the actual pair coefficients

    Π_i=r_i({i,a(i)})−s_i,
    K_i=r_i(O(i))−s_i,
    b_i=−Γ_i,a(i),                  c_i=Π_i+b_i.

Require

    σ_i c_i>0,          σ_i Π_i≥0,          σ_i K_i≤0.         (2)

In particular c_i≠0, but b_i and the own levels s_i may have either
sign. Set

    m=min_{i,j}G_ij,       L=max_{i,j}G_ij,       κ=m/(4L),
    A₀=4mκ³∑_i σ_i c_i > 0.

Choose a finite R>0 satisfying A₀R²>1, and define

    B_i=max(−c_i,0)(1+R)²/(2κ).

The remaining hypotheses are twelve finite raw inequalities:

    r_i({i}∪T)≤s_i−B_i
                  for every i and every nonempty T⊆O(i).    (3)

R is an auxiliary numerical parameter for these inequalities, not a
strategy or continuation input. Equations (1)–(3) can be checked from
the finite reward table. In particular no root, phase value, hazard,
Nash certificate, Q-matrix assumption, or equilibrium is supplied.

**Theorem.** Under (1)–(3), there is a period-two profile with proper
independent Quit probabilities for the scheduled pair at each phase,
and pure Continue for the other pair, that is an exact terminal Nash
equilibrium against all unilateral behavioral deviations. Its phase-A
terminal value is one uniform-equilibrium payoff of the original game.
The same profile and the same target work at every requested accuracy
once the finite horizon is sufficiently large.

The theorem does not assert stationary equilibrium or completeness of
two-phase profiles. It permits negative own levels, negative scheduled
participant premiums, and passive phase values below own singleton.
The signs σ act only on algebraic equations. No player's utility or
Nash ordering is reversed.

## 2. The original odds equations

For X_i>0 put q_i=X_i/(1+X_i). Schedule pair A, then pair B, repeating.
For i, denote its value before its own pair's phase by U_i, and before
the opposite pair's phase by W_i. The active Quit endpoint must be

    U_i=s_i+Π_iq_a(i).

Its active Continue endpoint is

    q_a(i)(s_i+Γ_i,a(i))+(1−q_a(i))W_i.

Equating these endpoints gives the necessary formula

    W_i=s_i+c_iX_a(i).                                      (4)

Let O(i)={j,k} and D_i=(1+X_j)(1+X_k). Passive Continue has value

    [U_i+X_j(s_i+Γ_ij)+X_k(s_i+Γ_ik)
                                  +X_jX_k(s_i+K_i)]/D_i.

Thus its equality to W_i is exactly

    c_iX_a(i)D_i
       =Γ_ijX_j+Γ_ikX_k+K_iX_jX_k+Π_iX_a(i)/(1+X_a(i)).     (5)

After moving the linear mate term, (5) is equivalent to ΓX=N(X), where

    N_i(X)=c_iX_a(i)(X_j+X_k+X_jX_k)
              +Π_iX_a(i)²/(1+X_a(i))−K_iX_jX_k.             (6)

All rewards in (5) are literal singleton or scheduled-pair rewards of
the original table. Simultaneous quitting is retained. There is no
linearization or approximation in these equations.

## 3. Production of a positive actual root

Let Ñ(X)=diag(σ)N(X). By (2), every term of every coordinate of Ñ
is nonnegative on X>0, and its cubic coefficient σ_i c_i is strictly
positive. Therefore Ñ(X)>0. Define

    F(X)=G Ñ(X)=Γ⁻¹N(X).

Consider the nonempty compact simplex

    Δκ={x∈ℝ⁴: ∑_i x_i=1 and x_i≥κ for every i}.

It is nonempty since 0<κ≤1/4. For any X>0,

    F_i(X)≥m∑_j Ñ_j(X),       ∑_i F_i(X)≤4L∑_j Ñ_j(X).

Hence the normalized vector F(X)/∑F(X) lies in Δκ. For X=tx with
x∈Δκ, the positive cubic terms give

    ∑_i F_i(tx)≥4mκ³t³∑_i σ_i c_i=A₀t³.                    (7)

For 0<t≤1, every x_i≤1, so the two quadratic terms and one cubic
term in the first summand of (6) are bounded by 3t². Consequently

    ∑_i F_i(tx)≤C t²,
    C=4L∑_i[3σ_i c_i+σ_iΠ_i−σ_iK_i]>0.                    (8)

Choose 0<r<min(R,1,1/C). On Δκ×[r,R], use the continuous self-map

    (x,t) ↦ (F(tx)/∑F(tx),
              clamp_[r,R](t+1−∑F(tx)/t)).                  (9)

The first component belongs to Δκ by the preceding bounds. At t=r,
(8) gives ∑F(rx)/r<1, so the second component is strictly greater
than r. At t=R, (7) and A₀R²>1 make it strictly less than R.
Brouwer's theorem gives a fixed point with r<t<R. At that interior
radius, the clamp can output t only if its input is t. Thus ∑F(tx)=t.
The angular equation then gives F(tx)=tx, not merely a positive scaled
eigenvector. Set X=tx. It solves the four original equations (5), with

    X_i≥κt>0,                   X_i≤t<R.                  (10)

This is the entire strategy-parameter producer. In particular, the
choice of R and all buffers precedes the root selection.

## 4. All phase endpoints and unrestricted deviations

Use the produced X and the definitions of q,U,W above. At i's active
phase, both pure actions equal U_i, by (4). At its passive phase,
Continue equals W_i, by (5). Write

    H_i=1−1/[(1+X_j)(1+X_k)]

for the probability of a nonempty opposite-pair coalition. The actual
passive Quit endpoint averages s_i on the empty coalition and the three
rewards in (3) on the nonempty coalitions. It is therefore at most
s_i−B_iH_i. From (10),

    H_i=(X_j+X_k+X_jX_k)/[(1+X_j)(1+X_k)]
         ≥2κt/(1+R)².

If c_i<0, then B_iH_i≥|c_i|t≥|c_i|X_a(i), so passive Quit≤W_i.
If c_i>0, then B_i=0 and passive Quit≤s_i<W_i. This proves every
endpoint for all four players at both phases:

| Role of i | Quit endpoint | Continue endpoint | Policy value |
|---|---|---|---|
| Active | U_i | U_i | U_i |
| Passive | at most W_i | W_i | W_i |

The prescription mixes only at active phases. Thus its policy equations
hold exactly, as do all local Nash inequalities. No phasewise singleton
floor was assumed; negative c_i gives W_i<s_i.

For every player i, let

    ρ_i=∏_{j≠i}(1−q_j)<1,                    ρ=max_iρ_i<1.

In each complete two-date cycle, each opponent is scheduled once. Against
any complete unilateral behavioral replacement, survival through n cycles
is at most ρ_iⁿ: survival requires all three independent opponent clocks
to Continue. Their probabilities are unaffected by i's replacement on
the unique continuing public history. Any private randomization or
history dependence in the replacement only changes the convex mixture
of its two current action endpoints.

Iterate the endpoint inequalities up to n cycles. The continuation
remainder is bounded in absolute value by a fixed bound on U,W times
ρ_iⁿ, and tends to zero. The inequality therefore bounds every deviating
terminal payoff by i's prescribed phase value. Under the prescribed
profile the policy equalities give equality in the same iteration, so
U,W are its actual terminal values. Never and unbounded stopping times
are included; opponent absorption is almost sure even for those deviations.

Let M=max_{S≠∅,i}|r_i(S)| and

    C_time=1+2/(1−ρ).

The geometric tail bounds expected time to absorption, including the
initial live-date convention, by C_time for the prescription and for
every unilateral behavioral replacement. Comparing the absorbing terminal
reward with an N-date average gives the conservative uniform bound

    |expected N-date payoff − expected terminal payoff|
                        ≤2M C_time/N.                     (11)

There are only zero live rewards before absorption; the extra factor two
also covers either endpoint convention for the selection date. The
prescribed profile delivers its phase-A terminal vector within (11), and
every deviation pays at most that fixed target plus (11). Its regret
relative to the prescribed N-date payoff is at most 4M C_time/N.
This proves the stated uniform-payoff conclusion with one fixed target
and the same profile for all accuracies.

## 5. A complete signed-column table

The following exact table establishes that the criterion includes a
nonbijective favorable singleton graph and a genuinely negative inverse
column. It also supplies bounded implementation-overlap tests below.

Take s_i=1 and

    Γ = [[ 0, 3,−1,−1],
         [−1, 0, 3,−1],
         [ 3,−1, 0,−1],
         [ 3,−1,−1, 0]],

    Γ⁻¹=(1/13)[[2,5,−7,13], [5,6,−11,13],
                [1,9,−10,13], [1,9,−23,26]].

Use scheduled pairs03 and12. Define

    Π=(1,4,−2,4),             b=(1,−3,1,−3),
    c=(2,1,−1,1),             σ=(1,1,−1,1),
    K=(−4711507/97125,−41341/22950,36491/10300,−94597/7650).

Then G>0, m=1/13, L=2, κ=1/104, A₀=5/3655808. Choose R=1000.
Only the third buffer is nonzero: B₂=D=52104052. The complete rewards are

| S | r(S) |
|---|---|
| 0 | (1,0,4,4) |
| 1 | (4,1,0,0) |
| 2 | (0,4,1,0) |
| 3 | (0,0,0,1) |
| 01 | (1/2,1/2,0,0) |
| 02 | (1/2,0,−D,0) |
| 03 | (2,1+K₁,1+K₂,5) |
| 12 | (1+K₀,5,−1,1+K₃) |
| 13 | (0,1/2,0,1/2) |
| 23 | (0,0,−D,1/2) |
| 012 | (1/2,−10,100,0) |
| 013 | (−10,1/2,0,−10) |
| 023 | (−10,0,−D,−10) |
| 123 | (0,−10,100,1/2) |
| 0123 | (1000,1001,1002,−104) |

All coefficient signs in (2) are strict. The three capped rewards of
player2 are −D<1−D. Every other capped reward is 1/2 or −10, below1.
One exact solution, independently of the existence construction, is

    X=(1/50,3/100,1/50,9/250),
    q=(1/51,3/103,1/51,9/259),
    U=(268/259,55/51,97/103,55/51),
    W=(134/125,51/50,97/100,51/50).

Substitution in (5) verifies all four equalities. The phase-A target for
A=03 is (U₀,W₁,W₂,U₃). Player2's active and passive values are both
below its own singleton. Changing every nonempty reward of player i by
the same constant v_i changes s_i,U_i,W_i by v_i and leaves all raw
tests and odds unchanged. For example v=(−4,1,−2,3) gives signed own
levels (−3,2,−1,4). This is an application of the stated theorem to the
new table, not a claim that arbitrary terminal translations preserve
equilibrium when Never has positive probability.

### Singleton matrix and degree tests

The six pair determinants in order01,02,03,12,13,23 are
(3,3,3,3,−1,−1). The four triple determinants are (26,−10,6,2),
and det Γ=13. A homogeneous nonzero LCP solution cannot have support
of size at least two because the corresponding principal matrix is
nonsingular. Singleton support fails because every column has a negative
off-diagonal entry. Thus Γ is R₀.

At offset −1, the sole-positive-entry condition forces z₀,z₁,z₂>0.
If z₃=0, their equalities give z₀=z₁=z₂=1/2, but the fourth
residual is −1/2. Otherwise all equations give z=(1,1,1,1), which is
indeed a root. It is the sole root, with positive determinant13. The
finite regular-root degree formula therefore gives R₀ degree+1, and
nonzero degree gives standard Q at every offset. The formulas used are
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

Only child012 has a positive inverse; the literal outside inverse row is

    Γ_3,012 (Γ_012,012)⁻¹=(−1,−9,23)/26.

It fails nonnegative passive factorization. The favorable map is the
three-cycle0→1→2→0 with the additional arrow3→0, not a permutation.

## 6. Exact exclusion of every sure-quitter stationary profile

This section checks a possible simpler producer for the complete table.
It makes no claim about stationary profiles without a sure quitter.

Fix a player j with stationary Quit probability1. The other three
players face an ordinary simultaneous two-action game at the first
date, since j causes sure absorption. Any full stationary equilibrium
must induce an equilibrium of this game. Player j must additionally
prefer its immediate Quit to Never against the stationary opponents.

Put d_i=−1/2−K_i for i=0,1,3. Explicitly,

    d₀=9325889/194250>40,
    d₁=14933/11475>1,
    d₃=45386/3825>10.

Each ordered quadruple below lists the Quit-minus-Continue difference
at the indicated two other hazards (0,0),(1,0),(0,1),(1,1).

| Sure j | Recipient i | Other variables | Difference endpoints |
|---|---|---|---|
| 0 | 1 | (q₂,q₃) | (1/2,−10,d₁,1001) |
| 0 | 2 | (q₁,q₃) | (−D−4,100,−D−1−K₂,1002) |
| 0 | 3 | (q₁,q₂) | (1,−10,−10,−104) |
| 1 | 0 | (q₂,q₃) | (−7/2,d₀,−10,1000) |
| 1 | 2 | (q₀,q₃) | (−1,100,100,1002) |
| 1 | 3 | (q₀,q₂) | (1/2,−10,d₃,−104) |
| 2 | 0 | (q₁,q₃) | (1/2,d₀,−10,1000) |
| 2 | 1 | (q₀,q₃) | (1,−10,−10,1001) |
| 2 | 3 | (q₀,q₁) | (1/2,−10,d₃,−104) |
| 3 | 0 | (q₁,q₂) | (2,−10,−10,1000) |
| 3 | 1 | (q₀,q₂) | (1/2,d₁,−10,1001) |
| 3 | 2 | (q₀,q₁) | (−D,−D−1−K₂,100,1002) |

The complete induced equilibria and their failures are

| Sure j | Complete hazards | Sure player's failure |
|---|---|---|
| 0 | (1,(D+4)/(D+104),1/21,0) | Q₀−Never₀=−724795040468913623231/692156460057385664250 |
| 1 | (1,1,1,0) | Q₁−Never₁=−10 |
| 2 | (0,0,1,1) | Q₂−Never₂=−D |
| 2 | (1,0,1,0) | Q₂−Never₂=−D−4 |
| 2 | (10/1011,1/101,1,1) | Q₂<0≤Never₂ |
| 3 | (1,1,1,1) | Q₃−Never₃=−104 |

Here is an exhaustive derivation, including all ties and partially mixed
faces. For j=0 write (x,y,z)=(q₁,q₂,q₃). If z>0, its owner's
nonnegative difference1−11x−11y−83xy forces x,y≤1/11. Player2's
difference is at most −D(1−x)+1002x≤(−10D+1002)/11<0, so y=0.
Player1's two y=0 endpoints are positive, forcing x=1, a contradiction.
Thus z=0. The other differences are 1/2−21y/2 and
−D−4+(D+104)x. Their only equilibrium is the displayed interior pair;
player3's difference there is negative.

For j=1 write (x,y,z)=(q₀,q₂,q₃). If y<1, its owner's
difference −1+101x+101z+801xz≤0 gives x,z≤1/101. Player3's
difference is positive for every y: at y=0 it is1/2−21x/2>0,
and at y=1 it is d₃−(d₃+104)x>0. It forces z=1, impossible.
Thus y=1; player0 is then forced sure and player3 forced inactive.

For j=2 write (x,y,z)=(q₀,q₁,q₃). At z=0 player0 has positive
difference, giving x=1 and then y=0. At z=1 the other two differences
are −10+1010y and −10+1011x. Their equilibria are (0,0),(1,1),
and (10/1011,1/101). The (1,1) point fails player3's sure condition;
the other two satisfy it. At the mixed point its difference is
194644636/390574575>0.

If 0<z<1, x=0 would give a strictly positive player3 difference,
and x=1 a strictly negative one, so 0<x<1. If y=0, mixed x,z
would equal1/21, at which player1's difference is1001/441>0.
If y=1, player0 is forced sure. At an all-proper point, player3's
zero difference forces x>1/21. Player1's equation
1−11x−11z+1022xz=0 then forces x>1/11 and
0<z<11/1022<1/21. Player0's difference is at least
1/2−21z/2>0, a contradiction. This exhausts its remaining faces.

For j=3 write (x,y,z)=(q₀,q₁,q₂). If z=0, player1 is forced
sure, then player0 inactive, and then player2 has positive difference100.
Thus z>0. Its nonnegative difference gives y≥D/(D+1002)>1/2.
If y<1, player1's difference≤0 gives z≥1/21. On this rectangle,
player0's difference2−12y−12z+1022yz is strictly positive: both
partial derivatives are positive and its lower-corner value is
−4+499/21>0. Thus x=1, making player1's difference
d₁(1−z)+1001z>0, a contradiction. Hence y=1, then z=1 and x=1.

For the first remaining profile let x=(D+4)/(D+104), y=1/21.
The literal owner endpoints are

    Q₀=1/2+(1−x)(1−y)/2,
    Never₀=[4x(1−y)+(1+K₀)xy]/(x+y−xy).

Their difference is the negative fraction in the table. In the mixed
j=2 row, Q₂≤(−100D+1002)/101<0, whereas
Never₂=(1+K₂)(10/1011)(100/101)>0. The other four comparisons are
literal first-date reward comparisons. Opponent absorption is sure or
geometric in every calculation. All sure stationary possibilities,
including pure coalitions, have therefore been excluded.

## 7. Exact raw-source separation

The comparisons here concern literal sufficient predicates and their
produced strategy classes. They are not claims that no other equilibrium
exists for the example.

### Every proper child fails nonnegative join rows

For a proper nonempty child S, a nonnegative weighted join comparison
for an omitted player k requires, at every nonempty T⊆S,

    r_k(T∪{k})−r_k(T)
       ≤∑_{i∈S} λ_ki[r_i(T∪{i})−r_i(T)],       λ_ki≥0.    (12)

The following table defeats (12) for all fourteen children. The vector
lists child joining gains in increasing order of the members of S.

| S | T | k | Child joining gains | Omitted gain |
|---|---|---|---|---|
| 0 | 0 | 1 | (0) | 1/2 |
| 1 | 1 | 3 | (0) | 1/2 |
| 2 | 2 | 0 | (0) | 1/2 |
| 3 | 3 | 0 | (0) | 2 |
| 01 | 1 | 3 | (−7/2,0) | 1/2 |
| 02 | 0 | 1 | (0,−D−4) | 1/2 |
| 12 | 1 | 3 | (0,−1) | 1/2 |
| 23 | 3 | 0 | (−D,0) | 2 |
| 03 | 03 | 1 | (0,0) | d₁ |
| 13 | 13 | 2 | (0,0) | 100 |
| 012 | 1 | 3 | (−7/2,0,−1) | 1/2 |
| 013 | 13 | 2 | (−10,0,0) | 100 |
| 023 | 03 | 1 | (0,−D−1−K₂,0) | d₁ |
| 123 | 123 | 0 | (0,0,0) | 1000 |

Every right-hand coefficient is nonpositive and every left side is
positive. This is a raw-table exclusion, not an inference from a chosen
unsafe child equilibrium. The literal two-row certificate is
`CappedClockParentFutureJoinCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`.

The more flexible universal child-debt-plus-Never bounds also fail.
For each row except S=123, prescribe the displayed T as a sure coalition
in the child. Its quitting members do not gain by withdrawing: solos have
positive own payoff; pair03 members have rewards2 and5 versus passive
rewards0 and4; pair13 members have reward1/2 versus passive0. The listed
child joining gains control every nonmember. With sure absorption these
are exact child terminal Nash profiles, all with zero joint-Never mass,
and the omitted gain in the table is strictly positive.

For S=123 instead use

    q₁=D/(D+100),             q₂=1/21,             q₃=1.

Players1 and2 have Quit and Continue values zero. Player3 has Quit
value1/2+(1−q₁)(1−q₂)/2>0, while its Never payoff is negative,
since opponent coalition12 has reward1+K₃<0 and all other opponent
rewards to3 are zero. Thus this is an exact child terminal Nash profile.
The omitted player0 has Never value0 and immediate Quit gain
5210405575/136773399>0. Every such profile has zero child debt and
zero joint-Never mass. Hence no fixed nonnegative weighted sum of those
quantities bounds omitted gain universally over child profiles. This
also excludes certificates implying that universal bound, including
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Neither exclusion rules out existence of a specially selected safe child
profile. The distinction between the simple rows (12) and withdrawal
certificates with additional gain terms is retained.

### Premium traps, floors, and aggregate charges

A premium trap is a nonempty set E such that each i∈E has a coalition
T⊆E containing i with r_i(T)>s_i. Direct inspection gives exactly
the traps03 and I. Each player has a negative participant premium:
use01 for players0,1, pair02 for2, and pair13 for3. Thus no player
has globally nonnegative participant premiums. Criteria requiring a
nonempty protected set of such players cannot apply; neither can
criteria requiring the greatest premium core to have size at most three.

For the global weighted forced-Quit floor define

    W_λ(T)=∑_i λ_i[r_i(T∪{i})−s_i],               λ_i≥0.

At T={1} its coefficient vector is (−1/2,0,−2,−1/2), so W_λ≥0
forces λ to be supported only on1. At T={3}, that last coefficient
is −1/2. Consequently no nonzero nonnegative λ satisfies the global
floor tests. Separately, r(013) is strictly below s in all coordinates,
so no nonzero nonnegative weight has a floor on every actual reward row.
The forced-Quit and actual-reward tests are different statements.
The implemented forced-floor consumer is
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`.

For a trap E and ∅≠T⊊E, put

    P_E(T)=∑_{i∈E\T}[r_i(T∪{i})−s_i],
    L_E(T)=∑_{i∈E\T}[r_i(T∪{i})−r_i(T)].

At E=I,T=13, the exact values are P_I(13)=88 and L_I(13)=90.
Thus the nonpositive intermediate-subset requirements of boxed larger-
trap charges fail, including their combination with separate pair traps.
At q₀=q₃=1/2,q₁=q₂=0, the active forced-Quit values are3/2 and3,
both above1. This excludes the product-low predicate that requires some
active player to have its forced-Quit value at most its own singleton,
and hence also its supportwise nonpositive weighted-premium sufficient
condition. These are raw failures, not an alleged negative gap.
The predicate is `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`;
the supportwise implication is
`hasProductLowQuittingPremium_of_supportwiseBalance` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumProductLow.lean`.

### Matrix, response, and sign-based predicates

Section5 verifies full R₀, standard Q and degree+1, so their contrary
matrix exits do not consume this example. The negative full inverse
column persists under every positive playerwise affine reward transport:
the matrix's rows scale positively, so its inverse columns scale positively.
Relabeling only permutes them. In particular no full nonnegative-inverse
predicate can apply. The only positive three-player inverse is012;
the other three inverse matrices have negative entries, for example
(Γ_013⁻¹)_11=−3/10, (Γ_023⁻¹)_00=−1/6, and
(Γ_123⁻¹)_11=−1/2, with subscripts denoting the original recipients.
The passive factorization for012 fails as computed above.

Since Γ1=1, a nonnegative terminal upper-bound weight with Γᵀλ≤0
must satisfy ∑λ_i≤0 and hence vanish. The same row sums exclude every
nondiscrete response-invariant partition, even after positive affine
row transports. To see this, equality of the response functions within
a receiver block implies equality of all blockwise singleton row sums,
by differentiation at zero hazards. Summing those equalities over source
blocks forces the positive row scales within a receiver block to agree.
At all-sure hazards, however, the four original response displacements
are1000,1001,1002,−104, which are pairwise distinct. Equal row scaling
cannot make two of them equal. Translations cancel from both comparisons.
This covers all fourteen nondiscrete partitions. The precise derivative
necessity is `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

The unique favorable map0→1→2→0,3→0 has unequal indegrees and is
neither a favorable matching nor a four-cycle. Thus it fails matching
singleton chambers and transitive Klein-four symmetry. Every row has
two below-own singleton entries, failing predicates with only one such
partner per row. The mutually negative pair13 also fails tournament
singleton signs. Any literal source requiring an off-diagonal singleton
equality fails, since all off-diagonal comparisons are3 or−1.

One can exclude all proper two-pair profiles whose every phase coordinate
is below its own level without guessing a neighborhood radius. For the
word03/12, players0,1,3 have positive active premiums and therefore
active values above1. For01/23, player1 has
c₁=r₁(01)−r₁(0)=1/2>0; for02/13, player0 has
c₀=r₀(02)−r₀(2)=1/2>0. Formula (4) forces a passive value above1
in each case. These are all three pair partitions, including relabelings.
Strict comparisons to one's singleton are preserved by positive affine
playerwise transports. Thus a local theorem whose output is of this
all-below form cannot deliver this table, regardless of its neighborhood
description.

### Actual conditional-range and polynomial-guard failures

For every ordered owner/passive pair, the following pure-face witness
violates one of the weak-unit polynomial guards. A lower witness is an
opponent coalition T avoiding the owner and passive players, with
r_owner(T+owner)−r_owner(T)<0. An upper witness has owner∈T and
passive∉T, with r_passive(T+passive)−r_passive(T)>0.

| owner, passive | Face | T | Difference |
|---|---|---|---|
| 0,1 | lower | 23 | −10 |
| 0,2 | lower | 1 | −7/2 |
| 0,3 | lower | 1 | −7/2 |
| 1,0 | lower | 23 | −10 |
| 1,2 | upper | 01 | 100 |
| 1,3 | lower | 02 | −10 |
| 2,0 | lower | 1 | −1 |
| 2,1 | lower | 0 | −D−4 |
| 2,3 | lower | 0 | −D−4 |
| 3,0 | upper | 3 | 2 |
| 3,1 | lower | 02 | −10 |
| 3,2 | lower | 01 | −10 |

The actual predicates and consumers are `QuittingOneSidedWeakUnitGuards`,
`QuittingOneSidedWeakUnitRawGuards`,
`stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards`, and
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
Each singleton also has a profitable join, as in the child table, so the
instant-no-join alternative fails independently.

For the conditional-face range criterion, recipient2 has Continue upper
bound at least4, from singleton0. Its Quit lower bound without any chosen
blocker is at most1, from the empty background. Its Quit lower bound with
the blocker is at most−1: pair02 or23 gives−D, and pair12 gives−1.
No required convex combination of those lower bounds can exceed1.
It therefore cannot strictly exceed Continue upper4. This excludes every
blocker and range choice in `IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.

Let a membership gain mean the reward increment from a player's own
joining. Adding player1 changes player0's membership gain by−9/2 at
empty background and by−1−K₀>0 at background2. Hence the influence
is neither always nonnegative nor always nonpositive, and is not
background-independent. This violates `SignConsistentQuittingInfluence`
in `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

### Cyclic-child inputs and local-neighborhood scope

Only012 has the directed favorable three-cycle required by the canonical
cyclic-child singleton source; the pivot must be3. Its passive inverse
weights have two negative coordinates. The resonance and low-degree exits
fail at the exact R₀ degree+1 matrix. The declarations used are `RawRows`
and `exists_uniformPayoff_of_resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`,
and `outsideInverseWeight_eq` and `exists_uniformPayoff_of_passiveNumerators`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`.

For a positive-premium pivot joint phase, the only pivot pair whose two
participants both have positive premiums is03. Its joint passive increment
for child2 is K₂>0, violating the nonpositive outsider requirement.
Pairs13 and23 have negative pivot premiums; none has zero participant
premium. A raw variant requiring two nonnegative pivot singleton comparisons
also fails, since pivot3 has only one. These conditions are intrinsic
raw comparisons, not references to an unnamed theorem. Their implemented
counterpart is `CyclicChildJointPhase.RawTable` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`, with
`JointPhaseData.q₂_nonpos` and `JointPhaseData.q₃_nonpos` in
`MathUE/CyclicChildJointPhasePivot.lean`.

No absence of all proper-three or all-full-support stationary equilibria
is asserted. In particular an existential local theorem at a different
center does not decide this table's membership without a usable radius
or another actual membership proof. The declarations
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
and its full-table local producer in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistence.lean`
are of that local form. Neither membership nor exclusion from every possible
neighborhood satisfying such an existential statement is claimed. A
verifier for an additionally supplied stationary root is not a raw-table
producer for the class (1)–(3). The coverage evidence above is a bounded
comparison with actual numerical predicates, not a claim that all possible
equilibrium architectures are absent.

## 8. Implementation handoff and exact semantic boundary

A raw structure may store the finite pair partition, signs, inverse
identity, entrywise positivity, coefficient inequalities, scalar R and
the twelve caps. It must not store rates, phase values or an equilibrium.
The producer should first obtain the positive root of (6) by (7)–(9),
then set the proper hazards and the two phase-value vectors using (4).
The root theorem should retain the coordinate bounds (10), which are
needed by the original-utility passive inequalities, not merely return
an unquantified positive eigenvector.

For the literal downstream compilation, define phase0 to schedule A and
phase1 to schedule B. Their value vectors use U_i on the active pair and
W_i on the passive pair. Section4 supplies exact policy recursion, local
root Nash for every player/action, and opponent-cycle survival strictly
below1. These are exactly the hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The former handles complete behavioral deviations; the latter produces
one fixed uniform target. Bound (11) gives a direct quantitative route too.

The new obligation is the finite raw producer, not another supplied
certificate interface. Its conclusion concerns the original reward table
and zero live payoff, with no normalization of utility signs. This proof
and its displayed arithmetic are ordinary mathematics; no new Lean
verification or strategy-class completeness is claimed.
