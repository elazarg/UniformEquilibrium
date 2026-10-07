# Coarse Nash-regret tests for every quitting base

Status: proved ordinary mathematics. The finite LP recognizer and exact
same-profile/all-horizon theorem are valid, but their entire UE existence
class is contained in the existing concrete persistent-base sources in
Section6. The raw withdrawal-family separation is genuine; it does not
establish a new UE counterexample exclusion.

## 1. Raw finite criterion and counterexample restriction

Let I be any nonempty finite player set. At each live date the players
independently choose Continue or Quit using private randomization and the
public history. The first nonempty quitting coalition S absorbs at its
arbitrary finite real reward vector r(S). The initial live stage, including
the date selecting the absorbing state, pays0; subsequent stages pay r(S).
Joint Never pays0. Every unilateral replacement is an unrestricted complete
behavioral strategy. All payoff claims are in expectation.

Write s_i=r_i({i}). Own levels and all other reward coordinates may have
either sign. There is no public correlation device, prescribed root,
continuation value, finite stopping bound or matrix assumption.

For every nonempty base E⊆I put J=I∖E. Define the finite binary free game

    u_j^E(T)=r_j(E∪T),                    j∈J, T⊆J.

For b∈{Continue,Quit}, let T^{j,b} be T with player j's action fixed to b,
and define pure-deviation regret margins

    R_{j,b}^E(T)=u_j^E(T)−u_j^E(T^{j,b}).

Let C_E be the finite polytope of laws on T⊆J satisfying

    ν_T≥0, Σ_Tν_T=1, EνR_{j,b}^E≥0 for every j,b.        (1)

These are the free game's coarse Nash inequalities. A correlated law is
only a convex relaxation used in the raw test, never a strategy played in
the quitting game. The polytope is nonempty because an internally selected
independent mixed Nash point exists in every finite free game and its law
satisfies(1). It is compact. Empty J is allowed and gives one empty atom.

For every i∈E define the literal base-member gap

    G_i^E(T)=r_i(E∪T)−r_i((E−i)∪T),          if |E|≥2.  (2)

Both coalitions in(2) are nonempty. For E={i}, the correct gap is instead

    G_i^{i}(∅)=min(s_i,0),
    G_i^{i}(T)=r_i(T+i)−r_i(T)                    if T≠∅. (3)

The exceptional empty row retains the anchor's complete delayed-Quit/Never
alternative. Replacing it by s_i is wrong for positive own levels; replacing
it by0 is wrong for negative own levels.

Define reward-dependent, attained finite LP minima

    v_{E,i}(r)=min_{ν∈C_E} EνG_i^E,
    v_E(r)=min_{i∈E}v_{E,i}(r).                         (4)

**Theorem.** If v_E(r)≥0 for any nonempty base E, the original quitting game
has an internally produced exact terminal Nash profile and one fixed
uniform-equilibrium target. The same profile is exact behavioral Nash at
every positive finite horizon and delivers each target coordinate with error≤M/N,
where M=max_{S,i}|r_i(S)|.

Thus EVERY counterexample to original-game UE, and EVERY table with a
positive unrestricted terminal-exploitability floor, obeys

    for EVERY ∅≠E⊆I, SOME i∈E and SOME ν∈C_E satisfy
    EνG_i^E<0.                                         (5)

The negative member and minimizing coarse law may depend on the base.
Different members need not admit one common negative law. These laws are
not asserted product, implementable, or sufficient for nonexistence.

The criterion is finite raw game data, not a supplied-strategy verifier.
For |E|≥2 it includes every pointwise complement-leave-safe base; for
singleton bases it includes nonnegative-own, pointwise join-monotone anchors.
The complete table in Section5 strictly separates the recognizer from
pointwise anchor and raw withdrawal tests. Section6 proves containment
in the stronger existing concrete induced-Nash sources, so neither this
existence class nor(5) is a new UE counterexample restriction.
No claim that every quitting table passes(4) is made.

## 2. Finite raw dual sufficient rows

For each i∈E it suffices to find nonnegative coefficients λ_{i,j,b} and
β_i≥0 such that

    G_i^E(T)≥β_i+Σ_{j,b}λ_{i,j,b}R_{j,b}^E(T)
                                      for every T⊆J.  (6)

Averaging(6) against any ν∈C_E gives EνG_i^E≥β_i, hence v_E≥0.
The coefficients may differ between base members. No LP-duality converse,
dual attainment or assertion that every table satisfying(4) has such a displayed
certificate is needed. These are finitely many inequalities between actual
reward coordinates; no equilibrium is certificate data.

Crucially, nonnegative minima for ALL members control the SAME internally
chosen product Nash law: if p∈C_E, then E_pG_i^E≥0 simultaneously for
every i. The proof does not choose incompatible free equilibria for different
base members.

## 3. Actual strategy, all behavioral deviations and horizons

Choose any mixed Nash point μ of the finite free game internally. Let p be
its independent product coalition law. At date0 every base member Quits
surely and the free players use μ independently. Every player Continues
forever after date0, including on histories created by a unilateral change.
The actual terminal target is

    V=E_p r(E∪T).                                      (7)

This target and profile are chosen once, before accuracy or horizon.

### Bases with at least two members

Against every unilateral replacement there is still a sure base opponent.
Absorption occurs at date0 regardless of the deviator's later policy. A free
player's two endpoint payoffs are exactly its finite-game endpoints, so μ's
Nash property caps its complete replacement. A base member's Quit-minus-
Continue endpoint is E_pG_i^E≥0. Its first random action is independent
of the simultaneous opponents; mixing those endpoints cannot improve on
Quit. All later behavior, including Never and arbitrarily late stopping,
is preempted. This proves exact terminal Nash with arbitrary signed rewards.

For N≥1, date0 absorption yields h_Nr, with h_N=(N−1)/N. This is the
actual law even under every unilateral replacement. Multiplication by
h_N≥0 preserves the endpoint Nash inequalities, so the profile is exact
N-horizon Nash. Under the prescribed profile its payoff is h_NV and its
error in every coordinate of V is≤M/N. At N=1 everyone earns0.

Stationary repetition of this first row is also valid in this branch:
its later rows remain unreachable against every unilateral replacement.
This extra conclusion is NOT carried over to singleton bases.

### Singleton bases, either sign of the own reward

Let E={a}. Against a nonanchor replacement, a still Quits surely at date0,
so all later behavior is preempted and the binary-game Nash inequalities
again suffice. Against an anchor replacement, the free players use μ at
date0 and really Never thereafter.

If the first free coalition T is nonempty, it immediately absorbs. If
T=∅, the anchor faces a quiet opponent system forever; the full payoff
cap for any delayed randomized stopping or Never is max(s_a,0). Therefore
its two terminal endpoints have cap

    V_a=p_∅s_a+Σ_{T≠∅}p_T r_a(T+a),
    C_a=p_∅max(s_a,0)+Σ_{T≠∅}p_T r_a(T),
    V_a−C_a=E_pG_a^{a}≥0.                              (8)

The anchor cannot condition its date0 draw on the simultaneous free draw.
Any complete replacement first mixes Quit and Continue; the latter endpoint
is capped by C_a even after conditioning later behavior on the observed
empty event. Thus(8) proves exact terminal Nash. No opponent-contraction
assumption is inserted into the quiet event.

For N≥1 every nonempty first-date exit scales by h_N. On the empty event
any later anchor payoff is at most h_Nmax(s_a,0): if s_a≥0, a later quit
has fewer rewarding stages; if s_a<0, every quit is nonpositive and Never
pays0. Hence every replacement is capped by h_NV_a. The nonanchor
comparisons scale by h_N too. The same profile is exact N-horizon Nash
and delivers every coordinate of V within M/N. Negative V causes no difficulty.
For any ε>0, choose N₀≥max(1,M/ε). At every N≥N₀ this one profile
has payoff error≤ε and behavioral regret0; V was fixed before ε.

The finite exact profile implies UE directly and disproves any positive
terminal-exploitability floor. Taking the contrapositive gives(5);
compactness of C_E supplies an attained negative law when a minimum is
strictly negative. No changing-target limit or reward translation is used.

## 4. Signed and quantifier stress tests

These tests check scope; they are not additional-coverage witnesses.

For two players a,b take

    r(a)=(−2,0), r(b)=(−5,1), r(ab)=(−4,2).

With singleton base a the free player strictly Quits, so C_a is the nonempty
atom. Nevertheless the empty gap is−2. In atom order(∅,{b}),

    G=(−2,1), R_{b,Q}=(−2,0), G=1+(3/2)R_{b,Q}.

The dual criterion produces both Quit with the signed target(−4,2).
The original empty-event bound is retained, not changed to a zero own level.

For a base of size two with an empty free set, take

    r(0)=(−3,−4), r(1)=(−4,−3), r(01)=(−2,−2).

The two gaps are2,2. Both Quit is exact Nash with negative own levels and
negative target, because every unilateral replacement still faces a sure
opponent. Empty free sets and negative targets require no separate limit.

Negative minima are not sufficient for nonexistence, and no common-negative-
law strengthening is valid. For three players take the complete table

    r0=(1,2,0), r1=(0,1,0), r2=(0,0,0),
    r01=(1,1,0), r02=(1,0,0), r12=(2,1,0), r012=(1,1,0).

For E=01 the free player is indifferent, so C_E is the entire two-atom
simplex. Its member gaps are G₀=(1,−1), G₁=(−1,1). Each separate minimum
is−1, but no law makes both expectations strictly negative. The uniform
free product law is an actual exact base equilibrium with target(1,1,0).
The quantifiers in(5) are therefore essential.

## 5. Complete LP-positive table and raw-source separations

The following strict singleton case separates the global CCE class from
every implemented five-kind raw withdrawal family on a full sixty-coordinate
open reward box. It is nevertheless already admitted by the stronger
concrete singleton-base source in Section6.

Here is every nonempty reward vector; all four own levels are1.

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (0,−1,0,0) |
| 02 | (1,0,1,0) |
| 03 | (1,4,0,−1) |
| 12 | (100,5,5,0) |
| 13 | (100,5,0,5) |
| 23 | (−100,0,5,5) |
| 012 | (102,1,1,98) |
| 013 | (96,−1,101,1) |
| 023 | (−99,99,−1,−1) |
| 123 | (1000,6,6,6) |
| 0123 | (1002,100,100,99) |

For anchor0, the free utility differences at hazards(q₁,q₂,q₃) are

    A₁=−5+6q₂,       A₂=1−2q₃,       A₃=−1+2q₁.       (C1)

These are exactly the table's own-action differences, not an approximation.
Their product Nash point is uniquely(1/2,5/6,1/2). Indeed if any coordinate
is0 or1, successive strict best responses around the odd negative-feedback
cycle force that coordinate to be its opposite. Thus every equilibrium is
proper; setting the three differences zero gives the stated unique point.
The large terms99q₂q₃,101q₁q₃,98q₁q₂ are independent of the respective
recipient's action and do not change these response equations.

In order T=∅,1,2,3,12,13,23,123, the literal raw vectors are

    g₀=(0,−4,1,1,2,−4,1,2),
    R_{1,C}=(0,−5,0,0,1,−5,0,1),
    R_{2,Q}=(−1,−1,0,1,0,1,0,0).

A finite dual inequality has eight strict slacks:

    g₀≥1/4+R_{1,C}+(1/2)R_{2,Q},
    slacks=(1/4,5/4,3/4,1/4,3/4,1/4,3/4,3/4).          (C2)

Consequently v₀≥1/4. The raw CCE producer in Sections1–3 supplies the original
unrestricted one-shot equilibrium. Its internally selected unique free
product Nash point gives

    V=(641/3,503/12,101/4,245/6),
    E g₀=23/24,       C₀^wait=5105/24.                 (C3)

Every player has a negative nonempty joining difference: use T1,T0,T03,T0
for players0,1,2,3, with values−4,−5,−1,−1. Thus no label satisfies
the raw join-monotone-anchor condition.

### All fourteen children: one structural obstruction, all five kinds

For EVERY nonempty proper child S choose the following nonempty sure
coalition T⊆S and omitted k. Players in T Quit at date0; all other child
players Never. The child gap vector gives, in increasing child order,
Quit-minus-withdraw for members of T and Continue-minus-join for nonmembers.

| S | T | k | Child gaps | Omitted joining gain |
|---|---|---|---|---|
| 0 | 0 | 2 | (1) | 1 |
| 1 | 1 | 2 | (1) | 5 |
| 2 | 2 | 3 | (1) | 1 |
| 3 | 3 | 2 | (1) | 1 |
| 01 | 0 | 2 | (1,5) | 1 |
| 02 | 02 | 1 | (1,1) | 1 |
| 03 | 0 | 2 | (1,1) | 1 |
| 12 | 12 | 3 | (5,5) | 6 |
| 13 | 13 | 2 | (5,5) | 6 |
| 23 | 23 | 1 | (1,1) | 6 |
| 012 | 012 | 3 | (2,1,1) | 1 |
| 013 | 0 | 2 | (1,5,1) | 1 |
| 023 | 02 | 1 | (1,1,1) | 1 |
| 123 | 123 | 0 | (6,6,6) | 2 |

Every displayed child profile is exact terminal Nash against complete
behavioral replacements. If T has at least two members, every deviator has
a sure opponent at date0, so its full deviation reduces to its pure date0
choice. If T is a singleton, its owner has positive own reward1 and all
other child players Never: neither a delayed quit nor Never improves it.
All nonmembers have the strictly negative displayed joining comparisons.
Each profile has zero child debt and zero Never mass. Its positive omitted
gain therefore defeats EVERY universal omitted-gain bound by any fixed
nonnegative weighted sum of child debts and Never mass.

There is also a direct literal raw-row proof, not only a semantic inference.
With advance and withdrawal weights λ_i,ω_i≥0, its necessary J row is

    r_k(T+k)−r_k(T)≤Σ_{i∈S}[λ_i(r_i(T+i)−r_i(T))+ω_i w_i(T)].

Here w_i(T)=0 for i∉T, equals r_i(T−i)−r_i(T) for a member of a
nonsingleton T, and is its kind's restart floor minus s_i for T={i}.
At the displayed T, every advance joining gain is≤0. For a nonsingleton
member the withdrawal gain is r_i(T−i)−r_i(T)<0; a nonmember's withdrawal
gain is0. At a singleton member, every actual restart floor is≤own1:
patient≤max(1,0), deadline and evaluated security≤0, and terminal security
≤1 by the singleton LP row. Cancellation has the deadline floor. Thus
every withdrawal gain is≤0. The actual J row has strictly positive left
side and nonpositive right side, for ALL nonnegative advance and withdrawal
weights and ALL five `WithdrawalFutureJoinKind` values: patient, deadline,
evaluated security, terminal security and cancellation. No F or Never row
can repair it. This also excludes the simpler future/join-only certificates.

The literal source is `WithdrawalFutureJoinRewardCertificate`,
especially `join_row` and `WithdrawalFutureJoinKind.gain`, in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
The exact restart bounds are
`patientWithdrawalFloor_le_ownNeverAlternative` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`,
`deadlineWithdrawalZeroFloor_le_zero` and `deadlineWithdrawalGainFloor` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
and `deadlineWithdrawalSecurityValue_le_singleton` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`.
The universal debt conclusion is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
This result does NOT
exclude a specially selected safe child equilibrium that avoids these
witnesses; it excludes the actual universal raw-weight families.

### Explicit full sixty-coordinate neighborhood

Let every reward coordinate vary independently by absolute amount<1/40.
Own rewards remain positive. On a nonempty T, g₀ varies by<2δ,
R_{1,C} by<2δ and R_{2,Q} by<2δ, where δ=1/40; the total right-minus-left
variation in(C2) is<5δ=1/8. On T=∅, g₀=0 and R_{1,C}=0 still, and
the remaining variation is smaller. Thus(C2), with β=1/4, remains valid
with strictly positive slacks. The selected Nash point may change; the
raw finite producer does not require an IFT or prescribe its coordinates.

All child and omitted comparisons in the fourteen-row table have margin
at least1 and vary by<2δ. Their exact child Nash, zero Never and positive
omitted-gain obstructions persist. Singleton withdrawal floors are still
bounded by the new positive own rewards. Hence this entire open full-table
box is produced by the CCE criterion while no implemented five-kind raw
withdrawal family can consume it. This disproves structural inclusion of
the global LP class into the union of those raw families.
The other source comparisons below concern the exact displayed center;
they are not silently asserted throughout this entire1/40 box.

### Other finite raw-source comparisons

For a pair partition, let a(i) be i's mate and O(i) the opposite pair.
Use the numerical comparisons

    Γ_ii=0, Γ_ij=r_i({j})−s_i for i≠j,
    Π_i=r_i({i,a(i)})−s_i,
    c_i=Π_i−Γ_i,a(i)=r_i({i,a(i)})−r_i({a(i)}).

The singleton comparison matrix is

    Γ=[[0,3,−1,−1],[3,0,−1,−1],[−1,−1,0,3],[−1,−1,3,0]],
    Γ⁻¹=(1/15)[[2,7,3,3],[7,2,3,3],[3,3,2,7],[3,3,7,2]],
    det Γ=45.

Its row sums are1 and its favorable partners are(01)(23).
On word01/23, c₀=−4 and c₁=−5. On03/12, c₃=−1. On02/13,
c=(1,5,1,5)>0, but player0's opposite triple reward r₀(013)=96 exceeds
own1. Thus EVERY pair partition fails the raw weak two-pair condition
“c_i≥0 for every i and r_i({i}∪T)≤s_i for every ∅≠T⊆O(i)”,
and also its stronger matching and all-positive signed-inverse subcriteria.
Indeed Γ⁻¹diag(σ)>0 forces σ_i=+1 for every i; a signed-inverse
criterion retaining σ_i c_i>0 and opposite caps≤own therefore fails too.
No harmful pair contains two below-mate participants: pair02 has Π₀=Π₂=0, pair03 has
Π₀=0, and pairs12,13 have positive participant premiums. This defeats
the negative-participant matching arm's necessary condition that one harmful
scheduled pair has c_i<0 for BOTH its members. Its normalized premium
requirement Π_i/b_i<−1, with Γ_i,a(i)=−b_i<0, implies exactly that condition.

Every proper all-below-singleton two-pair output is excluded intrinsically,
not through a guessed persistence radius. To see the necessary value formulas,
write X_j=q_j/(1−q_j)>0. Active-phase mixing gives

    U_i=s_i+Π_iq_a(i)
       =q_a(i)r_i({a(i)})+(1−q_a(i))W_i,
    W_i=s_i+c_iX_a(i).

These equalities follow from the two active endpoints regardless of any
outsider cap. On either harmful word, player0
has Π₀=0 and c₀=1, forcing W₀=1+X_mate>1. On the favorite word01/23,
players2,3 have Π=4, forcing their active values>1. These exhaust all
pair partitions and relabelings.

No persistent base E of cardinality≥2 is complement-leave-safe. A failing
recipient and opponent coalition T⊇E−i are:

    E01:(i0,T1), E02:(i2,T03), E03:(i0,T13),
    E12:(i2,T013), E13:(i1,T03), E23:(i2,T03),
    E012:(i2,T013), E013:(i0,T13), E023:(i2,T03),
    E123:(i2,T013), EI:(i2,T013).

Their joining differences are respectively−4,−1,−4,−1,−5,−1,
−1,−4,−1,−1,−1. The exact predicate and strategic consumer are
`QuittingPersistentBaseComplementLeaveSafe` and
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.

For the polynomial comparisons, if p_T(q) is the independent law of player i's
opponent coalition, set

    Q_i(q)=Σ_Tp_T(q)r_i(T+i),
    C_i(q)=Σ_{T≠∅}p_T(q)r_i(T),
    D_i(q)=(1−p_∅(q))Q_i(q)−C_i(q).

This is the actual zero-discount stationary displacement and depends only on
opponents. With a sure opponent it is the averaged literal joining difference.
Every one-sided weak-unit guard fails its UPPER face. For(owner,passive),
choose T containing owner and omitting passive with positive passive join:

    (0,1):T02, (0,2):T0, (0,3):T01,
    (1,0):T12, (1,2):T1, (1,3):T1,
    (2,0):T2,  (2,1):T2, (2,3):T2,
    (3,0):T3,  (3,1):T3, (3,2):T3.

At these pure hazards the polynomial displacement IS that positive joining
difference, so this excludes both raw and polynomial guards, not merely a
stronger sufficient ranking. The literal declarations are
`QuittingOneSidedWeakUnitGuards`, `QuittingOneSidedWeakUnitRawGuards` and
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`, and
`QuittingWeakUnitJoining` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitRawGuards.lean`.

The two-sided weak half-polynomial guards also fail under every relabeling.
Their actual lower face, together with this invertible nonnegative inverse,
forces the selected reciprocal singleton entries positive. Thus the selected
pair must be01 or23; this is the literal
`QuittingHalfWeakPolynomialGuards.reciprocal_pos` necessity in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.
For selected01, recipient0 with partner1 hazard1/2 and outsiders2,3 sure
has displacement(g₀(23)+g₀(123))/2=3/2>0. For selected23, recipient3
with partner2 hazard1/2 and outsiders0,1 sure has displacement
(r₃(013)−r₃(01)+r₃(I)−r₃(012))/2=(1+1)/2=1>0.
Each is on its required nonpositive upper-half face. This excludes the
broader polynomial guards and hence their finite weak/strict raw subclasses.
The raw and polynomial consumers are
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingProducer.lean`
and `exists_stationary_terminalApproximation_of_weakHalfPolynomialGuards`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`.
The displacement definition is in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` and
depends on opponents only; the displayed sure-outsider rows therefore
equal the averaged literal joining gains just computed.

Global inserted-premium weights obey λ≥0 and
Σ_iλ_i[r_i(T+i)−s_i]≥0 on every coalition T. Such weights must vanish.
At T0 the coefficient vector
is(0,−2,0,−2), forcing λ₁=λ₃=0. At T03 it then forces λ₂=0; at T23
it forces λ₀=0. Therefore `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
fails, since the grand coalition is a premium trap and requires positive
weights. Its weak reward-closure consumer is
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`.
A premium trap E is nonempty and each i∈E has some S⊆E containing i
with r_i(S)>s_i. The actual traps are12,13,23,012,013,123,I. Write

    L_E(T)=Σ_{i∈E∖T}[r_i(T+i)−s_i],
    J_E(T)=Σ_{i∈E∖T}[r_i(T+i)−r_i(T)].

None has all its proper-subset L and J charges nonpositive:
witnesses T1,T1,T2,T1,T1,T1,T13 have both
positive charges. In particular L_I(13)=100,J_I(13)=2. No player has every
participant reward at least its own level: use01 for0,1,023 for2,03 for3.
Sure I's four forced-Quit values all exceed own1, defeating
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.

For conditional ranges, player0 has Continue upper≥r₀(123)=1000.
For every blocker, its Quit-without lower≤own1, and its Quit-with lower≤1
using pair01,02 or03. Thus no convex mixture of those lower bounds strictly
exceeds its Continue upper. This directly defeats
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
Membership influence1→0 changes sign: at empty background the literal
joining gain changes by−5, whereas at background2 it changes by+1.
Thus `SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
fails. The interaction coefficient6 also defeats
`IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

Γ row sums1 imply Γᵀλ≤0 with λ≥0 forces λ=0. For a response-invariant
partition, recipients in one block must have equal displacement polynomials
when every source block uses one hazard. Differentiating at zero hazards
equates their blockwise singleton row sums. Summing over source blocks
forces equal positive row scales within any such block after
playerwise positive affine transport. The all-sure displacement vector is
(2,1,−1,1); only the pair{1,3} could share a block. That pair's singleton0
block sums are3 and−1, so it too fails. Thus all fourteen nondiscrete
response-invariant quotient partitions fail even after such transport.
This uses the actual necessity `quittingSingletonBlockRowSum_eq_of_responseInvariant`
in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

### Sure-stationary census and transient-center output

If0 is sure, the unique free Nash point from(C1) applies. Repeating it gives
Never₀=5104/23 and Q₀=641/3, hence Q₀−Never₀=−569/69<0. The one-shot
profile must not be stationary repeated.

If1 is sure, player3's joining difference is strictly positive: when0
Continues it is5+q₂, and when0 Quits it is1. Thus3 is sure. The free0,2
response differences are−4+6q₂ and6−7q₀, giving unique Nash
(q₀,q₂)=(6/7,2/3). Sure1's difference is then−1/21<0.
If2 is sure, player1 is forced sure (its difference is5+q₃ when0 Continues,
and1 when0 Quits); then player0 has difference2 and player3 difference1,
forcing the grand coalition, where player2's difference is−1.

If3 is sure, free0,1,2 differences are

    G₀=1−5q₁+6q₁q₂,
    G₁=(1−q₀)(5+q₂)+q₀(−5+6q₂),
    G₂=(1−q₀)(1+5q₁)−q₀.

At q₀=0 the other two are forced sure, contradicting G₀>0. At q₀=1,
the unique free response is(q₁,q₂)=(0,0). If q₀ is proper, q₁=0 makes
G₀=1; q₁=1 forces(q₀,q₂)=(6/7,2/3) and G₁=−1/21; q₂=0 forces
(q₀,q₁)=(1/2,1/5) and G₂=1/2; q₂=1 makes G₀>0. All boundary cases
fail. At an all-proper point G₀=0 gives−5+6q₂=−1/q₁. The G₁,G₂
equations then respectively give

    q₀/(1−q₀)=q₁(5+q₂),
    q₀/(1−q₀)=1+5q₁,

hence q₁q₂=1, impossible. The only finite Nash completion is therefore
(q₀,q₁,q₂)=(1,0,0), where sure3's difference is−1. No sure-quitter
stationary equilibrium exists. This excludes actual sure-anchor stationary
sources, but does not claim absence of all-proper stationary equilibria.

The implemented nearby transient center with one sure anchor and every
free hazard in(1/4,3/4) cannot output this table. Anchor0 forces q₂=5/6;
anchor1 forces free3 sure; anchor2 forces free1 sure; anchor3 has no
all-proper finite completion by the preceding calculation. This is an
intrinsic output exclusion for `exists_nearby_oneDate_sameProfile_horizon_equilibrium`
in `UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`,
not a claim about an unspecified perturbation radius.

## 6. Whole-class inclusion in the concrete persistent-base sources

The unconditional declarations
`exists_uniformPayoff_or_singletonBase_pos_gap` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
already consume EVERY CCE-admitted table. Their alternative is a positive
uniform gap on the ACTUAL complete induced product-Nash carrier, not a
pointwise leave-safety assumption or stationary-Never comparison.

For singleton base a choose free=I∖{a}, leaving no outsiders. Write
P_a=quittingPunishmentValue reward a. At an induced product Nash law p,
`quittingSingletonBaseOwnerFloorExcess` is exactly

    floorExcess=C_nonempty+p_∅P_a−V_a
               =−E_pG_a^{a}+p_∅[P_a−max(s_a,0)].       (9)

The literal theorem `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives
P_a≤max(s_a,0), for either own sign: opponents who always Continue
cap every reply by max(s_a,0). Hence(9)≤−E_pG_a^{a}. Every internally
chosen product Nash law lies in C_a, so our admission implies
floorExcess≤0. With no outsiders and zero free-player components,
`quittingSingletonBaseExcess`≤0. This contradicts the existing alternative's
strict positive-gap branch and yields its UE conclusion.

For |E|≥2 take free=I∖E. The source's
`quittingPersistentLargeBaseComponent` equals−E_pG_i^E on each base
member and0 on every free player; there are no outsiders. Admission
gives every component≤0, hence `quittingPersistentLargeBaseExcess`≤0,
contradicting its positive-gap branch and again yielding the existing UE.
No own-sign, matrix, punishment attainment or special free-game structure
is needed for either inclusion.

At Section5's exact center, p_∅=1/24 and E_pG₀^{0}=23/24. Therefore
floorExcess≤−23/24 and its maximum with the free zero components is0.
The center and its CCE-admitted full reward box are already covered.
The sure-stationary census does not exclude this source: its actual
singleton compiler uses punishment after a quiet owner replacement,
not stationary repetition of the nominal free hazards. That compiler is
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.

The old no-UE alternatives also imply a stronger necessity than(5).
On EVERY singleton induced product Nash point their owner-floor excess
is≥γ>0, so(9) forces E_pG_a^{a}≤−γ. On EVERY large-base induced
product Nash point some member has E_pG_i^E≤−γ. The bad member may
vary with the point; γ is uniform on that carrier. These imply the
existential negative coarse-law condition simply by selecting any finite
Nash point. Thus the value retained here is finite LP recognition and
the exact same-profile/all-horizon strengthening, not additional UE coverage.

## 7. Source handoff and limits

The finite induced game, internally available mixed Nash set and extended
independent row are `quittingPersistentBaseUtility`,
`quittingPersistentBaseNashSet`, `quittingPersistentBaseNashSet_nonempty`
and `quittingPersistentBaseRoot` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.
The nonemptiness theorem imposes no own-sign, cardinality-at-least-two or
pointwise leave-safety premise. It also covers an empty free type.

The actual pointwise producer is
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.
It assumes `QuittingPersistentBaseComplementLeaveSafe` and |E|≥2.
The LP recognizer supplies expected member endpoint inequalities without
requiring pointwise leaving safety or a strategic input.

The supplied-profile consumers
`quittingOneDateThenNeverProfile_exactHorizonNash` and
`quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness` in
`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`
already transfer exact one-date/Never terminal Nash to exact horizons and
one fixed target. Sections1–3 give the raw LP recognition route to their
exact strategic premise, using private independent μ rather than a coarse
law as the implemented profile. Section6 explains why this does not add
an existence class beyond the older concrete sources.

A formal raw predicate should record a nonempty base and the minima or
feasibility conditions in(1)–(4), or use the finite sufficient rows(6).
It must not store μ, a stopping law, continuation values or Nash inequalities
as additional strategic data. The strategic lemma then constructs the
one-date/Never row and proves the original terminal inequalities; the existing
horizon consumers finish the fixed-target theorem.

This is ordinary mathematics, not a new Lean seal. The global criterion is
sufficient, not necessary for UE. Negative laws may depend on the base and
recipient. There is no public-correlated-play theorem, arbitrary-table
completeness claim, all-proper stationary absence claim, or blanket exclusion
of unspecified local equilibrium neighborhoods. Stationary repetition is
licensed only when |E|≥2; the exact singleton counterexample to repetition
in Section5 remains part of the scope.
