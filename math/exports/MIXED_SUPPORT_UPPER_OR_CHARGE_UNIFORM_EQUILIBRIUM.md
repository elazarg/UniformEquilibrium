# Mixed supportwise upper averages and boxed Nash charges

This is an ordinary-mathematical finite-reward class theorem. Its raw
supportwise adapter has not been implemented in Lean. The semantic
consumer below is an existing named declaration, used with all its
stated hypotheses. No arbitrary-game UE theorem, strategy-class
completeness, or exhaustive producer census is asserted.

## 1. Original game and uniform-payoff conclusion

There are four players I={0,1,2,3}. At each live date they independently
choose Continue or Quit. The first nonempty quitting coalition S
absorbs at a fixed reward vector r(S), received at every subsequent
date. The live date selecting that coalition pays zero, as do all other
live stages and perpetual continuation. All
sixty reward coordinates are arbitrary real numbers. Strategies and
unilateral deviations are unrestricted behavioral strategies based on
the public history, with independent private randomization. No public
correlation, bounded controller, or prescribed deviation menu is added.

Write sᵢ=rᵢ({i}) and M=max[S≠∅,i∈I]|rᵢ(S)|. Assume sᵢ≥0 for every i.
A uniform-equilibrium payoff means one target u, fixed before accuracy,
such that for every ε>0 there are a behavioral profile and a horizon
threshold N so that every finite horizon n≥N has expected average payoff
within ε of u, and every complete unilateral behavioral deviation earns
at most uᵢ+ε. The profile may depend on ε; the target may not.

## 2. Finite raw certificates and the class theorem

A nonempty A⊆I is a premium trap if each i∈A has some nonempty S⊆A
containing i with rᵢ(S)>sᵢ. Singletons are never traps. Require that EACH
premium trap A admits at least one of the following two certificates.
Different supports may use different types and different parameters.

### Upper-average certificate

There are weights wᵢ≥0 on A, with ∑[i∈A]wᵢ>0, such that

    H_{A,w}(S)=∑[i∈A]wᵢ·(rᵢ(S∪{i})−sᵢ)≤0
                              for EVERY S⊆A, including S=∅.       (1)

Weights may vanish at some active players. There is no condition outside
A, nor a requirement that the same weights work for different supports.
This is a NONPOSITIVE support-local forced-Quit upper average, not a
nonnegative global forced-Quit floor.

### Boxed-charge certificate

Here m=|A|≥3. There are d,τ,g,ℓ>0 such that, for every nonempty proper
T⊊A, put

    P_A(T)=∑[i∈A\T](rᵢ(T∪{i})−sᵢ),
    L_A(T)=∑[i∈A\T](rᵢ(T∪{i})−rᵢ(T)).

Require the three finite ranges

    |T|=1:             P_A(T)≤−d,    L_A(T)≤−g;
    2≤|T|≤m−2:         P_A(T)≤0,     L_A(T)≤0;
    |T|=m−1:           P_A(T)≤τ,     L_A(T)≤−ℓ.                    (2)

An empty middle range imposes nothing. Require the strict threshold

    C_A=m·(d/τ)^(1/(m−2))·(g+ℓ·d/τ)>∑[i∈A]sᵢ+mM.                (3)

In Fin4, C₃=3(d/τ)(g+ℓd/τ) and C₄=4√(d/τ)(g+ℓd/τ).

THEOREM. Every reward table satisfying these raw hypotheses has a
uniform-equilibrium payoff in the original four-player game.

No equilibrium, continuation annotation, Nash selector, actual tail,
response-cap selector, or potential is an input to this class theorem.
The hypotheses are finite inequalities and finite weight feasibility.

## 3. The full exact-root relation

For any q∈[0,1]^I let μ_q be the independent product coalition law and
c=μ_q(∅). At any continuation annotation v∈ℝ⁴, define

    W(v,q)=c·v+∑[S≠∅]μ_q(S)r(S),
    Qᵢ(q)=∑[T⊆I\{i}]μ_{−i}(T)rᵢ(T∪{i}),
    Cᵢ(v,q)=μ_{−i}(∅)vᵢ+∑[∅≠T⊆I\{i}]μ_{−i}(T)rᵢ(T).

An exact root is a Nash equilibrium of the finite action game with
all-Continue continuation v. Thus

    Wᵢ=qᵢQᵢ+(1−qᵢ)Cᵢ,       Wᵢ≥Qᵢ,       Wᵢ≥Cᵢ.

Finite-game Nash existence supplies an exact full root at every v.
Let A={i:qᵢ>0}. Supported optimality gives

    Wᵢ=Qᵢ≥Cᵢ for i∈A;
    Qᵢ=Cᵢ for i∈A if qᵢ<1.                                    (4)

These are the FULL finite Nash inequalities. We never replace them by
Nash inequalities of an active-player subgame. The annotation v need
not be a payoff of an actual behavioral tail.

## 4. Upper and nontrap supports return to a singleton sublevel

For an upper-average certificate extend its weights by zero outside A.
The full product identity is

    ∑[i∈A]wᵢ(Qᵢ−sᵢ)=∑[S⊆A]μ_q(S)H_{A,w}(S).                  (5)

For each i, summing the full product law over i's own coordinate leaves
the opponent law defining Qᵢ, because rᵢ(S∪{i}) is independent of
whether i belongs to S. Coalitions containing a quiet player have zero
mass. There is no division by qᵢ or 1−qᵢ. Identity (5) is therefore
valid also at partly-sure and all-sure roots, and with any quiet players.

The right side is nonpositive. If every active Qᵢ>sᵢ, the left side is
strictly positive: the weights are nonnegative and one is positive.
Hence some active Qᵢ≤sᵢ, and (4) gives Wᵢ≤sᵢ.

If nonempty A is not a premium trap, some i∈A satisfies rᵢ(S)≤sᵢ for
every S⊆A containing i. Only those coalitions occur in its forced-Quit
average, so Qᵢ≤sᵢ and again Wᵢ≤sᵢ. This covers every singleton support,
including sure singletons. The empty support has zero absorption and
is not part of an absorbing-root return assertion.

## 5. Charge supports: boundary roots and interior charge

The exact aggregate gap identity on the active support is

    ∑[i∈A](1−qᵢ)(Qᵢ−Cᵢ)
      =c·∑[i∈A](sᵢ−vᵢ)+∑[∅≠T⊊A]μ_q(T)L_A(T).                (6)

Multiplication by 1−qᵢ changes each opponent mass into the full coalition
mass. The empty term is c(sᵢ−vᵢ); collecting the nonempty proper terms
gives exactly L_A(T). Identity (6) holds on the entire cube before odds
are introduced.

All proper nonempty leave sums in (2) are nonpositive. If some but not
all active players are sure, c=0. Choose a nonsure active i. The event
T=A\{i} has strictly positive product probability and L_A(T)≤−ℓ<0.
Thus the right side of (6) is negative, whereas its left side is
nonnegative by (4). This is impossible at an exact root.

If ALL active players are sure, the erased-support coefficient is the
individual gap rᵢ(A)−rᵢ(A\{i})≤−ℓ. Player i gains by withdrawal.
This separate case is necessary: both sides of (6) vanish at all sure.
Consequently every exact root with this support has 0<qᵢ<1 on A.

Suppose all active Qᵢ>sᵢ. Put zᵢ=qᵢ/(1−qᵢ)>0 and

    U=∑[i∈A]zᵢ,       E=∑[i∈A]∏[j∈A\{i}]zⱼ.

Divide each positive Qᵢ−sᵢ by its positive opponent-Continue mass.
The empty term vanishes, and collecting proper coalitions gives

    0<∑[∅≠T⊊A]P_A(T)∏[j∈T]zⱼ≤−dU+τE.                       (7)

The elementary symmetric bound E≤U^(m−1)/m^(m−2) implies

    E>(d/τ)U,       U>m(d/τ)^(1/(m−2)).                         (8)

To verify that bound, maximize E at fixed nonnegative sum U. A positive
maximum has at least m−1 positive entries. Holding all but a,b fixed,
E=ab·e_{m−3}(rest)+(a+b)·e_{m−2}(rest). At an unequal maximizing pair
the coefficient e_{m−3}(rest) is positive; averaging the pair increases
E. Thus all entries at a maximum are U/m, giving the bound. For m=3,
e₀=1; the argument also covers a boundary maximizing vector when m=4.

All active players are now indifferent by (4). Divide (6) by c>0:

    ∑[i∈A](sᵢ−vᵢ)
      =∑[∅≠T⊊A](−L_A(T))∏[j∈T]zⱼ
      ≥gU+ℓE
      >(g+ℓd/τ)U
      >C_A.                                                    (9)

In a box |vᵢ|≤B with ∑[i∈A]sᵢ+mB<C_A this is impossible. Quiet-player
Nash constraints were not discarded to produce a root: we used necessary
supported constraints to EXCLUDE a bad full root. Thus every absorbing
full exact root with this charge support has some Wᵢ≤sᵢ.

## 6. One common box and the actual uniform-payoff consumer

There are finitely many traps. Select one available certificate for
each. The strict inequalities (3) permit ONE B with M<B<M+2 and
∑[i∈A]sᵢ+|A|B<C_A for all selected charge supports. If no charge support
is selected, any such B works. The upper and nontrap arguments do not
depend on B. We have proved the universal return property

    EVERY |vᵢ|≤B and EVERY absorbing full exact Nash root q at v
       have SOME player i with Wᵢ(v,q)≤sᵢ.                     (10)

At a boxed v with some vᵢ<sᵢ, choose any full Nash root. It cannot be
all Continue, because that player gains by quitting alone. The root
therefore absorbs and (10) supplies the return. No continuous selector,
realized tail, or uniform positive absorption bound is needed.

The exact semantic consumer is
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.
Its inputs are:

- all own singletons are nonnegative;
- M is a coordinate reward bound;
- M<B and B≤quittingRewardBound reward+2;
- `HasBoxedSelectedSingletonSublevelReturn reward B`.

Our M is the maximum absolute entry, so M≤quittingRewardBound reward.
The common-box choice meets the size conditions. Nash existence and
(10) give the actual selected-return predicate, which only asks for
ONE full root returning at each boxed source strictly below some own
singleton. The declaration concludes
`(quittingGame reward).IsUniformEquilibriumPayoff none payoff` for some
ONE payoff target. This proves the class theorem with the unrestricted
original behavioral and all-large-horizon quantifiers in Section 1.

The consumer imports
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`
and `UniformEquilibrium/Quitting/Classification/Existence/BoundaryDifferentiablePotentialUniformPayoff.lean`.
The algebraic adapter (5) is exactly
`quittingWeightedQuitPremium_eq_fullCoalitionAverage` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.
The one-support charge estimate (9) is exactly the scope of
`QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`.
That declaration does not require charge certificates at other supports.
The new assembly combines these support-local facts; it does not invoke
the globally failed boxed-charge predicate discussed below.

## 7. A complete full-core fixture and certificate audit

The fifteen rows below specify all sixty rewards, in player order
(0,1,2,3). Never pays zero.

| S | r(S) |
| --- | --- |
| {0} | (1,3,3,0) |
| {1} | (4,1,−1,−1) |
| {2} | (0,2,1,2) |
| {3} | (4,−2,0,1) |
| {0,1} | (−200,−200,5,5) |
| {0,2} | (1,5,−200,5) |
| {0,3} | (−200,5,5,1) |
| {1,2} | (5,−200,0,5) |
| {1,3} | (5,−1,5,−200) |
| {2,3} | (5,5,−200,−200) |
| {0,1,2} | (4,4,4,−4) |
| {0,1,3} | (4,4,−4,4) |
| {0,2,3} | (4,−4,4,4) |
| {1,2,3} | (−4,4,4,4) |
| I | (−200,−200,−200,−200) |

Call this table r*. Here s=(1,1,1,1), M=200. Every pair has both
participant rewards ≤1, so no pair is a trap. Every triple is a trap,
and so is the full set. The COMPLETE trap list is 012,013,023,123,I.

At I choose wᵢ=1. The empty H coefficient is zero. All nonempty
coefficients, in the indicated coalition order, are

    singletons 0,1,2,3:           −402,−403,−402,−404;
    pairs 01,02,03,12,13,23:      −396,−195,−195,−196,−197,−396;
    triples 012,013,023,123:      −192,−192,−192,−192;
    grand:                       −804.                        (11)

Thus I has an upper-average certificate. Every absorbing full-support
product action profile even satisfies ∑[i∈I](Qᵢ−1)<0 before Nash is used.

For every triple choose (d,τ,g,ℓ)=(201,3,198,1). The complete singleton
coefficient pairs (P_A({j}),L_A({j})), in increasing j order, are

| A | singleton coefficient pairs |
| --- | --- |
| 012 | (−402,−406), (−202,−203), (−201,−201) |
| 013 | (−201,−202), (−402,−403), (−203,−203) |
| 023 | (−201,−202), (−201,−201), (−402,−404) |
| 123 | (−202,−198), (−402,−404), (−203,−199) |

For every pair T⊂A, its omitted owner has P_A(T)=4−1=3 and
L_A(T)=4−5=−1. There is no middle range. The common threshold is

    C₃=3·67·(198+67)=53 265>3+3·200=603.

Use B=201; the same threshold exceeds 3+3B=606. Thus this exact table
is consumed by the class theorem and the actual semantic consumer.

Every pure terminal coalition strictly escapes. At singletons the
outsiders 3,2,0,1 respectively gain1 by joining. At every pair a member
at −200 can leave for a singleton passive reward ≥−2. Every triple
member leaves for passive pair reward5>4; every grand member leaves
for −4>−200. At all Never, each own solo1 improves on0. This pure audit
is NOT the UE argument and does not exclude all mixed or periodic
equilibria.

## 8. A full sixty-coordinate open-neighborhood theorem

THEOREM. Every table r satisfying max[S≠∅,i]|rᵢ(S)−r*ᵢ(S)|<1/100 has
a uniform-equilibrium payoff. No singleton matrix, equality stratum,
or fixed collision row is preserved: all sixty coordinates may vary
independently.

Put η=max|r−r*|<1/100. Then sᵢ≥1−η>0 and the maximum absolute reward
M lies between 200−η and 200+η. The same five traps persist: every pair
retains a participant at most −200+η below its own singleton at least
1−η, while every triple participant premium is at least3−2η>0.

At full support retain wᵢ=1. Each nonempty H coefficient changes by at
most8η, and its original value is at most−192. It therefore remains
negative. The empty coefficient remains identically zero.

At each triple, singleton P and L each change by at most4η; penultimate
P and L each change by at most2η. Use the fixed slack coefficients

    (d,τ,g,ℓ)=(200,4,197,1/2).

Indeed P_single≤−201+4η<−200, L_single≤−198+4η<−197,
P_pair≤3+2η<4, and L_pair≤−1+2η<−1/2. Their threshold is

    C₃=3·50·(197+25)=33 300.

Keep B=201. We have M<200.01<201 and
∑[i∈A]sᵢ+3B<3.03+603=606.03<33 300. Also B<M+2, since M>199.99.
Thus all raw class and semantic-consumer inputs hold with one common
fixed box. This proves the full-coordinate open-neighborhood conclusion.

## 9. Complete root-level sure-base exclusion and true punishment

For r*, the true punishment value of every player is −4, under actual
independent unrestricted opponent strategies. Never guarantees at least
−4, because every passive singleton, passive pair, omitted triple and
Never payoff is at least−4. Opponents all surely quit at date0 in
I\{i}; player i then gets −4 by Continue or −200 by joining. Its full
best-response value is exactly−4. Thus P=(−4,−4,−4,−4), with no public
correlation or nominal-floor substitution.

Stronger, at ANY continuation annotation v, the full finite action game
has NO exact Nash root with ANY sure coordinate. This is a whole-root
exclusion, not a selected-root computation.

If at least three players are sure, choose a member of a three-sure set.
Its gap Quit−Continue is −1−195p<0, where p is the fourth hazard.
Three sure gives triple4 versus passive pair5; four sure gives grand
−200 versus omitted triple−4. Such a sure player is not best responding.

If exactly two a,b are sure, let x,y be the other hazards. Each sure
member's gap is a convex combination of its directed pair joining gap,
two copies of −1, and −196. The four weights are respectively
(1−x)(1−y), x(1−y), (1−x)y, xy. The complete directed pair-gap list is

    01:(−204,−203), 02:(1,−203), 03:(−204,1),
    12:(−202,1),   13:(1,−199), 23:(−200,−202).                (12)

Each pair has a member with all four coefficients negative. Therefore
two sure players are impossible at a full exact root, regardless of
the other rates and of v.

If exactly z is sure, each free player's gap is a convex combination
of its directed joining gap against {z}, two copies of −1, and −196.
Exactly one free player f(z) has positive first coefficient1, where

    f(0)=3, f(3)=1, f(1)=2, f(2)=0.

The other two free players have uniformly negative gaps and must be
quiet. With both quiet, f(z)'s gap is1, forcing it sure. This creates
the already excluded two-sure case. The annotation is irrelevant to
these free comparisons because an opponent is sure; after f(z) becomes
sure, it is also irrelevant to the original owner's comparison.

This proof applies to ALL active supports and free-rate choices.
For every table in the neighborhood of Section8 it remains valid:
each directed joining gap in (12) changes by at most2η; each −1 triple-
versus-pair coefficient by at most2η; each −196 grand-versus-omitted-
triple coefficient by at most2η. The favorite gaps stay positive and
all the other coefficients stay negative. Thus the no-sure-root
conclusion also holds throughout that full-coordinate neighborhood.

These are root-level statements, not exclusions of proper stationary
or quiet-child equilibria with all hazards below1. Any producer whose
accepted data imply a full exact root with a sure player is excluded
over its COMPLETE owner, base, and free-rate selection set. In
particular it rules out the accepted persistent-base inputs. A point in
`quittingPersistentBaseNashSet` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`,
TOGETHER WITH the required base-leave and outsider-join signs, supplies
the prohibited full root when the base has size at least two. The exact
adapter and consumer are
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
The induced Nash set alone is NOT asserted empty. For a singleton base,
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
use the owner-floor field to supply Continue optimality at the TRUE
punishment value, with the same induced-Nash and outsider-join screens.
Also every choice in `HasQuittingPunishmentVectorNashRootWithSureQuitter`
in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`
is ruled out. No arbitrary existential child certificate is excluded
by this assertion.

## 10. Selection-set comparison with the relevant raw class producers

The fixture establishes that the mixed per-support assembly succeeds
where the following COMPLETE raw selection sets fail. These are bounded
source comparisons, not a census of every possible UE theorem or supplied
certificate. The pure triple witnesses below are product action profiles,
NOT exact Nash roots; this distinction is required by the actual predicate.

1. `HasProductLowQuittingPremium` in
   `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
   fails at any sure-triple product action profile: all active Qᵢ=4>1.
   The predicate quantifies over every absorbing product action profile,
   not merely Nash roots. No alternate weight or decision witness can
   repair this universal failure. Thus the standalone product-low producer
   `exists_uniformEquilibriumPayoff_of_productLowPremium` in
   `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
   does not consume the table through that hypothesis.

2. `HasBoxedQuittingNashCharges` in
   `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
   fails at the full trap: EVERY pair T has P_I(T)=6>0. Its required
   middle-range coefficient is P_I(T)≤0, independently of every possible
   d,τ,g,ℓ and every box. All proper triple traps pass, but the original
   global predicate requires coefficients at the full trap too.

3. `IsSupportwiseBalancedQuittingPremiumTable` in
   `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`
   fails over ALL nonzero nonnegative participant-weight choices at I.
   Each contained triple has participant premium3 at all its members;
   a triple containing any positive weight has a strictly positive
   weighted participant premium. This defeats the finite participant-
   weight certificate, which weights qᵢ(Qᵢ−sᵢ), rather than (5).

4. ALL protected/common/support-specific leaver choices fail. Every
   grand participant reward is −200<1, so the maximal protected set is
   empty. `HasProtectedParticipantPremiums` in
   `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`
   admits no nonempty protected set, whereas every trap must select a
   protected leaver. The strict and weak versions both fail for EVERY
   protected set and per-support witness. The passive-perturbation closure
   `exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave` in
   `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`
   retains this participant data. `IsCommonQuittingPremiumLeaver` in
   `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
   likewise fails for each player; the four triple traps additionally
   have empty intersection.

5. ALL weighted trap-leaver choices fail. In
   `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
   `HasWeightedQuittingTrapLeavers` requires positive weights on the trap,
   zero outside, and a global NONNEGATIVE inserted premium. At coalition
   I this is −201·∑[i∈A]wᵢ<0 for every allowed weight. The strict and weak
   leave versions cannot repair a violated global floor. Our upper
   alternative deliberately uses the opposite sign and only its support.

6. The premium core is all four players, so every at-most-two-core or
   exactly-three-core producer fails its cardinality hypothesis under
   every labeling. In particular
   `hasBoxedSelectedSingletonSublevelReturn_of_mixedSignTriple_core` in
   `UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreSelectedReturn.lean`
   requires one three-element premium core, which does not exist here.

7. An all-profile prescribed-payoff-deficit hypothesis does not hold.
   The exact singleton matrix Γᵢⱼ=rᵢ({j})−sᵢ is

       Γ = [ [ 0,  3, −1,  3],
             [ 2,  0,  1, −3],
             [ 2, −2,  0, −1],
             [−1, −2,  1,  0] ].

   With λ=(2,1,5,1)/9, Γλ=(1,6,1,1)/9>0 in every coordinate. Actual
   stationary hazards qᵢ=ελᵢ, repeated forever with ε=1/10 000, give
   every player's terminal prescribed payoff strictly above its own1.
   Indeed each unnormalized terminal premium numerator has singleton
   contribution at least ε/9−3ε². The singleton product-factor loss is
   bounded by the sum of opponent hazards and |Γᵢⱼ|≤3. The probability
   of a nonsingleton row is at most ∑[j<k]qⱼqₖ≤ε²/2, and every premium
   is at least−201. Thus every numerator is at least
   ε/9−(207/2)ε²>0. Division by the positive per-row absorption gives
   the repeated stationary terminal payoff. This law is NOT asserted
   Nash; it disproves a prescribed-payoff-only deficit predicate.
   Also no nonzero nonnegative terminal upper-chamber weight can work:
   its singleton conditions would imply wᵀΓ≤0, contradicting Γλ>0.

All the failures in items1--5 are strict where nontrivial and persist
through a small full reward neighborhood; arbitrarily close reward
closure does not evade them. These failures are distinct from the
positive whole-class proof, and they do not assert nonexistence of
any equilibrium.

## 11. Exact singleton-matrix and deadlock-family source alignment

Γ is literally `FullCoreDeadlock.deadlockMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`.
Its named `deadlockMatrix_normalCore_eq_univ` gives full normal core.
Arbitrary completion results there and in
`DeadlockGlobalContraction.lean` and `DeadlockSharperBound.lean` supply
positive debt upper bounds, not a zero-gap UE producer for the entire
completion family.

Here is also an exact complete matrix-regime check. The principal
determinants on supports of size at least2 are

    pairs 01,02,03,12,13,23:       −6,2,3,2,−6,1;
    triples 012,013,023,123:       10,−3,5,8;
    full:                         25.

They are all nonzero. Every Γ column has a negative offdiagonal entry.
A nonzero homogeneous complementary solution with support of size≥2
would lie in the kernel of that support's principal matrix, impossible;
one-point support violates the negative entry in its column. Thus Γ
is R₀ and has no homogeneous simplex LCP solution.

For positive anchor a=(1,2,3,5), the complete inverse-principal candidate
list at right-hand side −a is below. Displayed z coordinates are in
the listed support order. Outside that support z is zero. Residual is
−a+Γz. A candidate is admissible exactly when every listed z is
strictly positive and all outside residuals are nonnegative.

| support | z on support | outside residuals |
| --- | --- | --- |
| 01 | (1,1/3) | row2:−5/3, row3:−20/3 |
| 02 | (3/2,−1) | row1:0, row3:−15/2 |
| 03 | (−5,1/3) | row1:−13, row2:−40/3 |
| 12 | (−3/2,2) | row0:−15/2, row3:0 |
| 13 | (−5/2,−2/3) | row0:−21/2, row2:8/3 |
| 23 | (5,−3) | row0:−15, row1:12 |
| 012 | (3/2,0,−1) | row3:−15/2 |
| 013 | (21,−13,40/3) | row2:155/3 |
| 023 | (3,8,3) | row1:3 |
| 123 | (−3/2,2,0) | row0:−15/2 |
| I | (12/5,−3/5,31/5,3) | none |

There is no empty or singleton solution, since the right-hand side is
strictly negative and the diagonal is zero. Only support023 is
admissible. Its inactive slack3 is strict and its determinant5 is
positive. Thus the degree is1 by
`r0Degree_eq_sum_admissible_inverse_supports` in
`MathUE/LinearProgramming/FiniteSupportDegree.lean`; all its negative-
column, principal-nonsingularity, positive-anchor and strict-inactive-
slack hypotheses have just been supplied. Consequently Γ is StandardQ
by `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. These exact ordinary instance
calculations exclude the generic homogeneous and ordinary non-Q exits;
they are not a new Lean-checked fixture instance or a finite grid argument.

The relevant named deadlock UE producers are specific completions:
`FullCoreDeadlock.reward_isUniformEquilibriumPayoff_jointBlock` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`
is for zero nonsingleton rewards, and
`integerTableTarget_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockIntegerTablePeriodThree.lean`
is for its named integer table and algebraic certificate. Neither is
this completion. The arbitrary-baseline polyhedral producer
`isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean`
requires the ENTIRE pair13 payoff vector to equal the singleton baseline.
Here the baseline is forced to (1,1,1,1), but pair13 is (5,−1,5,−200).

That comparison covers ALL allowed player labelings. The four
offdiagonal row multisets of Γ are respectively
{−1,3,3}, {−3,1,2}, {−2,−1,2}, {−2,−1,1}, all distinct. Any simultaneous
row/column permutation preserving Γ must fix every row, so its only
automorphism is identity. No alternative labeling can shift another pair
into the required slot while preserving the singleton hypotheses.
Likewise no labeling makes Γ circulant, because a circulant matrix has
equal offdiagonal row multisets. This defeats the defining equality of
the cyclic singleton producer, not merely one selected balance root.

## 12. Universal quiet transports: a precise, limited obstruction

The favorite joining map f of Section9 is one cycle
0→3→1→2→0. Every nonempty proper child S⊊I cuts an edge z→k=f(z),
with z∈S and k∉S. Otherwise closure under f would force S=I.
In that child prescribe z surely at date0 and every other child player
Never. This is an exact unrestricted terminal child Nash profile:
owner z receives1 and withdrawal gives0; every other player in S has
a negative joining gap because z's unique positively joining outsider
is the excluded favorite k. Later changes cannot alter date0 absorption.
Every mixed stopping-time deviation is an average of these pure actions.

Hence all child debts dᵢ are zero and child joint Never probability
Q_child is zero, but the quiet parent outsider k gains1 by joining at
date0. For EVERY proper child there can therefore be no fixed finite
nonnegative coefficients satisfying a bound

    d_k(quiet(p))≤∑[i∈S]cᵢdᵢ(p)+ρQ_child(p)
                         for EVERY actual child profile p.      (13)

This excludes universal child-debt/Never transport certificates over
all child and weight choices. For example the raw structure
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`
would imply such a universal bound by
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
For a chosen S and its cut outsider k, apply this structure after
restricting the reward table to S∪{k} and labeling k as `none`.
Remaining parent outsiders are quiet and do not change either payoff
in the countertest. Thus no such accepted universal certificate exists
for any proper child/outsider transport needed to cover that cut edge.

This is NOT an exclusion of an EXISTENTIAL selected safe-child equilibrium.
Another child profile or continuation might be safe. No claim that all
quiet lifts have a gap, or that all proper stationary/periodic controller
producers fail, follows from (13). The universal certificate obstruction
is supporting selection-set evidence, not part of the class theorem.

## 13. Scope and nonclaims

The proved result is a raw arbitrary-table class and a full-coordinate
open UE chamber. Every trap is checked and every absorbing full exact
root is covered on a common box. The semantic conclusion uses one
fixed target and all unilateral behavioral deviations over all large
finite horizons. No bounded controller or Never-floor assumption is
introduced.

The exact fixture lies outside the complete raw ProductLow, global
boxed-charge, participant-balance, protected/support-specific leaver,
weighted-floor and relevant deadlock selection sets compared above.
Its standard-Q/full-normal-core status and no-sure-root theorem prevent
the identified matrix and sure-base producers from silently retiring it.
These comparisons are carefully scoped; arbitrary supplied equilibrium
verifiers and existential safe-child choices are not universally excluded.

No positive unrestricted gap is claimed for the fixture; it has UE by
the theorem. The full finite-quitting conjecture, general stochastic-game
existence, and a finite-amplitude repair for an arbitrary worst-table SUM
minimum remain open. The new raw supportwise assembly and finite fixture
are ordinary mathematics, not additional Lean verification or evidence seals.
