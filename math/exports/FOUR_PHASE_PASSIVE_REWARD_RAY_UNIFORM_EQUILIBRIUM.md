# A complete passive-reward ray by symmetric/asymmetric joint clocks

An explicit symmetric/asymmetric branch switch produces exact private-
clock terminal equilibria throughout the raw reward family below. The
same profiles produce fixed uniform-equilibrium payoffs. All persistent-
base selections fail on this family; no arbitrary-completion or arbitrary-
Fin4 coverage is asserted.

## 1. Self-contained theorem and exact raw data

There are four players 0,1,2,3. Their original singleton rewards are

    r(0)=(1,4,0,0),    r(1)=(4,1,0,0),
    r(2)=(0,0,1,4),    r(3)=(0,0,4,1).

Define the mate permutation m=(0 1)(2 3). The allowed parameters are

    T=(5+sqrt(5))/2,
    T<A<4,
    D=sqrt((4-A)/(A-1)),  J=(A-1)*D,
    0<B<=J,
    C=(1-D)*(1-J),
    Kcrit=C/(1-sqrt(D))^2,
    0<=K<infinity.

In this range 0<D<(3-sqrt(5))/2<1 and 0<J<1, so C>0 and
0<Kcrit<infinity. Define the complete nonsingleton table by

| S | r(S) |
| --- | --- |
| 01 | (A,A,K,K) |
| 02 | (B,K,-B,K) |
| 03 | (-B,K,K,B) |
| 12 | (K,-B,B,K) |
| 13 | (K,B,K,-B) |
| 23 | (K,K,A,A) |
| 012 | (K-1,K-1,K-1,K) |
| 013 | (K-1,K-1,K,K-1) |
| 023 | (K-1,K,K-1,K-1) |
| 123 | (K,K-1,K-1,K-1) |
| 0123 | (-1,-1,-1,-1) |

There is no normalization or modification of these original rewards.
Live and Never pay zero, randomization is private and independent, and
every deviation replaces a complete behavioral law, including Never.

Theorem: for EVERY allowed A,B,K, the ORIGINAL game has an exact terminal
Nash profile against every complete unilateral replacement. Its actual
value at each initial phase is a uniform-equilibrium payoff, with the
same profile supplying all positive accuracies over sufficiently long
finite horizons. No payoff translation, public correlation, supplied
root or limiting behavioral law is an input. The profile is constructed
below solely from the raw parameters, before choosing an accuracy.

For proper hazards a,b in(0,1), use the four-date owner word0,2,1,3,
giving the owner's mate hazard b:

    phase0: q0=a, q1=b;
    phase1: q2=a, q3=b;
    phase2: q1=a, q0=b;
    phase3: q3=a, q2=b.

All omitted players Continue. Every listed coin is independently drawn,
across players and dates. These roots equivalently specify four independent
complete date-or-Never laws. The private randomization has no common seed.
The selection of a,b uses two branches, with a common exact boundary.

## 2. The symmetric branch and the exact switch boundary

Write qstar=1-sqrt(D). For 0<=K<=Kcrit define, for 0<q<1,

    f_K(q)=1+(A-4)*q/(1-q)
           -K*q^2-(1-q)^2*(1+(A-1)*q).             (E1)

This function is continuous, extends to f_K(0)=0, and has derivative
f'_K(0)=-1. Therefore f_K(q)<0 for all sufficiently small positive q.
At the other endpoint its value is exactly

    f_K(qstar)=C-K*qstar^2
             =qstar^2*(Kcrit-K)>=0.               (E2)

For completeness, put z=sqrt(D), so qstar=1-z and
4-A=(A-1)*z^4. The part of f_K(qstar) not containing K is

    1-z^2-(A-1)*(1-z)*(z^2+z^3)
      =(1-D)*(1-(A-1)*D)=C.

The intermediate value theorem supplies a q in(0,qstar] with f_K(q)=0.
Select any such q and put a=b=q. When K=Kcrit take q=qstar exactly.
This includes K=0; no division by K or positive K hypothesis is used in
this branch. No uniqueness or continuity of the root selection is claimed.

## 3. The asymmetric branch above the switch

For K>Kcrit set

    x=C/K,  s=1-D+x,
    a=(s+sqrt(s^2-4*x))/2,
    b=(s-sqrt(s^2-4*x))/2.                          (E3)

Here 0<x<(1-sqrt(D))^2. Hence the discriminant is
positive, 0<b<a<1, and

    ab=x,       (1-a)*(1-b)=D.                      (E4)

Indeed the discriminant factors as
`[x-(1-sqrt(D))^2]*[x-(1+sqrt(D))^2]`; positive roots sum to s, and
their Continue probabilities have positive sum 2-s and product D.
Here s<2 because x<(1-sqrt(D))^2<1. In particular neither root
reaches or exceeds one.

At K downarrow Kcrit, both roots tend to qstar: the discriminant
vanishes and a=b=1-sqrt(D). Thus the symmetric boundary and the limiting
asymmetric policy agree exactly. The theorem uses the IVT branch below
and the explicit radical branch above this boundary, not an asserted
globally unique continuation through every possible equilibrium branch.

## 4. Actual values and both owner equations

Let tau=(0 2 1 3), and let tau act on payoff coordinates in the usual
way. Both the raw table and the root calendar are equivariant under
this permutation/phase shift. Define

    d=(1-a)*(1-b),    x=a*b,
    L=1+(A-1)*b,      H=1+(A-1)*a,
    W=K*x+d*L,        Z=K*x+d*H,
    U0=(L,H,W,Z),     Ut=tau^t(U0).                (E5)

Here tau acts by (tau u)_i=u_(tau^(-1)i). In the symmetric branch
d=(1-q)^2; only in the asymmetric branch and at the switch is d=D.

These will be shown to be ACTUAL policy values, not supplied arbitrary
continuations. At phase0 the two active players' pure Quit endpoints
are L and H. Their Continue endpoints are respectively

    4*b+(1-b)*Z,       4*a+(1-a)*W.

Thus both active players are indifferent exactly when

    Z=1+(A-4)*b/(1-b),
    W=1+(A-4)*a/(1-a).                            (E6)

In the symmetric branch both equations are precisely f_K(q)=0, so the
IVT has supplied BOTH owner equalities, including at the boundary.

In the asymmetric branch d=D and D^2=(4-A)/(A-1). Subtracting the
right side of the W equation from W and using a+b-ab=1-D gives

    W-[1+(A-4)*a/(1-a)]
      =K*x+D-1+(A-1)*D*[b+a*(1-b)]
      =K*x-(1-D)*(1-(A-1)*D)=0.

Interchanging a,b gives the Z identity. Thus neither owner equation
was discarded by solving only their difference or sum.

For passive player2 at phase0, the only nonzero absorbed reward is
the pair01 reward K, of probability x. Joint Continue has probability
D, and the next phase's player2 value is L. Therefore its policy
recursion is W=K*x+d*L. The same argument gives player3's recursion
Z=K*x+d*H. The active policy recursions follow from(E6) and their
indifference. Thus ALL sixteen coordinate policy recursions hold,
by equivariance. Joint survival per period is d^4<1, so these bounded
recursions uniquely identify the actual geometric policy values.

## 5. Every inactive endpoint, on both branches

At phase0, player2's pure Quit endpoint is

    Q2=d+B*(b-a)+(K-1)*x,

and player3's is

    Q3=d+B*(a-b)+(K-1)*x.

These account respectively for no opponent Quit, either sole opponent,
and both opponents. In particular the triple term is the ORIGINAL
K-1, not a clipped or discarded reward. Continue equals W or Z by
actual policy evaluation. The endpoint margins are exactly

    W-Q2=(A-1)*d*b+B*(a-b)+x,
    Z-Q3=(A-1)*d*a-B*(a-b)+x.                     (E7)

For a=b=q these are BOTH

    (A-1)*(1-q)^2*q+q^2>0.

For the asymmetric branch they are respectively

    J*b+B*(a-b)+x>0,
    a*(J-B)+B*b+x>0,

because d=D, 0<B<=J and a>b>0. Equivariance checks all
eight inactive endpoints at the other three phases. Along with both
active equalities per phase, this verifies all sixteen local endpoint
pairs. Simultaneous pair quits and the triples caused by a unilateral
Quit are explicitly included.

## 6. Complete caps and fixed-profile uniform payoffs

Each player has one a coin and one b coin per period. Deleting that
player leaves three of each, with opponent survival d^3<1 per period.
The exact policy equations and endpoint inequalities therefore iterate
to a bound on EVERY complete replacement, with vanishing remainder
controlled by the deleted geometric clock. Pure Never and arbitrarily
late deadlines satisfy the same comparison. The profile is exact
terminal Nash at every initial phase.

For any finite bound M on the original table's absolute rewards, the
same profile has delivery error at most M*C_hor/N and full horizon
regret at most2*M*C_hor/N, where

    C_hor=1+4/(1-d^3).

Thus every fixed actual value Ut in(E5) is one uniform-equilibrium payoff,
chosen before accuracy. More explicitly, if
M=max_(i,S)|r_i(S)|, then for every epsilon>0 the SAME selected profile
is epsilon-horizon Nash and delivers Ut within epsilon whenever
N>=2*M*C_hor/epsilon. The table-specific
M may grow with K; no bound uniform over changing reward tables is
needed. The calendar and targets need not be inherited from any old
certificate or approximate family.

The clock estimate is independent of the deviator's rule: absorption
occurs no later than the first opponent Quit. At each complete block of
four dates its surviving probability is multiplied by d^3, so the sum
of opponent live probabilities is at most4/(1-d^3). Iterating the
coordinate Bellman inequalities against an arbitrary replacement gives
the actual terminal cap Ut_i; the tail vanishes even for Never. Comparing
the terminal reward with its finite-horizon delivery loses at most M
times this live-time budget divided by N for either the prescribed
profile or ANY replacement. This proves the displayed delivery and
regret bounds, with no restriction to cyclic, stationary or finite-menu
deviations.

## 7. What the high-K branch actually synthesizes

At fixed A,B and K->infinity,

    a -> 1-D,    b ~ (1-J)/K,
    K*ab=C.

Thus a macroscopic independent owner clock coexists with a genuinely
rare joint collision. Its passive reward K compensates the vanishing
probability and retains a finite continuation contribution. The actual
policy remains geometrically proper uniformly in this limit, because
the deleted survival remains D^3. Dropping the rare collision BEFORE
evaluating its payoff would destroy the construction.

At the boundary A downarrow T with FIXED K>0 and a fixed admissible B,
J approaches1, C approaches0, Kcrit approaches0, and the eventual
asymmetric profile approaches the golden singleton calendar
`a=(sqrt(5)-1)/2, b=0`. For A>T the positive rare mate hazard and
passive pair transfer repair that calendar's violated favorite-join
cap. This gives a concrete continuation mechanism through a reward
threshold, not an arbitrary local IFT neighborhood or ancestry claim.
The qualification K>0 is essential: at K=0 the symmetric root instead
approaches a=b=(3-sqrt(5))/2. If K varies with C, other branch limits
may occur; the theorem asserts no universal golden limit along such paths.
To verify the K=0 assertion, put p=(sqrt(5)-1)/2 and c=1-p. At A=T,

    (1-q)*f_0(q)=(T-1)*q*(q-c)*(q-p)*(q-(1+p)).

The only nonzero root at or below the limiting endpoint qstar=c is c.
The derivative f'_0(0)=-1 uniformly for A near T excludes a limiting
zero root. Compactness of the selected q in[0,qstar] then forces q->c.

An exact small parameter instance is A=19/5, B=1/2, K=10. Here
D=1/sqrt(14), J=sqrt(14)/5, and(E3) is an exact radical policy.
Numerically a is about0.725771 and b about0.0254085, only as a check;
the source and proof above are exact.

## 8. Whole persistent-base exclusion for every K>=0

For EVERY sure owner j, its mate has joining-minus-passive
gain A-4<0 when the other nonowners Continue. Its other noncollider
has gain -B<0. If one further nonowner quits, either player's gain is
`(K-1)-K=-1`; if both do it is `-1-K<0`. Both are strictly dominated
Quitters in the ENTIRE induced mixed game. The remaining nonowner
kappa(j), with kappa=(0 3 1 2), then has gain B>0 and Quits surely.
The full induced Nash set is this unique point. There owner j gets
-B by Quit and0 by Continue, while all-opponents-Continue mass is
zero. No punishment value can repair its leave gain B.

This also excludes every larger persistent base and free set, not just
singleton bases. Fix j in the base. Were the required leave, free-Nash
and outsider-no-join signs all true, the remaining base players' sure
Quits, the free players' mixed actions and the outsiders' Continues
would together constitute a Nash point in the FULL j-induced game.
Its uniqueness would force the point above and its strictly profitable
owner leave, a contradiction. There is no missing tail coefficient:
the sure kappa(j) Quit makes every all-opponents-Continue probability
zero. This is a whole-correspondence calculation for all K>=0.

The exact source objects inspected are `quittingPersistentBaseUtility`,
`quittingPersistentBaseNashSet`, `quittingPersistentBaseRoot` and
`quittingPersistentBaseRoot_free_purePayoff_le`
(`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`), and
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`).

## 9. Every proper-child raw F/J withdrawal test fails

For EVERY nonempty proper child E choose j in E with kappa(j) outside.
Such a j exists because kappa is a four-cycle. Use the singleton
coalition{j} and outsider kappa(j). Its joining gain is B>0. For ANY
permitted child donor the advancement gain is respectively

    donor j:                 0,
    donor m(j):              A-4<0,
    other noncollider donor: -B<0.

The unique positive-gain donor kappa(j) is not in E. Withdrawal by a
nonmember has gain zero. Withdrawal by the member j has gain equal to
its selected restart floor minus its own singleton1. Each of the five
raw withdrawal kinds has floor at most1 on this literal singleton:
the patient floor is at most max(1,0)=1; the deadline/cancel floors
are at most0; the evaluated security minimum is at most0; and the LP
security maximum is at most1, since its feasible floor has the literal
singleton constraint. Hence every withdrawal gain is nonpositive.

For any nonnegative donor weights, every F/J weighted left side is
therefore nonpositive and cannot dominate the strictly positive outsider
gain. Requiring the additional Never row cannot repair this failed
joining row. Thus all the named F/J-only and N/F/J raw child certificates fail
over ALL children, weights and withdrawal kinds, including the smaller
advancing-only capped-clock cone. This is a raw coefficient witness, not
a claim that every arbitrary child strategy fails.

The inspected definitions are `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`)
and their floor definitions in the same subtree's
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean`,
`DeadlineWithdrawalSecurityMixedPointwise.lean`,
`DeadlineWithdrawalSecurityLP.lean` and
`CappedClockPointwiseDomination.lean`.

## 10. Singleton and ALL response-quotient comparisons

The original singleton matrix, with recipient rows and quitter columns,
is

    Gamma=[[0,3,-1,-1], [3,0,-1,-1],
           [-1,-1,0,3], [-1,-1,3,0]].

Its determinant is45. Its inverse has diagonal2/15, mate entries7/15
and cross-pair entries1/5, all strictly positive. If w>=0 is nonzero
and Gamma*w>=0, then w is strictly positive: if one coordinate were
zero, its mate's row would force the other pair's two coordinates zero,
and a cross row would force the remaining coordinate zero. Hence the
homogeneous complementarity system Gamma*w>=0, w_i*(Gamma*w)_i=0
has no nonzero solution; Gamma is R0, and its nonnegative-inverse degree
is +1. In particular the existing ordinary/projective non-Q and
degree-not-one exits do not apply. Each singleton column also has two
outsider rewards0 below their own singleton1, excluding the strict
positive-column source.

There is no proper balanced singleton word of ANY finite period. Its
active owner value must be1 and every player's phase value at least1.
At a transition from a nonempty run of owner i to a different owner j,
if j is not m(i), j's rewards during the run are zero and its value at
the next j root is1. Positive run absorption then makes its value at
the run's start strictly below1. Thus every distinct-owner transition
must stay within one mate pair. Such a cyclic word uses at most that
pair and gives the other pair payoff zero, another contradiction.
Zero-hazard dates may be deleted. The positive directed graph of Gamma
also consists only of the two mate transpositions, so no relabeling gives
the positive three-cycle or four-cycle required by the named cyclic-child
singleton and signed-four-cycle raw sources. These facts do not exclude
general singleton strategies with arbitrary periods and approximate caps.

For response-invariant quotients one must test the actual raw stationary
displacement, not just Gamma. The necessary within-block singleton-row-
sum identities leave exactly the following seven set partitions:

    0|1|2|3;  01|2|3;  0|1|23;  02|13;
    03|12;    01|23;   0123.

The other eight partitions fail a singleton row-sum identity. Of the
seven displayed, four fail actual response invariance on the closed
block-constant cube. Let H(q) be the zero-discount displacement from
`quittingDiscountedDisplacement`. Exact row witnesses are

| partition | block-constant q | unequal rows of H(q) |
| --- | --- | --- |
| 01\|2\|3 | (0,0,1,0) | H0=B, H1=-B |
| 0\|1\|23 | (1,0,0,0) | H2=-B, H3=B |
| 02\|13 | (1,0,1,0) | H0=B, H2=-B |
| 03\|12 | (1,0,0,1) | H0=-B, H3=B |

They fail because B>0, independently of K. The mate-pair partition
01|23 IS response-invariant by the tau^2 automorphism, and the all-player
partition IS invariant by tau. Their quotient matrices are respectively
[[3,-2],[-2,3]] and [1], with positive determinants5 and1, positive
inverses and degree+1. The discrete quotient is Gamma itself. Therefore
EVERY actual quotient fails the currently favorable negative-determinant/
nonnegative-inverse or degree-not-one exits; no claim that all quotients
are absent is made.

The exact inspected quotient objects are
`QuittingResponseInvariantOnUnitCube` and
`quittingSingletonBlockRowSum_eq_of_responseInvariant`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`),
`quittingDiscountedDisplacement`
(`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`),
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`).
The last criterion explicitly requires determinant<0, not merely a
nonnegative inverse. The literal cyclic-child source inspected is
`GameTheory.CyclicChildJointPhase.RawTable`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`),
whose three-child singleton pattern has a positive directed three-cycle.

## 11. Other named raw-data coverage boundaries

These are bounded comparisons with literal criteria, not a claim of
exhaustive novelty or disjointness from unspecified qualitative IFT
neighborhoods. All label choices in each listed finite matching/base
criterion are included.

For the paired affine raw-region producer, each recipient here has TWO
singleton quitters below its own singleton. But
`RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`) permits
only the unique scheduled partner. Thus no schedule meets that raw region.
For the strict/weak crossed-matching sources, the favorite is forced by
the unique positive singleton difference, and its required participant
cap A<=1 fails. The positive-inverse crossed source also fails every
scheduled matching: its scheduled singleton must be below own, so the
mate pair is unscheduled and its A>1 violates one of the two unscheduled
participant caps. These are the actual `RawSource`, `WeakRawSource` and
`InverseRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.

The below-singleton raw family forces the favorite mate and row scale1
from the singleton rows. Its common scheduled premium<-1 would require
both participants of each cross scheduled pair to receive a negative
reward. But every cross pair here has one participant B>0. Hence
`GameTheory.PairedCycle.BelowSingleton.RawFamily`
(`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`)
fails every labeling. The two-pair join-cap criterion requires
r_i({i,mate(i)})>=r_i({mate(i)}) for every scheduled mate, plus outsider
insertion caps at the own singleton. Its joining-versus-partner condition
fails each matching:
favorite pairs have A<4, whereas every cross matching contains a
participant -B below its passive singleton0.

For the pair-mass raw bounds,
`hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean`) requires
every singleton's surplus average on either recipient pair to be
nonpositive. The singleton of a mate of a recipient yields an average
at least1, for EVERY recipient partition, violating that requirement.
`hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`)
requires the designated recipient's positive mate singleton surplus3
to be nonpositive; its sole favorable indicator is a PAIR coalition,
so no relabeling avoids this contradiction.

For premium criteria, both01 and23 are positive-premium traps since
A>1. Their union is the full core. Every player has the negative grand
premium -2, so there is no protected player, and all criteria requiring
nonnegative participant premiums fail. Empty/pair/triple greatest-core
criteria fail the core's size4. The weighted-floor criterion fails on
the grand coalition: every nonzero nonnegative weight vector gives a
strictly negative forced-Quit floor, since every participant grand
premium is -2. The boxed Nash-charge criterion requires every trap to
have size at least3, contradicted by01 and23. The mixed support-local
low/charge criterion also fails at either pair trap: the product root
giving both members hazard1/2 has each active Quit endpoint (1+A)/2>1,
and a pair trap cannot use the boxed-charge alternative. The same root
refutes `HasProductLowQuittingPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`).
Finally every triple contains a cross pair with one negative join gap
-B, excluding raw triple sources requiring six positive pair joins.

For the four-joint local raw class centered at favorite participant5,
the declared radius is at most1/2, incompatible with A<4. The unbounded
four-joint rectangle class fixes favorite participant coordinates5 and
9/2, likewise incompatible with A<4. The common-large-pair-participant
source requires positive common participant rewards on all pairs,
contradicted by the cross entries-B. These comparisons concern these
declared raw classes, not every strategy architecture or every unquantified
neighborhood.

## 12. Whole positive singleton-word exclusion at the exact singleton rows

Consider the named chronological singleton word0,2,1,3 with ANY four
proper positive hazards p_i, indexed in chronological word order, and
its corresponding relabelings preserving the paired singleton pattern.
Each owner's mate occurs two phases later. Write u_i=1-p_i in(0,1).
An active owner's value must be its singleton1. Its Continue endpoint
collects zero at the next nonmate, reward4 if its mate quits at the next
phase, zero at the remaining nonmate, and value1 upon return. Therefore
the four owner-indifference equations, cyclically indexed, are exactly

    E_i=u_i*(4-4*u_(i+1)+u_(i+1)*u_(i+2))-1=0.      (E8)

Put alpha=u0-u2 and beta=u1-u3. Subtract opposite equations:

    E0-E2=4*(1-u1)*alpha-u2*(4-u0)*beta,
    E1-E3=u3*(4-u1)*alpha+4*(1-u2)*beta.             (E9)

All four coefficients displayed in these two rows are strictly positive.
The determinant of this two-by-two system is

    16*(1-u1)*(1-u2)+u2*u3*(4-u0)*(4-u1)>0.

Hence alpha=beta=0. Put u0=u2=x and u1=u3=y. The remaining equation
difference is (4+x*y)*(x-y)=0, so x=y=u. The common equation factors as

    u^3-4*u^2+4*u-1=(u-1)*(u^2-3*u+1)=0.

Its unique root in(0,1) is u=(3-sqrt(5))/2. Thus EVERY all-positive
proper owner solution for this named singleton word has the golden
hazards p=(sqrt(5)-1)/2, not only one locally continued branch.

At a root of owner j, its inactive mate has policy value H=2+p and
forced-Quit value 1+p*(A-1). Since T=3+p and p^2=1-p, the required
inactive inequality is exactly A<=T. Our strict A>T violates it.
Consequently this entire named positive proper singleton-calendar
architecture fails on the raw family, including any locally selected
positive branch at these exact singleton rows. No unspecified IFT
radius needs to be chosen. This does NOT exclude arbitrary owner words,
longer calendars, zero/sure hazards or general singleton strategies.

## 13. Source/consumer scope and the remaining global problem

The source is entirely raw: for the exact allowed A,B,K, equations
(E1)--(E4) PRODUCE the legal hazards. Equations(E5)--(E7) then identify
actual policy values and all endpoint signs. Deleted-player contraction
proves unrestricted terminal Nash and the finite-horizon bounds. This
is the same mathematical consumer chain represented by
`quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
(`UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`), followed
by `quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
These declarations are semantic consumer anchors; the raw source here
is the explicit mathematical hazard construction(E1)--(E4), with its
own full endpoint and clock proof. The comparison does not assert a
strategy-class completeness theorem.

What is removed is the need to stay on one locally continued equilibrium
branch, in one small reward neighborhood, or at uniformly tiny hazards.
The branch switch covers this ENTIRE nonnegative passive-reward ray while
every persistent-base selection fails. Its high-K branch couples a large
owner clock to a small collision whose reward contribution remains order1.

What remains is genuinely global: select a compensation architecture from
arbitrary collision data after the existing matrix, child and base exits
have failed. Nothing here shows that an arbitrary table admits the exact
symmetries, passive transfers or owner equations used above. The concrete
next question is whether a global construction can choose WHERE to retain
macroscopic joint roots and WHERE to disperse clocks, rather than enlarging
this family in further parameter directions.
