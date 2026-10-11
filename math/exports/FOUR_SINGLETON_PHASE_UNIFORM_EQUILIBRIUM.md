# Four singleton phases below the solo floors

## Statement

Consider four players I={0,1,2,3}. At each live integer date they
independently choose Continue or Quit, using private randomization and the
public action history. The first nonempty quitting coalition S absorbs at
a specified finite reward vector r(S). The live and selecting dates pay
zero; every subsequent absorbed date pays r(S). Perpetual continuation
pays zero. A deviation is an unrestricted complete behavioral replacement,
including arbitrary deadlines, unbounded random stopping laws and Never.
All conclusions below concern expected payoffs; no public correlation is
introduced.

Fix the sixteen singleton entries

| S | r(S) |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |

Set

    q=(sqrt(5)-1)/2,  c=1-q=(3-sqrt(5))/2,
    H=(3+sqrt(5))/2,  T=(5+sqrt(5))/2.

Assume these twelve participant pair bounds:

| pair S | bounds |
| --- | --- |
| 01 | r_0(S)<=T, r_1(S)<=T |
| 23 | r_2(S)<=T, r_3(S)<=T |
| 02 | r_0(S)<=1, r_2(S)<=0 |
| 03 | r_0(S)<=0, r_3(S)<=1 |
| 12 | r_1(S)<=0, r_2(S)<=1 |
| 13 | r_1(S)<=1, r_3(S)<=0 |

There is NO lower bound on these twelve coordinates. The remaining32
coordinates are arbitrary finite numbers: twelve nonparticipant pair
entries, sixteen triple entries and four grand entries.

**Theorem1.** The repeated singleton schedule

    0 -> 2 -> 1 -> 3 -> 0,

with only the scheduled player quitting, independently with probability q,
is exact terminal Nash against all complete behavioral deviations at every
initial phase. Its actual terminal values in that chronological order are

    U0=(1,H,c,1), U2=(1,c,1,H),
    U1=(H,1,1,c), U3=(c,1,H,1).                         (1)

The same profile at each phase witnesses that phase's value as one fixed
original-game uniform-equilibrium payoff. The profile is chosen before
the accuracy and horizon. In particular no Fin4 counterexample can
satisfy these raw singleton identities and participant pair bounds, under
any relabeling.

**Theorem2.** Let r* be the complete strict table printed below. Partition
the sixty reward coordinates into P_rw, the sixteen singleton entries;
C_rw, the twelve participant pair entries; and F_rw, the remaining32
entries. There exists delta>0 such that every finite raw table satisfying

    |r_i(S)-r*_i(S)|<delta       for (S,i) in P_rw,
     r_i(S)<=r*_i(S)+delta       for (S,i) in C_rw         (2)

has an exact terminal Nash profile of the SAME repeated singleton word,
with four scheduled hazards in (1/2,3/4). Its actual initial-phase values
are fixed uniform-equilibrium payoffs, witnessed by the same selected
profile at every positive accuracy. No constraint beyond finiteness is
placed on F_rw. The radius is existential, not numerically produced.

These are ordinary mathematical statements. No new Lean verification or
unrestricted strategy-class completeness is asserted.

## Actual policy values and all twelve endpoint inequalities

At phase t let j_t be the scheduled player and R_t=r({j_t}). The repeated
independent coins absorb almost surely. Their actual values are

    U_t=[q R_t+c q R_(t+1)+c^2 q R_(t+2)
                          +c^3 q R_(t+3)]/(1-c^4),      (3)

with cyclic phase indices. Direct substitution gives(1), and

    U_t=q R_t+c U_(t+1).                               (4)

The scheduled player's own value equals one both before and after its
phase. Its pure Quit reward and pure Continue reward are therefore both
one. For an inactive player i at j's phase, the Continue endpoint is U_ti
and the Quit endpoint is

    c*r_i({i})+q*r_i({i,j})=c+q*r_i({i,j}).             (5)

The twelve inactive values in(1) are H,1,c. Solving(5)<=U_ti yields
respectively the exact thresholds T,1,0. Listing the scheduled owners
0,2,1,3 yields precisely the twelve printed bounds. This verifies every
endpoint, not only on-path owners. Some Continue values equal c<1, so an
all-phase solo-floor condition is deliberately NOT imposed.

Every possible absorption under the prescribed policy is a singleton.
Under ONE player's complete replacement, at most one other player is
scheduled at a date. Thus every possible terminal coalition is still a
singleton or a pair containing the replacing player. This proves, rather
than assumes, that the32 F_rw entries cannot enter any policy value or
unilateral response payoff. They remain arbitrary finite game data.

## Unrestricted behaviors and uniform finite horizons

Fix any replacing player i and any initial phase. Removing i leaves
three scheduled independent opponent coins in every four consecutive
dates. Opponent survival over n dates is bounded by

    rho^floor(n/4),  rho=c^3<1.                         (6)

The bound is uniform over i's complete replacement. It follows either
by pre-sampling independent stopping laws or directly on the unique live
public history. A player's private randomization and arbitrary memory do
not change its opponents' three scheduled hazards.

At every live history the endpoint inequalities bound every replacing
mixture of Quit and Continue by U_ti. Iterating the Bellman inequality
through n dates leaves only a bounded continuation remainder times
opponent survival(6), which tends to zero. Therefore every complete
behavioral replacement earns terminal payoff at most U_ti. The policy
recursion(4) identifies the prescribed payoff as U_ti. Pure Never and
arbitrarily late deadlines are included in the same comparison.

For a quantitative finite-horizon statement choose

    M>=max(1,max_(S,i)|r_i(S)|),
    C=1+4/(1-rho).

The sum of opponent live probabilities is at most4/(1-rho). Actual
selection is no later than the first opponent stop, even after the
replacement. The additional one in C covers the selecting-date indexing.
For every replacement, its expected N-date average differs from its
terminal payoff by at most M*C/N: pathwise only dates through selection
can differ, and their total discrepancy is at most M per date. The
prescribed policy obeys the same bound. Its delivery error is at most
M*C/N and full behavioral horizon regret at most2*M*C/N. This proves
Theorem1 with one profile and one fixed target before every accuracy.

For Theorem2 all hazards are in(1/2,3/4), so one can use the uniform
deleted-cycle bound rho=1/8 and C=39/7. The reward bound M may depend on
the full original finite table, including F_rw. No uniform reward bound
over the arbitrary-coordinate family is required.

## Exact local producer and upper-only transfer

Write p=(p0,p1,p2,p3) in CHRONOLOGICAL order(0,2,1,3), not player order.
For arbitrary singleton data write s_i=r_i({i}). The cleared owner field
F_t is the sum over the other three future owners j of
r_i({j})-s_i times j's first-stop probability, starting immediately
after owner i=j_t's phase and ending just before i's next phase. Explicitly,

    F_t(r,p)=sum_(k=1)^3 p_(t+k)*prod_(l=1)^(k-1)(1-p_(t+l))
                              *[r_(j_t)({j_(t+k)})-s_(j_t)].

For the printed singleton center this is

    F_t(p)=-p_(t+1)+3*p_(t+2)*(1-p_(t+1))
            -p_(t+3)*(1-p_(t+1))*(1-p_(t+2)).           (7)

These fields are polynomials in p and the sixteen singleton entries.
Let P be the product of the four Continue probabilities. Actual periodic
policy evaluation gives the exact identity

    (1-P)*(U_(t+1),i-s_i)=F_t,  i=j_t.                 (8)

To check(8), expose the next three other-owner coins and then i's own
coin. The own stopping branch has reward s_i and the all-Continue branch
returns to the same post-owner phase. After subtracting s_i the three
other singleton terms are exactly F_t. Thus F=0 is EXACT active
indifference of the actual policy values, not an equation on an arbitrary
prescribed continuation.

At p=q*1 the field is q*(1-q-q^2)=0. Its Jacobian is the circulant matrix
with diagonal zero and chronological offsets+1,+2,+3 equal to

    A=-2-q,  B=2-q,  D=3*q-2.

Its eigenvalues are q-2, 3*(2-q), and -(2-q)+/-4*q*sqrt(-1). Hence

    det J=-3*(2-q)^2*((2-q)^2+16*q^2)
         =(-2205+945*sqrt(5))/2<0.                     (9)

The implicit-function theorem selects hazards p(r) continuously from
the sixteen nearby singleton entries. Shrink the singleton neighborhood
until all hazards lie in(1/2,3/4). At the strict table below all twelve
inactive gaps are positive: the four mate cap margins are
(sqrt(5)-2)/2 and the eight other cap margins are1/2, with actual endpoint
gaps q times these quantities. Continuity preserves the inequalities
when the twelve participant pair entries are at most their strict table
values plus one sufficiently small delta. There is no lower-bound
requirement: decreasing such an entry only lowers its Quit endpoint and
does not change actual policy evaluation or selected hazards. The32
remaining entries are absent from every relevant expression. Equations
(8), all inactive inequalities, and the deleted contraction then prove
Theorem2 against the same unrestricted deviations as above.

## Fixed strict completion and bounded source comparisons

The strict table used in Theorem2 is

| S | r*(S) |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (7/2,7/2,0,0) |
| 02 | (1/2,0,-1/2,0) |
| 03 | (-1/2,0,0,1/2) |
| 12 | (0,-1/2,1/2,0) |
| 13 | (0,1/2,0,-1/2) |
| 23 | (0,0,7/2,7/2) |
| 012 | (-1,-1,-1,0) |
| 013 | (-1,-1,0,-1) |
| 023 | (-1,0,-1,-1) |
| 123 | (0,-1,-1,-1) |
| 0123 | (-2,-2,-2,-2) |

The following are bounded comparisons to named raw sources. They do NOT
assert stationary nonexistence, necessity of this calendar, disjointness
from unquantified local neighborhoods, or failure of arbitrary supplied
strategic verifiers.

### Entire sure-owner and persistent-base/free selections

Let m exchange0<->1 and2<->3, and let kappa be the four-cycle
0->3->1->2->0. Fix ANY sure owner j. In the full induced binary game
of its three nonowners, both m(j) and the other noncollider have
Quit-minus-Continue -1/2 if no other nonowner quits, -1 if exactly one
does, and -2 if both do. These are strictly negative against every mixed
support and every boundary law. Both players therefore Continue surely
at EVERY induced Nash point. The remaining player kappa(j) then has
gain+1/2 and Quits surely. The ENTIRE induced-Nash set is this single
point. Owner j earns-1/2 by Quit and0 by Continue. Since kappa(j) quits
surely, all punishment-floor terms have zero coefficient. The actual
owner leave gain is+1/2 independently of the punishment value.

Thus there is no Nash root with ANY sure owner. A partial free-player
Nash point plus outsider no-join signs extends to the full induced game
and is covered by this classification. A larger persistent base, free
Nash signs, base leave signs and outsider no-join signs would constitute
a full zero-tail Nash root with a sure owner, also impossible. This
screens all base/free subsets and mixed supports, not selected pure
witnesses.

### Every proper child, all five withdrawal kinds

For any nonempty proper child A choose j in A with e=kappa(j) outside A;
a directed four-cycle has no nonempty proper forward-closed subset.
At child coalition{j}, e's joining gain is+1/2. Every donor advance
coefficient is zero(j itself) or-1/2(any other child donor). Every
withdrawal coefficient is nonpositive: nonmembers of{j} have gain zero;
for j itself the gain is its restart floor minus own singleton1.
Patient floor<=max(1,0)=1, deadline/cancellation floor<=0, evaluated
security floor<=0, and terminal-security floor<=1 by the security LP's
literal singleton row and zero-floor bound. This covers even a
one-player child. Every nonnegative weighted advance/withdrawal sum is
therefore<=0 and cannot dominate the parent's+1/2 join row. All five
`WithdrawalFutureJoinKind`s and the advance-only capped-clock certificate
fail for every proper child and every allowed choice of weights.

### Whole balanced singleton class and signed-cycle sources

The singleton comparison matrix is

    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0].

No balanced singleton certificate of ANY finite length or owner word
exists. Suppose its values u_ti>=1, active owner value1, singleton arc
and opponent divergence hold, with hazards in[0,1). At a positive owner-j
phase, its next own value remains1, whereas each of its two nonmates'
next values is u_ti/(1-a)>1. Follow to the first different positive
owner, which opponent divergence guarantees. Until then only j moves;
its own coordinate remains1 and both nonmate coordinates remain>1.
The first different owner must therefore be m(j). But its positive
hazard a, with r_j({m(j)})=4, forces next j coordinate
(1-4a)/(1-a)<1, a contradiction. The bounds-enriched certificate has
the same relevant fields. This obstruction is not itself claimed new;
the producer escapes it by using actual below-solo Continue values with
literal collision caps.

The matrix's positive off-diagonal graph consists of two disjoint
transpositions. A `SignedFourCycleSingletonData` input, under any
relabeling, would require a positive predecessor Hamiltonian four-cycle,
which this graph lacks. Both signed spectral branches fail that same
input. The generic four-phase singleton certificate based on these
signed data and balanced values does not apply either.

The strict positive-singleton-column source also fails for every owner:
each singleton column has two outsiders' rewards zero, strictly below
their own singleton one.

### Actual response quotients and product-low premiums

The complete table IS equivariant under the transitive permutation
(0 2 1 3). Symmetry is not declared absent. The following exact check
shows why it nevertheless does not enter the current favorable
response-quotient source.

For a block map, actual response invariance on the block-constant unit
cube requires equality of literal stationary displacement rows within
each block. Its derivative at zero forces equality of Gamma's block row
sums. Enumerating the fifteen partitions using the displayed Gamma
leaves only

    discrete; 01|2|3; 0|1|23; 02|13; 03|12; 01|23; 0123.

Write H_i=(1-C_-i)*Q_i-E_-i, where C_-i is opponents' Continue mass,
Q_i is the pure-Quit expected reward and E_-i the unnormalized reward
from nonempty opponent-only quitting coalitions. These are the exact
zero-discount `quittingDiscountedDisplacement` rows. Four potentially
favorable partitions fail the actual identity at these block-constant
hazards, listed in PLAYER order:

| Partition | Hazards | Unequal rows |
| --- | --- | --- |
| 01\|2\|3 | (0,0,1,0) | H0=1/2, H1=-1/2 |
| 0\|1\|23 | (1,0,0,0) | H2=-1/2, H3=1/2 |
| 02\|13 | (1,0,1,0) | H0=1/2, H2=-1/2 |
| 03\|12 | (1,0,0,1) | H0=-1/2, H3=1/2 |

The mate partition01|23 is invariant under the subgroup generated by
(0 1)(2 3); the all-player block is invariant under the transitive
four-cycle. Their actual quotient singleton matrices are respectively

    [[3,-2],[-2,3]] and [1].

Both are P-matrices of degree+1: their nonempty principal minors are
3,3,5 and1. The mate quotient inverse is entrywise POSITIVE,
(1/5)*[[3,2],[2,3]], as is the all-block inverse[1]. The implemented
nonnegative-inverse exit ALSO requires NEGATIVE determinant (`hdet` in
`FinFourResponseQuotientCriterion.lean`); it is the positive determinant
and degree+1, not failure of inverse positivity, that blocks these exits.
They likewise supply no degree-different-from-one exit. The discrete quotient is the
original known degree-one paired matrix. Thus EVERY actual response
partition fails the stated favorable quotient exits, even though
nontrivial invariant quotients genuinely exist. The claim is NOT that
all block quotients are forbidden.

The product-low premium condition fails at hazards(1/2,1/2,0,0): both
active players' pure-Quit payoffs are(1+7/2)/2=9/4>own1. Thus there is
an absorbing product root with no active low-premium coordinate.

### Named pair and mass-bound raw sources

`PairedCycle.RawRegion.eq_partner_of_singleton_lt` allows only one
below-own singleton opponent per recipient, while every recipient here
has two. No pair schedule satisfies it. In the strict/weak
`CrossedMatching.RawSource` the unique singleton favorite must be m(j),
whose joining7/2 violates the passive cap<=own1. In its inverse source
the scheduled singleton must be below own, hence cannot be the mate;
the mate is again capped by1. The pure scheduled-pair cap source is
already covered by the sure-owner exclusion.

`BelowSingleton.RawFamily` forces a cross scheduled pairing. Every cross
pair here contains a participant with joining+1/2 against passive
singleton0, contrary to its strictly negative scheduled premium. The
favorite pairing fails its scheduled singleton requirement.

The complementary-pair join-cap source requires every scheduled pair
participant reward at least its partner's passive singleton. Mate
pairing fails7/2>=4; each cross pairing has a participant failing
-1/2>=0. This covers all three pair partitions.

The two-pair average-surplus mass-bound source requires every designated
pair's average singleton surplus nonpositive. At the mate singleton of
one of its players the pair's total reward is at least4 against total
own2, so surplus>=1. The separate-cross determinant source has no
positive singleton row for a designated recipient, whereas its mate
singleton surplus is3. Both fail every relabeling.

The four-joint-phase local raw source with singleton center as above
requires a favorite-pair participant reward within delta<=1/2 of5;
our value7/2 differs by3/2. The four-joint-phase rectangle source fixes
that favorite participant5 and another9/2. These stated raw regions
therefore do not contain this table under any relabeling, since the
singleton preferences uniquely identify the mate pairing. No assertion
is made about the capabilities of their underlying generic verifiers.

## Source handoff

The strategy and terminal semantics match the actual periodic consumers
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`: actual
policy recursion, zero root-Nash error, and deleted opponent contraction.
The source-free full-behavior comparison is
`quittingSubBellmanValue_le_superSolution_of_survival_zero` in
`UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`.
The exact-terminal same-profile uniform consumer is
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
These are conditional checked interfaces; the new golden raw producer
and its IFT neighborhood have not been implemented in Lean here.

The bounded comparisons use actual definitions in:

- `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` and
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
  `PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
  `DeadlineWithdrawalSecurityLP.lean`,
  `DeadlineWithdrawalSecurityMixedPointwise.lean`,
  `DeadlineWithdrawalRestartPointwiseCore.lean` and
  `CappedClockPointwiseDomination.lean` in that same quiet-extension directory;
- `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`,
  `FourPhaseSingletonCertificate.lean`, `SignedFourCycleRewardAdapter.lean`,
  `SignedFourCycleLargerRewardAdapter.lean`, `PairedCycleSchedule.lean`,
  `CrossedMatchingPhaseSource.lean` and `BelowSingletonJointPhaseSource.lean`;
- `UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean` and
  `TwoPairCrossMassRewardExclusion.lean`;
- `QuittingResponseInvariantOnUnitCube` and
  `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
  `responseInvariant_of_reward_subgroup_automorphisms` in
  `ResponseInvariantQuotientPlayerOrbits.lean` in that same directory,
  and the raw quotient consumers in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`;
- `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`;
- `RationalQuittingStrictSingletonColumn` in
  `UniformEquilibrium/Quitting/Paths/RationalPositiveSingletonColumnExit.lean`.

The hard paired singleton matrix has existing R0/Q/degree-one facts in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`
and `FourPlayerPairedSingletonResidualHard.lean` in that same directory.
Those matrix facts do not supply arbitrary-completion equilibria. The
current statements are a particular raw-table producer, not a new
matrix-only exit or an arbitrary-Fin4 selection theorem.
