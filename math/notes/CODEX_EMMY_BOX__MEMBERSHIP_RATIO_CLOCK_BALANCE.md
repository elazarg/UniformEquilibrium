# Membership ratios and balanced private clocks

Status: ordinary mathematics, not Lean checked. Sections 1–3 and 6 passed
one bounded independent adversarial review by CODEX_TURING_BOX, recorded in
`feedback/CODEX_EMMY_BOX__MEMBERSHIP_RATIO_CLOCK_BALANCE__BY_CODEX_TURING_BOX.md`
against source SHA256
`4ac5d975aedf308712260acad7d1880f611d7f65285f20f834426997b0439b55`.
Section 7's additional named-source comparisons were not reviewed.
This gives actual full-response stationary equilibria from a raw reward
identity, with no strategic witness, inverse, degree or large-scale input.
New reward-class coverage is NOT established. The first symmetric four-player
test is contained in the broader induced-Nash/punishment-tail source, as
shown below. A later asymmetric rational completion excludes the ENTIRE
sure-owner correspondence, with that whole-correspondence exclusion included
in the bounded review. The additional named-source comparisons await
independent checking. The accompanying search
is only a numerical diagnostic, not an input to the exact proof.

## 1. Self-contained question and answer

Let I be finite, n=|I|>=2. The first nonempty quitting coalition S absorbs
at r(S); live dates and perpetual continuation pay0. Players use independent
private randomness. Deviations replace a player's complete behavioral law,
including every finite deadline and Never. Payoffs are expected.

Choose arbitrary real s_i and arbitrary real g_i(A) for every NONEMPTY
A subset I\{i}; put g_i(empty)=0. Choose M_i>1. Specify EVERY nonempty
recipient coordinate by

    r_i({i})=s_i,
    r_i(A)=s_i+g_i(A)                  if i notin A, A nonempty,
    r_i(A union{i})=s_i+M_i*g_i(A)     if A nonempty, i notin A.     (1)

Each recipient's array is independent of the others. No consistency beyond
(1) is imposed. Put

    a_i=1-1/M_i,
    k=(product_i a_i)^(1/(n-1)).

Assume the weak rate balance

    k<=min_i a_i.                                             (2)

Then (1) has an EXACT stationary terminal Nash equilibrium against all
complete behavioral deviations, with continuation probabilities

    p_i=k/a_i,       q_i=1-p_i.                               (3)

At least two hazards q_i are positive, every q_i<1, and the SAME profile
is a uniform equilibrium at its actual terminal payoff. If (2) is strict,
all hazards are positive. In particular a common M>1 always satisfies
strict balance and gives

    q_i=1-(1-1/M)^(1/(n-1)).                                  (4)

This is a producer for the literal reward identity (1), not a claim that
an arbitrary table can be transformed into that identity preserving agency.

## 2. Exact endpoint cancellation and complete response caps

The product of p_i is k: indeed k^(n-1)=product_i a_i. Hence the opponent
continuation probability is alpha_i=(product_j p_j)/p_i=a_i. If only q_j
were positive, alpha_j would be1, contradicting a_j<1. This proves the
at-least-two assertion, including equality cases in (2).

Draw the product opponent coalition A at one date and let
gbar_i=E[g_i(A)]. The immediate Quit endpoint and opponent-stopping term are

    Q_i=s_i+M_i*gbar_i,
    B_i=s_i*(1-alpha_i)+gbar_i.

Consequently the SELF-CONSISTENT stationary endpoint field is

    H_i=(1-alpha_i)*Q_i-B_i
       =[M_i*(1-alpha_i)-1]*gbar_i=0.                         (5)

Since alpha_i<1, set V_i=B_i/(1-alpha_i)=Q_i. Every prescribed player
earns V_i. A pure finite deadline h earns exactly

    V_i+alpha_i^h*(Q_i-V_i)=V_i,

and Never earns V_i. On the unique live history every complete private
behavioral replacement is a mixture of such deadlines and Never independent
of opponents, so its payoff is also V_i. No reward sign assumption is used.

For the fixed table/profile, opponents have a geometric stopping bound
uniform over the entire deviation class. If C bounds all reward magnitudes,
the terminal/finite-average discrepancy is at most
2C/[N*(1-alpha_i)]. Thus one fixed terminal payoff is a uniform-equilibrium
target; the profile itself need not change with accuracy.

The full-cap consumer agrees with the inspected declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

## 3. Boundaries and a raw open-neighborhood extension

Balance is necessary for THIS simultaneous coefficient-cancellation
operation: the equations product_(j!=i)p_j=a_i force (3). For example
a=(1/100,1/2,1/2) has k=1/20>a_0, so p_0=5 is illegal. This is not an
equilibrium nonexistence example. Weak balance is genuinely allowed; zero
hazards do not invalidate (5) or the full cap calculation.

At a strict-balance center, the actual Jacobian of H at (3) is

    dH_i/dq_i=0,
    dH_i/dq_j=M_i*alpha_i*gbar_i/p_j    for j!=i.

The derivative of gbar drops out because its multiplier in (5) is0.
Writing d_i=M_i*alpha_i*gbar_i gives

    det(DH)=(-1)^(n-1)*(n-1)*(product_i d_i)/(product_i p_i).    (6)

If every gbar_i!=0, the ordinary implicit-function theorem therefore
gives an open neighborhood in ALL raw reward coordinates with an interior
stationary exact terminal Nash equilibrium and the same-profile uniform
conclusion. No strategic certificate is supplied in this neighborhood:
the actual H=0 root is selected by the theorem. This local extension has
not been checked for independent class novelty.

## 4. Exact early whole-source kill of a symmetric four-player test

Take mate pairs01 and23, own rewards1, singleton g_i({mate(i)})=3 and
g_i({j})=-1 for the other two opponents. Set M_i=2. At an opponent pair
equal to the OTHER mate pair put g_i=A>0; at every other opponent pair
and at the full opponent triple put g_i=-1.

All absent rewards are nonnegative, so Never guarantees every player0.
An opposite sure quitter also caps the recipient by0, so its punishment
value is0. A fixed owner0 quitting surely leaves the following exact
three-player finite best-response signs:

    gbar_1=4*(1-q_2)*(1-q_3)-1,
    gbar_2=(A+1)*q_1*(1-q_3)-1,
    gbar_3=(A+1)*q_1*(1-q_2)-1.                             (7)

For 0<A<=1 there is the induced Nash point

    q_1=1, q_2=q_3=A/(A+1).

The two sure mate players each have gbar=4/(A+1)^2-1>=0, so the resulting
profile is already an exact sure-base equilibrium.

For A>1 there is the induced all-mixed Nash point

    q_1=2/(A+1), q_2=q_3=1/2.

For owner0, alpha=(1-q_1)/4 and gbar_0=(A-2)*alpha. Its immediate Quit
minus opponent-stopping term is

    Q_0-B_0=alpha+gbar_0=(A-1)*alpha>0.                     (8)

Together with punishment value0, this meets the broader induced-Nash
punishment-tail owner comparison. Thus even when the sure owner's
stationary Never comparison fails (1<A<2), the already implemented broader
source covers the table. Testing only a stationary sure-owner cap would
incorrectly report a separation.

The other two induced Nash points have one outsider at3/4, the other0,
and q_1=1/(A+1). There Q_0-B_0=-A/[2(A+1)]<0, so bad and good selected
components coexist. One bad induced equilibrium cannot exclude the whole
source. The symmetric family is retired as a separating fixture.

## 5. Narrow source comparison and current question

Read `IsAffineQuittingMembershipGain`,
`IsComponentwisePositiveSymmetrizable`, and
`quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.
The gain in (1) on NONEMPTY backgrounds is (M_i-1)*g_i(A), but at the
empty background it is s_i. Arbitrary g does not imply the source's affine
identity on EVERY background, let alone positive SCC symmetrizability.
No exhaustive accepted-source comparison is claimed from this observation.

`CODEX_EMMY_BOX__MEMBERSHIP_RATIO_SEARCH.py` enumerates generic three-player
Boolean supports on owner faces for diagnostic asymmetric completions.
It skips degenerate continua and uses floating-point algebra; its output
is not a proof of whole-correspondence exclusion.

Concrete next question: does some four-player completion of (1), with
degree-one singleton data and strict balance, avoid the ENTIRE
sure-owner/punishment source, or does the membership-ratio identity itself
force another already consumed source? A successful stationary formula
alone does not settle this coverage question.

## 6. An asymmetric exact whole-sure-owner separation

The following FOUR-player rational table uses s_i=1 and M_i=2 throughout.
Singleton g is3 at the mate, -1 at both other opponents, with mates01,23.
The remaining opponent-background data are

    recipient0: g(12)=3/10, g(13)=-1, g(23)=16, g(123)=4;
    recipient1: g(02)=16, g(03)=4, g(23)=8, g(023)=3/10;
    recipient2: g(01)=1, g(03)=-1, g(13)=-1, g(013)=-1;
    recipient3: g(01)=16, g(02)=8, g(12)=3/10, g(012)=3/10.   (9)

Equations(1) specify every raw reward, including the grand row
(9,8/5,-1,8/5). Every absent reward is nonnegative. In particular an owner
using Never earns at least0 against EVERY opponent continuation, not merely
against a prescribed punishment family.

The produced all-interior stationary equilibrium has
q_i=1-2^(-1/3). Nevertheless there is NO exact terminal Nash profile having
ANY player quit surely at date0. This excludes all sure-base and all
sure-owner induced-Nash/punishment-tail selections for this literal table.
It does not yet exclude every other named raw producer.

### 6.1 Why a complete owner-face audit suffices

If owner i quits surely, the other three players' initial independent
actions must be an ordinary three-player binary Nash equilibrium, with
their own join-minus-Continue signs equal to g_j({i} union A). Every full
replacement reduces to its first action because a sure opponent absorbs
at that date. For ANY such owner-face Nash point write

    alpha=product_(j!=i)(1-q_j),
    gbar=E[g_i(A)],
    Q_i-B_i=alpha+gbar.                                     (10)

If(10)<0, the owner's immediate Quit earns Q_i whereas the complete Never
deviation earns at least B_i: the initial nonempty opponent coalition pays
the stopping term B_i, and after an empty coalition all subsequent absent
rewards are nonnegative. Thus the owner strictly benefits from Never
regardless of its opponents' future strategies. No supplied continuation,
stationary-tail restriction, or punishment lower-bound hypothesis is used.

### 6.2 Owner0: a unique pure opponent face

Player1 has positive gain for all four backgrounds containing0, namely
3,16,4,3/10. Hence q_1=1. Player3 then has positive gain16 or3/10, so
q_3=1. Player2's gain is now-1, so q_2=0. The face Nash is unique:

    (q_1,q_2,q_3)=(1,0,1).

Owner0 has alpha=0 and gbar=g_0(13)=-1. Thus Q_0-B_0=-1.

### 6.3 Owner1: exclude the third support before solving the cycle

For the other players0,2,3, the exact gains are

    f_0=3-(27/10)q_2-4q_3+(77/10)q_2*q_3,
    f_2=-1+2q_0*(1-q_3),
    f_3=-1+17q_0+(13/10)q_2-17q_0*q_2.

Suppose q_2>0. Nash requires f_2>=0, hence q_0>=1/2 and q_3<=1/2.
For every q_3 in[0,1/2], both endpoint values of f_0 as a function of q_2
are positive: 3-4q_3>=1 and3/10+(37/10)q_3>=3/10. Therefore q_0=1.
Now f_3=16-(157/10)q_2>=3/10>0 forces q_3=1, a contradiction. So q_2=0.

The remaining two-player response cycle has f_0=3-4q_3 and f_3=-1+17q_0.
It has no pure equilibrium and its unique mixed equilibrium is

    (q_0,q_2,q_3)=(1/17,0,3/4).

At this point f_2=-33/34<0, so the removed player really prefers Continue.
Here alpha=4/17 and gbar=-33/68, so Q_1-B_1=-1/4.

### 6.4 Owner2: a unique pure opponent face

Player3's four gains on backgrounds containing2 are3,8,3/10,3/10, all
positive, so q_3=1. Then player0's gain is16 or4, forcing q_0=1.
Player1's remaining gain is3/10>0, forcing q_1=1. The unique face point
has all three opponents quit surely. Owner2 has alpha=0 and
gbar=g_2(013)=-1, so Q_2-B_2=-1.

### 6.5 Owner3: the potentially missing all-mixed support is impossible

For players0,1,2 the exact gains are

    f_0=-1+17q_2-12q_1*q_2,
    f_1=-1+5q_0+9q_2-(127/10)q_0*q_2,
    f_2=-1+4*(1-q_0)*(1-q_1).

Suppose q_0>0. Then f_0>=0 implies q_2>0. If q_2=1, f_1=8-(77/10)q_0
is positive, so q_1=1; then f_2=-1 contradicts q_2=1. Thus0<q_2<1,
so f_2=0. This gives (1-q_0)(1-q_1)=1/4, in particular q_0<=3/4 and
q_1<=3/4. Hence q_0 is also mixed and f_0=0. Writing x=q_0 gives

    q_1=1-1/[4*(1-x)],
    q_2=(1-x)/(8-5x),
    f_1=[1+(233/10)x-(123/10)x^2]/(8-5x)>0
                  for 0<=x<=3/4.

Therefore q_1=1, contradicting q_1<=3/4. We conclude q_0=0.
The remaining response cycle is f_1=-1+9q_2, f_2=3-4q_1, so the unique
face Nash point is

    (q_0,q_1,q_2)=(0,3/4,1/9).

At this point f_0=-1/9<0, so the removed player really prefers Continue.
Owner3 has alpha=2/9 and gbar=-67/120, giving
Q_3-B_3=-121/360. This completes the exact whole-face proof, including
the all-mixed support; no numerical root census is an input.

### 6.6 The open-neighborhood mechanism is nondegenerate here

Put q=1-2^(-1/3), p=1-q. At the explicit symmetric stationary profile,
the four background expectations from(9) are respectively

    q*p^2+(153/10)*q^2*p+4*q^3,
    q*p^2+28*q^2*p+(3/10)*q^3,
    q*p^2-q^2*p-q^3,
    q*p^2+(243/10)*q^2*p+(3/10)*q^3.

All are strictly positive; the third equals q*(p^2-q)>0 since q<1/4
and p>3/4.
Thus(6) is nonzero. Both the actual interior root and the strict
whole-owner-face obstruction persist locally: any sequence of nearby
owner-face Nash points has a Nash cluster point on the compact cube,
and each center owner-face point is unique with the strict gaps above.
Absent rewards at the center can equal0, so persistence of the stronger
'Never is everywhere nonnegative' argument requires the nonnegative
absent cone, or a separate quantitative continuation/punishment bound.
No unrestricted open sure-owner exclusion is asserted here from that
boundary condition alone.

### 6.7 The same whole-owner obstruction is unbounded in M

Keep the same s and ALL g in(9), but let the common membership multiplier
be ANY M>=2. The opponent face gains are (M-1) times the gains already
listed, so the FOUR UNIQUE face Nash points are unchanged. Their owner
Quit-minus-stopping differences become

    owner0: -(M-1),
    owner1: 4/17-(M-1)*33/68,
    owner2: -(M-1),
    owner3: 2/9-(M-1)*67/120.                               (11)

All remain strictly negative. Absent rewards remain nonnegative and fixed.
Thus NO member of this unbounded family has an exact terminal Nash
profile with an initial sure quitter, while EVERY member has the explicit
all-interior stationary Nash in(4). This is not another shrinking-clock
calibration of one bad selector: it excludes the ENTIRE initial-sure-owner
correspondence, for every M>=2.

## 7. Bounded actual-source comparisons for the asymmetric family

These are ordinary calculations from the displayed table, not an exhaustive
producer census or a claim about unknown implicit-function neighborhood
radii. Relabelings and all choices within the stated predicates are retained.

### 7.1 Matrix exits do not explain this family's existence

The singleton matrix is exactly

    Gamma=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0].

This is the tracked `matrix` in
`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseMatrix.lean`.
Its declarations `matrix_isR0`, `matrix_r0Degree_eq_one`,
`matrix_positive_inverse` and `matrix_standardQ` were inspected. Every
player has a negative distinct-row witness, so the normal core is all four.
The matrix is R0 of degree1 and standard Q, with strictly positive inverse.
Every harmful pair has matrix[0,-1;-1,0], so full projective-Q-bar fails.
No nonunit-degree, homogeneous or ordinary-nonQ exit follows from these
singletons. Every deleted three-player inverse has a negative diagonal
entry (the isolated mate's entry is-3/2); hence the nonnegative-child-inverse
prerequisite of the selective passive-row source also fails for all choices.

### 7.2 One literal mate trap defeats whole weighted/boxed return choices

The mate pair A=01 is a premium trap: both participants receive1+3M>1.
For its nonempty proper background{0}, player1's inserted premium is3M
and its leave gain is3(M-1)>0; interchange0,1 for the other background.
Consequently:

* The support-local upper-average predicate of
  `exports/MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md` forces
  w_1=0 at{0} and w_0=0 at{1}, so no nonzero nonnegative weight works.
  Its alternative boxed certificate requires cardinality at least3 and
  cannot handle this two-player trap.
* `QuittingTrapChargeCoefficients` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
  also requires cardinality at least3; the boxed producer fails directly.
* `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
  requires positive weights on BOTH trap members and a nonpositive proper
  leave sum. The single positive term3(M-1)w_1 already contradicts it.
  Neither zero weights outside A nor different weights at other traps help.
* `HasSupportSpecificQuittingLeavers` in
  `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`
  has no weak or strict leaver at this trap, regardless of protected set.

Every player also has a harmful participant pair1-M<1 and a favorite
participant pair1+3M>1, so neither global direction of participant dominance
holds. The maximal protected participant set is empty. The exact affine
gain identity of Section5 fails already for recipient0 on background12:
its singleton-determined affine prediction is2(M-1)-1, whereas its actual
gain is(3/10)(M-1). Equality would require M=27/17<2.

### 7.3 Two-pair, triple-singleton and crossed guards

For the mate partition01|23, the opposite-pair joining cap in
`exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md` fails at recipient0:
r_0(023)=1+16M>1. For either other pair partition, its scheduled pair is
harmful and its joining gap is1-M-0=1-M<0, violating the first comparison.
Thus EVERY pair partition fails that raw producer.

Every three-player set contains a harmful ordered pair whose joining gap
is1-M<0. Hence the six positive pair-joining gaps required by
`exports/TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md` fail for
EVERY triple choice.

The `RawSource` and `WeakRawSource` definitions in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean` were
reopened. The singleton favorite is forced to be the literal mate, but
its participant cap requires1+3M<=1, impossible. Independently every
scheduled harmful joining comparison asks0<=1-M, also impossible. This
defeats every relabeling. For each ordered guarded pair (i,p), one of i's
two harmful labels j differs from p; the sole-sure outsider j yields
actual joining residual (M-1)*Gamma_ij=-(M-1)<0. Thus no lower guard valid
against every outsider root can hold for that pair.

### 7.4 Every proper child has an exact unsafe child equilibrium

If a nonempty proper child is not a complete mate pair, it contains a
player d whose mate lies outside. The child solo d profile is exact full
terminal Nash: all other child members have harmful singleton joining
gain1-M<0, while d receives1 rather than Never0. Its absent mate strictly
gains3(M-1)>0 by joining d.

For child01, the exact sure-pair child equilibrium has outside recipients2,3
joining gains M-1 and16(M-1), respectively. For child23 the corresponding
outside gains are16(M-1) and8(M-1). These cover ALL nonempty proper children,
including every three-player set, not only one convenient child selector.
Any raw quiet-lift condition which would preserve EVERY exact child Nash
therefore fails, including the universal withdrawal/future-join kinds.
This implication uses actual unsafe child equilibria, not an assumed
equivalence of the broader withdrawal rows with advancing-only rows.
The inspected complete-debt consumer is
`quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/PureAbsorbingChildDebtObstruction.lean`.
The all-kind source comparison appears explicitly in
`exists_outside_no_quiet_certificate` in
`UniformEquilibrium/Quitting/Examples/NegativePremiumCyclicChildFixtureChildren.lean`:
the same implication uses only exact child debts0, joint Never0 and a
strictly positive actual outside gain, all supplied above.

### 7.5 The recent signed-pair account is genuinely unavailable

The incoming containing-pair coefficient matrix of this M-ray is C=Gamma.
For z=(1,1,0,0), its quadratic field P_C has values(3,3,-4,-4).
For z=(0,0,1,1), the values are(-4,-4,3,3). A nonnegative weight w making
w*P_C strictly copositive would need BOTH

    3(w_0+w_1)>4(w_2+w_3),
    3(w_2+w_3)>4(w_0+w_1),

which is impossible for any nonzero w. Thus the independently reviewed
signed-pair coercivity theorem does not subsume this raw balance mechanism.
The original positive-cycle incoming-pair theorem also lacks its bounded
other-containing-pair premise: EVERY harmful participant pair grows as-M.

The earlier selected signed-inverse-column pole theorems have a different
scaling source: a containing selected pole at a positive inverse column
must have positive leading sign, and all unselected coordinates must be
bounded or sufficiently small on their specified scale. This ratio ray has
large NEGATIVE containing pairs in every recipient column. The displayed
ray is not an immediate specialization of that bounded-completion class.
This is a family/source comparison, NOT a proof that an isolated fixed
member lies outside every unknown quantitative threshold or IFT radius.

The exact singleton-phase source also cannot directly supply its golden
word equilibrium: a favorite participant reward1+3M>=7 exceeds its favorite
cap T=(5+sqrt(5))/2. The complete golden owner-word uniqueness proof is
recorded in the earlier independently reviewed source packets; it is not
reproved here. No exclusion of every alternative singleton word is claimed.

### 7.6 The full-response quotient has no nontrivial blocks

The actual predicate `QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
requires equality of the zero-discount stationary displacement coordinates
within every block at EVERY block-constant hazard vector in the cube.
At the all-sure vector, those displacements are

    -(M-1)*(4,3/10,-1,3/10).

Therefore only players1 and3 could share a block;0 and2 must be separate.
Now take the block-constant root with player0 surely quitting and all others
continuing. The displacements of1 and3 are-3(M-1) and+(M-1), respectively,
so they cannot share a block either. Thus every such block map is injective,
even into an arbitrary label type. No finite/surjective-label assumption or
singleton-only quotient test is substituted for the full-response predicate.

The literal local box in
`exports/FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` has radius<=1/2 and
favorite-pair participant centers5 and9/2. The current family has both
favorite participants1+3M>=7, so it misses that stated box under every
relabeling preserving the forced singleton favorites. The explicit
rectangle and passive-ray raw families respectively require favorite
participants5,9/2 or a common A<4, also impossible here. This does not
exclude any unrelated unknown open neighborhood or arbitrary alternative
periodic calendar.

The raw finite-n producer, weak-balance boundary/full agency, nonsingular
local extension and complete four-owner-face exclusion in Section6 passed
the bounded review stated at the top. Section7's named-source comparisons
remain separate, unreviewed admission evidence, not an exhaustive universal
producer census. Broad new-class coverage and export admission remain
unproved.

## 8. Equal inner and outer degrees do not obstruct the balanced source

Status: exact ordinary calculation, not independently reviewed. This tests
the genuinely new degree-comparison hypothesis in Section13 of
`CODEX_EMMY_BOX__INCOMING_PAIR_DEGREE_DEFECT_PRODUCER.md`; it does not claim
new raw-table coverage or remove that hypothesis from its global argument.

Consider the zero-diagonal matrix

    Gamma=[0,-1,2,-5; 1,0,-2,-3; -3,5,0,2; 5,1,-5,0].

BOTH Gamma and -Gamma are R0 and have ACTUAL minimum-map degree1. Nevertheless
the row-proportional signed-pair source with C=Gamma and a=ones has an
explicit nondegenerate all-positive leading root z*=ones/3. Thus equality
of the two degrees is not a stationary-root impossibility certificate.

Here is an exact finite certificate, without a floating-point root census.
Every column of Gamma has both a positive and a negative external entry,
and its principal determinants in support order

    01,02,03,12,13,23,012,013,023,123,0123

are respectively

    1,6,25,10,3,10,4,10,-55,71,264.

Consequently a nonzero homogeneous complementary root of either matrix
cannot have a nonsingleton support: its active principal block would be
singular. A singleton support is excluded by the negative external entry
in that column of the chosen signed matrix. This proves both R0 claims.

Use the positive offset b=(2,3,5,7). The active candidate
-Gamma_SS^(-1)b_S for every nonsingleton support is:

| Support | Candidate active vector for Gamma |
| --- | --- |
| 01 | (-3,2) |
| 02 | (5/3,-1) |
| 03 | (-7/5,2/5) |
| 12 | (-1,3/2) |
| 13 | (-7,1) |
| 23 | (7/5,-5/2) |
| 012 | (-15,-10,-6) |
| 013 | (-6/5,-1,3/5) |
| 023 | (173/55,50/11,122/55) |
| 123 | (-77/71,84/71,15/71) |
| 0123 | (-13/11,-2,-2/11,8/11) |

The candidate for -Gamma is the NEGATIVE of each displayed vector. All
but two rows therefore exclude both signs by a negative active coordinate.
For Gamma, support023 has omitted residual-48/5 at player1 and is illegal.
For -Gamma, support012 has omitted residual-48 at player3 and is illegal.
Singleton supports cannot solve the active equation because b_i>0 and the
diagonal is0. The empty root is the ONLY standard-LCP root for either
matrix at this offset, and its residual b is strictly positive.

The support-sum formula
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` (read in place) therefore gives
degree1 for each matrix. The local index is the sign of the active
principal determinant, with no extra active-cardinality sign.

The row sums of Gamma are(-4,-4,4,1), all nonzero. At z*=ones/3, the
balanced leading field is

    L_i(z)=[sum_(j!=i)z_j-1]*(Gamma*z)_i.

Its Jacobian has zero diagonal and constant off-diagonal row values
(-4/3,-4/3,4/3,1/3). Its determinant is-64/27, not0. Section12's
explicit-root argument consequently yields actual all-interior stationary
equilibria for EVERY sufficiently large row-proportional pair inflation,
arbitrary bounded pair residuals and signed size-k rewards bounded by
R*M^(k-2). That ordinary general argument remains unreviewed; the exact
membership identity of Sections1–3 already gives the explicit equilibrium
for every M>1 on its narrower completion family.

What survives: unequal degrees are a useful global selector but NOT a
necessary condition for the desired stationary source. A vanishing annulus
degree permits cancelling nonzero roots. This calculation does not claim
that every equal-degree coefficient pair has such roots: C=-Gamma in the
incoming-pair note gives the opposite exact leading-root test. The concrete
remaining question is how to select roots for raw coefficient families
outside both degree separation and the row-proportional neighborhood,
without assuming a supplied equilibrium or root Jacobian.
