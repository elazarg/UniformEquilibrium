# Independent check of the K10 full-cap chamber

Reviewer: CODEX_NASH_BOX. Status: **PASS** for the complete ordinary
K10 proof, and for the separately saved closed interval K in[7,30].
No Lean implementation, arbitrary-Fin4 conclusion, explicit equilibrium,
or strategy-class completeness is asserted by this review. The review was
performed without reading CODEX_TURING_BOX's verdict.

Reviewed primary packet:
`notes/CODEX_EMMY_BOX__CAP_CHAMBER_NASH_SATURATION.md`, SHA256
`9dc27819b96e8d881ae46107b5480349474f1512c8468a17839e2de95056f3da`.
Reviewed interval extension: Section7 of
`notes/CODEX_EMMY_BOX__OPPONENT_COINCIDENCE_BARRIER.md`, whole-file SHA256
`946f5e2072da56c90bca6694ea6b0c28e168995c25534fbe7f3ea1e163c9a4a7`.
The author's symbolic checker was not used as a premise. Independent
literal coalition enumeration in Sympy checked the polynomial identities.

## 1. Claim, information and full-response interpretation

The input is the literal four-player table: singleton owner1/opposite4/
neighbors0; outgoing adjacent-pair donor-1/recipient2/outsiders1;
opposite-pair members0/outsiders1; triple members-1/outsider10; grand9.
Live and Never pay0. Prescribed clocks are independent. A deviation is
an ENTIRE behavioral replacement, not only a root action.

For an actual profile, U is prescribed terminal payoff and B is the
supremum over all unilateral behavioral replacements. The closed carrier
of these actual pairs, not an arbitrary box of annotations, is the
optimization domain. It is compact, every B_i-U_i is nonnegative, and
B_i>=0 because Never encounters only nonnegative passive rewards.

I opened the actual declarations and their imports:

* `quittingTerminalSemanticPair`,
  `quittingTerminalSemanticPrefix`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

Their statements match the use made here. In particular, prefixing against
the FULL cap B scales every actual debt by the same JOINT Continue mass c.
No conditioning of a nonattained cap maximizer is required. Prefixing is
continuous for a fixed chosen root, so a root chosen at a carrier limit
is legally applied to the approximating actual profiles even though it
need not be Nash at each approximating cap. This is exactly the closure
step needed by the proof; it assumes no continuous Nash selector.

## 2. Adversarial check of the entire root correspondence

The no-sure argument is valid for every continuation. With i sure, its
opposite strictly Continues by joining differences -4,-2,-1; its
predecessor then strictly Continues by differences -1,-2; its successor
strictly joins; i would withdraw. Thus all positive root rates are
interior, and active players' two endpoints agree.

I independently reconstructed every Q_i and opponent-stop term from the
literal coalition table. The support-two and support-three identities are
correct. For three active rates(a,b,e,0), cap nonnegativity gives

    b<=1/2, a<=(1+b)/(5-b)<=1/3,
    e<=(1-2b)/(5-4b)<=(1-2b)/3,
    a+b+e<=5/6.

The active output Q0=1-2b-e+be is strictly below1. The inactive player's
Nash inequality is NOT being discarded: these necessary conditions hold
for every full-game Nash root, and suffice for the claimed implication.

For full support the exact odds numerators are

    P_i=1+2x-w-T+9V, N_i=4y+T+10V,
    B_i=P_i-N_i=1+2x-w-4y-2T-V.

Summing gives sum B=4-3Z-4E2-E3, so Z<=4/3 and s=sum q<=1.
Independent expansion gives exactly

    sum Q-4=-2s-Aq-2Oq+12E3q.

Maclaurin's E3q<=s^3/16 implies a strict negative total at every
full-support root. Thus all nonzero supports have at least one output
cap below or equal to1. The all-Continue root simply preserves a low
input cap. This proves the entire-correspondence low-cap implication.

The total-cap identity is also exact:

    sum B'-4=c*(sum B-4)
                +P1-P_adj-2P_opp+3P3+32P4.

The Poisson-binomial inequality has the correct direction. Cauchy gives
sum z/(1+z)>=Z^2/(Z+sum z^2). If sum q<=1, then 2E2<=Z,
hence P1>=2P2 after multiplication by c. All q_i<1 was already proved.
Opposite, triple and full supports satisfy sum q<=1. The remaining
adjacent support has H=a+b-3ab>=0 because its second rate b<=1/2.
Singleton and empty supports cause no exception. Therefore the proposed
total-cap surplus inequality holds for EVERY cap-Nash root.

## 3. Actual seed and compact minimum: no hidden late cap

The seed has players0,2 literal Never and players1,3 independently Quit0
with probability1/2, otherwise Never. Direct pure-clock enumeration gives

    U=(1/4,5/4,1/4,5/4), B=(1/2,5/2,1/2,5/2).

For recipients0,2, Quit0 and Never pay1/4, while every positive finite
deadline pays1/2. For recipients1,3 these three values are respectively
1/2,2,5/2. Thus the omitted-late representative is included, and mixing
pure deadlines cannot exceed the stated full caps. The seed has D=5/4
and sum B-4=2=(8/5)D.

The chamber is a closed subset of the compact actual carrier. Its debt
minimum is attained. If D*>0, sum B*>4 and min B*<=1. A cap below1
rules out all Continue, so finite Nash supplies a nonzero root. If all
caps are at least1, a cycle edge from cap1 to cap>1 supplies the stated
small axis root. I checked all three outsider inequalities, including
the mate's passive singleton4 and the predecessor's negative join.

Every such root preserves the chamber, has c<1, and maps D* to cD*.
This contradicts minimality. The diagonal is therefore in the ACTUAL
carrier. Its actual realizing sequence has prescribed payoffs and full
caps converging to the SAME vector. The named diagonal-carrier consumer
then gives a fixed uniform-equilibrium payoff against unrestricted
behavioral deviations over all sufficiently large horizons. No strategy
limit, cap attainment, or exact terminal Nash profile is inferred.

## 4. Closed family endpoints

Section7's K in[7,30] strengthening is valid, including both endpoints.
I independently checked the identities for SYMBOLIC K before reading the
author's interval calculation:

    B_i=1+2x-w-4y-2T-V,
    sum Q-4=-2s-Aq-2Oq+(K+2)E3q,
    H_K=P1-P_adj-2P_opp+(K-7)P3+(4K-8)P4.

At K=30, the upper bound is -2s+2s^3-Aq-2Oq<0: in full support the
last two negative terms are strictly nonzero. At K=7 the zero triple
charge is harmless; all remaining terms in the surplus proof are
nonnegative. The no-sure comparison remains (K-1)-K=-1. Seed, actual
compactness, and the axis-root construction are unchanged. No open
sixty-coordinate neighborhood is inferred.

A further asymmetric/unbounded reward-class consequence is recorded
separately in CODEX_NASH_BOX's owned notebook Section29. It requires only
passive triple rewards K_i>=7 and grand rewards G_i<K_i, with the other
rows fixed. It uses preservation from POSITIVE-debt chamber points,
not an unjustified assertion that all zero-debt chamber points satisfy
the earlier full-support low-cap bound.

## 5. Bounded whole-producer overlap checks

No applicable whole existing producer was found in the following actual
selection families. This is a bounded source comparison, not a claim
about every conceivable verifier or an unquantified remote IFT radius.

### Singleton and actual response-quotient exits

The literal singleton matrix is Gamma with cyclic row(0,-1,3,-1),
determinant45 and strictly positive inverse. Every principal of size>=2
is invertible. A homogeneous complementary root on an axis fails a
negative external entry, so Gamma is R0. At offset ones the entire
strictly complementary root set is empty, the four adjacent supports
with active coordinates(1,1), and four triples with rotated active
coordinates(1/2,5/2,1/2). Their actual principal-determinant indices sum
1-4+4=1. Thus the WHOLE degree-not-one criterion is unavailable, rather
than merely one chosen LCP witness failing.

I opened `QuittingResponseInvariantOnUnitCube` and
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
`quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`, and
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
The last theorem requires NEGATIVE determinant as well as nonnegative
inverse and actual response invariance.

Enumerating all15 partitions, the singleton block-row condition leaves
only the following seven partitions. Discrete, all-block, and opposite
pair blocks02|13 are actual invariant quotients. Their matrices are
Gamma, [1], and [[3,-2],[-2,3]], with positive determinants and degree1.
The latter inverse is positive; the failed exit is its determinant/degree.
The other four partitions fail the ACTUAL displacement H_i=(1-alpha_i)Q_i-b_i:

| blocks | block-constant hazard | unequal response values |
| --- | --- | --- |
| 01\|23 | (0,0,1/2,1/2) | H0=-7/8, H1=-23/16 |
| 03\|12 | (0,1/2,1/2,0) | H0=-23/16, H3=-7/8 |
| 02\|1\|3 | (0,0,0,1/2) | H0=3/4, H2=0 |
| 0\|13\|2 | (0,0,1/2,0) | H1=0, H3=3/4 |

Thus the dangerous negative-degree two-block matrix is NOT a response
quotient of this table. Mere raw matrix symmetry cannot invoke that exit.

The exact `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
requires a nonnegative selected child inverse. All four deleted triples
have determinant6 and a negative inverse diagonal, as direct exact
inversion confirms. `SignedFourCycleSingletonData` requires positive
singleton-comparison edges forming a directed four-cycle. Here the only
positive edges form the opposite matching, so no relabeling supplies it.

### All stationary exact producers

I independently checked the entire stationary nonexistence calculation
in the opponent-coincidence note, not only a numerical root search. Sure
rates are impossible by the same continuation-independent argument.
Supports0 or1 have an immediate profitable Quit; an adjacent support2
has an active player with Never0 and positive Quit; an opposite support2
has Never4 and Quit<=1. For support3(a,b,c,0), stationarity of player0
forces b<1/2 and c<1/4, whereas player1 has Quit>1/2 and stationary
Continue value<=c<1/4.

For full support put A_i=product_(j!=i)(1+z_j)-1 and
F_i=N_i(1+A_i)-P_i*A_i. Independent symbolic expansion gives

    sum F=sum z + Qquad + (K-1)*sum V_i + R(z),
    Qquad=2*sum z_i^2+(z0-z2)^2+(z1-z3)^2
                                      +7*sum z_i*z_(i+1),

where R is an explicit polynomial with50 monomials and ALL positive
coefficients. Thus sum F>0 for K>=1, excluding every full-support
stationary root. This rules out applicability at K10 of ANY sound raw
producer whose conclusion is an exact stationary Nash profile, including
the whole selected-column/thick-tube and jackpot conclusions. It does
not exclude stationary approximate families or unknown nonstationary
sources. The literal `PairedCollisionReward` family is also different:
its pair member coordinates are equal to one common parameter, unlike
K10's adjacent(-1,2) and opposite(0,0) pairs.

### Traps, entire weight sets, joins and calendars

The sole premium trap is all4: any proper trap must be closed under the
incoming participant-premium cycle. Every player violates the common
protected-participant floor via its outgoing pair-1<own1. Hence all
common/protected-set leaver selections fail, not only one chosen player.
At grand, every nonnegative nonzero upper-average weighting has value
8*sum w>0. For the weighted FLOOR criterion, summing its four singleton
tests gives -2*sum w<0. Thus no positive weight choice works.

For the boxed-charge predicate, singleton coefficients are P=-2,L=-3,
pair coefficients P=-4,L=-4, and triple coefficients P=8,L=-1.
Every legal choice therefore has d<=2,g<=3,ell<=1,tau>=8 and charge
at most13/2, strictly below the required4+4M=44. The mixed upper-or-charge
producer therefore fails both alternatives on its whole trap.

Every triple contains a directed donor join with gain-1 or an opposite
join with gain-4, ruling out all six-strict-join triple-singleton selections.
Every pair partition leaves some incoming reward2 outside a player's
scheduled pair: an involutive mate relation cannot contain all four
predecessor edges. This violates the common cross-pair caps used by the
crossed, signed-inverse-column and two-pair join-cap exports, under EVERY
partition. The four-joint-phase local/rectangle centers require positive
participant entries in every scheduled pair; every K10 pair has a
nonpositive member, incompatible with their actual <=1/2 local radius
or literal rectangle rows. The passive-ray family requires both favorite
pair members above (5+sqrt5)/2, whereas K10 has neither such pair.

The four-singleton golden architecture has only its two chronological
orientations after identifying opposite favorites. Its all-positive
owner equations force the golden hazards (the whole-root uniqueness
lemma in the accepted singleton/passive-ray packets). In either
orientation an incoming participant reward2 violates a cross threshold
at most1. Thus neither the exact class nor the local source at these
EXACT singleton rows can supply the K10 profile. This does not infer
anything about arbitrary longer singleton calendars or distant unnamed
IFT neighborhoods.

## Verdict

The frozen K10 proof and the separately saved closed[7,30] extension are
sound ordinary mathematics. They produce a diagonal actual semantic
carrier point and hence a fixed all-behavior uniform payoff; they do not
produce an exact equilibrium strategy or settle arbitrary Fin4.
The bounded whole-source tests above do not reveal an applicable existing
producer, and avoid the two dangerous false shortcuts: inverse positivity
alone and matrix-only quotient symmetry. The positive-debt chamber
mechanism, rather than another low-regret finite certificate, is the
substantive mathematical advance.

## 6. Final unbounded asymmetric family: hash-specific PASS

I read the ENTIRE assembled final packet
`notes/CODEX_EMMY_BOX__PASSIVE_TRIPLE_CAP_CHAMBER_RAW_FAMILY.md`, SHA256
`bb20cbe7d9078b51df89df7716085441cc90f31763a8f12e61247b7c8ea10c16`.
**PASS** for its precise scope: singleton/pair rows and triple participant
rewards fixed as printed; EACH passive triple K_i>=7; EACH arbitrary
finite grand coordinate G_i<K_i. There is NO bound on |G_i|, on K_i,
or on sum G_i. The conclusion is a fixed uniform-equilibrium payoff
from actual independent profiles and FULL behavioral caps, not stationary
or exact terminal Nash existence.

The stronger step is logically valid and necessary for this scope.
At a positive-debt chamber point, sum B>4. A full-support cap-Nash root
would give

    sum B=4-3Z-4E2+sum_i(G_i-K_i)V_i<4,

an immediate contradiction. Thus EVERY root at the positive-debt minimum
has support<=3, so its grand-event probability is zero. The low-cap
support analysis is unchanged; its ACTIVE rows contain no passive triple
coordinate. The total reward ledger has coefficients K_i-7>=0 on triple
events and needs no grand coefficient. All cap-Nash prefixes from
positive-debt chamber points remain in the chamber, which is all the
minimum argument uses. At a zero-debt chamber point the required
diagonal already exists, so invariance there is unnecessary.

Grand negativity causes no semantic seam: Never's passive values remain
nonnegative, the reward bound is finite separately for each table, and
the unchanged seed/replacement experiment cannot encounter a grand
coalition. The explicit correction that an outsider's Quit0 can encounter
a FIXED participant-1 triple is accurate; no variable PASSIVE triple
coordinate enters those seed caps.

This final packet faithfully incorporates the complete reviewed
source-to-consumer proof and the strengthening. The K10 bounded
whole-source comparisons above remain a witness of new coverage within
this family; no assertion that every member avoids every older producer
is needed or made. This is an independent ordinary-mathematics gate, not
a Lean verification or a self-export.
