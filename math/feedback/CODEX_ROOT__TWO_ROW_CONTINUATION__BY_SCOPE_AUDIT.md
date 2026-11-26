# Two-row nonredundancy audit at an interior fixture

Status: ordinary exact mathematics and static source review, not checked in
Lean. This is a bounded comparison of raw producers, not a claim to exclude
every abstract sufficient predicate for uniform equilibrium. Its sole exact
checker is `math/experiments/CODEX_COORDINATOR__TWO_ROW_SCOPE_CHECK.py`;
it uses rational arithmetic, symbolic polynomial identities, and rational
outward bounds for square roots. It has no scratch-file dependencies and
runs in under one second in the review environment. No search result or
floating-point sign is used as proof. The checker does not rerun the
separate stationary-gap certificate attributed below.

The fixture is the literal table in
`math/notes/CODEX_ROOT__TWO_ROW_CONTINUATION.md` at

    delta=1/8, epsilon=139/200, r_i(S)=1+Z_i(S), live/Never=0.

For a complete independent specification, set

    A=[0,1,-6,-1/100; 1,0,-3/2,-2/5;
       -delta,-3/5,0,1; -7/100,-epsilon,1,0].

Set J=.01 on the favorite directions01,10,23,32; set J=-.9A on
02,21,13,30 and J=-.1A on03,12,20,31. Set Z_i({i})=0,
Z_i({j})=Gamma_ij=A_ij+J_ij and Z_i({i,j})=J_ij.
For each opponent pair B in order01,02,03,12,13,23, give its smaller
outsider contact d_i(B) the sign(+1,-1,+1,+1,-1,-1), and its larger
outsider the opposite sign. Set Z_i(B)=max(0,-d_i(B)) and
Z_i(B+i)=max(0,d_i(B)). Finally Z_i(I-i)=1 and Z_i(I)=0.
This specifies all60 rewards, and also defines the reference table used
in the conditional-average check by allowing arbitrary delta,epsilon.

All twelve native pair participant premiums J_ij are strictly positive,
all native nonsingleton reward vectors are nonnegative, and every player
has exactly one positive singleton premium: the favorite matching01/23.
Every reciprocal singleton pair has the same strict sign. The exact
singleton matrix is

    Gamma=[0,101/100,-3/5,-9/1000;
           101/100,0,-27/20,-1/25;
           -9/80,-3/50,0,101/100;
           -7/1000,-1251/2000,101/100,0].

Its determinant is10300929979/16000000000 and K=Gamma^-1 is strictly
positive. The original own offsets all equal one are essential for the
punishment and finite-calendar calculations below.

## 1. Stationary-producing criteria: complete selection excluded

The retained stationary-gap theorem in the section "No exact stationary
equilibrium at an interior parameter" of
`math/notes/CODEX_ROOT__TWO_ROW_CONTINUATION.md`, with
`math/experiments/CODEX_COORDINATOR__TWO_ROW_STATIONARY_EXCLUSION.py`, has been independently
reviewed and rerun by the coordinator. It gives a strictly positive gap for
EVERY stationary profile at this fixture. Accordingly any raw theorem that
produces exact stationary Nash or stationary Nash approximations of every
accuracy cannot apply here, regardless of its chosen support, root, row
scaling, inverse column, bonus decomposition, threshold, or polynomial
weights. This is stronger than failing a proposed coefficient choice.

It covers the stationary conclusions of the weighted-collision,
signed-passive-coalition, positive-inverse-coalition-jackpot,
signed-single-column-jackpot, boundary-inverse-column, contact-preserving-coalition-bonus,
three-passive-pole, and proper-triple bonus criteria; sure-exit and
potential/toggle criteria when their stated conclusion is stationary; and
the stationary-response quotient/guarded crossed-response producers.
For `POLYNOMIAL_ROW_WEIGHT_UNIFORM_EQUILIBRIUM.md`, det Gamma is nonzero
and there are no negative-own owners, so the theorem's extra negative-own
strict guards are vacuous: its applicable conclusion would be exact
stationary Nash. All permitted row-weight choices are therefore excluded.

This reasoning alone does NOT reject punishment continuations or an
arbitrary nonstationary construction using a stationary induced game.
Section2 supplies the separate necessary check.

## 2. All sure-quitter punishment roots fail

Every player's actual punishment value is exactly1. Immediate Quit
guarantees at least1 because every participant reward is at least1.
Opponents all Never cap every possible response at1, giving the converse.
Let g_i(q) be Quit minus Continue in the one-stage game with continuation
vector(1,1,1,1). For a root, g_i=0 at a mixed owner, g_i>=0 at a sure
quitter, and g_i<=0 at an inactive owner. Write d_i(B)=Z_i(B+i)-Z_i(B),
with d_i(empty)=0. Then g_i is the product expectation of d_i(B).

There are65 patterns in {inactive,sure,mixed}^4 containing a sure owner.
The exact checker exhausts all61 patterns having at most two mixed owners:

| Pattern class | Number | Exact rejection |
|---|---:|---|
| Pure nonempty coalition |15| At least one wrong action inequality |
| Exactly one mixed owner |28| Its constant gain is nonzero |
| Two mixed owners, no interior solution |16| Their linear equations fail |
| Two mixed owners with interior solution |2| The candidates below fail |

The only two lower-dimensional interior candidates are

    q=(1,7/107,0,1/2),     g0=-13/214;
    q=(1/2,0,1,6/7),      g1=1/28, g2=-95/112.

For full support, three owners are strictly mixed and one is sure.
The following exact equations exhaust the remaining four patterns.

- Sure0: g1=0 gives q3(1-q2)=1/2, hence q3>1/2.
  Then8g2=7q1(1-q3)-9q3+1<7(1-q3)-9q3+1<0.
- Sure1: g0=0 gives q2(1-q3)=1/2, hence q2>1/2.
  But g3=0 would give (1-q0)(1-q2)=200/339>1/2, impossible.
- Sure3: g2=0 gives q1(1-q0)=1/2, hence q1>1/2.
  But g0=0 would give (1-q1)(1-q2)=100/101>1/2, impossible.
- Sure2: write x=q0. The equations

      g3=2q0(1-q1)-1=0,
      2g1=q0*q3-5q0-q3+3=0

  force q1=1-1/(2x), q3=(3-5x)/(1-x). The remaining mixed equation is
  9x^2+5x-5=0. Its only positive root is (sqrt205-5)/18, in(1/2,13/25).
  After substitution, g2 has denominator80x(1-x)>0. Its numerator
  reduced modulo that quadratic is(176290x-92572)/81, strictly negative
  already at x=13/25. Thus the sure owner fails too.

No sure punishment root exists. Compactness of the sure-root face then
also forbids approximate roots of every accuracy there. This rejects the
complete selection input to
`quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor`
in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean`.
It rejects every corresponding persistent-base/free-carrier choice: with
at least two sure base owners, deleting one still leaves absorption;
with one sure owner, any admissible punishment continuation for that owner
is at least1, and replacing it by1 can only improve its Quit comparison.
The other owners face certain immediate absorption by the base owner.
Thus any accepted persistent-base selection would give a root just excluded.

## 3. Every admissible adaptive nonnegative ledger fails simultaneously

The following obstruction applies to every adaptive ledger, not only a
single coefficientwise joining ledger.

For every proper nonempty B define

    H_a(B)=sum_i a_i Z_i(B),
    J_a(B)=sum_(i outside B) a_i[Z_i(B+i)-Z_i(B)],
    f_a(z)=sum_(empty!=B proper) (product_(j in B)z_j) J_a(B).

Let a>=0, sum a=1 and a^T Gamma>=0. The latter is the singleton part of
H_a(S)>=0 in the marked-support orientation, same-sign-pair ledger, and
support-filtered weighted-ledger raw theorems. Put h^T=a^T Gamma>=0.
Then a^T=h^T K, h is nonzero, and every row sum of K is<5. Therefore

    1=h^T K1<5 ||h||_1.

Writing A=Gamma-J, exact calculation gives

    -K A[:,2]=(75679478400,87911025000,44769477730,13652082000)
                    /10300929979,

whose entries are all>1. Hence

    J_a({2})=-a^T A[:,2]>1/5.

Take the SAME strictly positive odds z=(eta,eta,1,eta), eta=1/200,
for every a. All singleton joining coefficients have absolute value<=6;
all pair and triple joining coefficients have absolute value<=1.
Consequently the sum of the absolute values of every term of f_a(z)
other than singleton2 is at most

    18eta+3eta+6eta^2+eta^3<1/5.

Thus f_a(z)>0 for EVERY a satisfying the mandatory singleton H condition.
No finite or infinite adaptive selection of such a can provide the required
odds cover. Marked sets, passive floors, root orientations, and omitted-unit
choices cannot repair this preceding failed condition. Relabelings and
positive recipient scalings merely permute the odds and rescale/renormalize
the effective nonnegative weights.

This excludes the whole ledger-selection set in
`MARKED_SUPPORT_ORIENTATION_LEDGER_UNIFORM_EQUILIBRIUM.md`,
`SAME_SIGN_PAIR_LEDGER_UNIFORM_EQUILIBRIUM.md`, and
`SUPPORT_FILTERED_WEIGHTED_LEDGERS_UNIFORM_EQUILIBRIUM.md`.
It also rejects scalar H/J predecessors whenever their singleton H and
coefficientwise joining conditions imply this odds-cover condition.
In particular this includes `SINK_OR_RECEIVER_CAP_CHAMBER_UNIFORM_EQUILIBRIUM.md`.
The argument uses the literal grand rewards; it does not silently range
over a different reference grand reward.

The arbitrary-positive-matrix product-cover theorem, which DOES allow a
different reference grand reward, has a separate complete obstruction.
Here Z(01)=(.01,.01,0,1)>=0 is nonzero. For every P>0, put
rho=min_(i,k)P_ik/(sum_l P_lk). Every coordinate of PZ(01) is at least
rho times its coordinate sum. Its raw outsider cap requires at most eta
times that sum, with eta<e<rho_star<=rho. Impossible, for every P,
normalization, adaptive cover, and reference-grand choice. The same proper
coalition obstruction rejects the fixed-inverse global coalition cone.

## 4. Universal quiet lifting, premium/core and payoff selectors

The following rule supplies exact witnesses for ALL14 nonempty proper child
sets. A singleton child uses its sole quitter. A favorite-pair child uses
one of its members alone. A crossing-pair child uses both members. The four
deleted-pivot triples use pairs12,03,13,02 respectively; the third child
member remains quiet. Prescribe these quitters at date zero and the other
child players Never. Each is exact child Nash with child debts0 and joint
Never0: crossing participants have positive dropping-out loss -A_ij;
the quiet member of each triple has joining gain-1; a favorite quiet mate
has joining gain-1; and a sole quitter against Never gets1 rather than0.
An omitted owner has positive joining gain: a crossing outsider to a
singleton, or the +1 outsider to a crossing pair. These witnesses
reject every universal bound by finite weighted child debt plus finite
joint-Never correction, including capped-clock, patient, deadline,
evaluated-security, terminal-security, and cancellation variants, every
pivot and mixed operation choice. The witnesses persist within raw reward
distance1/1000, so reward-closure does not bypass the obstruction.

The same witnesses and premium signs exclude every
supportweight, ordering, protected-owner, trapweight, core, boxed-charge,
and nonnegative-inverse-triple selection in the named formalized routes.
All pair premiums are strictly positive; every pair is an actual trap and
the actual premium core is all4. In particular a crossing trap02 has the
strictly positive weighted leave sum(1/8)w2 on subset{0}, for EVERY positive
trap weight. Each principal triple Gamma has positive determinant and all
negative inverse diagonal entries. These are complete auxiliary-choice
failures, not just failure at a sampled choice.

For `MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md`, a pair trap
admits neither alternative: its singleton-coalition upper-average tests
force both nonnegative weights to vanish, while charging requires size>=3.
For `MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md`, every triple is a trap,
and a singleton inserted-premium sum is the sum of two positive J entries,
contradicting its required bound by a negative constant. Thus all choices
of support certificates and charge constants fail as well.

The named quiet inputs are `CappedClockParentRewardCertificate` and
`CappedClockParentRewardSlackCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`,
and `WithdrawalFutureJoinRewardCertificate` in the same directory's
`WithdrawalFutureJoinRaw.lean`. Its consumer
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`WithdrawalFutureJoinDebt.lean` makes the universal quantifier explicit.
Under `UniformEquilibrium/Quitting/Classification/`, the premium predicates
are `HasSupportwiseQuittingPremiumBalanceAt` in
`SupportwiseQuittingPremiumBalanceAt.lean`, `HasProductLowQuittingPremium`
in `ProductLowQuittingPremium.lean`, `IsCommonQuittingPremiumLeaver` in
`CommonQuittingPremiumLeaver.lean`, `HasWeightedQuittingTrapLeavers` in
`WeightedQuittingTrapLeavers.lean`, and `HasBoxedQuittingNashCharges` in
`BoxedQuittingNashChargeReturn.lean`.
Pair positivity defeats supportweights and product-low; pair traps defeat
any earlier-player peeling order and any common leaver; a boxed charge
requires trap cardinality>=3. The raw triple-inverse predicate is in
`LCP/ThreeCore/RawPassiveRowInverseCriterion.lean` under that directory.

One finite-calendar profile rejects the universal payoff-exclusion tests
PD, WE_J, GE and all nonzero nonnegative social-weight upper chambers:
every owner uses independent probability1/2 of Quit on one date, then Never.
Its original payoff minus the own-singleton vector is exactly

    (2203/4000,157/800,11/40,11/50)>0.

Thus no selected nonempty subset, normalized nonnegative weight or strict
deficit margin can make such a universal payoff bound valid.

## 5. Pair-cone, fixed-tube and spectral raw producers

The singleton matrix also passes the hard-side matrix conditions; an
unexamined easy matrix exit is not hidden in this comparison. Every
principal matrix of size at least2 is nonsingular. At homogeneous offset0,
an active support of size>=2 therefore cannot give a nonzero LCP root;
a singleton support has a negative outside slack. Thus Gamma is R0.
At offset(-1,-1,-1,-1), feasibility in row i forces its only positive
column, the favorite of i, to have positive weight. Every weight is
therefore positive, and the only complementary solution is K1>0.
Its index is sign(det Gamma)=+1. The finite-support degree sum gives
degree1 and therefore standard Q. The relevant named mathematical
interface is `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`; finite-support enumeration is
in `MathUE/LinearProgramming/FiniteSupportDegree.lean`. This paragraph
is an ordinary calculation, not a new Lean instantiation.

Every row has negative entries, so the recursive normal core remains all4.
Actual punishment values equal own values, so the punishment-normal core
also contains all4. A negative reciprocal principal pair, for instance02,
has neither a standard LCP solution at offset(-1,-1) nor a nonzero
homogeneous nonnegative solution. Hence it is not projective Q, and the
full matrix is not projective Q-bar. This uses the definitions/equivalence
`IsProjectiveQBarMatrix` and
`isProjectiveQMatrix_iff_standard_or_homogeneous` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, as
described in `math/formalized/THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION.md`.
Thus a projective-Q-bar path hypothesis fails as well. The raw theorem
`NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md` fails its
explicit pair-sign condition on every crossing pair.

The combined checker verifies the finite arithmetic for these additional
all-choice obstructions.

- Every principal triple has
  det(lambda A_S+J_S)=(lambda+.01)[KH(lambda-.9)^2+KL(lambda-.1)^2]
  with (KH,KL) equal to(18/5,3/16),(7/250,139/20000),
  (21/50,1/800),(6/25,417/400) for012,013,023,123 respectively.
  Thus no positive real triple mode or positive Jordan mode
  exists on any triple, under any relabeling/positive recipient scaling.
  This rejects criteria requiring those modes, not arbitrary spectral planes.
- For arbitrary positive invariant-cone matrix V, its ratios satisfy
  R_ab R_ba>=1. The matching01/23 has negative scheduled contacts.
  Matching02/13 would require R_1,0<=1/8 and R_0,1<=139/200;
  matching03/12 would require R_2,3<=1/100 and R_3,2<=3/2.
  All are impossible. This rejects the entire finite invariant-cone pair
  criterion and its positive-inverse specialization, not just a fixed V.
  The queried unit triple rewards are Z2(123)=Z3(023)=1 for02/13 and
  Z0(012)=Z1(013)=1 for03/12. They force the stated ratio bounds directly
  from Z_i(i+j+k)<=c_i/(R_j,m(i)+R_k,m(i)).
- The bounded-inverse-corner version fails its required participant-triple
  cap ell_i<=c_i/8. Two-pair join-cap and signed-inverse-column versions
  require a nonpositive nonscheduled participant pair, impossible here.
- The dominated-row and stronger conditional-average raw classes have
  been checked at ALL24 roles and arbitrary positive recipient scales.
  Only identity can satisfy the controlled-row identities; then row2's
  passive conditions demand simultaneously lambda<=1 and lambda>=64/5.

For the last enumeration, the stronger raw criterion is the section
"A larger class from conditional averages" in
`math/notes/CODEX_ROOT__PROOF_MECHANISM_DIVERSIFICATION.md`.
Write B=Z^(8/5,0), c=7/50, and W for any relabeling of the fixture.
The empty-T equations for i=0,1 uniquely force

    a_i=[c W_i(i2)-W_i(2)]/[c B_i(i2)-B_i(2)],
    k_i=W_i(2)-a_i B_i(2).

The denominator is positive. For every T subset I\{i,2}, the criterion
then demands

    (1-c)W_i(T+i)+cW_i(T+i+2)
      =a_i[(1-c)B_i(T+i)+cB_i(T+i+2)]+k_i,
    (1-c)W_i(T)+cW_i(T+2)
      =a_i[(1-c)B_i(T)+cB_i(T+2)]+k_i[1-(1-c)1_(T=empty)],

with empty native rewards zero. The checker exhausts24 permutations and
all these identities, leaving only identity, a0=a1=1,k0=k1=0.
Positive control-row scales are absorbed into a_i,k_i. For row2, the
favorite singleton3 forces lambda<=1 and singleton0 forces lambda>=64/5,
so no positive scale remains. This also excludes the fixed-row special
case in `DOMINATED_ROW_ARBITRARY_ROW_STATIONARY_UNIFORM_EQUILIBRIUM.md`.

The combined checker also rejects every role assignment in the
WHOLE fixed-tube algebraic criterion in Sections3–4 of
`REPEATED_PAIR_RAW_REWARD_UNIFORM_EQUILIBRIUM.md`, not just its displayed slab.
Sixteen permutations fail singleton signs; three fail M0; two fail R
positivity; two have G2>0 at the required upper endpoint; one has G2<0 at
the required lower endpoint. The endpoint signs are exact outward interval
signs, not floating-point decisions. Each tested sign is unchanged under
independent positive recipient scaling. No role or positive scale remains.

## 6. Other displayed nonstationary raw families

The following groupings use mandatory raw conditions, before any later
strategic or scalar root selection. Names abbreviate files in `math/exports/`.
They include all stated parameters, not just a chosen numerical example.

| Producer group | Necessary failure at the fixture |
|---|---|
| Arbitrary-one-joint; both-joint; global-two-joint cyclic child; mixed-pair-positive-passive; crossed-matching; exact-opposed-pair | A required native participant pair is nonpositive, whereas all twelve J entries are positive. |
| Ordered-anchor-block; calendar-polytope | For every marked set/order and positive block weights, a pair meeting the earliest block has a strictly positive participant sum. |
| Passive-bound-triple-selection; passive-threshold; quiet-face-opposed-pair; explicit-singleton-chamber; finite-singleton-split; negative-pair-outer-dichotomy; signed-collision-bridge/parameter; compact-negative-premium-ratios; unbounded-pair-premiums | A queried row has all participant premiums nonpositive, or a particular participant pair is strictly negative. All roles fail before free coordinate/threshold choices. |
| Core-free-joint-return; joint-quitting-negative-value; three-owner-joint-return | A=-Z1(13)>g>0 requires a negative participant pair, irrespective of their cubic/quadratic root selection or unbounded K. |
| All-nonnegative-pair-premiums; central-positive/negative-wedge; nine-independent/unordered-nine-core; unequal-premium-contraction; three-diffuse-flows; crossed-premium-hybrid; no-child-premium | Their fixed singleton matrix has a row with two strictly positive entries; ours has one in every row. |
| Two-contracting-blocks, including its general signed chamber and unbounded pair branch | Its general chamber requires Gamma20>0 and Gamma23<0, giving an opposite-sign reciprocal pair with Gamma02<0, Gamma32>0. Our reciprocal pairs always have the same sign. This precedes its inverse-column exit and threshold selection. |
| Signed-four-cycle/Hamiltonian, cyclic-child, scalar-singular-circuit, three-owner-joint-positive-passive-triple and attached-negative-pair raw versions | Required positive directed3/4cycle or opposite-sign reciprocal pair absent; favorite graph is two disjoint2cycles. This is not an exclusion of a supplied arbitrary cycle. |
| Negative-pair-funded-boundary | A required positive reciprocal singleton pair must have J_ij>Gamma_ij; every actual favorite has J_ij=Gamma_ij-1. |
| Triple-singleton-collision-box | All six joining contacts on a selected triple must be positive; every triple contains a favorite pair with joining contacts-1. |
| Full-passive-parameter; monotone-passive-cap; four-phase-passive-ray; negative-passive-paired-phase; below-singleton-joint; opposite-sign-matching; unordered-rotating-mixed-pairs; four-singleton completion | Their required negative/nonpositive native participant pair fails. |
| Four-joint-phase stated local/upper-only/free cylinder and rectangle | The radius<=1/2 retains a negative native participant pair; the rectangle requires a queried participant reward below -24ML. |
| Ten-phase middle-reward cube; global-asymmetric-pair-phase explicit cube | Their specified small raw cubes retain a designated negative participant premium. Their unbounded scalar family also requires equal two negative singleton entries within each row. |
| Zero-premium-joint-phase | Its scheduled03 pair has exactly zero participant premiums; none of our pairs does. |
| Paid-joint-return exact table and explicit raw cube | Their fixed or cube-retained negative participant pair is incompatible with all J>0. |

For the crossing-transport raw criterion in
`CROSSING_TRANSPORT_AND_PASSIVE_COMPLETIONS_UNIFORM_EQUILIBRIUM.md`,
the main flexible class requires all eight directed crossing J in
[.01-10^-6,.01+10^-6]. Its favorite contact guards force the actual
favorite matching. Each recipient's two crossing J must therefore have
ratio at most10001/9999 under any positive row scale. The fixture's ratios
are5400,12/5,216/5,139/126, all larger. No role or scale works.
The alternative signed finite-box region keeps the Section6 singleton
matrix fixed. The compensated cone retains crossing J=.01 and the same
contact pattern, so the same ratio obstruction applies. Its negative-tube
branch is stationary and already excluded. The three-parameter passive
family and its explicit10^-1000 tube retain favorite J/Gamma near values
at least1/2; our corresponding ratio is1/101 in every row. Free higher
coordinates do not change these singleton/pair tests.

## 7. Explicit prior parameter coverage and logical limits

The complete complex-spectrum ray fixes epsilon=.04. The earlier corner,
middle and upper periodic rectangles have delta in[0,.002], [.099,.101],
or[.98,1.02]. The earlier affine stationary frontier at delta1/8 is
1489/2000, strictly above139/200. The dominated-row literal family starts
at delta>=3/2. These explicit regions miss the fixture. Literal Jordan,
weak-crossing and other fixed families may have our favorite ratio, so one
must use their actual parameter restrictions or mode hypotheses, not the
different favorite-ratio obstruction valid for the transport examples.

Some prior results assert existence of an open full-reward neighborhood
around specified tables without giving a radius or an equivalent effective
membership condition. These include qualitative extensions in actual-marked-source,
full-dimensional cyclic-child, four-singleton-phase, below-singleton-joint,
and the long-period examples. Excluding their centers does NOT prove disjointness
from every possible valid neighborhood. Conversely the statement
"there exists a positive radius" does not imply that this fixture belongs
to that neighborhood or that an entire new concrete rectangle is covered.
No inspected statement/proof supplies a radius or membership condition
reaching this fixture for those qualitative extensions. This is a limit on
what the earlier theorem establishes from its stated data, not a claim
about the maximal mathematical extent of its mechanism.

Still outside this nonmembership claim are arbitrary supplied periodic
cycles, endpoint/cap certificates, favorable individual child laws,
finite-menu strategies and general face/cell root witnesses. In particular
the reusable interval-face criterion permits an arbitrary phase word,
hazard box and preconditioner. A newly produced cycle might satisfy that
old verifier. That would not mean its old proof produced this raw family
from rewards. The terminal-Nash-lift and stationary-endpoint compiler
consumers have the same distinction. We have not excluded every possible
strategy accepted by those general consumers; such a claim would contradict
the purpose of constructing the new periodic equilibria.

The defensible conclusion is that the new completed two-row cover adds
an explicit raw family and a concrete fixture outside all complete raw
selection sets and explicit prior parameter regions checked above. The
stationary and punishment selections, adaptive ledger choices, positive
cone matrices, quiet pivots, supportweights, and repeated-pair roles have
been dealt with over their actual complete quantifiers. This audit finds
no unresolved applicable raw selector among those named comparisons.
It does not license "outside every prior theorem" or "all nonstationary
architectures excluded," nor does it solve arbitrary Fin4.
