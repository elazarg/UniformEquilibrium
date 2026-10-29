# Independent coverage review of the exact opposed-pair path criterion

Reviewer: EXACT_COVERAGE. Ordinary mathematics; no Lean build was run.
Verdict: PASS for new raw-class coverage against the complete selection sets
of the producer families identified below. The full existence proof has
separate independent reviews. No unrestricted exploitability-gap claim is made.

Reviewed packet: `math/exports/EXACT_OPPOSED_PAIR_PATH_UNIFORM_EQUILIBRIUM.md`,
SHA256 `d7f3fdd20419800f8e5150c5e512129a24e97ebdc365645acd68fa8f493967bf`.
Reviewed canonical census and path checker:
`math/experiments/CODEX_COORDINATOR__EXACT_PAIR_PATH_CHECK.py`,
SHA256 `6b9af6036c8e2d9c0e78f136bb9f7cf21268c4d9af5a65454cfa6523498052f5`.
I inspected and reran the final merged source, including the interior-vertex
maximum controls; every check passed. Its census and path sections agree
with the separately inspected author sources. Independent extra calculations
also parsed the literal tables and exhausted the core permutations/scalings;
their argument is reproduced below, so no temporary checker is a dependency.

## 1. Literal input and new membership

I parsed the packet's fifteen table rows independently and verified exact
agreement with the census input. Relative to the previously audited quiet-face
calibration, precisely two of sixty native rewards change:

    Z1(012): 6 -> 33/5,       Z2(012): -11 -> -58/5.

Original rewards are r_i(A)=1+Z_i(A), so all original own levels are1.
All singleton entries, every pair entry, every row0 and row3 entry, and
all passive rewards are unchanged. These facts explain the transfer of the
specific old symbolic certificates below; no continuity assumption is used.

The new raw quantities are s=1/4,c=3,l=12,m=-101,n=7,W=5,X=5/3,
d0=e0=1,d1=e1=8/5, tau=5/32, and all four quiet increments are-1.
The four unbounded-negative-continuation quadratic tests pass exactly.
For y=0, the constant/slope endpoint pairs are

    (-1203/4,-283761/1024), (-2419/5,-283761/640);

for y=5/3 they are

    (-259,-248721/1024), (-25463/60,-248721/640).

The two quadratic vertices lie beyond tau; the two slope polynomials are
affine. All endpoint values are strictly negative. The row0 endpoint gains
9/10 and11 are positive. The triple guards are

    F=268/3, G=295/3, Y=15/67, Bstar=6469/67,
    Delta=6926587/268, a_star=190, last affine endpoint=860/3,

all strictly positive. I reran the exact path checker, including the symbolic
factorization, both active gaps, individual-increment monotonicity, the two
additional boundary controls, and these literal membership calculations.

## 2. Complete stationary and arbitrary-punishment sure-first exclusions

The census passes all80 nonzero stationary patterns in1343 subdivision
nodes and all65 patterns with at least one sure owner in162 nodes. There
are no unresolved boxes or floating-point decisions.

For stationary hazards, F_i=(1-H_i)Q_i-P_i has necessary signs <=0,=0,>=0
for quiet, mixed, sure owners respectively. These are the complete stationary
Quit/Continue comparisons after cancelling the original own shift on absorbing
play. For a sure-first root with any actual punishment continuation, the
native cap floor is L=(-10000,-3,-10,-1000). Indeed the original literal Never
response is a mixture of0 and original passive rewards, so after subtracting
own level1 it is at least min(-1,all passive native rewards). The full cap is
at least that response. The sure owner's necessary inequality is therefore
Q_i-P_i-H_i L_i>=0. Every other owner has H_i=0 because it faces a sure
opponent. Thus its Nash comparisons are exact and independent of punishment.
This includes arbitrary actual punishment tails, not just stationary tails.
The floor is checked for original own levels1 only.

I inspected the rational degree2 tensor Bernstein conversion and midpoint
subdivision, including coefficient rescaling and the strict rejection signs.
A polynomial's range lies in its Bernstein coefficient hull. The zero/free
faces and all hazard boundary patterns are included. Linear combinations
added from inverse principal singleton matrices preserve the mixed equalities.
The no-sure origin exemption is justified by F_S=-Gamma_SS q+R(q), with
||Gamma_SS^(-1)R(q)||<=D||q||^2 on the unit cube. The chosen dyadic radius
is strictly below1/D. Hence a nonzero root cannot lie in an exempt origin box.

Two analytic simplifications remain valid because they use unchanged rows:
q0=0, mixed2 and q1+q3>0 imply Q2>=0>P2, hence F2>0; a sole mixed owner
reduces all quiet tests to q_j J_ij-Gamma_ij<=0. For sole0, quiet1 requires
q0<=2/3 whereas quiet3 requires q0>=3/4. The other sole-owner interval
intersections are empty too. Pure patterns are checked separately.

The origin cannot hide a stationary approximate-equilibrium sequence. Every
singleton column has a negative entry, and every principal singleton matrix
of size>=2 is nonsingular. A zero-hazard limit would give a nonzero
complementary vector x>=0, Gamma x>=0, x_i(Gamma x)_i=0. A support of size>=2
contradicts its principal nonsingularity; a singleton support contradicts the
negative entry in that column. AllNever itself is not original Nash since
own rewards are1. This also excludes the compared vanishing-hazard stationary
producers. Exact stationary-output criteria, including collision-dominance and
signed-column jackpot producers, are excluded by their output guarantee.

## 3. The most recent frozen repair is excluded over all its choices

Only owner0 has every participant reward nonpositive, so it must be the
anchor in any labeling of the frozen quiet-face criterion. I independently
enumerated all24 permutations and additionally allowed positive recipient
scalings of the fixed numerical core. The sole match is the identity labeling,
with scales1 on rows1,2,3. One can see this without enumeration: among123,
only actual row2 has both off-own singleton entries negative, so it must
fill role2. Swapping roles1 and3 would invert its absolute singleton ratio
2 to1/2, impossible under positive row scaling. Identity then fixes each
recipient scale at1 from its nonzero prescribed singleton entries. Thus
its free scalar must satisfy f<=1 because
all four row3 increments are-1. At the legitimate old CVX corner
(v1,v2,alpha)=(0,0,5/32), the exact expression is

    -21/5+(57/32)f <= -387/160 <0.

This excludes EVERY permissible f, not a particular scalar choice. The old
all-real-a cylinder also fails its unit-gain equalities d1=e1=1. Its outer
parameter cases do not apply: the unchanged core has a=1/4,p=1.
This is a strict accepted-producer coverage increment. The uncommitted
arbitrary-core curvature draft is not treated as an accepted result; it may
cover this particular witness. The new four-increment comparison's stronger
mathematical scope is separately demonstrated by the packet's positive-delta
control, for which every common scalar bound fails.

## 4. All other compared selectors survive the two-entry change

I read the earlier complete coverage review, checked which coordinates each
certificate uses, and reran every displayed exact certificate on the NEW table.
The comparison includes complete existential choices, as follows.

- Return and reset roles. All24 joint/solo-return role assignments satisfy the
  weak common sign requirements only at(0,1,2,3). There K=-Z1(12)=-1/4, failing
  the positive K premise of finite-singleton split, core-free joint return,
  and three-owner joint return; eta=Z2(02)-Gamma20=-1 independently defeats
  the direct positive-return branch. All12 oriented reset macros fail their
  two required improved joining comparisons. Only pair12 has both participant
  rewards positive; its joining gaps(-1/4,3) make one active continuation
  negative in either orientation, excluding the positive-continuation variant
  for both outside owners. The raw02-to-023 recovery can only anchor at0;
  its only positive anchor joining gain is toward2, whose reciprocal gain-1
  fails. These exclusions use unchanged singleton/pair data.

- Earlier passive and index criteria. The participant-capped anchor is only0.
  Every remaining owner has a strictly positive pair reward in123, defeating
  all passive-threshold labels. Its negative-K subregion requires p bounded
  by a nonpositive quantity, whereas p=1. The abstract passive-bound signs
  J13<0,J32<0,J31>0 admit only the identity labeling: BLOCK fails J12>0,
  and INDEX fails the opposed pair c12=-1/4 with both J12,J21>0.

- Participant and marked selections. Triple123 has all participant rewards
  strictly positive and is the greatest premium core. Every coalition with0
  fails a strict participant-premium condition in row0. Thus the signed-pair
  core source fails its cardinality2 requirement. The triple joining products
  are negative on12,13,23, excluding the joining-attractive and compared
  mixed-sign triple sources; the mixed-premium pair condition also fails12.
  Every ordered calendar or participant-block criterion first meeting123 has
  a positive participant sum for every positive weight. The positive singleton
  graph is strongly connected, forcing every predecessor-closed marked set
  to be all4; its first block meeting123 fails in the same way.
  For all15 coordinate-minimum invariant candidates, the unchanged exact
  small-root controls produce strictly positive marked output from a marked
  nonpositive input inside the passive box. These are virtual-continuation
  countercontrols, not actual-source or no-UE claims.

- All14 proper withdrawal children. In the relaxed future/join inequalities,
  each child has a single row with positive left side and all nonpositive
  coefficients of every nonnegative lambda,mu. These cover patient, deadline,
  evaluated-security, terminal-security, cancellation and advancing-only
  variants, with singleton withdrawal gains relaxed to0 and future gains to
  positive parts. The rows use only singleton coalitions or123 and their
  joins/withdrawals; neither changed012 recipient entry occurs. Every old
  child dual therefore remains literally identical. No compared child lift
  can begin, for ANY weights or ordering of child choices.

- Universal weight criteria. The exact coefficient vectors remain
  H12+H1+H3=(-6,-11/4,-2,-8) and
  -(J12+J13+J23)=(-19,-2,-3,-7). For forced-Quit floors the sole change is
  k(01)+k(2)+k(3)=(-10201/10,-387/4,-43/5,-102), still strictly negative
  coordinatewise. Thus every nonzero nonnegative weight, and every finite
  menu of such weights, fails the respective full-proper-payoff, universal
  joining, or forced-Quit-floor premise. This includes the marked-support
  orientation, support-filtered and same-sign pair ledger variants under
  their stated raw premises.

- Singleton magnitude and matrix choices. Gamma is unchanged, with determinant
  53/2 and all principal determinants of size>=2 nonzero. Only triple023 has
  nonnegative inverse; its outside inverse row(-23/24,1/8,-11/24) excludes
  the passive-inverse extension. The full inverse has a negative entry and
  a mixed-sign column2, defeating the compared all-column inverse choices.
  All24 exact-reference permutations and positive recipient scales fail;
  the unique eight-sign chamber orientation has B1=-11/42<0. The unique
  attached-negative-pair role is(3,1,0,2); Z1(13)=-100 and Gamma21=-2 defeat
  its two respective premium variants. The sole positive reciprocal pair01
  and negative pair13 intersect. Opposite-sign degree at vertex1 is one,
  so no opposite-sign Hamiltonian cycle exists. All three matching choices
  fail at unchanged joining increments-23,-97,-1003. Only two distinct
  recipients have eligible scalar singular-circuit pairs. These tests exhaust
  the named matrix, role, matching, reference and circuit selections.

## 5. Source audit and scope

I inspected the raw statement and relevant proof clauses of the two frozen
passive/quiet-face packets, `THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`
(including its complete sure-first and withdrawal comparisons),
`PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md`,
`SUPPORT_FILTERED_WEIGHTED_LEDGERS_UNIFORM_EQUILIBRIUM.md`,
`SAME_SIGN_PAIR_LEDGER_UNIFORM_EQUILIBRIUM.md`, and
`WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md`.
Also inspected the conditional Lean declarations
`exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives`
(`UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`) and
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn`
(`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`).
Those conditional interfaces do not themselves produce the missing raw return.
The earlier detailed coverage record supplies the named selector inventory;
its table-dependent exclusions were independently re-evaluated here.

The new theorem assumes only finite raw reward conditions and produces its
strategic witnesses internally. No strategy or continuation is an unproduced
premise. Subject to the separate full-proof reviews, the exact separating
literal table supports promotion as a new UE class. It does not support a
coverage percentage, arbitrary Fin4 closure, a claim about every unknown
qualitative neighborhood of other theorems, or an all-behavior positive gap.
Only the displayed original-own-level1 table received the complete census.
The two additional boundary controls verify theorem scope, not separate
complete prior-producer coverage.
