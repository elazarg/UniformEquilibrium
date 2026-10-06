# Independent review of the below-floor matching producer

Identity: CODEX_NOETHER. Ordinary mathematics; no new Lean claim.

Status: **accepted, with no unresolved mathematical objection.** The tested
surface is §29, from “A negative scheduled-premium arm of the matching
two-phase producer” through EOF, in
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, at whole-file SHA256

    84cf88f403ed0004abc2c7bf107f0d9b8e5b4b5312a9ef14da9ebdbafedc31d9

I read all of that surface, independently recomputed its exact finite data,
and attempted to falsify the root, strategy and coverage implications.
Sections 1–28 are not covered by this verdict. No other conference review
was read. I did not export, edit Lean, compile, stage, commit or push.

## Exact claim checked

Four players independently Continue/Quit at simultaneous live dates, with
public histories, zero live-stage and Never rewards, and fifteen finite
signed terminal reward vectors. Unilateral deviations replace any entire
behavioral strategy. Let f=(01)(23), a=(02)(13), and o=f∘a. Own levels
s_i are arbitrary signed reals, b_i>0, and H>2. The singleton gaps are
Hb_i at f(i) and−b_i at a(i),o(i). Both scheduled-pair participant
increments are Πb_i and passive increments Kb_i, where

    Π<−1,       K<(7Π+10−2H)/2.

The twelve cross-pair/triple joining rewards are at most
s_i−4(−Π−1)b_i/3; all other entries are free. The claim produces one
proper period-two exact terminal Nash profile and one fixed uniform target,
with the same profile at every accuracy. A separate claim gives a full
sixty-coordinate neighborhood of its H=3,Π=−11/10,K=−179/60 table,
using actual four-odds equations rather than normalized equalities.

## Valid root and original-game steps

The cubic P has P(1/2)<0 and P(1)=H−2>0, so a root t∈(1/2,1)
exists. A root below1/2 is neither selected nor needed. Set q=1−t.
The displayed U_i=s_i+qΠb_i and W_i=s_i+q(Π+1)b_i/t exactly solve
both active endpoints and the passive Continue identity. W_i<s_i is
intentional. Against the stronger caps its passive advantage is at least

    q b_i[(1+t)4(−Π−1)/3−(−Π−1)/t]>0,

because t(1+t)>3/4. Every simultaneous unilateral coalition is included.
The large100 entries belong to the other scheduled members at their triple,
not to the unilateral deviator; the grand coalition is unreachable under one
deviation. No terminal entry was incorrectly omitted or translated away.

Joint survival t⁴ realizes the two vectors by bounded policy iteration even
for signed values. Opponent-deleted survival t³ removes the bounded remainder
under every behavioral deviation, including Never, randomized histories and
arbitrarily late stopping. The finite-horizon error2M[1+2/(1−t³)]/N
and regret twice that are valid. The target is selected before accuracy;
the same original-game profile works for every sufficiently large horizon.

I rechecked the exact signatures of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Their
policy, root-Nash and deleted-opponent contraction inputs are all produced.
The direct proof also gives the full semantic result. No no-UE-to-Q
hypothesis, sign assumption on own rewards, or supplied strategic certificate
is needed for this below-floor producer.

## Exact fixture, Jacobian and neighborhood

Independent rational arithmetic confirms every one of the sixteen endpoints:
active Quit and Continue19/30; passive Continue19/20; passive Quit1/3;
margin37/60. The actual equations E vanish at X=(1/2)1. The displayed
Jacobian is correct, with eigenvalues79/72,−307/72,−41/72,269/72 and
determinant267486337/26873856. It is nonsingular without a supplied
implicit-function premise.

For T_r(X)=X−J⁻¹E(X,r), the derivative at the center is zero. Continuity
on a compact positive ball gives a uniform derivative norm at most1/2 for
nearby reward tables; shrinking that neighborhood also makes center movement
at most half the radius. This is a self-map and contraction on a complete
ball. Its iterations produce a unique root there, approaching the center
root continuously. All hazards remain proper and all four actual passive
gaps stay strict. This proves a genuine full reward-space UE neighborhood;
it imposes no singleton, pair or cap equality nearby. Global root uniqueness
or strategy-class completeness is not asserted.

The proper-three exclusion is correct. Its player2 equation forces
0<x<1/1001 and10/11<a<1. The displayed F and ∂_aF recompute exactly;
concavity gives ∂_aF>0, and F(10/11,c) has minimum29/33. Thus Never
strictly dominates Quit for player1 in every prospective support012 profile.
Klein permutations handle all four supports. No full-support or sure-boundary
stationary nonexistence follows.

This exclusion is robust. For a reward perturbation δ≤1/1000, player2
gives |1−(11/10)a−x/2+(503/5)ax|≤2δ. It forces x<11/1006 and
a>9/10. The same derivative argument gives

    F≥F(9/10,c)=(64c²−512c+621)/200≥173/200.

Since D≤1, the center Never-minus-Quit gap is at least173/200. Perturbing
each endpoint by at most δ leaves it positive. A smaller full reward
neighborhood thus excludes the actual proper-three local source
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.

## Actual raw coverage, not another conditional interface

The accepted arbitrary-K theorem in
`exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md` does not cover this fixture.
Favorite signs force f under every relabeling. Scheduled02/13 fails
participant comparison−1/10≥0; scheduled03/12 has participant comparison
but outsider triple reward100>1, violating its actual caps. Both failures
have strict slack and persist under small perturbations and positive affine
row transports. All pair premiums are negative, so no partition meets the
separate Π≥0 inverse criterion. Its pure-pair arm also fails: every pure
coalition has an explicit profitable deviation.

I confirmed that the only premium trap is the full set. Greatest-core
two/three criteria do not apply. Forced Quit at hazard(1/10)1 is
(24739,24729,24719,24709)/10000, violating product-low and supportwise
nonpositive premium balance. Negative grand premiums exclude every protected
player and every nonzero nonnegative weighted forced-Quit floor. At T=01,
the boxed/mixed-trap insertion sum198>0 violates their actual intermediate
charge condition. Singleton terminal tests force Γᵀλ≤0 for a nonnegative
weighted terminal upper bound, but row sum1 forces λ=0. This contradicts
the hypotheses of `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.

The full Γ has determinant45, positive inverse and R₀ degree+1, not the
negative-determinant inverse exit. Harmful principal pairs are not Q or
homogeneous admissible; all triple inverse diagonals are−1/6. I inspected
the exact hypotheses of `r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`),
and `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).
These are failures of named sufficient conditions, not claims of nonexistence.

Every proper child also fails the actual accepted nonnegative quiet F/J
criterion, not merely a supplied-child verifier. If S cuts an o-pair,
choose j∈S,k=o(j)∉S and A={j}. Outsider join gain is1/2; child joining
gains are0,−7/2,−1/10, so no nonnegative weights satisfy J. If S cuts
neither o-pair, S=03 or12, and at A=S any outsider gains100 while all
child joining gains are zero. This excludes every child in
`exports/NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md`. The exact Nash,
zero-Never child witnesses additionally falsify universal debt-plus-Never
families, including the exact consumer
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`).
It does not imply that every separately chosen quiet-child profile is unsafe.

The quotient, singleton sign, crossed weak polynomial/one-sided guard,
conditional range and visible affine period-three comparisons are valid.
The actual range definition `IsQuittingConditionalFaceGapRange`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`)
requires ContinueUpper≥4 while its lower Quit mixture is at most1, for
every blocker. The exact center `overlappingPeriodThreeRewardRow` and
`IsInvisibleRewardCoordinate` in their named cyclic example files confirm
that all participant pair coordinates are visible and center at own level1;
their normalized gap is tiny in that cylinder but at least1/2 here, under
every relabeling and positive affine row transport.

Two additional raw screens fail strictly: influence1→0 is−9/2 at∅ but
1001/10 at{2}. This contradicts `SignConsistentQuittingInfluence`
(`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`)
and `IsAffineQuittingMembershipGain`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`).
It excludes their raw potential/influence branches and persists nearby.

## Scope and handoff

The proof passes the substantive gate: it removes a previously surviving
open original-table neighborhood beyond the strongest accepted matching
criterion and compared actual raw producers. It does not merely verify an
externally supplied root. It does not settle arbitrary Fin4 or assert
absence of all stationary, periodic or selected-child equilibria. No new
L/A/C seal is justified. The math-unicode skill affects notation only.

A future standalone packet must include the complete original-game proof
and named-source coverage, and receive its own byte-bound assembly verdict.
The current §29 mathematical candidate is accepted at the hash above.

## Separate final standalone verdict

**Accepted for mathematical export, with no unresolved objection.** The
separately tested artifact is the complete 660-line file
`exports/BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md`, SHA256

    6b75ada2ad8e675fd32216d0f1d98fbfdfee6ef5a47d0b7ca8aed05eb2d0e3ca

I read the entire standalone and checked its assembly against the accepted
§29 proof and independent coverage strengthenings above. It includes the
raw-family scalar producer, all sixteen endpoints, actual signed terminal
values, all behavioral/Never deviations, one fixed target and all-large-
horizon bounds, and the separate full-coordinate contraction theorem. No
root, continuity certificate or strategic object remains an unproduced input.
The full mixed-strategy raw coverage evidence, direct quiet joining rows,
influence/potential failures and robust proper-three exclusion are present.

The simplified robustness argument is correct: for a≤9/10, the center
Q₂* affine in x has both endpoints at least1/100, contradicting
|Q₂*|≤2/1000. This directly supplies the same a>9/10 bound as the
independent derivation. The proof still asserts neither full-support nor
sure-boundary stationary nonexistence.

I separately checked the new wrong-root boundary. Its cubic factorization
is exact, the second proper root lies below1/20, its formal W<−9/10
while actual passive Quit>13/15, so it fails Nash. The selected2/3 root
instead has passive Quit25/27 and gap13/540. This valid falsifier prevents
inflating the raw theorem to arbitrary cubic-root selection.

The scalar equality-stratum family and the one full-coordinate neighborhood
remain distinct conclusions. The packet gives real new UE coverage beyond
the accepted arbitrary-K matching class, not a supplied-certificate interface.
New content remains ordinary mathematics and carries no new L/A/C assertion.
This is the independent final mathematical acceptance of these exact bytes.
