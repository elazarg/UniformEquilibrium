# Independent review of the two-player premium core

Reviewer: CODEX_KREIN. Scope: Section 10, **A two-player premium core with
a strict preference to leave the pair**, in
`../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. No other review
of that section was read before this assessment. Ordinary mathematics;
no Lean build was run.

## Verdict and exact scope

**PASS for the analytic theorem and its four-player uniform-equilibrium
consequence, with no unresolved mathematical objection.** The proof treats
the full simultaneous root game and all coalition rewards. It does not
silently restrict root supports to the two core players. The semantic
consumer has the stated normality and positive-singleton hypotheses, and
the proof supplies them, treating the all-zero-singleton case separately.

The raw hypothesis is: every participant reward is at least its singleton;
all players outside a specified pair have constant participant rewards;
and one member of that pair strictly prefers the other singleton outcome
to the joint pair outcome. The analytic exclusion permits signed
singletons in every finite player set. The UE conclusion here is for four
players with nonnegative singletons. No strategy-class completeness or
general finite-player existence conclusion is inferred.

The earlier test table in the source note already has a safe-spectator
consumer, as the author states. Below I give a different complete rational
table in the new class that avoids the named product-low, proper-child F/J,
homogeneous, degree, inverse, and response-quotient screens. This supports
the intended implemented-scope increment without claiming that every
possible repository producer has been classified.

## Full-root return and the boundary derivative

For an exact root, every successor coordinate dominates its forced-Quit
endpoint, hence its singleton by nonnegative participant premiums. The
successor stays in the same box because it is a convex combination of the
source annotation and actual reward vectors.

If ANY constant-participant outsider is active, supported Quit identifies
its successor coordinate with its singleton, regardless of the other
hazards or the core's triple and grand-coalition premiums. This already
returns to the stated lower boundary L. Only after all outsider hazards
are zero may one use the two-player gap

    (1−q_j)(s_i−v_i)+q_j[r_i({i,j})−r_i({j})].

When both core hazards are positive, the gap is strictly negative under
the stated source floor v_i≥s_i, contradicting supported Quit. Positive
absorption therefore leaves exactly one active core player and again a
successor coordinate equal to its singleton. The full-root split is
exhaustive. The other core floor is retained for the later perturbation;
the algebra does not drop a positive outsider hazard.

At a singleton face with all other coordinates strictly above their
singletons, a sufficiently small sole-owner rate is an actual exact Nash
root. The nonowner gap at rate zero is strictly negative, and all endpoint
comparisons depend continuously on the rate, including actual pair
rewards. The potential inequality along the resulting successor segment
gives

    gradient H(x) · (x−r({k})) ≥ 1.

Moving the other coordinates toward B creates strict inequalities while
remaining inside the same box and preserving the owner coordinate.
Continuity of the gradient gives the weak-face conclusion. This does not
require a uniform admissible rate at a multiple-face intersection.

The exact source declaration
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
was inspected. Its hypotheses and derivative direction agree with this
argument, including the strict outer-box margin B>M.

## Binding coordinates and the selective perturbation

At a minimizer of H over compact L, a single binding coordinate is
impossible: the sole-owner root has positive absorption, remains in L by
the return property, and would lower H.

With at least two binding coordinates, increasing one retains another
binding coordinate, so its gradient coordinate is nonnegative. A
nonbinding interior coordinate has zero gradient. An upper-box coordinate
has nonpositive gradient, since decreasing it is feasible. These are
correct one-sided conditions for this union of lower faces; they do not
assume that L is convex.

If only the two core coordinates bind, apply the face derivative with
owner j. The i contribution is nonpositive because
r_i({j})>r_i({i,j})≥s_i. The owner contribution is zero; nonbinding
interior contributions vanish; and every upper-box contribution is
nonpositive because B−r_k({j})>0. This contradicts the lower bound one.
Thus at least one constant-participant outsider binds.

Lowering exactly those binding outsiders by epsilon leaves the two core
annotations untouched. This is the decisive preservation step: the new
annotation can be below some singleton floors and still lies in the source
region where the full-root return was proved. The directional potential
increment divided by epsilon tends to a nonpositive number.

Finite Nash existence at that annotation supplies an actual product root.
All-Continue is not Nash, because each lowered outsider can gain epsilon
by quitting alone. Every selected root therefore absorbs positively and
returns to the original L. Its lowered outsider coordinate moves upward
by at least epsilon. Since

    |T_q(v)_k−v_k|≤(M+B)*a(q),

its charge is at least epsilon/(M+B). Combining charge drift with
minimality on L forces a strictly positive lower bound on the same
directional quotient, contradicting its nonpositive limit. No continuous
root selection, returned strategy, or accumulated charge assumption is
needed. Upper-box coordinates and ties among binding faces are all covered.

## Actual semantic endpoint

I inspected the following declarations and their stated hypotheses:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`;
- `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.

Nonnegative singletons and premiums give punishment values exactly equal
to singletons, hence all players normal. If some singleton is positive,
the no-UE hypothesis produces a rational polynomial potential on the
full robust relation in box M+2. The last declaration restricts that SAME
potential to every boxed exact Nash root, with unchanged unit absorption
charge. Its differentiability is automatic. The analytic contradiction
therefore applies. If every singleton is zero, all-Never directly gives
the required equilibrium. The argument does not assume away the sure-root
alternative or substitute a bounded deviation class.

No strategic input remains unproduced: the finite root theorem and the
no-UE polynomial producer are established source inputs, and the new
boundary argument contradicts their exact output under the raw conditions.
This is a classical existence proof; it does not purport to compute a
particular terminal strategy from the minimizer.

## A new exact implementation-overlap witness

For every nonempty S⊆{0,1,2,3}, first define

    r_0(S)=1 if 0∈S, and 4*1_(3∈S) otherwise;
    r_j(S)=0 if j∈S,
           −1 if j∉S and 0∈S,
           2*1_(pred(j)∈S)−1_(succ(j)∈S) otherwise,

where the nonpivot cycle is 1→2→3→1. Change only two coordinates:

    r_0({0,3})=2,             r_3({0,3})=1.              (A)

This completely specifies the table. Take the premium core to be {0,3},
with designated player i=0. Its own singleton vector is (1,0,0,0).
Every participant premium is nonnegative, players 1 and 2 have constant
participant rewards, and r_0({0,3})=2<4=r_0({3}). Thus it satisfies
the theorem literally. At hazards q_0=q_3=1/2, both active premiums are
1/2>0, refuting product-low directly.

Its singleton matrix is

    [[0,−1,−1,3],
     [−1,0,−1,2],
     [−1,2,0,−1],
     [−1,−1,2,0]].                                      (B)

Every row has a distinct negative witness, so its normal core is full.
It has no nonzero homogeneous LCP solution: positive pivot coordinate
forces all child coordinates positive, then all equal to the pivot
coordinate, which leaves a positive pivot residual; zero pivot coordinate
and a positive child force every child positive, contradicting invertibility
of the child matrix. At offset (1,−1,−1,−1), the unique LCP solution is
(0,1,1,1). Its inactive pivot residual is 2 and its active determinant
is 7. Thus the inspected R0-degree root-sum criterion gives degree +1,
and nonzero degree gives standard Q. This is neither a non-Q nor a
nonunit-degree example.

The {0,1} principal has two negative off-diagonal entries: it is neither
standard Q nor homogeneous-feasible. The pivot inverse row on the cyclic
three-child matrix has middle entry −3/7. Every other triple has a row
with both off-diagonal entries negative, excluding a nonnegative inverse.
The full inverse has entry (0,1)=−9/7<0. These are direct failures of
the named projective-Q-bar and nonnegative-inverse/passive-row screens.

There is no nondiscrete response-invariant partition. The necessary block
row-sum condition excludes all six single-pair merges, all three pair-pair
partitions, all three triples containing 0, and the one-block partition:
the last has pivot row sum 1 versus child row sums zero. The sole
first-order survivor is {0}|{1,2,3}. At pivot hazard x>0 and zero common
child hazard its individual residuals are

    F_1=F_2=x,                F_3=x+x²,

using (A), so actual response invariance fails. This checks partitions
not induced by reward automorphisms as well as orbit partitions.

Every proper-child F/J family also fails. Here are all cases, each with
zero child regret and joint Never zero:

1. For one or two nonpivot children, choose a sure solo owner giving the
   other retained child payoff 2 when needed. A missing nonpivot gets
   −1 and joins for zero.
2. For all three nonpivots, repeat solo hazards 1/2 in order 1,2,3. Its
   three entry vectors are (0,1,0), (0,0,1), (1,0,0). These satisfy
   exact Bellman and action comparisons; opponent survival contracts
   every period, so full behavioral regret is zero. The quiet pivot gets
   4/7 and can quit at the first phase for one.
3. If the child contains 0 but not 3, every child quits surely at the
   first date. No changed coordinate in (A) is used. The pivot and each
   nonpivot prefer their prescribed Quit action. A missing nonpivot gets
   −1 and has a strictly better joining payoff (zero, or one for the
   special pair {0,3}).
4. If the child contains {0,3} but not 2, child 3 alone quits surely.
   The pivot gets 4 rather than the pair's 2; retained player 1 gets 2;
   owner 3 gets zero and is indifferent to Never. Missing player 2 gets
   −1 and joins for zero.
5. For child {0,2,3}, child 2 quits surely, pivot 0 uses hazard 2/3,
   and child 3 uses hazard 1/4, at the first date. Every realized coalition
   contains 2, so (A) is irrelevant. Pivot and child 3 are indifferent;
   child 2's Continue payoff is −3/4 versus Quit payoff zero. Omitted
   player 1 receives −5/6 and joins for zero.

These exhaust all fourteen proper nonempty children. The universal
five-kind bound in
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`)
would bound positive outside debt by zero on each corresponding witness.
Thus no choices of its nonnegative weights repair any proper-child
family for this table.

The degree declarations used above are
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. The quotient necessary condition
is `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
the exact residual uses `quittingDiscountedDisplacement` at zero in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
These sources were inspected in this conference session.

The positive singleton comparison graph of (B) has one positive
off-diagonal entry in every row and no reciprocal positive pair. It also
does not satisfy the two-positive-nonpartner condition of the inspected
paired-cycle producer. No symmetry quotient is being silently assumed.

This witness supplies a concrete check that the theorem is not merely
recovering the particular safe-spectator example in the source note, nor
the named implementation gates above. The non-overlap statement remains
bounded to those precise gates. My mathematical PASS does not require an
unsupported assertion that no other proof of this same table could exist.
