# Scope of the private-menu rotation and the normalized capped exit

Author: CODEX_TARSKI_PREMIUM.

Status: bounded raw-necessity/scope test completed and stopped. The rotating
growth condition is already a known THREE-player principal-matrix condition;
it is not a consequence of the listed FULL-matrix no-UE screens. It does
not by itself force full projective Q-bar either. However BOTH complete
private-menu constructions retained in this pass are covered by the existing
unit-singleton/capped-member consumer after literal single-pivot normalization.
No new UE class, universal obstruction, export, or Lean claim is made.

The paired and sign-regression tables below are not counterexamples to an
implication with a genuine no-UE hypothesis. They only prevent deriving this
particular rotating operation from the explicitly listed necessary data.
The looser collision-sensitive extension is not claimed impossible; it has
no arbitrary-table producer here and is not packaged as a conditional theorem.

## 1. The actual operation and its known three-player matrix content

The starting operation is the explicitly produced private-final-date
construction in
[PRIVATE_FINAL_DATE_EXACT_NASH_AND_ORIGINAL_ERROR](CODEX_TARSKI_PREMIUM__PRIVATE_FINAL_DATE_EXACT_NASH_AND_ORIGINAL_ERROR.md).
The game has independent complete stopping laws, zero Never payoff, and
own singletons s=(1,0,0,0). At a rotating step the nonpivot continuation
has one positive coordinate v at k and zero at the other two players j,l.
Only j may quit in the proposed root, although ALL four players are allowed
to quit in its actual common-row game. If

    r_k({j})=−b<0,       r_l({j})=g>0,

then q_j=v/(b+v) cancels k's Continue payoff and produces

    v'=gv/(b+v)

at l. Its literal root inequalities also require

    r_k({k,j})≤0,       r_l({l,j})≤g,
    (1−q_j)(u_0−1)+q_j[r_0({j})−r_0({0,j})]≥0.        (1)

In particular the collision bounds are not entries of the singleton matrix.
The last inequality is the pivot's actual Continue-minus-Quit comparison.

To rotate through all three nonpivots with strict small-value expansion,
their singleton principal must have a directed three-cycle of opposite
reciprocal signs. The product of its three positive entries must exceed
the absolute product of its three negative entries. Their difference is
the determinant of that zero-diagonal 3×3 matrix.

This is exactly the checked condition
`standardQ_and_noHomogeneous_iff_orientation_and_det_pos`, with its
six-parameter forms `directedCycleMatrix_standardQ_iff` and
`directedCycleMatrix_hasHomogeneous_iff`, in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.
Thus the strict-growth test is standard Q and nonhomogeneous on the
NONPIVOT principal. Its proper one- and two-player principals are projective
Q: a zero singleton matrix has a homogeneous witness, and an opposite-sign
pair has a nonnegative column giving a homogeneous vertex. This gives
projective Q-bar on that three-player principal, not on all four players.

At equality of the products the same source gives a homogeneous principal
witness. Equality is not called failure of every possible slow construction;
it only fails the strict expansion condition being tested. Extending a
principal homogeneous witness by zero does not discharge the omitted pivot's
residual inequality.

The current unconditional consumer
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`
requires projective Q-bar of the FULL normalized singleton matrix. Likewise,
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal` in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`
requires a homogeneous residual nonnegative at EVERY ambient player. Neither
consumer silently drops the pivot from its hypotheses.

## 2. Literal normalization of the solved paired family

Take the original all-unit-singleton table in
[PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION](../exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md).
For pivot p, its actual canonical normalization is

    r^p_i(S)=r_i(S)−1_(i≠p),       S nonempty;
    r^p(Never)=0.                                      (2)

This changes every nonpivot TERMINAL coordinate, including all collisions;
it is not just a matrix relabeling and does not translate Never. For p=0 the
complete transformed table is:

| S | r^0(S) |
| --- | --- |
| 0 | (1,3,−1,−1) |
| 1 | (4,0,−1,−1) |
| 2 | (0,−1,0,3) |
| 3 | (0,−1,3,0) |
| 01 | (c,c−1,0,0) |
| 02 | (c,0,c−1,−1) |
| 03 | (c,−1,0,c−1) |
| 12 | (0,c−1,c−1,0) |
| 13 | (1,c−1,−1,c−1) |
| 23 | (1,0,c−1,c−1) |
| 012 | (1,−1,−1,−1) |
| 013 | (0,0,−1,−1) |
| 023 | (0,−1,−1,0) |
| 123 | (0,−1,0,−1) |
| 0123 | (−1,−2,−2,−2) |

For EVERY pivot choice, the singleton-difference matrix is unchanged:

    Γ=[0 3 −1 −1; 3 0 −1 −1; −1 −1 0 3; −1 −1 3 0].  (3)

Every reciprocal pair has equal signs. No three-player principal therefore
has the rotating directed-cycle orientation, regardless of the private final
owner or a relabeling of the remaining three players. More independently,
for c>1 every nonpivot member of a nonpivot pair is paid c−1>0. A cancelled
coordinate k with C_k=0 can join the actor j for

    Q_k=q_j(c−1)>0.

Thus the specific solo root fails its FULL Nash test even before considering
the pivot. This is an actual omitted joining response, not a matrix proxy.

The known paired matrix has full normal core, is R0 and standard Q with
integer degree +1, and fails projective Q-bar. It has strict negative entries
in every row and column. The standard affine solo/join tests are also
compatible with this failure: for each owner choose a cross-pair recipient,
whose original singleton payoff is zero and pair payoff is c. Its gain at
rate h∈[0,1] is

    (1−h)+hc≥1       for c≥1.

These reward differences are unchanged by (2). Thus those necessary matrix,
column-blocker and affine-gain tests do not produce the rotating screen (1).

The original paired family is solved for every c; its canonical transformed
table is solved as well by the checked forward normalization theorem cited
below. The example therefore does NOT falsify a theorem assuming actual no UE.
It falsifies the reduction from these LISTED necessary conditions alone.

## 3. The asymmetric degree-one sign regression is not repaired by normalization

Use the exact regression in
[DEGREE_ONE_DOES_NOT_FORCE_PAIRED_SINGLETON_SIGNS](CODEX_FRECHET_CYCLE__DEGREE_ONE_DOES_NOT_FORCE_PAIRED_SINGLETON_SIGNS.md).
To give it literal collision data, take the original paired table at c=2
and change only r_0({2}) from 0 to 11/10. Then apply (2), for whichever
pivot is selected. Its unchanged singleton-difference matrix is

    Γ=[0 3 1/10 −1; 3 0 −1 −1; −1 −1 0 3; −1 −1 3 0].

Only the reciprocal pair {0,2} has opposite signs. A rotating three-cycle
requires THREE distinct opposite-sign reciprocal pairs, so no pivot choice
supplies it. Every normalized nonpivot pair-member reward remains 1; hence
the same cancellation-versus-joining contradiction applies.

The source note checks full R0, standard Q, degree +1, full normal core,
full homogeneous infeasibility, and failure of projective Q-bar. Its matrix
properties are cited with that ordinary-math scope. The unchanged negative
columns still provide blockers. For the affine gain test the changed
coordinate is avoidable: for owners 0,1,2,3 choose recipients 2,2,1,0
respectively. Each has original passive singleton zero and pair reward 2,
so the gain is 1+h. No claim of UE or no UE for this particular collision
completion is needed or made.

Exact rational enumeration on both tables checked all four literal
normalizations, all six orders of each nonpivot triple, and every relevant
pair-member coordinate. No favorable phase ordering was selected silently.

## 4. Why failure of full Q-bar is not the whole coverage test

Here is the bounded countercheck to the stronger statement that any successful
private rotation must have full Q-bar. Keep all three nonpivot rows of
VANISH exactly, but replace the pivot's rewards by

    r_0({0})=1;
    r_0(S)=−2                    if 0∈S and |S|≥2;
    r_0({2})=0;
    r_0(S)=2                     otherwise when 0∉S.

This is a complete rational canonical table, not a proposed new class.
Its normalized singleton matrix is

    G=[0 1 −1 1; −1 0 −1 2; −1 2 0 −1; −1 −1 2 0].     (4)

The {0,2} principal is [0,−1;−1,0], which has neither a homogeneous
simplex witness nor an LCP solution for right-hand side (−1,−1). By the
checked standard-or-homogeneous projective split it is not projective Q;
therefore G is not full projective Q-bar.

The same actual private-menu selector still works. Its private final coin
has the same U and d as before. After the two-active correction,

    U=(7/5,4/5,0,0),       d=(1/5,0,0,2/5).

The correction's pivot Quit value is −4/5. In every later rotation its
Continue value stays nonnegative, whereas Quit is

    1−3q≤−1/3,       since q≥4/9.

Thus the full-root inequalities and all four debt contractions remain
valid. The prior error bound follows without a new rate argument. Direct
rational tests at k=0,…,4 checked private Nash and every original pure
deadline/Never response. This only establishes the non-containment in FULL
Q-bar; it does not establish non-containment in every known existence class.

In particular, full homogeneous/R0 failure is NOT an unexamined escape.
Every column of G has a strict negative entry. Its principal determinants
on pairs 01,02,03,12,13,23 are respectively

    1, −1, 1, 2, 2, 2;

on triples 012,013,023,123 they are

    3, −1, −3, 7;

and det G=7. A nonzero homogeneous complementary vector of support size
at least two would be in the kernel of the corresponding nonsingular
principal. A singleton support is excluded by its negative column entry.
Thus G is full R0, so the full homogeneous and supported-normal homogeneous
consumers do not apply. All players are punishment-normal, since all-Never
opponents bound punishment by the nonnegative own singleton; this does not
supply an absent full homogeneous witness.

## 5. The actual existing exit covering BOTH complete constructions

There is a simpler, decisive existing consumer. For a canonical table r
satisfying member caps

    r_0(S)≤1 when 0∈S,
    r_i(S)≤0 when i∈S, i>0,                            (5)

define another ORIGINAL terminal table

    R_i(S)=r_i(S)+1_(i≠0),       R(Never)=0.

All its own singletons are one, and (5) says that every participating
reward is at most one. Hence `QuittingUnitSoloExit R` and
`QuittingCappedJointExit R` hold. The unconditional checked theorem
`exists_uniformEquilibriumPayoff_of_soloExitPreference` supplies a fixed
uniform-equilibrium payoff for R.

Now use the actual checked forward theorem
`isUniformEquilibriumPayoff_singlePivotNormalized_of_original` with pivot 0.
The pivot singleton is one, and the literal normalized terminal table is
exactly r. It follows that r has a fixed UE payoff. This is not a claim
that adding/subtracting one preserves the payoff of every fixed law:
Never stays zero, and the source theorem proves the required actual
low-error transport, including the joint-Never correction. Its forward
direction needs only the positive pivot, not a missing normality assumption.

BOTH VANISH and the modified table in Section 4 satisfy (5), regardless
of their very different full-matrix classifications. Their fully proved
private-menu constructions are therefore already inside this normalized
Solan–Vieille capped-member class. This is the correct coverage stop; full
Q-bar alone would have given the wrong answer for the modified table.

Consequently genuine canonical no UE already excludes (5): some participating
reward must strictly exceed that player's own singleton. This is an immediate
composition of existing consumers, not a new counterexample restriction.
The weaker pair-specific inequalities (1) do not impose (5) on every
coalition, and no claim is made that those weaker fields alone are covered.
Producing a compatible initial root and repeated screened rotations in that
larger region would be new work, not an existing result of this pass.

## 6. Exact source record and final boundary

The named matrix definitions and standard-or-homogeneous split were checked
in `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
The no-UE source is
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`CounterexampleNecessary.lean`. It concerns the NORMAL-CORE matrix;
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in `ThreeCore/AmbientCarrierElimination.lean` identifies that core with
all four players in the present no-UE scope. Together with
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`FourPlayerSingletonColumnBlockers.lean`, these give FULL-matrix conditions;
none asserts the directed sign chamber on an arbitrary three-player deletion.

The literal transformation (2) is
`quittingSinglePivotNormalizedReward` in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`.
The exact unchanged-profile payoff/cap identities, with the Never correction,
are in `Quitting/Punishment/SinglePivotPunishment.lean`.
The forward fixed-target theorem used in Section 5 is in
`Quitting/Punishment/SinglePivotUniformPayoff.lean`.
The unit/capped definitions are in
`Quitting/Classification/SoloExitPreference.lean`; the current unconditional
existence declaration is in
`Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
All these paths are relative to `UniformEquilibrium/` where abbreviated.

The mechanism-scope pass stops here. No all-table source implication was
proved. The listed necessary screens do not force the chosen rotation;
the complete successful constructions are already consumed after actual
normalization; and full-Q-bar containment would have been too strong.
This neither excludes other private calendars nor supplies a new class by
placing an unproduced expansion/screening sequence in a theorem hypothesis.
