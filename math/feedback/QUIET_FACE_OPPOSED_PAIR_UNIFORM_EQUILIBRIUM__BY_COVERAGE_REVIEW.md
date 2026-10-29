# Complete prior-producer coverage review of the quiet-face calibration

INVARIANT_GEOMETRY, incorporating the independently reconstructed exact
withdrawal, weight and matrix audit by TRIPLE_CROSSINGS. Ordinary mathematics,
not Lean checked. Verdict: PASS for the explicitly compared producer scopes.
The existence proof for the new raw criterion has a separate mathematical
review; the exclusions below are not premises in that proof.

Reviewed packet:
`math/exports/QUIET_FACE_OPPOSED_PAIR_UNIFORM_EQUILIBRIUM.md`, SHA256
`8fc808db2c7a6e06439719b0d36d71a1002c30d12c2244a78a0d7486c2c7966c`.
Its literal table agrees exactly with the checked table. The main raw class
uses four independent joining increments d0>=0, d1>0, e0,e1>=0, eight
explicit convexity corners, four row3 upper bounds and a scalar endpoint
bound. It imposes no equalities between the two d increments or between
the two e increments. For a fixed reward table, the allowed scalar f is
exactly the intersection of fourteen affine inequalities: four row3 bounds,
eight corners and the two endpoint tests at v2=0,W. Zero affine coefficients
are handled as constant tests; this is a finite interval calculation.

The all-real-a, p>=0 corollary retains the constant increments
d0=d1=e0=e1=1 and row3 increments at most -1. There is no passive row3
cap. The main theorem permits W<=5(p+2), weak row0 joining gains and
e1*tau<=c; the endpoint can then be a sure-owner good root. The literal
witness has strict row0 and hazard guards. These generalizations do not
change any prior-producer comparison below.

The complete literal sixty-entry table is the `rows` dictionary of
`math/experiments/CODEX_COORDINATOR__QUIET_FACE_COVERAGE_CHECK.py`;
original own levels are all 1. It has fixed core a=1/4, p=1,
d0=d1=e0=e1=1, row3 joining increments -1, W2=5, R3=1, and row0 joining
gains 9/10 at 2 and 11 at 12. With f=1, all eight convexity corners equal
36 and the endpoint bound is -243. Thus the generalized raw theorem accepts
the unchanged separating table.

The additional unequal-increment control changes only Z1(012)=6 to 601/100.
It has d0=1, d1=101/100, e0=e1=1 and tau=25/101. For f=1 the eight corner
values are 3531/100 and 884/25, each repeated four times, with endpoint
bound -24568/101. For f=1/2 they are 7059/200 and 883/25, each repeated
four times, with endpoint bound -24468/101. Every remaining raw guard is
checked from this perturbed table. For f=1/2 all four row3 bounds and every
other nonstructural guard are strict, giving an open neighborhood in the
free completion coordinates with the core fixed. This does not remove the
fixed-core restrictions. The prior-producer exclusions below concern the
unchanged separating table; the perturbation certifies generalized raw
membership and is not silently substituted into those censuses.

The canonical exact checker is
`math/experiments/CODEX_COORDINATOR__QUIET_FACE_COVERAGE_CHECK.py`, SHA256
`0bfda0fb7355c124e40a30484efb733ce37a59a0af7af252383b174a63298c59`.
It retains one literal rational table and all census, return, invariant,
withdrawal, weight and matrix checks, together with symbolic repair-path
identities. The unequal-face extension verifies both active indifferences,
the exact hazard derivatives, cubic curvature and endpoint formulas, clip
domination, the constant-case value 36de, and both sets of eight perturbed
corners. It copies the literal table and checks that the original is
unchanged. I inspected the exact concatenation of the previously reviewed
checker and this independently reviewed extension, then reran the merged
source: every check passes. The legacy certificates were also reconstructed
independently by TRIPLE_CROSSINGS before inclusion in this single checker.

The census closes all80 stationary patterns in1495 subdivision nodes and
all65 sure-first patterns in186 nodes, using the actual-cap lower bound
L=(-10000,-3,-10,-1000). No floating-point decision or unresolved box is
accepted. Every table-dependent shortcut and every old certificate below
is recomputed from this literal table.

## 1. Exact census scope and analytic boundary checks

The checker uses F_i=(1-H_i)Q_i-P_i for stationary patterns and
G_i=Q_i-P_i-H_i L_i for sure-first necessary conditions. The latter follow
from every actual original punishment cap being at least its native
own-Never payoff, hence at least L_i after subtracting own level1. With
another sure owner H_i=0; for the unique sure owner this lower bound only
weakens the required Quit inequality. Thus arbitrary actual punishment tails
are included in the exclusion, not just fixed or stationary tails.

The exact degree2 Bernstein bounds and midpoint subdivision are the method
retained in `math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`,
Section6.1. For no-sure supports S of size>=2 the checker proves the origin
bound from F_S=-Gamma_SS q+O(||q||^2), using literal coefficient sums and the
exact inverse Gamma_SS. All relevant principal matrices are nonsingular.

The two analytic boundary simplifications are re-proved for this table.
If q0=0, q2 is mixed and q1+q3>0, then
Q2=q1(1-q3)+q3(3-q1)>=0 and P2=-2q1(1-q3)-q3<0, so F2>0.
On a sole mixed-owner face j, quiet i requires q_j J_ij-Gamma_ij<=0.
The checker intersects all these exact affine intervals with0<q_j<1.
For j=0, row1 requires q0<=2/3 while row3 requires q0>=3/4. The other
owners also have empty intersections. Pure faces are checked separately.
No old negative-column shortcut is silently imported.

Every singleton column has a negative entry, and every principal matrix of
size>=2 is nonsingular. Thus stationary approximate equilibria cannot
converge to the zero-hazard profile: normalized Quit and Never comparisons
would produce a nonzero complementary singleton vector, excluded support by
support. AllNever itself fails for original own levels1. Consequently the
census excludes stationary-output raw producers and every sure-first
producer within the stated actual-punishment semantics. It is not an
unrestricted behavioral exploitability gap.

## 2. Return and reset roles

For a joint/solo-return role assignment(a,b,c,d), even the signed three-owner
version requires

 Gamma_ad>0, Gamma_cd<0, Gamma_bd<0,
 -Z_b(bd)>-Gamma_bd, Z_c(cd)>0.

These are weaker than its full raw conditions: no sign on beta,e,f is
imposed here. Exhausting all24 assignments leaves ONLY(0,1,2,3). At this
assignment K=-Z1(12)=-1/4. The finite-singleton split and the direct, signed
and joint return producers require positive K (the explicit joint thresholds
are at least1). Hence every role fails before any root or asymptotic
threshold selection. Also eta=Z2(02)-Gamma20=-1, excluding the direct
positive-return branch independently.

This comparison includes
`FINITE_SINGLETON_SPLIT_UNIFORM_EQUILIBRIUM.md`,
`CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md` and
`THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md` in `math/exports/`.
It does not infer an exclusion by evaluating an unspecified large-K bound.

The newer quadratic two-pair reset requires an oriented macro pair(i,j) with
Z_i(ij)<0, Z_i(ij)>Gamma_ij, Z_j(ij)>0 and Z_j(ij)>Gamma_ji.
All twelve orientations fail. In particular02 has improved negative row0
but row2 joining gap-1;21 has improved positive row2 but row1 gap-1/4.
The exact checker tests all orientations, so no reset role is omitted.

Only pair12 has both participant rewards positive. The positive-continuation
variant in Section2 of
`math/notes/CODEX_COORDINATOR__COMPLETE_SOLO_RETURN_GEOMETRY.md` additionally
requires both active continuations in(P2) positive. Its exact formulas are
b*(J_ij-Gamma_ij)/(1-b) and x*(J_ji-Gamma_ji)/(1-x). The joining gaps of12
are(-1/4,3), so one required continuation is strictly negative in either
orientation, for every proper hazard choice. Both outside choices0 and3 are
therefore excluded before their cubic or scalar-return selection.

The raw02-to-023 recovery lemma in the canonical bounded-crossing note also
fails under every role with a nonpositive-participant anchor. Only0 can be
that anchor. Its joining gaps toward1,2,3 are -23,9/10,-1003. Only pair02
has positive anchor gap, but its mate gap is-1; the lemma requires both
strictly positive. Its specific positive-eta specialization fails as well.

## 3. All marked coordinate-minimum invariants fail

The safe-positive directed edges j->i require Gamma_ij>0 and J_ij<=Gamma_ij.
They include

    0->2, 2->1, 1->0, 2->3, 3->0,

a strongly connected graph. Every nonempty proper marked C has an entering
edge j outside C,i inside C. For small epsilon>0 set q_j=epsilon, all other
hazards0, v_j=v_i=0, and

 v_k=epsilon(1+|Gamma_kj|+|Z_k(kj)|) for k outside{i,j}.

This is exact Nash, min_C v=0, and every output in C is positive. The
anchored comparison is Gamma_ij>=J_ij; the other quiet comparisons and
outputs have strict first-order margins.

For the full marked set use

 q=(0,epsilon,epsilon,0),
 v=(0,-epsilon/[4(1-epsilon)],3epsilon/(1-epsilon),2epsilon).

The active equations are exact. The output is

 (2epsilon-14epsilon^2, epsilon/4, epsilon,
  epsilon-9epsilon^2+2epsilon^3)>>0

for sufficiently small epsilon. The quiet0 Quit offer is
-201epsilon/10+191epsilon^2/10<0; quiet3's is
-90epsilon+91epsilon^2<0. The input has v1<0 and tends to0.
Every passive interval contains0 in its interior, so all fifteen marked
invariant choices fail inside the literal passive box and every open
neighborhood of0. Positive recipient scaling preserves these failures.
The checker verifies all fifteen controls exactly at epsilon=10^-6.
No actual independent realization of these virtual continuations is claimed.

## 4. Prior selected and passive criteria

Only owner0 has all participant entries nonpositive. In the passive-threshold
producer, the designated owner1 must have nonpositive rewards in both of its
pairs with the other core owners. Each actual owner in123 has a positive
pair reward to another core member, so every labeling fails that premise.
The later negative-K sufficient region is also inapplicable: p=1>0 while
its upper bound is nonpositive at K=-1/4.

For the previous abstract passive-bound index theorem, the common signs
J13<0,J32<0,J31>0 force the identity labeling once anchor0 is fixed. At that
labeling BLOCK fails because J12=1/4>0. INDEX fails because J12,J21>0 but
c12=J12-Gamma12=-1/4<0. Thus its complete BLOCK/INDEX disjunction does not
accept this table under any relabeling.

The greatest premium core is123, even though12 is now also a premium trap.
All0-participant rewards are nonpositive, while triple123 has participant
vector(11,2,1)>0. The implemented signed-pair source requires greatest-core
cardinality2 and therefore fails. The mixed-sign triple source requires
positive reciprocal joining products, whereas12 has product(-1/4)*3<0,
13 has(-97)*12<0 and23 has4*(-101)<0. The joining-attractive source also
fails. The ordinary `MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md` even in its
weak strategic version requires nonnegative pair-trap product, contradicted
by12. These are source-hypothesis checks, not claims about conditional
negative-index interfaces.

The calendar-polytope producer requires a marked set of size2 with ordered
nonpositive participant caps. Every such set meets123, whose entire
participant vector is strictly positive. Its first block meeting123 therefore
violates that cap for every positive weighting. This excludes all calendar
owner/partition/weight selectors without estimating any polytope threshold.

The positive singleton graph is strongly connected. Its predecessor-closure
condition forces the nonempty marked set of every ordered-anchor criterion
to be all four players. The first block meeting123 then has strictly positive
participant sum for every positive weight. Thus every block order and weight
choice fails; the all15 explicit invariant controls above give the stronger
semantic comparison for coordinate-minimum invariance.

## 5. All fourteen withdrawal children and all weights

Use the relaxed necessary rows F_A,J_A and nonnegative lambda,mu from
Section 6.6 of `math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`.
These include patient, deadline, evaluated-security, terminal-security and
cancellation variants, and advancing-only capped clocks by mu=0. Singleton
withdrawal gains are relaxed to zero, future gains to their positive parts,
and Never rows are omitted, enlarging every compared feasible set.

Every child now has a SINGLE positive-LHS/nonpositive-RHS row. Coordinates
within C are listed in increasing order:

| C | outsider | row | LHS | lambda coefficients | mu coefficients |
|---|---:|---|---:|---|---|
| 0 | 1 | J0 | 1 | (0) | (0) |
| 1 | 2 | J1 | 3 | (0) | (0) |
| 2 | 0 | J2 | 9/10 | (0) | (0) |
| 3 | 1 | F3 | 3 | (0) | (0) |
| 01 | 2 | J1 | 3 | (-23,0) | (0,0) |
| 02 | 1 | J0 | 1 | (0,-1) | (0,0) |
| 03 | 1 | J0 | 1 | (0,-1) | (0,0) |
| 12 | 0 | F2 | 1 | (-1/2,0) | (0,0) |
| 13 | 2 | J3 | 4 | (-97,0) | (0,0) |
| 23 | 0 | J2 | 9/10 | (0,-101) | (0,0) |
| 012 | 3 | F0 | 3 | (0,-2,-5) | (0,0,0) |
| 013 | 2 | J3 | 4 | (-1003,-97,0) | (0,0,0) |
| 023 | 1 | J0 | 1 | (0,-1,-1) | (0,0,0) |
| 123 | 0 | J123 | 9980 | (0,0,0) | (-2,-3,-7) |

Thus no sequence of the compared raw child lifts can begin. This excludes
all their weights and all child choices, not merely one child equilibrium.
It does not exclude arbitrary strategically supplied extensions beyond
these certificates.

## 6. Three universal weight exclusions

Write H_A=w dot Z(A), J_A for the weighted outside joining increment, and
k(A)_i=Z_i(A union {i}). Exact coefficientwise identities are

    H12+H1+H3=(-6,-11/4,-2,-8) dot w,
    -(J12+J13+J23)=(-19,-2,-3,-7) dot w,
    k(01)+k(2)+k(3)=(-10201/10,-387/4,-8,-102) dot w.

Every right side is strictly negative for every nonzero nonnegative w.
The first excludes every full-proper-payoff ledger, including the premise
H_a(S)>=0 for every proper S in
`MARKED_SUPPORT_ORIENTATION_LEDGER_UNIFORM_EQUILIBRIUM.md`.
The second already contradicts the requirement J_a(S)<=0 for every proper S
in `SUPPORT_FILTERED_WEIGHTED_LEDGERS_UNIFORM_EQUILIBRIUM.md`, independent of
safe supports or singleton H rows. The third excludes universal forced-Quit
floors. Every finite menu of such weights is also excluded.

## 7. Singleton magnitudes, matrices and role selectors

The new singleton matrix is

    Gamma=[0,3,-1,3; 2,0,1/2,-3; 5,-2,0,-1; -3,-2,1,0].

The eight-sign role test in
`math/exports/EXPLICIT_SINGLETON_CHAMBER_UNIFORM_EQUILIBRIUM.md` has exactly
one permutation, the identity. Recomputing all its rational guards gives

    C=4/3, b=4/7, a=4/25, L0=9/25, A10=14/25,
    J=23/18, B1=b*(1/2)-(1-b)*J=-11/42<0.

Thus its B1>0 premise fails. The negative-pair outer dichotomy additionally
requires Gamma10<0, whereas the unique orientation has Gamma10=2.
This B1 argument is not applied to the finite-singleton-split theorem,
which permits B1<0; Section2 above separately excludes its core/return roles.

All 24 permutations and positive recipient scales fail the compared exact
reference singleton matrix: only identity matches its sign pattern, and
Gamma12/Gamma10=1/4 rather than its required 1/2. This is a literal-class
comparison, not a claim about an unspecified qualitative perturbation radius.

The pair principal determinants in order 01,02,03,12,13,23 are
(-6,5,9,1,-6,1); the triple determinants in order 012,013,023,123 are
(23/2,15,12,7); the full determinant is 53/2. The full inverse is

    (1/53)*[14,10,12,9; 23,24,-3,11; 88,78,30,102; 24,2,13,23].

Only principal triple023 has nonnegative inverse. Its outside inverse row
is (-23/24,1/8,-11/24), so all four passive-inverse child choices fail.
The full inverse is not nonnegative, its determinant is positive, and its
mixed-sign column2 prevents every signed all-column positive-inverse choice.
Signed single-column jackpot sources require a separate stationary-output
comparison; the exact stationary census supplies it. Every singleton column
has a positive off-diagonal entry, so the compared all-negative incoming
cyclic-child columns are absent.

The unique positive reciprocal pair is01 and the unique negative pair is13;
they intersect. Thus the compared no-negative-pair, two-positive-pair,
two-negative-pair and signed-cycle templates fail. The opposite-sign edge
graph gives vertex1 degree one, excluding every Hamiltonian cycle of that
kind. The three perfect matchings fail at joining increments -23 on01,
-97 on13, and -1003 on03, respectively. Every principal triple contains
one of these failing pairs. This excludes all matching proof weights and
the compared good-subset criteria requiring those increments throughout.

The attached-negative-pair ten-sign template has exactly the role tuple
(3,1,0,2). Its pair is original13, with participant reward Z1(13)=-100,
contradicting its nonnegative premium requirement. The broader
`BOTH_JOINT_PREMIUMS_ARBITRARY_UNIFORM_EQUILIBRIUM.md` allows that premium
but fails its m>=0 premise, since m=Gamma21=-2 in the sole orientation.

The entire scalar singular-circuit eligibility list is
(recipient,mate)=(2,1),(2,3),(3,1). Only two distinct recipients qualify,
so every criterion requiring three such recipients fails.

## 8. Scope of the conclusion

Together these checks exclude the named stationary-output and sure-first
families, all tested return/reset and positive-continuation roles, all fourteen
withdrawal children and their arbitrary nonnegative weights, the compared
weighted and matrix selectors, all ordered-anchor and calendar participant
choices, and the earlier passive-threshold and selected-index raw producers.
The opposite-sign pair is treated through every applicable old selection;
it is not excluded merely by displaying one bad root.

The literal table therefore supplies an additional UE coverage witness for
the new quiet-face producer against the inspected accepted capabilities.
This is not an unrestricted behavioral positive-gap claim. It does not
exclude unknown maximal neighborhoods of qualitative existence theorems,
arbitrary strategically supplied child extensions, or conditional mechanisms
whose raw-data producer has not been established. No Lean verification or
full Fin4 conclusion is asserted. The new completion identities also do not
by themselves establish openness in all sixty reward coordinates.
