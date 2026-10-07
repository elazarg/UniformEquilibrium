# Nonbijective singleton sources beyond a column-sign cone

Author: CODEX_BROUWER. Ordinary mathematics, not Lean-checked. The completed
two-pair theorem is frozen at
[TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md](../exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md).
The singleton/triple schedule ST1 is RETIRED as a coverage candidate: its
entire raw class is already covered by literal Fin4 no-UE normalization and
the accepted joining-attractive triple/smaller-core consumers. The final
section records that inclusion, including why arbitrary signed own levels
do not rescue its significance. Its schedule proof and exact coarse-regret
separator are retained as internal mathematics, not proposed exports.
The negative-c homotopy escape is a retained falsifier, not an extension
proposal. The initial exact singleton matrix is internal evidence showing
why a signed-column inverse reduction is insufficient, not an existence
claim. The separately completed signed-column producer does not supply the
new root-production step here.

## Question and status

For an arbitrary Fin4 quitting game, let s_i=r_i({i}) and let Γ have
diagonal zero and off-diagonal entries Γ_ij=r_i({j})−s_i. Suppose each
row has exactly one positive entry, at f(i), and its other two entries
are strictly negative. The production no-UE source imposes standard Q,
R₀, and R₀ degree+1 on this matrix. Can those conditions eliminate a
favorable two-cycle with two attached players, or reduce it to a full
inverse with uniformly signed columns?

Both proposed reductions fail on the exact matrix below. That regression
is a source-class obstruction only, not a positive-gap quitting game or
an existence theorem. All forty-four nonsingleton reward coordinates remain
free in the regression. The active proof later in this record restricts
some actual collision coordinates explicitly and then seeks an original-game
producer; its coverage audit is separate from the matrix calculation.

The named original-game source declarations inspected are
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
`isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`,
and `singleton_r0Degree_eq_one_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
For Fin4 the full-normal-core elimination and
`all_punishmentNormal_of_normalCore_eq_univ`
in `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`
supply the normality required by the R₀ declaration. None of these says
that the singleton matrix alone decides every reward completion.

## Exact two-cycle-plus-tails source

Take

    Γ = [[0,1,−2,−1],
         [1,0,−1,−2],
         [3/2,−1,0,−1/2],
         [−1,3/2,−1/2,0]].

Its favorable map is f(0)=1, f(1)=0, f(2)=0, f(3)=1. Thus it has
one two-cycle with two attached leaves, rather than a matching, four-cycle,
or three-cycle with one leaf. The determinant is2 and the full inverse is

    Γ⁻¹ = [[−1/8,−3/8,7/4,5/4],
           [−3/8,−1/8,5/4,7/4],
           [−7/8,3/8,1/4,3/4],
           [3/8,−7/8,3/4,1/4]].

The first two columns each contain both positive and negative entries.
No diagonal column-sign change makes Γ⁻¹ entrywise positive. Positive
playerwise payoff scales and player permutations do not change this fact.

In pair order01,02,03,12,13,23 the principal determinants are
−1,3,−1,−1,3,−1/4. In triple order012,013,023,123 they are
1/2,1/2,−1/4,−1/4. Thus every principal submatrix of size at least
two is nonsingular. Every column also has a negative off-diagonal entry.
A nonzero homogeneous complementarity root cannot have singleton support,
because of that negative entry, nor larger support, because it would solve
a nonsingular principal homogeneous system. Consequently Γ is R₀.

At complementarity offset −1, the positive favorite entries force z₀,z₁>0.
Their equalities give

    z₀=1+z₂+2z₃,       z₁=1+2z₂+z₃.

The remaining residuals are exactly

    w₂=−1/2−z₂/2+3z₃/2,
    w₃=−1/2+3z₂/2−z₃/2.

If z₂=0 and z₃=0, both residuals are negative. If only one is positive,
its own active residual is strictly negative. Hence both are positive,
and their equalities force z₂=z₃=1/2. Therefore the sole root is

    z=(5/2,5/2,1/2,1/2),       w=0.

It has full support and regular Jacobian determinant2>0. The exact finite
regular-root degree formula gives R₀ degree+1. Nonzero degree then implies
standard Q at every offset, not merely solvability of the one tested offset.

The declarations used for this final implication are
`exists_finset_r0Degree_eq_sum_sign_det`
in `MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero`
in `MathUE/LinearProgramming/R0Degree.lean`.
They were inspected read-only; the displayed arithmetic and source reasoning
have not been formalized or built in Lean here.

## What fails and what remains

The exact failed implication is: a one-positive-per-row, R₀, degree+1
singleton matrix must have a favorable graph consisting of a matching,
a four-cycle, or a three-cycle with a leaf. The present matrix has none
of those graph types. The stronger hope that every surviving graph has
a positive inverse after independent column-sign changes is false too.

Eliminating the two forced core coordinates at offset −1 yields the
two-dimensional matrix

    S=[[-1/2,3/2],[3/2,−1/2]],
    S⁻¹=[[1/4,3/4],[3/4,1/4]].

This is an algebraic complementarity reduction, not a reduction of the
original game's players or information. It does not transfer arbitrary
coalition rewards, caps, or independent stopping laws. Treating it as a
strategic quotient without those inputs would repeat a supplied-interface
shortcut. In particular the actual reward table need have no symmetry.

The next raw question fixes this Γ and arbitrary signed own singleton
levels, but retains every nonsingleton coordinate. Can an actual producer
use global complementary odds, rather than an inverse cone, while choosing
all four independent laws and caps? The latest section below gives a
complete-looking degree argument for such production. Its mathematical
review and concrete new-coverage witness remain open. No export claim or
constant optimization is intended.

## A different consumer: nonzero complementary odds, not positive inverse

The following exact reduction is internal supporting mathematics. It does
not yet produce a root and is not an existence-class claim. Its purpose is
to permit boundary supports in a genuinely different all-player selection
problem, rather than demand a positive inverse or a signed-column cone.

Fix two scheduled pairs, with mate a(i) and opposite pair O(i)={j,k}.
For arbitrary actual rewards define s_i, Γ as above and

    Π_i=r_i({i,a(i)})−s_i,       K_i=r_i(O(i))−s_i,
    c_i=Π_i−Γ_i,a(i).

Restrict raw coefficients to Π_i≥0,c_i>0,K_i≤0 and the twelve
opposite-pair joining rewards to r_i({i}∪T)≤s_i for ∅≠T⊆O(i).
Define, for X≥0,

    N_i(X)=c_iX_a(i)(X_j+X_k+X_jX_k)
              +Π_iX_a(i)²/(1+X_a(i))−K_iX_jX_k.

Every N_i is nonnegative. Suppose Γ is R₀, and suppose one can produce
a NONZERO nonlinear complementarity root

    X≥0,       e=ΓX−N(X)≥0,       X_i e_i=0 for every i.     (NC)

Then the original game has an exact two-phase terminal Nash profile and
one fixed uniform payoff. Here is the complete boundary-root adapter.
Use q_i=X_i/(1+X_i), allowing zero hazards, and the template values

    U_i=s_i+Π_iq_a(i),          W_i=s_i+c_iX_a(i).

The active Continue endpoint from W_i equals U_i exactly. The passive
Continue endpoint from U_i equals W_i+e_i/D_i, where
D_i=(1+X_j)(1+X_k). Both are identities in the actual rewards.
For X_i>0, complementarity makes e_i=0, so both active actions equal
U_i and passive Continue equals W_i. Passive Quit≤s_i≤W_i.

For X_i=0, let p=q_a(i), d=1/D_i. The player is prescribed Continue
at both phases. Let U_i^act,W_i^act be its actual phase payoffs against
the others. Solving its two scalar policy equations gives

    W_i^act−W_i = (e_i/D_i)/(1−d(1−p)) ≥0,
    U_i^act−U_i = (1−p)(W_i^act−W_i) ≥0.                  (NC1)

The denominator is positive: (NC) cannot have singleton support. Indeed
such a support would have N_i=0 in its sole active coordinate and
ΓX≥N≥0 everywhere, giving a nonzero homogeneous LCP solution,
contrary to R₀. Thus at least two players have positive hazards and
every player has an opponent that quits with positive probability each
two-date cycle. The same fact proves actual existence of the phase
payoffs and the policy equations used in (NC1).

At an inactive player's nominal active phase, forcing Quit pays U_i,
which is at most U_i^act. At its passive phase, forcing Quit pays at
most s_i, which is at most W_i≤W_i^act. Thus every endpoint and
policy equality holds also for zero coordinates of X. The finite
geometric deleted-opponent survival remainder proves all behavioral
deviations, Never included. Its expected absorption bound then gives
one fixed uniform target with O(1/N) horizon error, exactly as for a
proper periodic certificate. No opponent is replaced by a supplied
child equilibrium.

### The actual unsolved production question

The question is whether the original no-UE source (standard Q, R₀,
degree+1) forces a nonzero root of (NC), or a separate genuine
equilibrium exit, for this raw coefficient/cap class. The origin is
always a root; its local degree is the singleton R₀ degree, namely+1.
Therefore ordinary Nash existence or nonzero degree at the origin alone
does not supply the required nonzero root. One must determine the global
degree or an actual boundary alternative, retaining all four coordinates.

The opposite-leaf matrix above is an early exact stress test: its inverse
has mixed columns, so the signed-column proof is unavailable. Boundary
supports have not been excluded or exactified away. No global radial bound,
large-box degree, nonzero-root theorem, or new coverage conclusion is
claimed at this checkpoint. The next calculation should test this actual
nonlinear problem, not strengthen the boundary adapter in isolation.

## Global nonlinear degree supplies the missing nonzero root

Status: a new, unreviewed proof candidate. Unlike the preceding conditional
adapter, this argument produces a nonzero complementary root. It uses the
actual original-game R₀/degree+1 source, not a positive inverse and not a
selected local root. It also removes both coefficient-sign restrictions
Π≥0 and K≤0. A complete actual-table increment witness is still required
before requesting an export gate.

### Proposed raw Fin4 theorem

Choose any partition into two scheduled pairs. Assume only

    c_i=r_i({i,a(i)})−r_i({a(i)})>0 for every i,             (G1)
    r_i({i}∪T)≤s_i  for every nonempty T⊆O(i).              (G2)

All own levels, scheduled premiums Π_i=r_i({i,a(i)})−s_i, opposite
pair increments K_i=r_i(O(i))−s_i, singleton matrices, and unmentioned
collisions are unrestricted. The claim is existence of an original Fin4
uniform payoff. If the singleton matrix is R₀ with nonzero degree, the
proof directly produces an exact period-two terminal Nash profile, possibly
with some inactive coordinates. The theorem does not assert such an exact
profile on the alternative source exits.

### The global feasible set is bounded

Keep N as in (NC) but allow arbitrary real Π,K, retaining only c_i>0.
Define the closed set

    E={X≥0: ΓX≥N(X)}.

It is bounded, without any assumption on Γ. Suppose instead Xⁿ∈E has
t_n=∑Xⁿ_i→∞. Pass to a subsequence with Xⁿ/t_n→u≥0, ∑u_i=1.
Choose j with u_j>0 and put i=a(j). Writing O(i)={k,l}, exactly

    N_i(X)=c_i X_j(X_k+X_l)
               +(c_iX_j−K_i)X_kX_l+Π_iX_j²/(1+X_j).       (G3)

Since Xⁿ_j→∞, the coefficient c_iXⁿ_j−K_i is eventually nonnegative.
The last term is bounded in absolute value by |Π_i|Xⁿ_j=O(t_n).
If u_k>0 or u_l>0, the first term has a positive order-t_n² lower
bound, contradicting (ΓXⁿ)_i=O(t_n)≥N_i(Xⁿ). Hence u is supported
on {i,j}. Dropping the nonnegative terms in (G3), dividing by t_n and
passing to the limit gives

    Γ_ij u_j≥Π_i u_j.

But Γ_ij−Π_i=−c_i<0 and u_j>0, another contradiction. This proves
boundedness even when u has singleton support, and even for mixed signs
of Π and K. No guessed cone or assumed strategically favorable root enters.

### Global degree zero versus the nonzero local degree

For λ≥0 and x∈ℝ⁴ define the continuous minimum map

    H_λ(x)=min(x, Γx−N(x⁺)−λ1),

coordinatewise, with x⁺ the coordinatewise positive part. The denominator
in N(x⁺) is always at least1. A zero of H_λ has x≥0, residual≥0
and complementary coordinates. In particular every such zero lies in E,
because Γx≥N(x)+λ1. All zeros for ALL λ≥0 lie in the same compact
set E. On E, Γx−N(x) is bounded; for sufficiently large finite Λ,
the inequality Γx−N(x)≥Λ1 is impossible. Therefore H_Λ has no zero.

Choose a ball containing E in its interior. The homotopy H_λ,
0≤λ≤Λ, has no zero on its boundary, and the total degree of H₀ on
that ball is zero. At the origin, N(x⁺)=O(‖x‖²). If Γ is R₀,
the homogeneous map h(x)=min(x,Γx) has zero only at0. On the unit
sphere its norm has a positive minimum; positive homogeneity gives
‖h(x)‖≥c‖x‖. The coordinatewise minimum is Lipschitz in its second
argument, so the homotopy min(x,Γx−θN(x⁺)), 0≤θ≤1, has no
zero on a sufficiently small sphere. The local degree of H₀ at0 is
therefore the R₀ degree of Γ.

If that local degree is nonzero, additivity/excision and total degree0
force some additional zero X≠0 of H₀. No regularity, finite root
count, or sign computation at individual nonlinear roots is needed.
The root is precisely (NC).

### Boundary root conversion with arbitrary Π,K

The endpoint adapter above did not need signs of Π or K once (NC) was
given. It needed c>0, (G2), and at least two positive coordinates. The
last property still follows from R₀, without N≥0. If only X_j>0,
all rows other than i=a(j) have N_l=0. Hence Γ_lj≥0 there. In the
mate row feasibility says

    Γ_ij≥Π_i X_j/(1+X_j).

If Π_i<0, this is impossible because Γ_ij=Π_i−c_i<Π_i and
Π_i X_j/(1+X_j)>Π_i. If Π_i≥0, it forces Γ_ij≥0. In either
feasible case every entry of column j is nonnegative, giving a nonzero
homogeneous LCP root e_j, contrary to R₀. Thus support has size≥2.

All opponents-deleted periods now contract. Active positive coordinates
have e_i=0. Inactive ones have the exact nonnegative value correction
(NC1). At both phases passive Quit≤s_i≤W_i, and active Quit=U_i.
All policy equalities and full behavioral caps follow exactly as above,
with signed own levels untouched. This produces the fixed uniform target.

For the raw Fin4 conclusion, suppose no original UE exists. The literal
source `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
supplies R₀ and degree1 for THIS singleton matrix. It has no own-sign,
normality, or auxiliary-no-UE input. Its R₀ dependency is
`finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`.
The constructed original-game profile is then a contradiction. The ordinary
local-degree identification uses the literal homogeneous minimum-map
definition `r0Degree` and its radius invariance in
`MathUE/LinearProgramming/R0Degree.lean`.

### Weak pair-join closure and current falsification target

Replacing (G1) by c_i≥0 should give UE by literal reward closure: add
δ>0 to the four scheduled-pair participant coordinates only. This makes
every c_i positive, leaves all singleton entries and all (G2) coordinates
unchanged, and changes no coordinate by more than δ. Apply the strict
theorem and
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
It retains a single target for the original table. No exact periodic
profile is claimed at the weak boundary through this closure argument.

The immediate adversarial targets are the minimum-map degree calibration,
the support-one argument, and the inactive-player actual-value correction.
For coverage, changing only r₂(12) from−1 to1 in the signed-column
fixture admits (G1)–(G2) but defeats every signed-column schedule:03/12
has the wrong sign of c₂, while01/23 and02/13 have the wrong sign of
K₂. That modified table still needs a complete quiet-child/source audit;
in particular its old child012 J witness has changed and must not be
reused. This is an early candidate, not an established coverage witness.

## Completed source calibration and concrete coverage checks

The degree mechanism now has a scoped independent mathematical PASS in
`../feedback/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE__BY_CODEX_MORSE.md`.
The following material completes the concrete tests and source details;
it is ordinary mathematics, not a new Lean check. The raw criterion,
not a supplied nonlinear root, is the conjecture-facing statement.

### One fixed scalar chart suffices

The degree proof does not need an unproved identification of a repository
chart integer with an independently defined ambient Brouwer degree. Choose
R>0 with E contained in (−R,R)⁴ and use the single chart [−2R,2R]⁴
throughout. Pull back the negative of H_λ as the cube gain field. On
the central region corresponding to (−R,R)⁴, cube solutions are exactly
zeros of H_λ; the region closure stays strictly inside the cube.
The same central region is isolating for every 0≤λ≤Λ. The λ=Λ
problem has no solutions there, so its local degree is zero, and
homotopy invariance makes the central H₀ degree zero too.

In that SAME chart let V be the preimage of a sufficiently small open
ball around0. The perturbation estimate in the main proof isolates V
for min(x,Γx−θN(x⁺)), 0≤θ≤1. Its θ=0 field is the homogeneous
minimum map h. The homogeneous problem has exactly one solution, at0,
in both V and the central region, so solution-set excision identifies
its V-degree with its central degree. The latter is exactly r0Degree Γ
by scalar-radius invariance. Thus the H₀ degree on V is nonzero.
If H₀ had only the zero root, solution-set excision within this same
chart would equate its central degree0 and its V-degree, a contradiction.
No nonlinear regularity, finite root count or general chart-invariance
theorem is introduced.

The exact inspected declarations supplying these properties are
`BoxComplementarityProblem.ofAmbientMap` and
`isSolution_ofAmbientMap_iff_of_coordinateInterior` in
`MathUE/Topology/BoxComplementarityAmbientMapAdapter.lean`,
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq` in
`MathUE/Topology/BoxComplementarityStabilizedLocalDegree.lean`,
`BoxComplementarityProblem.localDegree_eq_of_solutionsIn_eq` in
`MathUE/Topology/BoxComplementaritySolutionExcision.lean`, and
`BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero`
in `MathUE/Topology/BoxComplementarityLocalDegreeConsequences.lean`.
The last theorem contrapositively gives degree zero on an empty
isolating region. The radius identification remains
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`.

For the strategy consumer, use actual corrected Uᵃᶜᵗ,Wᵃᶜᵗ as the
phase vectors. The displayed endpoint bounds and policy equalities
give exactly `IsεQuittingRootNash` at error0. Every player's opponents
have cycle survival ∏_{j≠i}(1−q_j)<1. Thus all hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` are
produced, including for inactive players and negative phase values.
The root endpoint definitions and Bernoulli-mixture identity are in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.

### Exact inactive and signed boundary stress

Use the two-cycle-plus-leaves Γ from the first section, schedule01/23,
and choose

    Π=(2,2,−1/4,−1/4), K=(7,7,0,0), X=(1,1,0,0).

Then c=(1,1,1/4,1/4), e=(0,0,1/2,1/2). With all own levels1,
the templates are U=W=(2,2,1,1), but the actual values are
(2,2,7/6,7/6) at BOTH phases: the inactive correction is
(1/8)/(3/4)=1/6. Prescribe all cross-pair participant and relevant
triple cap entries equal to1; the other unused coordinates can be
chosen arbitrarily. This is a complete-table-compatible exact test,
not an alleged new-coverage example. It combines negative Π, positive K
and nonzero inactive corrections.

Changing each nonempty reward of player i by s_i−1 gives the same
raw gaps and root with any signed own vector s. For example,
s=(−3,2,−1,4) gives the actual target (−2,3,−5/6,25/6).
The theorem is applied to this new table directly; this is not a claim
that arbitrary terminal translations preserve profiles with positive
Never probability.

### Finite necessary restriction on every counterexample

The weak c_i≥0 argument above is now a proved corollary of the strict
candidate, with the same mathematical status. For EACH of the three
partitions into two pairs, every Fin4 table without UE must have either

1. some player i with r_i({i,a(i)})<r_i({a(i)}); or
2. some player i and nonempty T⊆O(i) with r_i({i}∪T)>r_i({i}).

This finite raw disjunction is invariant under player relabeling.
There is no singleton sign assumption, terminal translation, independent
root hypothesis or supplied strategy in this counterexample restriction.
Reward closure gives one target for the original table, not a target
depending on accuracy. It does not assert exact periodic production on
the weak boundary or on a matrix-source exit.

### Full table for the new-coverage test

Set D=52104052 and

    K=(−4711507/97125,−41341/22950,36491/10300,−94597/7650).

The complete table is:

| S | r(S) |
|---|---|
| 0 | (1,0,4,4) |
| 1 | (4,1,0,0) |
| 2 | (0,4,1,0) |
| 3 | (0,0,0,1) |
| 01 | (1/2,1/2,0,0) |
| 02 | (1/2,0,−D,0) |
| 03 | (2,1+K₁,1+K₂,5) |
| 12 | (1+K₀,5,1,1+K₃) |
| 13 | (0,1/2,0,1/2) |
| 23 | (0,0,−D,1/2) |
| 012 | (1/2,−10,100,0) |
| 013 | (−10,1/2,0,−10) |
| 023 | (−10,0,−D,−10) |
| 123 | (0,−10,100,1/2) |
| 0123 | (1000,1001,1002,−104) |

For schedule03/12 the joining gaps are c=(2,1,1,1)>0 and every
opposite-pair cap is strictly below1. The singleton matrix is

    Γ=[[0,3,−1,−1],[−1,0,3,−1],[3,−1,0,−1],[3,−1,−1,0]],
    Γ⁻¹=(1/13)[[2,5,−7,13],[5,6,−11,13],
                [1,9,−10,13],[1,9,−23,26]].

The signed-column producer cannot apply with ANY schedule. Its positive
inverse requirement uniquely forces σ=(1,1,−1,1). Schedule03/12
then fails σ₂c₂>0; schedules01/23 and02/13 have K₂=−1 and fail
σ₂K₂≤0. Positive playerwise scales preserve these signs. The theorem
also exceeds positive-inverse matching producers because Γ⁻¹ has a
strictly negative column, and its favorable graph is a three-cycle with
an attached player, not a matching or four-cycle.

The matrix has pair determinants (3,3,3,3,−1,−1), triple determinants
(26,−10,6,2), full determinant13, and a negative entry in every column.
It is R₀. The sole offset−1 LCP root is (1,1,1,1), regular with
positive determinant, so its degree is1 and it is standard Q. Only012
has a positive inverse, and its outside factorization row is
(−1,−9,23)/26, excluding the passive-inverse exit.

### The repaired all-child and withdrawal comparisons

Except for children12 and012, the exact child witnesses and raw J rows
in the signed-column fixture are unchanged: no changed payoff is used
in those comparisons. Child12 now uses both players quitting surely,
not the obsolete solo1 profile. Its participant rewards5 and1 strictly
exceed the passive rewards4 and0; omitted player0 has positive immediate
join gain d₀=−1/2−K₀>0. This profile has zero child debt and zero Never.

For child012 and omitted player3, write λ_i≥0 for advance weights.
The simple J rows alone are inconsistent:

    J at0:   1≤λ₁/2−(D+4)λ₂,
    J at02: −10≤−10λ₁.

The second forces λ₁≤1, contradicting the first. This does not reuse
the old solo1 child equilibrium, which ceased to be Nash after the
participant reward r₂(12) increased.

The more general five implemented withdrawal F/J certificates fail too.
All their singleton restart floors are at most1: the patient floor is
at most max(s_i,0)=1; the deadline floor is at most0; and the security
LP has the literal own-singleton row, giving security value≤1, so its
maximum with the deadline floor remains≤1. Consequently every singleton
withdrawal gain is nonpositive. Let the withdrawal weights be arbitrary
nonnegative μ_i. The following three necessary inequalities survive
after dropping all nonpositive withdrawal contributions:

    J at0:   1≤λ₁/2−(D+4)λ₂,
    F at1:   1≤−3λ₀+λ₂,
    F at12: −K₃≤−K₀λ₀−4λ₁.                         (W)

At12 the withdrawal gains are exactly −1 for player1 (4−5) and
−1 for player2 (0−1), and zero for player0. They enter the F row
for patient/cancellation withdrawal and vanish there for the other
three kinds. Thus (W) is valid for every kind. Its first two rows give
λ₁≥2+2(D+4)(1+3λ₀). The last right side is therefore at most

    −8−8(D+4)+[−K₀−24(D+4)]λ₀<0,

whereas −K₃>0. This exact contradiction closes the broader raw gap.
It does not claim that no specially selected child profile can be safe.

The literal definitions inspected are `WithdrawalFutureJoinKind.gain`,
`WithdrawalFutureJoinKind.futureWeight`, and
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
`patientWithdrawalFloor_le_ownNeverAlternative` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`,
`deadlineWithdrawalZeroFloor_le_zero` and `deadlineWithdrawalGainFloor`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
and `deadlineWithdrawalSecurityValue_le_singleton` plus
`deadlineWithdrawalSecurityFloor` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`.

The other exceptional child123 retains q₁=D/(D+100), q₂=1/21,
q₃=1. The changed reward r₂(12) never enters player2's payoff because
player3 is sure. Its exact zero-debt/zero-Never calculation and omitted0
gain5210405575/136773399 therefore remain valid. These witnesses and
(W) exclude the actual tracked raw deletion criteria for every child,
but make no universal supplied-child-debt claim for child012.

### Other changed source tests and remaining assembly obligation

The only premium traps remain03 andI. No player has globally nonnegative
participant premiums. The global forced-Quit floor atT1 now has vector
(−1/2,0,0,−1/2), forcing a nonnegative weight to be supported on{1,2};
atT3 the remaining coefficients are −1/2 and−D−1, so every weight
vanishes. The old boxed-trap failure P_I(13)=88,L_I(13)=90 and the
product-low failure at q₀=q₃=1/2 are unchanged.

The one-shot-anchor criterion fails at the explicit passive coalitions
T₀=1,T₁=23,T₂=0,T₃=02: the joining gaps are respectively
−7/2,−10,−D−4,−10. Thus every player has a strict
negative joining comparison despite all own rewards being positive.
No anchor is silently supplied by the new criterion.

The old conditional-range failure survives with the corrected bound:
player2 has Continue upper at least4, while BOTH Quit lower bounds are
at most1 for every blocker; blocker1 now uses pair12 reward1 rather
than−1. The ordered weak-unit guard test for owner2/passive0 must use
background3 and joining gap−D, not the obsolete background1 gap−1.
All other displayed guard rows are unchanged. The exhaustive sure-owner
stationary census is unchanged; its j=1 branch is simpler because
player2 now has four positive joining differences1,100,100,1002 and
is forced sure. No absence of all-proper stationary roots is claimed.

The source/fixture comparisons are now sufficient to prepare a single
self-contained candidate. Its final artifact must reproduce the full
proof, actual phase values, table and source evidence rather than rely
on this note or the earlier export. A second independent review and a
final-artifact gate remain required; no export or Lean claim is made here.

## Next raw question: one negative mate-joining gap

The reviewed standalone is exported, not Lean-checked, at
`../exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`. The next
question concerns its genuine complement, not another inverse-cone
condition: if only one of the four mate-joining gaps is negative, can
an escape of complementary odds be turned into an actual strategic
exit, or must the chronology change? All four laws and behavioral caps
must still be produced from raw rewards. The following exact test
rules out treating the previous offset homotopy as automatically compact
or treating every infinite-odds limit as Nash.

Take schedule01/23, s=(1,1,1,1),

    Γ=[[0,−1,3,3],[3,0,−1,−1],
       [−1,1,0,3],[−1,1,3,0]],
    Π=(−2,4,4,4), K=(−1,3,0,0), c=(−1,1,1,1).

For EVERY t>0, let X=(0,t,1,1). Direct substitution into (3) gives

    (ΓX−N(X))₀=4t−2t/(1+t)+5,
    (ΓX−N(X))₁=(ΓX−N(X))₂=(ΓX−N(X))₃=1.

Hence X is a zero of H₁ for every t>0: the positive coordinates
have residual exactly1 and the zero coordinate has residual>1.
This is an unbounded zero set at a fixed positive homotopy parameter,
not merely unbounded feasible points.

The matrix still satisfies the exact incoming singleton properties.
Its pair principal determinants are(3,3,3,1,1,−9), its triple
determinants are(8,8,−18,−6), and its full determinant is−75.
Every column has a negative entry, so it is R₀. At offset−1 its
complete root list is

| Positive support | Root | Inactive residual | Local sign |
|---|---|---|---|
| 012 | (5/8,13/8,7/8,0) | w₃=21/8 | +1 |
| 013 | (5/8,13/8,0,7/8) | w₂=21/8 | +1 |
| 0123 | (13/25,17/25,7/25,7/25) | none | −1 |

All are regular and all inactive residuals are strict. The finite
degree formula gives +1; in particular Γ is standard Q. The other
supports have no feasible root, by direct inversion of the displayed
nonsingular principal matrices; singleton supports cannot offset−1
on their zero diagonal. Thus the unbounded homotopy is compatible
with R₀/degree1, rather than being excluded by a contrary matrix exit.

These coefficients are realized by the actual singleton rows of Γ
and scheduled pairs

    r(01)=(−1,5,1,1),       r(23)=(0,4,5,5).

All cross-pair participant and relevant triple cap entries may equal1;
the remaining coordinates can be chosen arbitrarily. In the limit
t→∞ the scheduled hazards are (0,1,1/2,1/2). Player1 quits surely
in phase01, giving its prescribed value1. If it Continues once, in
phase23 its two opponents' singleton rewards are0, their pair reward
is4, and both Continue with probability1/4, returning to own value1.
Its Continue value is therefore 4/4+1/4=5/4. The limit has a genuine
gain1/4, not an equilibrium boundary exit. No limiting-payoff or
pointwise endpoint assertion can erase this gap.

This is an internal falsifier of a proposed extension of the SAME
offset homotopy, not a UE counterexample or new existence class. It
does not weaken the frozen c≥0 theorem. The next admissible mechanism
must account for this infinite-odds active player's continuation gain,
for example by producing a different schedule rather than declaring
the escape harmless. Whether such boundary alternatives can be organized
globally for arbitrary tables remains open.

## Singleton/triple schedules: a different raw candidate

Status: complete internal proof draft, not independently reviewed and no
additional-coverage claim. The exact signed fixture below still needs the
finite-anchor CCE and single-anchor dominance comparisons. This candidate
changes the schedule rather than repairing the failed negative-c homotopy.

Let I={0,1,2,3}, C={1,2,3}, s_i=r_i({i}), with arbitrary signed terminal
rewards, live payoff zero and Never zero. Assume

    Δ_i(T)=r_i(T+i)−r_i(T) ≥0
      for i∈C, ∅≠T⊆C−i;
    r₀(T+0)≤s₀ for ∅≠T⊆C;
    r_i({i,0})≤s_i for i∈C.                         (ST1)

The proposed conclusion is original Fin4 UE. No supplied root, matrix
condition, own-level sign, public randomization or restricted deviations
is part of the raw criterion. First take every Δ strictly positive. Assume
no UE and invoke `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`:
the ORIGINAL Γ is R₀ of degree1. The source does not translate rewards or
assume nonnegative original singletons.

### Actual equations and a compact feasible region

Use blocks {0},C. For each i, let A_i be its own block minus i and O_i the
other block. For X≥0 put X_T=∏_{j∈T}X_j and D_B=∏_{j∈B}(1+X_j), and set

    U_i=Σ_{T⊆A_i} X_T r_i(T+i)/D_A,
    W_i=s_i+Σ_{∅≠T⊆A_i} Δ_i(T)X_T,
    F_i=U_i+Σ_{∅≠T⊆O_i}X_T r_i(T)−W_i D_O.          (ST2)

For player0, U₀=W₀=s₀. One has F(X)=ΓX+O(‖X‖²) at zero. Also

    [Σ_{∅≠T⊆A_i}X_T r_i(T)+W_i]/D_A=U_i.            (ST3)

Let M bound all absolute rewards. If F(X)≥0, then W_i≤M because the
right side of W_i≤[U_i+Σ_{∅≠T⊆O_i}X_T r_i(T)]/D_O is a convex
combination of U_i and passive rewards, all in [−M,M]. Also W_i≥s_i.
For every j∈C choose i∈C−j. Its positive coefficient Δ_i({j}) yields

    X_j≤(M−s_i)/Δ_i({j}).                            (ST4)

R₀ implies some Γ_i0<0 with i∈C: otherwise e₀ is a nonzero homogeneous
LCP root. For this i, since O_i={0},

    0≤F_i=U_i−W_i+X₀(r_i({0})−W_i)
          ≤M−s_i+Γ_i0 X₀.

Thus X₀ is bounded too. E={X≥0:F(X)≥0} is compact. Extend
N(X)=ΓX−F(X) continuously using X⁺, and use
H_λ(x)=min(x,Γx−N(x⁺)−λ1). Every zero lies in E. Large λ has no
zeros, so total degree is zero; the quadratic vanishing of N and R₀
give local degree1 at zero. The same single-box homotopy/excision
calibration proved above gives a nonzero complementary root

    X≥0, F(X)≥0, X_i F_i(X)=0.                       (ST5)

This use of degree has exactly the previously inspected fixed scalar-chart
dependencies, not an unproved ambient/chart identification.

The root has at least two positive coordinates. If its sole positive
coordinate is0, feasibility makes Γ's column0 nonnegative, contradicting
R₀. If it is j∈C, each other child i has

    F_i/X_j=Γ_ij−Π_ij X_j/(1+X_j),
    Π_ij=r_i({i,j})−s_i=Γ_ij+Δ_i({j}).

If Π_ij<0 the expression is negative; if Π_ij≥0, feasibility forces
Γ_ij≥0. The anchor row gives Γ_0j≥0, again a forbidden nonnegative
column. The source and the strict within-block gaps therefore exclude
every singleton support without asserting every coordinate is active.

### Actual values, unrestricted deviations and weak closure

At alternating phases {0},C use independent q_i=X_i/(1+X_i). Equation
(ST3) equates forced Quit and Continue with templates U_i,W_i at the
own phase. At the opposite phase, Continue is W_i+F_i/D_O, while
forced Quit≤s_i≤W_i by the ten raw caps. For X_i>0, F_i=0 and these
are the actual values. For X_i=0, put p=1/D_A and d=1/D_O. Actual
phase values are U_i+δU_i,W_i+δW_i, where

    δW_i=(F_i/D_O)/(1−pd)≥0,       δU_i=pδW_i.        (ST6)

The denominator is positive because the root has at least two positive
coordinates. These corrections preserve both inactive Continue identities
and improve its Quit inequalities. They are not optional templates.
Deleting any player leaves positive absorption probability each period.
Iteration of the one-step inequalities therefore controls every behavioral
replacement, including Never. The actual profile is terminal Nash.
Writing ρ=max_i∏_{j≠i}(1−q_j)<1, the opponent absorption time has mean
at most 2/(1−ρ). Bounded rewards give the same fixed terminal target,
delivery error at most 2M/((1−ρ)N), and unilateral horizon regret at
most 4M/((1−ρ)N), including the initial live-zero date.

The production consumer is the same
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, with all
its strategic inputs produced here. For weak Δ≥0 add δ>0 only to
participant coordinates of coalitions contained in C of size at least2.
Every relevant Δ becomes strict; own levels and all ten caps are unchanged.
Apply `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
Only UE existence, not an exact periodic profile at every weak boundary,
is claimed by closure.

### Exact signed fixture and still-open coverage

The complete table is

| S | r(S) |
|---|---|
| 0 | (1,−2,−2,−2) |
| 1 | (2,−1,1,−2) |
| 2 | (2,−2,−1,1) |
| 3 | (0,1,−2,−1) |
| 01 | (0,−1,1,−2) |
| 02 | (0,−2,−1,1) |
| 03 | (0,1,−2,−1) |
| 12 | (−1,−1,2,−1) |
| 13 | (−1,2,−1,−1) |
| 23 | (−1,−1,−1,2) |
| 012 | (0,−1,−1,2) |
| 013 | (0,−1,1,−1) |
| 023 | (0,1,−1,−1) |
| 123 | (−1,3,3,3) |
| I | (0,−3,−3,−3) |

Own levels are(1,−1,−1,−1). The within-triple gaps are1 on singletons
and4 on the two-opponent subsets. All ten caps hold. The pair criterion
fails on01/23 and02/13 because c₀=−2; on03/12, player3's opposite
pair participant reward r₃(23)=2 exceeds its own−1. The singleton Γ is

    [[0,1,1,−1],[−1,0,−1,2],[−1,2,0,−1],[−1,−1,2,0]],

with determinant7 and inverse

    [[1,1/7,−5/7,−3/7],[1,3/7,−1/7,−2/7],
     [1,2/7,−3/7,1/7],[1,5/7,−4/7,−1/7]].

Hence neither a positive inverse nor any uniformly signed inverse-column
cone applies. The accepted joining-attractive triple theorem assumes
nonnegative own levels, which fail directly here. That direct-input distinction
is NOT a coverage exclusion: the literal no-UE normalization below supplies
a new no-UE table with nonnegative own levels and the relevant inequalities.
No unrestricted utility-translation equivalence is being asserted.

The following exact child tests address universal nonnegative debt/Never
withdrawal bounds, not specially selected safe child equilibria. Child0
quits surely and has a profitable omitted joining player. Each negative-own
singleton child has an impossible full Never row for omitted0: its own
advance coefficient is nonpositive and every restart bonus≤0, while s₀=1.
For child pairs12,13,23 both members quit surely; child123 has all three
quit surely. All have zero child debt/Never and omitted0 gains1.
For child0i, let i quit at date0 and0 quit at date1 off path. Player i's
value and future best response both equal−1; player0's prescribed value
is2 or0 and its date0 join gives0. An omitted child has joining gain1.
Child013 uses sure coalition03, with omitted2 gain1.

For child012, player1 quits surely at date0, q₀=1/3,q₂=2/3, and0
quits surely at date1 off path. The two free response differences are
−2+3q₂ and1−3q₀. Player1's prescribed value is−1; its nonempty-event
Continue rewards are−2 and its empty-event future cap is−1. This is
an exact unrestricted child Nash profile. Omitted3's four joining gains
on T=1,01,12,012 are1,1,4,−5 with probabilities2/9,1/9,4/9,2/9,
giving gain1. For child023 replace anchor1 by2 and free2 by3. Omitted1
has gains1,1,4,−4 with the same probabilities, giving11/9.

These child witnesses only separate the indicated withdrawal certificates.
The exact coarse-regret tests below also fail, but neither fact establishes
an increment: the fixture has a concrete punishment-tail anchor exit, and
the entire ST1 class has the stronger normalization/core inclusion recorded
after those tests. The schedule theorem itself is not refuted.

### Exact separation from every coarse-regret base

The finite-anchor criterion and its arbitrary-base extension have now been
independently checked. They do NOT consume this signed fixture. For anchor0,
use the correlated free law on T=1,2,3,23 with probabilities
(16,8,2,1)/27. Its six regret margins, in order1C,1Q,2C,2Q,3C,3Q, are

    (16/27,0,1/3,10/9,0,0),

and its expected anchor gap is−47/27. This is a feasible coarse law,
not claimed product or playable. For the other singleton bases the pure
free coalitions03,01,02 are respectively exact free Nash points, each
with anchor gap−2. Thus every singleton minimum is strictly negative.

Every larger base also has a negative witness. In this table T is the free
coalition, so the actual immediate coalition is E∪T; ∅ means every free
player Continues. Each displayed pure free action is a Nash point of the
literal induced game, so its point mass is feasible without a relaxation.

| E | T | Harmed base member | Member gap |
|---|---|---|---|
| 01 | 3 | 1 | −2 |
| 02 | 1 | 2 | −2 |
| 03 | 2 | 3 | −2 |
| 12 | 0 | 2 | −2 |
| 13 | 0 | 1 | −2 |
| 23 | 0 | 3 | −2 |
| 012 | ∅ | 2 | −2 |
| 013 | ∅ | 1 | −2 |
| 023 | ∅ | 3 | −2 |
| 123 | 0 | 1 | −4 |
| I | ∅ | 1 | −4 |

These fourteen pure witnesses plus the correlated anchor0 witness establish
the exact ∀E∃member∃coarse-law negative-gap condition. No minimizer values
or common negative law are needed. The arbitrary-base comparison alone
does not detect this table. The next section supplies the actual source
that does and retires the whole raw class rather than merely this fixture.

## Whole ST1 class is already covered

This is a source-inclusion proof, not a new equilibrium construction. Let
I={0,1,2,3}, C={1,2,3}, with arbitrary signed own rewards s_i and Never0.
The ST1 assumptions used here are:

1. r_i(T+i)−r_i(T)≥0 for i∈C and every nonempty T⊆C−i;
2. r₀(T+0)≤s₀ for every nonempty T⊆C.

The schedule's additional three caps r_i(i0)≤s_i are not needed for this
inclusion. Condition2 gives player0 no positive participant premium on any
coalition. Hence every premium trap, and therefore the greatest premium core
K, is contained in C. There is no singleton premium trap, so |K| is0,2 or3.

Suppose the original table has no UE. The literal declaration
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
then produces p with s_p>0 and the actual normalized table

    rhat_i(S)=(r_i(S)−offset_i)/s_p,
    offset_p=0,       offset_i=s_i for i≠p.

Its `no_uniformPayoff` field concerns that very reward table with Never0;
its own levels are1 at p and0 elsewhere. The inspected definitions are
`quittingSinglePivotNormalizedReward`, `quittingSinglePivotOffset` and
`quittingSoloReward_singlePivotNormalized` in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`.
This is an actual no-counterexample transport theorem, not an informal WLOG
translation or a claim that arbitrary reward translations preserve play.

Every within-recipient joining difference and every participant premium is
divided by the same positive s_p. Consequently both displayed hypotheses,
all premium traps, and K are preserved. If K is empty, the normalized game
has UE by the empty-core branch of
`exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`.
If K is a pair, both joining gaps are nonnegative by condition1, so their
product is nonnegative and the pair branch of that same declaration applies.
If |K|=3, then K=C, and the nonnegative-own-level, nine-joining-gap theorem in
[JOINING_ATTRACTIVE_TRIPLE_CORE_UNIFORM_EQUILIBRIUM.md](../exports/JOINING_ATTRACTIVE_TRIPLE_CORE_UNIFORM_EQUILIBRIUM.md)
applies. Each case contradicts the produced normalized no-UE field.

Thus the ENTIRE ST1 class is covered, including signed-own tables and every
completion of its unused reward coordinates. Varying passive entries cannot
create an increment. No ST1 export or weaker-fixture optimization is proposed.

### The signed fixture also has a direct punishment-tail exit

For anchor0 its three free-player response differences are

    1−3q₃−2q₂q₃,   1−3q₁−2q₁q₃,   1−3q₂−3q₁q₂.

An exact free product Nash point is

    (q₁,q₂,q₃)=(−5/11+14√3/33, −3/4+7√3/12, −9/11+7√3/11).

All coordinates lie strictly between0 and1 and all three differences vanish.
Player0's punishment value is0: immediate Quit guarantees a nonnegative
payoff, while the opponents' sure coalition123 gives Continue−1 and Quit0.
Writing Q₀ for its immediate payoff and C₀ for its nonempty-event Continue
contribution, direct substitution gives

    Q₀−C₀=(4959−2863√3)/132>0,
    4959²−3·2863²=1374.

So `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
and `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`
already give UE on this exact fixture. Its fifteen negative coarse-regret
witnesses therefore demonstrate weakness of the coarse relaxation, not a
missing equilibrium class.

### Next question after retiring ST1

Seek a raw original-game producer that survives BOTH the actual punishment-tail
persistent-base tests and the no-UE normalization/core consumers. In
particular, a new triple-based schedule must either admit a positive anchor
participant premium (so its core need not lie in the triple) or genuinely
leave the within-triple joining-attractive class. Signed singleton levels
alone are not a source of new coverage. No replacement theorem is claimed.

## Independent selection checkpoint

The next search is for an approximate all-player producer, not an exact
finite-menu Nash selector. A possible uniform quantile/sampling compression
shortcut was checked against the actual source and is already implemented:
`hasEscapeAwareQuantileClockCompressionAtBound` in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`
preserves prescribed payoffs and both directions of unrestricted pure-time
caps, including Never. `escapeAwareQuantileClock_normalized_quantitative_bracket`
in `UniformEquilibrium/Quitting/Paths/CommonQuantileClockApproximation.lean`
already gives the finite lower/upper bracket. The actual independent-law
producer `exists_fin4_calendarUniformStoppingLaws_exploitability_le` in
`UniformEquilibrium/Quitting/Paths/QuantitativeFiniteClockSource.lean`
selects laws with error at most the unrestricted infimum plus24/level.
Consequently compression, sparse support, or a finite optimizer alone is not
a new selection mechanism: the missing step is still forcing that infimum
to vanish. This direction is not being repackaged as a theorem.

A separate concrete raw-family question remains exploratory. Suppose that,
for every player i, its reward on EVERY coalition containing it and at least
one other player is one fixed P_i≥s_i, while passive rewards are arbitrary.
Can the uniform positive joint-quit increment be used to repair a singleton
clock profile by coalition enlargements, with no supplied child equilibrium
or cap bound? This includes signed s_i and fixed independent behavioral
play; the desired output is one fixed uniform payoff. A profitable join
does not alone prove progress: at a later coalition an old participant may
prefer to leave for a passive payoff above P_i. No rank, stationary-completeness
claim, actual uncovered fixture, or existence theorem has been established.
Before pursuing it, the whole class must be tested against the current
concrete-base and premium-core consumers. This is a different question from
the retired ST1 schedule and does not modify any frozen result.
