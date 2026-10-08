# Nonbijective singleton sources beyond a column-sign cone

Author: CODEX_BROUWER. Ordinary mathematics, not Lean-checked.

## Current full-goal status

The canonical ordinary-mathematical source theorem is frozen in
[RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md](../exports/RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md)
after two independent whole-artifact falsifications. From any Fin4
counterexample it selects ONE fresh bounded row-generic table with
positive unrestricted SUM-debt minimum and ONE common debt vector at
ALL carrier minima. EVERY produced marked minimum has a random terminal
law, no prescribed mass before its earliest active point, and a finite
isolated first collision with at least two root suppliers. Some owner
has genuinely different maximizing root and later PAYOFF kernels on
a positive-probability original opponent event. That owner can have
ZERO debt. This is a source restriction, not a UE theorem.

The exact open task is to consume that source by an actual independent
finite-amplitude root/tail change with an upper ledger for EVERY changed
response cap, or another genuinely global contradiction. Neither the
first row nor the old tail is assumed Nash or debt-minimizing. All finite
deadlines, Never, zero/sure root rates and actual carrier realization
remain in scope. Different cap kernels alone are not a paid charge.

NF1–NF8 below gives an ordinary finite-prefix restatement of the accepted
source: delete vanishing original pre-date mass, normalize the first
date to0, extract an ACTUAL carrier tail even at sure-owner boundaries,
and obtain an exact Q_i=A_i+α_i b_i bridge. Randomness forces a strictly
mixed root rate. NF8 makes this UNIVERSAL at EVERY nonzero finite-prefix
minimum of the SAME canonical table, including new grafted minima.
This is supporting consumer simplification, not a new export or an
additional counterexample-class reduction.

All earlier unique mathematical proofs, failed implications and exact
tests remain below. In particular local descent, separate-block repair,
atomless regularization, weak-clock security and convexified-payoff
sharing have been retired as universal producers. HP/EA7 remain
unreviewed supporting reselections; a late plateau is not a genuine
kernel charge. The full finite-quitting UE conjecture remains open.

## Original singleton-matrix question

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

## Constant joint-participant rewards: an exact early source test

The raw question is this: for four players with arbitrary singleton levels
s_i, suppose constants P_i≥s_i satisfy r_i(S)=P_i whenever i∈S and
|S|≥2, while passive coordinates are arbitrary. Never and live rewards
are zero; randomization is private and independent; complete behavioral
deviations are allowed. Can one produce approximate complete response laws
and one fixed uniform target without a supplied root or cap hypothesis?

The first shortcut, whole-class inclusion in actual concrete persistent-base
sources, fails even with own levels1, joint-participant levels2 and all
rewards nonnegative. The complete table below is only a source test.

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (2,2,4,0) |
| 02 | (2,4,2,0) |
| 03 | (2,0,4,2) |
| 12 | (0,2,2,4) |
| 13 | (4,2,0,2) |
| 23 | (4,0,2,2) |
| 012 | (2,2,2,4) |
| 013 | (2,2,4,2) |
| 023 | (2,4,2,2) |
| 123 | (4,2,2,2) |
| I | (2,2,2,2) |

Its Γ is the favorable matching H=3 matrix: favorable entries3 at
01/10/23/32 and every other off-diagonal entry−1. Pair determinants are
−9 or−1, triple determinants6 and full determinant45; every column has
a negative entry. Thus it is R₀. At residual ΓX−1, favorite-pair roots
have negative inactive residuals, harmful-pair and triple solutions have
negative coordinates, and the unique root is X=1 with positive determinant.
It has degree1 and standard Q by the degree declarations already cited
above. The original no-UE matrix necessities do not dispose of the table.

### All fifteen actual persistent-base screens fail

For each large base E with free set I−E, the COMPLETE free Nash carrier
is the one pure point below. Gap vectors are base players' Quit-minus-
Continue differences in increasing base order.

| E | Free quitters | Base gaps |
|---|---|---|
| 01 | 3 | (−2,2) |
| 02 | 3 | (−2,−2) |
| 03 | 1 | (−2,2) |
| 12 | 0 | (−2,−2) |
| 13 | 2 | (2,−2) |
| 23 | 1 | (2,−2) |
| 012 | ∅ | (2,−2,−2) |
| 013 | ∅ | (−2,2,2) |
| 023 | ∅ | (−2,−2,2) |
| 123 | ∅ | (2,2,−2) |
| I | ∅ | (−2,−2,−2,−2) |

For a pair base one free player receives4 from Continue regardless of
the other action, versus2 from Quit, and therefore strictly Continues.
The second then has Continue0 versus Quit2, so strictly Quits. For a
triple base the sole free player strictly Continues because4>2. This
proves completeness, not only a list of unfavorable selected Nash points.

For singleton anchors use increasing free-player order and hazards x,y,z.
The exact induced response differences are

    anchor0: (−2+4z(1−y), 2−4(x+z−xz), 2−4xy),
    anchor1: (−2+4y(1−z), 2−4x, 2−4y),
    anchor2: (2−4z, 2−4x, −2+4x(1−y)),
    anchor3: (2−4(y+z−yz), 2−4xz, −2+4y(1−x)).

Their unique Nash points and anchor gaps with empty tail0 are

| Anchor | Free Nash point | Quit-minus-nonempty-Continue | Empty probability |
|---|---|---|---|
| 0 | (1,0,1) | −2 | 0 |
| 1 | (1/2,1/2,0) | −1/4 | 1/4 |
| 2 | (1/2,0,1/2) | −1/4 | 1/4 |
| 3 | (0,1,1) | −2 | 0 |

Completeness follows directly. At anchor0, y>0 implies x,z≤1/2; then
the first difference is strictly negative, so x=0 and the third forces
z=1, contradiction. Thus y=0,z=x=1. At anchor3, x>0 implies y,z≤1/2;
the third forces z=0 and the second y=1, contradiction. Thus x=0,y=z=1.
At anchor1, y<1/2 forces z=1,x=0,y=1, while y>1/2 forces z=0,x=1,y=0.
Hence y=1/2. Positive z would force x=0 and then y=1, so z=0,x=1/2.
At anchor2, x<1/2 and x>1/2 similarly contradict the last two response
conditions. Thus x=1/2; positive y would force z=0,x=1, so y=0,z=1/2.

All passive rewards are nonnegative, so Never guarantees0 and each actual
punishment value PUN_i≥0. The literal owner-floor excesses are therefore
2, 1/4+PUN₁/4, 1/4+PUN₂/4 and2, all positive. Smaller free sets cannot
evade the census: their screened outsiders would extend by Continue to
a full-free Nash point already listed.

The exact inspected comparisons are
`quittingPersistentLargeBaseExcess_nonpos_iff`,
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff`,
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` and
`exists_uniformPayoff_or_singletonBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The unrestricted consumers are in the adjacent
`PersistentBaseNashSemanticAdapter.lean` and
`SingletonBaseSemanticDispatch.lean`. This example falsifies an inclusion
into these actual sources, not their soundness.

### Fourteen exact child-debt tests

For each proper nonempty child S, the following pure child equilibrium T
has zero child debt and Never mass. The omitted k gains2 by joining.

| S | T | k |
|---|---|---|
| 0 | 0 | 2 |
| 1 | 1 | 2 |
| 2 | 2 | 0 |
| 3 | 3 | 0 |
| 01 | 0 | 2 |
| 02 | 02 | 3 |
| 03 | 03 | 1 |
| 12 | 12 | 0 |
| 13 | 13 | 2 |
| 23 | 2 | 0 |
| 012 | 02 | 3 |
| 013 | 13 | 2 |
| 023 | 03 | 1 |
| 123 | 12 | 0 |

For singleton T its member earns1 rather than0 by quitting, and any
child nonmember receives4 rather than2 by continuing. For nonsingleton T
each member's relevant passive singleton is0 versus its joining reward2;
the possible child nonmember receives4 rather than2. These are exact
terminal equilibria against arbitrary complete child deviations.
Every fixed nonnegative omitted-regret bound by child debt plus Never
fails for at least one omitted player for each child. The pointwise J
row has nonpositive advance/withdrawal terms, including the five restart
floors bounded by own1, so the five raw withdrawal certificates fail too.
The inspected definitions are in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
No assertion excludes every specially selected child continuation.

### Scope and the remaining mechanism question

All pair partitions fail the two-pair cap theorem because joining the
opposite pair pays2>own1. Every triple contains a favorable pair with
joining gaps2−4=−2, so it fails the six-positive-pair premise of the
triple–singleton collision-box theorem under every relabeling. Every
set of size≥2 is a premium trap; harmful pairs have positive leave gaps,
excluding support-specific and weighted leaver tests there. Mixed-trap
charges fail on the positive singleton premium sums of every triple.
These are bounded comparisons, NOT a complete all-producer exclusion.

No absence of all-proper stationary equilibria is claimed. Such a root
may solve this particular table without settling the raw completion class.
The checkpoint only rejects the shortcut from constant joint-participant
rewards to the exhausted persistent-base or universal child-debt sources.
There is no new existence theorem, export candidate or positive-gap table.

The next question is whether the upper bound P_i on ALL forced-Quit
payoffs can be used at a genuine positive global debt minimum to construct
one complete response-law perturbation lowering total debt. Pure Never
need not be optimal when the cap exceeds P_i: a finite quit time can
preserve earlier high passive outcomes while avoiding later low ones.
The useful input must therefore be the whole stopping-time cap function,
not just the participant bound or a payoff-only projection. No descent
lemma or exactification shortcut is asserted.

## Bounded external mechanism lookup

A catalogue skim of [openai/math](https://github.com/openai/math), followed
by exactly three main-statement/introductory reads, found no direct transfer
to the current UE selector. This is relevance assessment, not a proof audit
or a statement about formal verification.

- Family149, [Uniform Permanence, Theorem1.1](https://github.com/openai/math/blob/main/preprints/Uniform-Permanence-in-Weakly-Reversible-Mass-Action-Systems-October-5-2026/permanence.pdf),
  concerns fixed-positive-rate weakly reversible mass-action systems.
  Its finite concave affine/log-scale trapping device is the useful
  brainstorm. A signed strategic flow would first need a genuine inward
  certificate; neither response cycles nor complementarity roots are
  automatically reaction networks. Fixed-rate bounds also do not supply
  uniform bounds over a regularization parameter.
- Family328, [Nonexpansive Fixed Points, Theorem1.1](https://github.com/openai/math/blob/main/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026/paper.pdf),
  requires a nonexpansive selfmap on a closed bounded convex domain in
  a reflexive space. No complete-cap-preserving strategy selector with
  those properties is produced here. Infinite stopping laws naturally
  use nonreflexive ℓ¹; moving them to ℓ² loses closedness, since uniform
  laws on the first m dates converge there to the zero vector.
- Family104, [Stochastic Mean-Payoff, Theorem1.1](https://github.com/openai/math/blob/main/preprints/Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026/stochastic-mean-payoff-games.pdf),
  is a turn-based two-player zero-sum algorithm. Its reusable comparison
  argument needs monotonicity and discounted scalar-translation symmetry;
  these are not known for a simultaneous four-law Nash selector. A
  fixed-opponent cap computation does not select all opponents.

The research question remains the complete-cap selection/descent question
above. No new conditional architecture or export is proposed from this skim.

## Constant joint rewards: source scope and the complete cap

The current class has r_i(S)=P_i whenever i∈S and |S|≥2, but allows
r_i({i})=s_i<P_i. It must not be confused with a constant participant
reward INCLUDING singleton exits.

### Narrow primary-literature and production check

[Solan–Vieille, Quitting Games, Theorem1.2](https://www.math.tau.ac.il/~eilons/quitting19.pdf)
uses simultaneous independent quitting and terminal Never0, as here. Its
normalized assumptions are s_i=1 and r_i(S)≤1 for every participant.
[Solan, book, Section12.3, Theorem12.11 and Comment12.12](https://www.math.tau.ac.il/~eilons/book.pdf)
gives the same no-positive-participant-premium condition and discusses
nonnegative own levels. Thus P_i=s_i≥0 is covered, while P_i>s_i has the
opposite premium sign. “Constant payoff processes” in these sources means
time-independent tables, not coalition-independent participant payoffs.
This bounded lookup located no general theorem for the joint-only constant
positive-premium class; it is not an exhaustive absence claim.

The precise inspected production predicates are `QuittingCappedJointExit`
and `QuittingWeakSoloExitPreference` in
`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`.
The faithful statement is `theorem1_2` in
`Literature/SolanAndVieille2001.lean`. The broader actual producer
`exists_uniformEquilibriumPayoff_of_productLowPremium` is in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`;
`hasProductLowQuittingPremium_of_noLargerOwnPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumMonotonicity.lean`
moves participant premiums DOWN, not up. At an interior product root in
the strict P_i>s_i class, every Quit premium is
(P_i−s_i)(1−∏[j≠i](1−q_j))>0, so this raw product-low test fails.

The inspected declaration
`exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`
requires every player outside a designated pair to receive exactly its
singleton reward in every coalition it joins. It does not cover a full
four-player positive-premium core. Finally, `IsEscapeGame` in
`Literature/Simon2007.lean` requires a separate `EscapeWitness`, including
closure under the full relation and boundary escape. Reward constancy
does not supply those hypotheses; no such composition was obtained.

### An exact stationary shortcut failure inside the class

Consider three players with singleton vectors

    r(0)=(1,0,3), r(1)=(3,1,0), r(2)=(0,3,1).

Every joint quitter receives2. A nonquitter facing the other pair receives4,
and r(012)=(2,2,2). Thus s_i=1 and P_i=2 for every player. This is a
simultaneous quitting table, not a turn-based approximation.

It has NO exact stationary terminal Nash profile. Write f(i)=i+1 modulo3
for the favorite singleton, and h(i)=i−1 for the harmful singleton. Against
stationary opponents with x=q_f and y=q_h, let a=x+y−xy. For a>0, quitting
now pays Q=1+a, while Never pays C=(3x+xy)/a. Hence the sign of C−Q is
the sign of

    H(x,y)=3x+xy−a−a².

On the square, ∂H/∂x=3+y−(1+2a)(1−y)≥4y≥0. For y>0,

    H(y,y)=y[(1−y)²+y²(3−y)]>0,

and H(x,0)=x(2−x)>0 for x>0. Therefore x≥y and a>0 implies C>Q.
An active stationary quitter must instead have C≤Q: its prescribed value
is a strictly positive mixture of Q and C, and it may replace itself by
Never. Consequently, with all three hazards positive each active row
requires q_f<q_h, an impossible cyclic chain.

With exactly two positive hazards, one active player's favorite is the
other active player, so that row has H(x,0)>0 and also cannot be active.
With just i active, player f(i) receives0 by continuing but has a strictly
positive immediate Quit payoff 1+q_i. With no active player, any player
can quit alone for1. These cases exhaust all cube boundaries, including
sure quitters. This is only an exact stationary exclusion. The known
three-player UE result is entirely compatible with it; no unrestricted
positive gap or new existence coverage is claimed.

### Whole response-function identity and a finite tied-cap test

Fix any independent opponent stopping laws, including Never. Let S_i(t)
be the probability all opponents stop at or after t, with Never after every
finite date. Let A_i(t) be the expected passive reward from opponent first
coalitions strictly before t. Writing d_i=P_i−s_i, the payoff from stopping
at exactly t is

    f_i(t)=A_i(t)+P_i S_i(t)−d_i S_i(t+1).

Indeed, on survival to t, simultaneous opponent quitting pays P_i and
strict opponent survival past t pays s_i. Therefore, if m_i(t,T) denotes
the probability that the opponents' first exit is T at t,

    f_i(t+1)−f_i(t)
      =∑[∅≠T⊆I\{i}] m_i(t,T)(r_i(T)−P_i)
         +d_i(S_i(t+1)−S_i(t+2)).

The true behavioral cap is max(sup_t f_i(t), A_i(∞)), where A_i(∞) is
the Never payoff. This follows from the same pure-time extremality as
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
the value definition and Bellman identity are in
`UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`.
The displayed specialization is ordinary mathematics, not Lean-checked.

Even with s_i=1,P_i=2, there need not be a distinguished finite cap time.
Take two opponents, good and bad, paying player i passive4 and0 respectively;
the fourth player, if present, always continues. For n periods the good
opponent alone has hazard3/5 at the first date, and the bad opponent alone
has hazard1/2 at the second date; both use Never after period n. Their
private stopping laws are independent. Survival of a complete period is1/5.
The passive contribution before period k, indexed from0, is
3(1−5^(−k)). Stopping at that period's bad date gives exactly3:

    3(1−5^(−k))+5^(−k)[(3/5)4+(2/5)(3/2)]=3.

Stopping at its good date gives 3−(7/5)5^(−k)<3. Never gives
3(1−5^(−n)), and stopping after the final period gives
3−2·5^(−n)<3. Thus all n bad dates are complete-cap maximizers, all
above P_i, while Never is strictly worse. No growing calendar creates
an extra unlisted profitable date. This is a fixed-opponent stress test,
not a four-player equilibrium or a genuine global-minimum source.

The class therefore does not make “cap above P_i” mean “Never is optimal,”
and coefficient constancy does not justify retaining only one cap time.
The attempted reduction to a single latest-response direction stops here.
The remaining question is to use the entire response-function identity at
an actual positive global debt minimum to select SIMULTANEOUS law changes
with all four caps controlled. The genuine source is not an arbitrary
fixed-opponent example: `finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`
retains the complete semantic carrier, global debt minimum and singleton
cap margins, but explicitly does not realize that minimum by one profile.
No descent, realization or all-player approximate-law producer has yet
been established from the identity.

## Approximate finite laws with a calendar-independent regularizer

The cyclic local-logit attempt does not close the gap. The actual source
`nonempty_interiorApproximateNashCyclicBlock` in
`UniformEquilibrium/Quitting/Cycles/EndogenousInteriorCyclicBlock.lean`
produces interior local-error blocks, while
`InteriorApproximateNashCyclicBlock.outsiderTerminalDeviationDebt_le` in
`UniformEquilibrium/Quitting/Cycles/InteriorCyclicAbsorptionAlternatives.lean`
requires an opponent absorption denominator. Constant positive collision
premiums do not provide a lower bound on that denominator. In particular,
balanced hazards can all vanish; deleting a one-fast-owner branch would
not delete this branch. No new selection consequence is claimed from this
local-logit construction.

Here is a distinct, explicitly approximate finite-law question. Use the
single-pivot normalized table s=(1,0,0,0), arbitrary remaining rewards,
and F_N={0,…,N−1,Never}. For a product law p put

    μ=(p₀+p₁+p₂+p₃)/4,
    J_i(p)=∑[a∈F_N] p_i(a) log(p_i(a)/μ(a)),
    V_i^τ(p)=U_i(p)−τ J_i(p),               τ>0.

A zero coordinate contributes0. This is a game on the four mixed-law
simplices, not a change to the actual quitting reward table. Each player
chooses its entire private law, and changing that law also changes μ.
There is no public random clock. The precise smaller question is whether,
for arbitrarily small τ, SOME finite N and SOME Nash point of this
regularized game satisfy the missing full pivot bound

    W₀(p)+p₁(Never)p₂(Never)p₃(Never)−U₀(p)→0.

The finite-menu half is already produced, not assumed. Relative entropy
is jointly convex in its two arguments; μ is affine in p_i. Thus J_i is
convex in p_i, whereas U_i is affine. Also J_i is continuous even where
μ(a)=0, since 0≤p_i(a)≤4μ(a), and

    0≤J_i(p)≤log4.

The ordinary compact-concave finite-player Nash existence argument applies:
best-reply sets are nonempty compact convex and their graph is closed.
At such a Nash point, for EVERY unilateral alternative law y_i,

    U_i(y_i,p_{−i})−U_i(p)
      ≤τ[J_i(y_i,p_{−i})−J_i(p)]≤τ log4.

Consequently all four finite-menu regrets are at most τ log4, independent
of N. These assertions are ordinary mathematics, not a Lean claim. A
narrow source search in MathUE and the stopping-law/terminal subtrees
found no existing common-marginal relative-entropy selector declaration.

This regularization has a useful exact support property. At any Nash
point, if one player's law assigns positive mass to a date, every player's
law does. Otherwise adding a small mass at that date has entropy derivative
−∞, overcoming the bounded linear payoff derivative. Therefore all four
laws have the SAME support, including agreement on whether Never is used.
If Never is absent, the produced finite law is already an unrestricted
τ log4 terminal approximate equilibrium: an opponent surely stops within
the calendar, so later deviations add no cap. The unresolved arm has
positive Never mass at every player, not a supplied favorable support.

The first-order identities retain the complete date dependence. Put
r_i(a)=p_i(a)/μ(a), and h(r)=log r+1−r/4. On the common support,

    f_i(a)−τ h(r_i(a))=c_i,

where f_i(a) is the actual pure-time payoff. This includes Never. The
derivative uses μ's dependence on p_i; dropping the −r/4 term would be
incorrect. On (0,4], h is strictly increasing and h(4)=log4. The shares
satisfy ∑_i r_i(a)=4 at every occupied date.

There remains a literal boundary condition when the calendar is extended.
Write α_i=p_i(Never)>0, D_i=∏[j≠i]α_j. Moving pivot mass from Never
to one NEW date after all occupied finite dates has right derivative

    D₀−τ[log4−h(r₀(Never))]

in V₀^τ. At the new date the mover is the only marginal with mass, so the
entropy contribution is exactly its moved mass times log4. A positive
derivative shows that the old law cannot remain regularized Nash after
that extension. It does NOT show that a newly selected Nash point has a
smaller Never mass or a better pivot cap: the other three laws may change.
That selection/escape issue is the remaining smaller assertion. No
calendar-independent late-cap estimate, limiting Nash point, or uniform
payoff follows from the finite regularizer alone. This is the live attempt;
the exact finite-Nash and single-cap-time selectors remain retired.

### Exact bad branch and a change to the actual minimum

The quantifier SOME regularized Nash is essential. The regularizer does
not itself remove the old exact-Nash branch. Define a complete canonical
Fin4 table by s=(1,0,0,0),

    G=((0,1,1,−1),(−1,0,−1,2),
       (−1,2,0,−1),(−1,−1,2,0)),
    r_i(S)=s_i                     if i∈S,
           s_i+∑[j∈S]G_ij          if i∉S.

Let t be the unique root of t=(1−t)³ in(0,1). It exceeds1/4.
On ANY nonempty finite calendar let all four laws put mass t at the
last date and 1−t at Never. The finite pure-time payoff of every player
is its own s_i at EVERY allowed response, including Never. At the last
row the child differences vanish, and the pivot difference is
(1−t)³−t=0; an earlier Quit gives s_i. Hence this is exact finite-menu
Nash. The four laws coincide, so J_i=0. Since all unilateral J_i are
nonnegative, this same profile is regularized Nash for EVERY τ>0.
But the pivot's unrestricted late payoff is1+t, whereas its prescribed
payoff is1. Its full debt remains t. This table is already covered by
product-low UE. The calculation refutes an all-regularized-Nash claim,
not the still-open existential favorable-selector question.

Rather than assuming favorable reselection after a profitable insertion,
the next attempt regularizes the actual full-debt objective. For p on
F_N define the literal full caps

    b₀(p)=max(B₀ᴺ(p), W₀(p)+D₀(p)),
    b_i(p)=B_iᴺ(p) for i≠0,
    D(p)=∑_i(b_i(p)−U_i(p)),
    I(p)=∑_i J_i(p),       Φ_τ(p)=D(p)+τI(p).

All cap tests are retained, including the pivot's late test and Never.
Each player chooses an independent law; no public mixture is introduced.
The exact supplied-profile identity inspected is
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
the existence consumer is
`exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source`
in `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuCompletion.lean`.
Their finite-law source still has to be produced. The present objective
does not replace it by exact finite Nash.

For each N and τ>0, compactness and continuity produce a global minimizer
of Φ_τ. This is joint optimization of the true sum of unrestricted debts,
not Nash equilibrium of an auxiliary game. One has 0≤I≤4log4. If δ_N
is the minimum of D on F_N, its selected minimizer therefore satisfies

    δ_N≤D(p)≤δ_N+4τlog4.

Embedding a law into a larger calendar by zero new masses changes neither
D nor I. Thus δ_N decreases to the infimum δ over all finite independent
laws, and the infima of Φ_τ similarly decrease to some δ_τ with
δ≤δ_τ≤δ+4τlog4. If the normalized original game has no uniform payoff,
the inspected finite-law consumer implies δ>0: otherwise vanishing sums
of full debts would supply both scalar-source inequalities. This is the
genuine global no-UE premise, not an arbitrary selected orbit minimum.

The following extra information holds at each finite global minimizer.

1. All four laws have common support. At a date occupied by another
   player but not by i, inserting i's mass has entropy derivative−∞,
   whereas D has a finite directional Lipschitz bound. Removing that
   mass from a positive coordinate supplies a feasible strict decrease.

2. On the occupied support the derivative of TOTAL I with respect to
   p_i(a) is log(p_i(a)/μ(a)), without the earlier h correction.
   Indeed I=∑_{i,a}p_i(a)log p_i(a)−4∑_a μ(a)log μ(a).
   The h correction belongs to a player's OWN J_i in the auxiliary
   regularized Nash game, not to this joint objective.

3. If |r_i(S)|≤M, changing only p_i changes D by at most
   7M‖Δp_i‖₁. Its own cap is independent of its law; its own payoff
   has Lipschitz constant M. Each of the other three cap-minus-payoff
   terms has constant at most2M. Every cap is a maximum of actual
   affine response payoffs, so this bound includes all tied cap tests.
   Transferring mass between two occupied dates consequently gives

       |log(r_i(a)/r_i(b))|≤14M/τ,
       exp(−14M/τ)≤r_i(a)≤4.

   The second bound uses ∑_a μ(a)r_i(a)=1, hence some r_i(b)≥1.
   It is calendar-independent and covers Never if Never is occupied.
   In particular the selected finite laws, and all their survival tails,
   are mutually comparable by a τ-dependent positive factor.

These are complete ordinary-mathematical facts, not yet a UE producer.
The factor can be exponentially small in1/τ. A full-debt error of orderτ
cannot silently be treated as negligible relative to a variation of that
size. This is an explicit scale obstruction to applying an ordinary
near-minimum Taylor lemma using only these bounds.

There is one exact way around that error for a limited class of variations.
Split any occupied atom a, for ALL players, into consecutively ordered
subdates with the same fractions θ₁,…,θ_m. Replace p_i(a) by
θ_k p_i(a) at subdate k. Each ratio p_i/μ is unchanged on the split
pieces, so EVERY J_i, and hence I, is preserved exactly. The same identity
holds when a Never atom is split into a new last finite date and remaining
Never, in common proportions. The strategic payoffs and caps generally
change, and must be recomputed from the independent product law; entropy
invariance is not payoff invariance or public randomization.

For a fixed τ, choose N and a finite global minimizer whose Φ_τ value
is within an arbitrarily specified η>0 of δ_τ. Any such refinement,
possibly on a larger calendar, then satisfies

    D(refined p)≥D(p)−η.

This follows from the global infimum of Φ_τ and exact entropy invariance,
not from monotonicity of a reselected Nash point. The error η can be chosen
independently of τ. It supplies a concrete full-cap variational restriction
at selected actual near-minimizers.

The current smaller question is whether δ>0 is incompatible with these
regularized global-minimum restrictions: produce a legal simultaneous
clock refinement, or another explicitly controlled law variation, that
strictly lowers the FULL D by more than its entropy change and η. Common
support, likelihood comparability and entropy-neutral refinement alone
do not prove this. No supplied inequality, one-player repair, or assumed
monotone reselection is being counted as an existence result.

## Fixed-temperature relative-clock compactness from the actual minimum

This section is ordinary mathematics, not Lean-checked and not a new UE
class or proposed export. Unlike the earlier finite-menu normalization,
the statement here applies to ANY finite real Fin4 reward table, with
original Never reward0. Fix M>0 bounding every absolute terminal reward.
For an independent finite stopping-law profile p, let U_i(p) be its actual
terminal payoff and b_i(p) its supremum over ALL complete behavioral
responses. Equivalently the cap tests are every finite pure time and Never.
For a finite support these include the response strictly after the last
occupied date, not just the occupied menu. Put

    D(p)=Σ_i[b_i(p)−U_i(p)],
    μ=(p₀+p₁+p₂+p₃)/4,
    I(p)=Σ_i KL(p_i‖μ),
    Φ_τ(p)=D(p)+τI(p),        τ>0,
    m_τ=inf{Φ_τ(p): p is any independent finite-law profile}.

This infimum ranges over every finite calendar; a global near-minimizer
below is not only a minimizer on one fixed calendar. Since D≥0 and
0≤I≤4log4, the infimum is finite and actual η-near-minimizers exist for
every η>0. No no-UE hypothesis or positivity of m_τ is used in the
compactness proof. The previously inspected single-pivot existence
consumer is the justification for δ>0 only in that normalized setting;
it is not silently substituted for a general-table theorem here.

### Actual coarsening, not assumed cap continuity

The needed general source is already implemented. I inspected
`quittingQuantileClockCompressedLaws`,
`hasEscapeAwareQuantileClockCompressionAtBound`,
`quantileClockSupport`, and `quantileClockScaledRadius` in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`.
The related `hasEscapeAwareQuantileClockCompressionAtRewardBound` is its
canonical game-specific reward-bound specialization; the arbitrary M used
here is supplied to the `AtBound` theorem.
Its mathematical content for Fin4 and level j≥1 is a COMMON deterministic
ordered quotient f_j of the stopping calendar, preserving Never as a
separate point, such that q_i=(f_j)_*p_i has at most8j+1 finite dates and

    |U_i(q)−U_i(p)|≤12M/j,
    |b_i(q)−b_i(p)|≤12M/j.                         (RC1)

The second bound is for unrestricted behavioral caps, proved by two-sided
transport of every pure response, including Never and the late finite
response. It is not a supplied stationary or selected-cap estimate. Thus

    |D(q)−D(p)|≤96M/j.                            (RC2)

The map's exact fibers are the singleton marked dates and the consecutive
unmarked intervals. `finiteClockActiveCompressedLaw` is the push-forward
through `finiteClockActiveQuotient` in
`MathUE/Probability/QuantileClock.lean`. Active-cell indexing deletes
unattained clock gaps; it does NOT insert a new response date between
consecutive original marks. This matters for complete-cap transport.
The quantitative finite-clock theorem is existing source material, not
being claimed as new work.

For a quotient fiber C write P_i(C)=p_i(C), μ(C)=Σ_iP_i(C)/4. On the
ORIGINAL calendar define the common-conditional reconstruction

    p̂_i(a)=μ(a) P_i(C)/μ(C),       a∈C, μ(C)>0,

and assign0 on zero-μ fibers. This is a probability law. Its quotient is
q_i, and (Σ_i p̂_i)/4=μ. Direct cancellation in the finite entropy sums
gives the exact chain rule

    I(p)−I(q)=Σ_i KL(p_i‖p̂_i)≥0.                 (RC3)

For example the summand difference on C is
Σ_{a∈C}p_i(a)log[p_i(a)/μ(a)]
−P_i(C)log[P_i(C)/μ(C)], exactly KL(p_i‖p̂_i) on C.
Zero probabilities are interpreted by continuity; a positive p_i(a)
always has positive reconstructed mass. Never is a singleton fiber, so
its contribution to this loss is zero and its four masses are retained.

Suppose Φ_τ(p)≤m_τ+η. The compressed q is an ACTUAL finite independent
profile in the same global optimization domain. Hence

    τ[I(p)−I(q)]≤D(q)−D(p)+η≤96M/j+η.             (RC4)

This is where genuine global near-minimality enters. The estimate would
not follow for an arbitrary common-support profile, an auxiliary Nash
point, or an optimizer restricted to a shorter calendar than q uses.
Pinsker's inequality, with natural logarithms, and Cauchy–Schwarz yield

    Σ_i ‖p_i−p̂_i‖₁²≤2(96M/j+η)/τ,
    Σ_i ‖p_i−p̂_i‖₁≤√[8(96M/j+η)/τ].             (RC5)

No comparison between τ and a Never product was used. The estimate says
that a genuine regularized near-minimizer cannot hide much player-specific
timing information inside quantile cells whose strategic effect is small.
It is stronger than merely bounding each player's total entropy.

### One fixed quantile domain and genuine strong compactness

Order the finite dates and then Never. On the fixed interval[0,1], give
each date a a half-open interval J_a of length μ(a), in that order; an
empty interval can be discarded. Define

    r_i(x)=p_i(a)/μ(a)                 on J_a.

Thus 0≤r_i≤4, Σ_i r_i=4 almost everywhere and ∫r_i=1. The last interval
has length μ(Never) and records Never separately. A common quotient fiber
C is a consecutive union of these intervals, so the density of p̂_i is
the CONSTANT P_i(C)/μ(C) on that union. In particular the four reconstructed
densities are step functions on the SAME[0,1], with a common partition
of at most8j+2 intervals, including Never. Moreover

    ∫|r_i−r̂_i|=‖p_i−p̂_i‖₁.                    (RC6)

This identification does not relabel each player independently and does
not introduce a common random draw. Each player's quantile draw remains
independent; the interval representation merely uses the common marginal
as a deterministic coordinate chart.

For fixed K, the family of four bounded step functions with at most K
common intervals is compact in the joint L¹ norm. Indeed parameterize it
by ordered endpoints0=t₀≤⋯≤t_K=1 and heights in[0,4]^{4K}.
This parameter domain is compact, and moving endpoints by small amounts
changes the functions only on intervals of small total length. Moving
heights is continuous in L¹ as well. Zero-length intervals cause no
problem. Consequently the parameter-to-function map is L¹-continuous.

Now fix τ>0 and any sequence of actual finite profiles pⁿ with
Φ_τ(pⁿ)≤m_τ+η_n, η_n→0. Given an L¹ tolerance, first choose one finite
j so that the limiting right side of(RC5) is below that tolerance, then
discard finitely many n to control η_n. The remaining quantile density
tuples lie within that tolerance of one compact K-step family. This proves
total boundedness, hence a subsequence converges STRONGLY in(L¹[0,1])⁴:

    r_iⁿ→r_i*,       0≤r_i*≤4,
    Σ_i r_i*=4 a.e.,       ∫r_i*=1.               (RC7)

This is not a weak-compactness assertion dressed as strong convergence.
Its substantive input is the near-minimum entropy-loss bound(RC4).
Since xlog x extends continuously and boundedly to[0,4], strong L¹
convergence gives

    I(pⁿ)=Σ_i∫r_iⁿ log r_iⁿ → Σ_i∫r_i*log r_i*.  (RC8)

If the sequence is chosen from exact minimizers on its increasing finite
calendars, the earlier transfer estimate additionally gives
r_iⁿ≥exp(−14M/τ) almost everywhere. The same lower bound passes to r_i*.
This extra bound is not needed for(RC7), and it does not remain uniformly
positive as τ→0.

### Never, collisions and the still-open realization step

Passing to a further subsequence, let a_n=μⁿ(Never)→a∈[0,1]. The four
Never masses also converge. If a>0, each limiting density is constant
almost everywhere on the terminal interval(1−a,1), with integral equal
to that player's limiting Never mass. This follows from the constant
Never density on each moving terminal interval and strong L¹ convergence.
Under the likelihood lower bound, a>0 makes all four limiting Never
masses positive; a=0 makes all of them zero. Neither alternative has
been excluded by the minimum argument.

The relative densities are NOT a complete strategic state. A finite
atom J_a represents simultaneous quitting whenever two independent draws
fall in that SAME interval, not two successive real times inside it.
The marked atom intervals must therefore be retained along with r_i.
Likewise an unoccupied date between two consecutive supported dates is
an extra pure response; a nonexistent gap must not be silently inserted.
The active-cell source in(RC1) already respects this distinction.

For a simple exact illustration, take all four laws equal. Then r_i≡1
for every player, regardless of their atom partition. Let each participant
receive1 when it is the sole quitter and−1 in every coalition of size≥2,
and let every nonparticipant receive0. If all laws put mass1 at date0,
each prescribed payoff is−1 and each cap is0 (Never). If all laws instead
are uniform on0,…,N−1, collision probability tends to0; symmetry gives
prescribed payoff tending to1/4 for each player, while the date0 cap
tends to1. Both families have IDENTICAL quantile densities and I=0,
but their semantic limits differ. Thus(RC7) alone proves neither payoff
nor cap convergence, let alone an original discrete-clock minimizer.

The same distinction occurs on ACTUAL global near-minimizers, not merely
arbitrary profiles. A subsequent exact stress supplied by CODEX_NOETHER
uses the common-payoff table r_i(S)=1 for |S|=1 and0 otherwise. Sure-all
at date0 is terminal Nash with payoff0, caps0 and I=0, so m_τ=0 for every
τ>0. If instead all four laws are uniform on{1,…,L}, all likelihood
functions are still identically1 and I=0. The payoff of each player is
the probability of a unique earliest draw,

    (4/L⁴)Σ_{k=0}^{L−1}k³=(1−1/L)².

The pure date0 response earns1, which is the maximal reward, so every cap
is1 and D=8/L−4/L²→0. Thus both the sure-all sequence and this uniform
sequence are genuine Φ_τ-near-minimizing sequences with the SAME density
functions but different limiting prescribed payoffs and caps. Keeping
their different tied-atom and tester marks is indispensable even under
the actual global-minimum premise. This does not contradict(RC7).

The next concrete question is to retain, on the same subsequence, the
nonvanishing tied intervals and the closed set of available pure-response
locations. A possible representation collapses each retained interval to
one simultaneous date and leaves the remaining quantile mass diffuse;
Never remains separate. Even if that produces independent laws and all
caps on a compact ORDERED calendar, that calendar need not embed in ℕ.
Such an attained relaxed minimum must be distinguished from an actual
discrete-calendar minimum. No such realization theorem, no τ→0 compactness,
and no tail-descent conclusion is asserted by(RC1)–(RC8).

The useful surviving target is now precise: can the atom-and-tester limit
be consumed by a legal full-cap variation, or by a uniformly controlled
finite-clock reconstruction, to force the unregularized global infimum
to zero? A common-support assertion or a supplied tail inequality would
not answer it. In particular an η error still cannot be divided by a
vanishing joint Never mass without an additional argument.

### Retaining tied atoms and the entire tester set

The following completes a REPRESENTATION of the fixed-τ selected limit.
It is not a realization on the original natural-number calendar. Its
point is to keep the complete cap coordinates, not only prescribed
payoffs, in the relative-clock limit.

**Proposition.** After a subsequence of the profiles in(RC7), there are a
compact ordered set T⊆[0,1], a distinguished extra Never point, and four
independent probability laws q_i on T∪{Never} such that:

1. the law of the first quitting coalition, including Never, is the limit
   of the original prescribed coalition laws;
2. each original unrestricted cap b_i(pⁿ) converges to the supremum over
   EVERY pure time in T and Never against q₋ᵢ;
3. I(q)=lim I(pⁿ), so D_T(q)+τI(q)=m_τ.

Here D_T uses all the just-specified cap tests on T. This is exact
attainment of the numerical regularized infimum by independent laws on
a compact ORDERED calendar. It does not assert that this calendar embeds
in ℕ, that the q_i are original behavioral strategies, or that arbitrary
changes of the calendar are automatically admissible minimum-preserving
variations. Those are separate strategic questions.

**Proof.** Let c_n=1−μⁿ(Never). Let E_n be the endpoints of all the
positive-μⁿ atom intervals, including0,c_n,1. For every original finite
pure response time t use its quantile location

    x_n(t)=μⁿ({a:a<t})+μⁿ(t)/2.

Thus a supported date is the midpoint of its tied atom interval, whereas
an unoccupied date is its preceding cumulative mass. All dates after the
last supported finite date have the SAME location c_n and the same
payoff against the source opponents. Let T_n be the finite set of these
locations. It includes c_n. Never remains an extra isolated response;
it is not identified with the last finite test, for either sign of the
singleton reward.

The E_n and T_n are nonempty compact subsets of[0,1]. Compactness of the
Hausdorff hyperspace, together with c_n→c, permits a common subsequence
with E_n→E and T_n→T. The already obtained strong density convergence is
retained. We have0,c,1∈E and T⊆[0,c], with c∈T. The open interval(c,1)
is the limiting Never interval.

Each component J=(a,b) of[0,c]∖E is the limit of ONE actual atom interval
J_n=(a_n,b_n), with a_n→a,b_n→b. To see this, any compact subinterval
of J eventually contains no endpoint from E_n; it is therefore contained
in a single original atom. Hausdorff convergence forces that atom's two
endpoints toward the endpoints of J. The limiting r_i* is constant
almost everywhere on J, because the approximating density is constant
on J_n and converges strongly. Moreover

    T∩J={(a+b)/2}.                               (RC9)

Indeed the only original pure-time location in the interior of J_n is
its atom midpoint. This proves both inclusion directions in(RC9).

Define an order-preserving collapse π on[0,1], ignoring null endpoints:
collapse each J to its midpoint, leave x∈E∩[0,c] unchanged, and send
(c,1) to Never. This map has values in T∪{Never} almost everywhere.
The only point requiring justification is E∖T: it is null. On any open
interval disjoint from T, the set E has at most one point. Otherwise two
nearby original endpoints inside that interval would enclose an original
atom midpoint there, contradicting Hausdorff convergence of T_n. There
are countably many components of the complement of T, so E∖T is at most
countable. Endpoint conventions have zero Lebesgue measure.

Let q_i be the push-forward under π of r_i*(x)dx. Use INDEPENDENT draws
for the four players; the common chart is deterministic. The reference
mixture of the q_i is π_*dx. Because each r_i* is constant on every
collapsed positive-length interval, including Never, this push-forward
loses no player-identity entropy. Consequently

    I(q)=Σ_i∫r_i*log r_i*=lim I(pⁿ).              (RC10)

For payoff convergence, represent the original profile in the same way
using π_n, which collapses each original atom to its midpoint and its
Never interval to Never. Its product density on[0,1]⁴ converges in L¹ to
the limiting product density: telescoping gives an upper bound by the
sum of the four marginal L¹ distances. With that density difference
removed, compare outcomes at a fixed tuple of quantile draws.

Outside a Lebesgue-null set, no draw equals c or an endpoint of any
component of[0,c]∖E, and no two distinct draws are equal. Whether two
finite draws are in the same actual atom then stabilizes: if they lie
in one component J, both eventually lie in J_n; otherwise some limiting
endpoint strictly between them eventually separates their original
atoms. An exception in the latter assertion would put a draw at a
component endpoint, already excluded. The Never membership of each draw
also stabilizes. Thus the first quitting coalition stabilizes almost
everywhere. Bounded convergence proves convergence of every coalition
probability and every prescribed payoff.

Now retain a moving pure response x_n∈T_n with x_n→x∈T. Its payoff
against the other three laws converges to the actual pure-x payoff
against q₋ᵢ. If x is the midpoint of a component J, (RC9) forces x_n to
be the corresponding atom midpoint eventually; the same-atom coalition
is retained exactly. Otherwise x∈E, and no opponent draw equals x with
positive Lebesgue probability. A large atom cannot cross this cut except
by having x as an endpoint; available response locations then approach
that atom only from the correct side, since its midpoint stays a positive
distance away. All remaining order and tie tests stabilize as in the
prescribed-payoff argument. The Never response is handled separately by
the same opponent first-coalition convergence. This proves convergence
for EVERY convergent sequence of available test locations, not just a
preselected maximizing response.

The limiting pure-time payoff is continuous on T: a retained atom
midpoint is isolated from all other available locations by its half-length,
and elsewhere the preceding cut argument applies. Never is isolated as
a tester label. Hence the limiting maximum is attained. For the upper
cap bound choose a maximizer in each finite T_n∪{Never} and extract a
convergent subsequence; the preceding paragraph bounds its limit by the
limiting cap. For the lower cap bound approximate a limiting maximizer
using Hausdorff convergence (or use Never unchanged). This proves both
cap inequalities and therefore the claimed full cap convergence.
Combining it with(RC10) and Φ_τ(pⁿ)→m_τ proves the proposition. ∎

This proof permits diffuse limiting time and tied atomic time together.
It does not turn a common quantile draw into public randomness. It also
does not assume that a Hausdorff limit of dates has every empty cut
available: T is the limit of the ACTUAL test locations. In particular a
cut between two adjacent nonvanishing tied atoms need not belong to T.

There is still a real variational boundary. A response location with zero
prescribed marginal mass can represent several collapsing empty dates;
the current semantic pair does not record their multiplicity. Giving
positive new mass to such a location can expose distinct before/tie/after
tests. Likewise a compact continuum T need not have the order type of
a subset of ℕ. Consequently numerical attainment at the represented q
does NOT justify arbitrary calendar changes or an original-game exact
minimizer. A proposed descent must either be transported to actual finite
profiles with all resulting tests, or prove a finite-reconstruction theorem
for the changed marked calendar. This is the next consumer question,
rather than a claimed closure of the positive-global-debt problem.

### Finite atomic replacements with the mandatory late test retained

Here is a smallest finite-amplitude variational domain for the represented
minimum. It is ordinary mathematics, and still not a descent theorem.

Take the selected represented profile q on T∪{Never} above, with
c=max T. Its prescribed mass at c is zero: c is an endpoint of the
finite quantile interval, never a midpoint of a positive-length finite
atom. Adjoin ONE new empty finite response c⁺>c, distinct from Never.
This does not change q's prescribed values or caps, since both c and c⁺
are after all prescribed finite stopping mass.

For each player choose an arbitrary λ_i∈[0,1] and a finitely supported
probability law ν_i on T∪{Never}. All choices may be made simultaneously.
Set

    q_i'= (1−λ_i)q_i+λ_iν_i.                     (RC11)

The claim is that there are independent finite laws p_i^{n,prime} on the
ORIGINAL natural-number calendar such that their prescribed coalition
laws, EVERY player's unrestricted behavioral cap and their total entropy
converge to those of q' on the enlarged tester calendar
T⁺=T∪{c⁺}, with Never separate. In particular

    D_{T⁺}(q')+τI(q') ≥ m_τ
                         =D_T(q)+τI(q).          (RC12)

Every pure time in T⁺ and Never is in the limiting cap; no selected
response is omitted. The extra c⁺ is ESSENTIAL when ν_i assigns mass to
c. In the original game a player can always quit strictly after the new
last finite atom. A compact calendar that simply makes c its last action
would miss exactly that response and could give a false inequality.
The claim permits ν_i(Never)>0 and arbitrary signed rewards.

The earlier exact G-table regression is a direct test of this completion:
on the menu{0,Never}, all four laws (t at0,1−t at Never), where
t=(1−t)³, have menu caps equal to their prescribed vector s=(1,0,0,0).
But the extra finite date after0 gives pivot cap1+t, hence actual total
debt t rather than0. This is exactly the response c⁺ that(RC12) retains.
No new selector or constant claim is inferred from that regression.

**Finite transport proof.** Let Z be the union of the finite supports of
the four ν_i after removing Never. For a point z∈Z already carrying
positive prescribed mixture mass, z is the midpoint of a retained tied
interval and is isolated in T. Use its corresponding original atomic
date. Its probability vector converges, so adding the four chosen masses
there preserves simultaneous quitting literally.

For a z with zero prescribed mixture mass, choose a shrinking interval
around z, disjoint from the neighborhoods for other points of Z and
eventually disjoint from EACH fixed positive atom not at z. Small atoms
may accumulate at z; they are not excluded individually at a fixed stage.
The neighborhood's original prescribed
mass can be made to tend to zero. This follows from weak convergence of
the original quantile-location mixture to π_*dx and the fact that the
limit has no atom at z. Choose the intervals to shrink slowly enough
that their widths dominate the Hausdorff errors of T_n→T; pass to a
diagonal subsequence if necessary. Inside each such interval consolidate
ALL its original response dates to one date, by a common monotone
coarsening. The union is a consecutive original-calendar block because
the quantile locations are ordered. Choose that date as the image of z.

At z=c take the block through the original last finite support and the
first empty date beyond it; later empty dates are not removed. They
become the single extra response c⁺ in the limiting description.
At every other zero-mass point the consolidation removes spurious
multiple empty dates which had the same limiting quantile location.
For a positive atom no such removal is needed. The consolidations
change only a vanishing amount of prescribed probability; all other
date order and nonvanishing simultaneous atoms remain unchanged.

Now on this actual coarsened calendar mix each player's coarsened law
with the finite law placing its ν_i masses at the chosen common dates,
using the weight λ_i. Keep its ν_i(Never) mass literally at Never.
The four randomizations are independent private randomizations. This
constructs p^{n,prime}, not merely a candidate limiting payoff vector.

Prescribed coalition-law convergence follows by coupling the base laws
as in the representation proof and the finitely many inserted atoms
exactly. A positive base atom and an inserted atom intended to coincide
use the same date. At a formerly zero-mass point, the probability of any
base draw in its shrinking consolidated block tends to zero. Thus only
the deliberately inserted masses can create a new nonvanishing tie.

For the caps, classify ANY sequence of pure response dates in the
modified finite profiles, passing to a subsequence. Away from Z its
limit is an old available time in T, and the previous moving-tester
argument applies. At z∈Z there are exactly three possible limits of its
position relative to the inserted atom: before, coincident, or after.
Coincident is the pure-z test itself. A before limit can survive the
consolidation only if T has available times approaching z from below;
otherwise Hausdorff convergence puts all nearby original tests inside
the consolidated block. When that approach exists, its limiting payoff
is bounded by the supremum of the actual pure tests of q' at those
times. The same argument applies to an after limit at an interior point.
At c an after response always exists and is exactly the additional c⁺
test. Never is unchanged and treated separately. This gives the upper
cap bound for EVERY possible maximizing sequence, including responses
which cease to attain a maximum in the limiting calendar.

For the lower bound, every fixed time of T∖Z is approximated by original
dates outside the shrinking blocks, each time of Z has its exact chosen
date, and c⁺ is realized by a date after the new last occupied one.
Never is literal. Taking the supremum supplies the opposite cap inequality.
Thus the transport controls the complete caps in both directions; a new
atom's before/tie/after tests have not been collapsed to its tie test.

Entropy convergence also survives the insertion. On the unchanged base
part the four densities are (1−λ_i)r_iⁿ and converge in L¹. Their
common-marginal entropy integrand is the continuous bounded function

    H(y)=Σ_i y_i log[y_i/(Σ_j y_j/4)],
    H(0,0,0,0)=0,

on[0,4]⁴. At a retained positive atom the total four masses after
insertion converge and their entropy contribution is continuous in
that finite vector. At a zero-mass insertion, the vanishing base mass
contributes no limiting entropy: 0≤H(y)≤(Σ_i y_i)log4, so its total
contribution is bounded by that mass times log4. The remaining inserted
mass vector contributes its exact finite-atom entropy. Never is handled
by the same finite-vector argument. Hence I(p^{n,prime})→I(q').

Each transported p^{n,prime} is in the original domain defining m_τ.
Taking the limit of Φ_τ(p^{n,prime})≥m_τ proves(RC12). ∎

This gives the represented minimum a concrete simultaneous finite-law
variational domain, rather than assuming all compact-calendar changes
are legal. It does not claim a negative direction. In particular choosing
one player's current best response can raise the other three COMPLETE
caps, and mixing all four best responses can create new tied outcomes.
The remaining research problem is to use(RC12), with its full tester
completion, to produce a quantitative debt decrease when the original
unregularized global infimum is positive. No universal gain/leakage estimate
that does so has yet been established.

## An actual late release and its complete cap account

This section leaves the fixed-temperature objective behind. Its source is
an actual sequence of independent finite laws with D tending to its global
infimum over ALL such laws. It does not assume positive likelihood ratios,
entropy convergence, or that a compact ordered calendar is an ℕ calendar.
The conclusion excludes one branch of a putative minimum, not every
positive minimum and not a new raw existence class.

Let I be finite, r any bounded real quitting table, and assume only that
the own singleton rewards s_i=r_i({i}) are nonnegative. For an independent
finite law profile p write U_i for its prescribed terminal payoff, b_i for
the cap over every pure natural-number time AND Never, and

    D(p)=Σ_i(b_i−U_i),   α_i=p_i(Never),
    β_i=∏[k≠i]α_k,      ρ=∏_i α_i.

Suppose α_i>0 for every i. Let W_i be player i's payoff from literal Never
against p_{−i}. At any date after all finite opponent support, pure Quit
has value W_i+β_i s_i. Thus define the nonnegative late buffer

    d_i=b_i−W_i−β_i s_i ≥0.                       (LR1)

For distinct i,j put

    C_ij=max(0, r_i({j})−s_i, r_i({i,j})−s_i),
    A_j=Σ_i r_i({j}).                             (LR2)

These are actual reward entries, not continuation annotations.

### Exact finite construction and all response tests

Choose j and 0≤θ≤1. Keep every original finite draw unchanged. Of player
j's original Never mass, privately send the fraction θ to a new date t
strictly AFTER an empty separating date beyond the entire old finite
support. Leave its remaining Never mass at Never. Do not alter any other
player's law. This is one legal independent finite profile p^{j,θ}; no
common/public random variable is used. There are still natural-number
dates strictly after t.

Only the original all-Never event changes its prescribed outcome: it now
has singleton {j} with conditional probability θ. Consequently

    U_i(p^{j,θ})−U_i(p)=ρθ r_i({j})               (LR3)

for EVERY recipient i. The mover's cap b_j is unchanged, because it is
a function only of its opponents' unchanged laws.

Fix i≠j. Every old finite response up through the empty separator is
unchanged. Such responses already attain b_i: the finite support gives
only finitely many different finite response values, and the old Never
value W_i is no larger than the old late response W_i+β_i s_i. The three
possibly new response values are exactly

    tie at t: W_i+β_i[(1−θ)s_i+θr_i({i,j})],
    after t:  W_i+β_i[(1−θ)s_i+θr_i({j})],
    Never:    W_i+β_i θr_i({j}).                  (LR4)

The Never value is bounded by the after-t value because s_i≥0. Dates
before t but after the separator give the old late value. Equations
(LR4), together with every retained old test, exhaust ALL pure responses.
Complete behavioral deviations have the same cap, since their private
stopping law averages these pure-time/Never values. Therefore

    b_i(p^{j,θ})−b_i(p)=[β_i θ C_ij−d_i]⁺,

    [D(p^{j,θ})−D(p)]/(ρθ)
      =−A_j+Σ[i≠j] α_i⁻¹[C_ij−d_i/(β_iθ)]⁺    (LR5)

when θ>0. This equality measures the entire cap leakage; it does not
discard late tests or replace a cap by one selected best reply.

In particular, if A_j>0 and d_i>0 for every i≠j with C_ij>0, choose
θ>0 small enough that β_i θ C_ij≤d_i for all such i. All caps then stay
EXACTLY fixed, and D decreases by ρθ A_j>0. The profile produced here
is finite and literal, not merely an element of a relaxed carrier.

### Consequence at a genuine finite-law infimum

Let pⁿ be a sequence of independent finite profiles with D(pⁿ)→D_*,
where D_* is the infimum over all independent finite profiles on ℕ.
Suppose, after taking a subsequence, that

    α_iⁿ→α_i>0,  b_iⁿ→b_i,  W_iⁿ→W_i.

Set β_i=∏[k≠i]α_k and d_i=b_i−W_i−β_i s_i. These limits are supplied
by the marked-calendar representation when its joint-Never atom has
positive mass; no fixed-τ density lower bound is being imported.

For any fixed j and θ>0 the construction above is legal at EVERY n.
Since D(p^{n,j,θ})≥D_*, taking limits in the unscaled form of (LR5)
and then letting θ decrease to zero gives

    A_j ≤ Σ[i≠j, d_i=0] C_ij/α_i.                (LR6)

Here ρⁿ→ρ>0, so the original near-minimum error vanishes before division
by ρθ. No assertion of a rate uniform as ρ→0 is made. More directly,
if the strict-buffer condition above holds at the limit, a single fixed
small θ works for all sufficiently large n and produces a decrease
bounded below by (ρ/2)θA_j, contradicting D(pⁿ)→D_*.

Thus every positive-social singleton j must be blocked by at least one
DIFFERENT player i whose late response binds, with C_ij>0. The stronger
weighted inequality (LR6) retains the amount of blocking required. In
particular, a positive-Never minimum cannot have all late buffers strict
if even one singleton has positive social sum.

### The positive-social singleton is supplied by the Fin4 no-UE source

For Fin4 define Γ_ij=r_i({j})−s_i, including Γ_ii=0. The declaration
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
produces, from bare original-game no uniform payoff, simplex weights w
with Γw strictly positive in every row. The exact matrix definition is
`quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`.
The same source file also proves
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`;
no supplied normality or homogeneous root is required.

Since Σ_i s_i≥0 here,

    Σ_j w_j A_j=Σ_i s_i+Σ_i(Γw)_i >0.

Some A_j is therefore strictly positive. Consequently the all-strict
late-buffer branch is impossible for a positive-Never global minimizing
sequence of a nonnegative-own-singleton Fin4 counterexample. This does
NOT assume that arbitrary signed rewards can be shifted without changing
Never; it states its own-sign hypothesis explicitly.

The related existing declaration
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`, and its literal
late-time limit and one-law movement precursors, were inspected in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
They charge ρs_i against individual debt. Equations (LR4)–(LR6) instead
keep the other players' complete cap changes when that movement is made.
No new Lean check was run.

### Exact check and remaining branch

Take r_i({i})=1, r_i(S)=2 when i∈S and |S|≥2, and r_i(S)=0 when
i∉S. Give all four players probability 1/2 of date0 and 1/2 of Never.
Then α_i=1/2, β_i=1/8, ρ=1/16, W_i=0, b_i=15/8, U_i=15/16,
and d_i=7/4. Here A_j=1 and C_ij=1 for i≠j. Releasing θ=1/2 of
one player's Never mass at a new late date leaves all caps 15/8 and
decreases D by exactly 1/32. This is a check of a literal variation,
not an uncovered game: the table already has a pure all-quit equilibrium.

The live obstruction is now explicit. Either a represented minimum has
zero joint-Never mass, or its binding late tests satisfy (LR6). The
standard-Q positive simplex does not by itself overcome those binding
cap charges. A useful next step must produce a simultaneous ordered tail
with gain exceeding that COMPLETE leakage, or a different legal variation
when ρ=0; repeating the strict-buffer argument does not settle either.

### Bounded source comparison for the late-release account

The inspected all-player escape declarations concern a different operation.
`QuittingTerminalSemanticEscapeAccount` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeAccount.lean`
records finite-coalition mass lost when converging marginal laws are
reconstructed. Its exact identity
`debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeDebtJump.lean`
balances that reconstruction's debt jump against escaped social reward
and cap drops. The consequence
`capDropSum_nonneg_and_le_escapeSocialReward_of_minimum` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeMinimumConsequences.lean`
applies at a supplied carrier minimum. The sign-chamber theorem
`reconstructedDebtJump_nonpos_of_singleton_nonneg_socialReward_nonpos` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`
uses nonpositive aggregate reward at EVERY coalition. None is a formula
for deliberately releasing one conditional Never atom and enumerating
the new collision and late responses as in (LR4). This distinction is
about the mathematical operation; no novelty claim is made for the
general principle that social surplus must pay for cap changes.

## A complete binding-late trap for the Never-tail-only mechanism

The next stronger attempt was: perhaps standard-Q, positive Never mass
and positivity of current debt guarantee some simultaneous independent
Never-tail replacement with lower debt. The following exact example
refutes that implication even for R₀ degree one. It is NOT a global
minimum and NOT a counterexample to UE. Its purpose is to identify
exactly why retaining genuine global minimality matters after (LR6).

Pair the players by f=(01)(23), set s=(1,0,0,0), and specify the entire
original reward table, with Never0, by

    r_i({i})=s_i;
    r_i({j})=s_i+4 if j=f(i), and s_i−1 otherwise, for j≠i;
    r_i(S)=s_i+1 if |S|≥2 and i∈S;
    r_i(S)=s_i+9 if |S|≥2 and i∉S.               (BT1)

Thus this test already has the single-pivot own-singleton vector; no
claim about transporting a selected minimizing law under affine reward
normalization is needed.

The singleton matrix and inverse are

    Γ = [[0,4,−1,−1], [4,0,−1,−1],
         [−1,−1,0,4], [−1,−1,4,0]],
    Γ⁻¹=(1/24)[[1,7,2,2], [7,1,2,2],
                [2,2,1,7], [2,2,7,1]],
    det Γ=192.                                  (BT2)

It is R₀. Indeed Γx≥0 with x≥0 forces positivity in the other pair
as soon as either pair has positive total; it then forces positivity
of all four coordinates. Complementarity would force Γx=0, hence x=0.
At offset −1, Γx≥1 forces all coordinates strictly positive, and the
unique complementary root is x=(1/2,1/2,1/2,1/2), with positive full
index. Thus the R₀ degree is one and Γ is standard Q. The source
declarations inspected for this exact inference are
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. This is an ordinary exact
matrix calculation, not a Lean instance checked here.

### A global inequality for EVERY independent tail

Let v be ANY independent natural-number-or-Never stopping profile for
(BT1), including unrestricted behavioral profiles through their stopping
laws. Put a=P(at least one clock is finite). Write U_i(v), b_i(v) for
its actual payoffs and complete caps. Then

    b_i(v)≥s_i for every i,
    Σ_i[b_i(v)−s_i] ≥ a,
    Σ_i U_i(v) ≤21a.                            (BT3)

The first inequality is supplied by pure Quit at date0: it pays s_i when
no opponent quits there and s_i+1 otherwise. For the second, define
S_{−i} as the first coalition among i's opponents, empty if they all
choose Never. The limiting pure late-Quit value is

    s_i+E[(r_i(S_{−i})−s_i) 1_{S_{−i} nonempty}].

This late limit is bounded by the actual cap, even for unbounded stopping
laws. Sum these four inequalities and condition on the first coalition S
of the complete clock tuple. When S is empty the summed integrand is0.
When S={j}, the three outside recipients contribute 4−1−1=2, while
recipient j's later-opponent contribution is at least−1; the total is
at least1. When |S|=2, the two outsiders each contribute9 and the two
participants each at least−1, giving at least16. When |S| is3 or4,
all four contributions are9. Thus the integrand is always at least
1_{S nonempty}, proving the second inequality. The largest social reward
of a coalition is21, achieved by any pair; singleton, triple and grand
social rewards are3,13,5 respectively. This proves the third inequality.
The actual late-limit declaration used here is
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`.

### A positive-debt profile that every nontrivial tail makes worse

Set α=1/32. Independently give each player mass1−α at date0 and massα
at Never. Its pure date0, Never, and late values are respectively

    Q_i=s_i+1−α³,
    W_i=s_i+9−25α²+(16−s_i)α³,
    b_i=W_i+α³s_i=s_i+9−25α²+16α³.              (BT4)

There are no other distinct cap values. Since b_i>Q_i, every player's
complete cap is its late value; the LR1 LATE buffers d_i vanish for all
four players, not their terminal deviation debts. The common
formula for the prescribed payoff is U_i=(1−α)Q_i+αW_i, and

    b_i−U_i=(1−α)(b_i−Q_i)+α⁴s_i>0.

Now replace ALL four Never atoms by any independent tail v, after an
empty separating date. The new tail may use any number of dates,
unbounded private stopping times and Never. Its pure responses include
every before/tie/after time; none is restricted to prescribed support.
Old tests remain available before the tail. Direct conditioning gives

    U_i'=U_i+α⁴U_i(v),
    b_i'=b_i+α³[b_i(v)−s_i],
    D'−D=α⁴(32Σ_i[b_i(v)−s_i]−Σ_iU_i(v))
         ≥11α⁴a.                                (BT5)

Thus every nontrivial tail strictly INCREASES debt, and the all-Never
tail leaves it unchanged. This rules out an arbitrary-amplitude,
arbitrary-calendar tail rescue, not merely a one-atom or first-order
candidate. All identities use original Never payoff0.

Yet (BT1) has the exact pure equilibrium {0,2}: each participant i receives
s_i+1 and would receive s_i−1 by leaving, while each outsider i receives
s_i+9 and at most s_i+1 by joining. Hence D_*=0; the source (BT4) is NOT a global
minimum. The counterexample does not falsify the actual-minimum route.
It falsifies replacing that source by its Q/R₀ data, positive debt and
the COMPLETE family of nonnegative Never-tail variations. A proof for
the binding-late branch must additionally consume global comparisons
that alter the old finite part; the tail inequality alone cannot do it.
No export or constant-optimization task is proposed for this example.

## Changing old finite mass: a strict-cap-region descent

The following move changes the OLD laws, not only their Never continuations.
It consumes a finite-profile branch, but its extension to an accumulating
ordered calendar has a genuine scale obstruction stated below.

Fix a finite profile p with α_i>0, nonnegative own singletons, and
S₀=Σ_i s_i>0. Keep each player's current finite support fixed and retain
Never as an available action. On this finite product of simplex faces let

    L_i(x)=W_i(x)+β_i(x)s_i,
    F(x)=Σ_i L_i(x)−Σ_i U_i(x).                  (OF1)

L_i is the actual payoff of quitting after every opponent support point.
It is affine in EACH opponent's law separately. U_i is affine in each
player's law separately. Thus F is a multi-affine polynomial in the
players' finite action masses, with their Never mass the residual.
At the all-Never vertex, F=S₀.

Assume that at p every complete cap is L_i(p), and that every pure
response whose payoff FUNCTION on this product face is not identically
L_i is strictly smaller at p. Only finitely many response functions occur:
the displayed dates, their empty intervening intervals, a late date and
Never. The Never function is identical to L_i when s_i=0, and strictly
below it when s_i>0 because β_i>0. Thus the stated condition is a literal
finite, strict complete-cap test, not a discarded Never constraint.

By continuity and the finite strict gaps, in some relative neighborhood
of p ALL complete caps remain the same late functions. Therefore D=F
throughout that neighborhood. Since p has positive probability on every
action of its selected support face, it is a relative interior point.

**Claim.** If D(p)≠S₀, arbitrarily small simultaneous reweightings of
these existing finite/Never actions strictly decrease D.

**Proof.** F is nonconstant because F(p)≠F(all-Never). Expand F(p+h)−F(p)
and select its lowest nonzero homogeneous part H_k. Each monomial has at
most one variable from each player's block, hence no variable is squared.
On independent symmetric ±1 choices of all the free mass coordinates,
the average of H_k is zero. Distinct such square-free monomials are
linearly independent on this sign cube; since H_k is nonzero, at least
one sign vector h has H_k(h)<0. For sufficiently small ε>0,

    F(p+εh)−F(p)=ε^k H_k(h)+O(ε^(k+1))<0.

Choose ε also small enough to preserve all positive action probabilities
and the strict cap region. The resulting four laws are independent
original finite laws, with their complete caps still L_i. Hence D drops.
No new clock, favorable Nash reselection, or cap estimate is assumed. ∎

This is a genuine old-law move on the binding-late test (BT4). More
explicitly, varying its common Never probability α gives, while the late
caps remain strict against the other response functions,

    D(α)=32−32α−100α²+168α³−67α⁴.

Its derivative at α=1/32 is negative. Increasing that α slightly deletes
some OLD date0 mass and strictly lowers debt, even though every addition
of a nontrivial Never tail increases it by (BT5). This illustrates the
missing operation without strengthening the table's coverage claims.

### Actual global-minimum consequence and the compact-calendar limit

The general strict inequality D_*<S₀ is already supplied by existing
prefix descent. Start with the literal all-Never profile, whose terminal
payoff is0 and whose debts are s_i, and choose j with s_j>0. The exact
declaration
`exists_exactRoot_terminalExploitability_le_and_debtSum_descent` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`
produces a one-date Nash prefix with strictly smaller total debt. Its
continuation is still all Never, so it is a finite law. Both terms in
the declaration's minimum gain are strictly positive in this application.
No new existence lemma is claimed for this already implemented step.

Consequently a FINITE global D-minimizer with positive Never probabilities
cannot satisfy the strict late-only cap test above. Some cap must either
strictly exceed its late value, or have an additional maximizing response
whose payoff function differs from the late function. This consequence
uses global minimality and an actual decreasing finite-law variation,
unlike merely imposing all Never-tail inequalities.

It does NOT yet dispatch the represented minimum from the earlier
compactness theorem. On an accumulating calendar, nonmaximizing responses
can approach the late value with no uniform gap. After truncation, a
small reweighting can then activate one of those omitted near-best
responses. The sign-cube polynomial decrease is of order ε^k, whereas
the uncontrolled cap increment may be only o(ε), which can dominate it
for k≥2. The finite proof may not be passed to the limit by saying that
the cap maximizer is unique or that the deleted tail mass tends to zero.

The concrete next question is therefore whether genuine global minimality
controls this near-late cap leakage relative to an old-law ε^k decrease,
or whether an actual finite-amplitude reweighting avoids that scale
comparison. All late/near-late pure tests and Never must remain present.
Neither outcome is established here.

## Positive-Never global minima have an earlier finite cap maximizer

Status: complete ordinary mathematical source-consumer candidate, not
Lean-checked, not a UE theorem or export proposal. The fixed-cut proof
below resolves the preceding near-late scale problem for the stated
late-only branch. It does not assert arbitrary compact-calendar minimality.

### Statement and the actual source being consumed

Let I be any finite nonempty player set. Fix a bounded real reward vector
r(S) for every nonempty coalition, with original Never payoff0. Suppose

    s_i=r_i({i})≥0 for all i,   S₀=Σ_i s_i>0.

For independent actual finite stopping laws p on ℕ∪{Never}, let U_i(p)
be their terminal payoffs and b_i(p) their caps over ALL pure dates and
Never, equivalently all behavioral deviations. Put

    D(p)=Σ_i[b_i(p)−U_i(p)],   D_*=inf_p D(p).

Take the marked ordered-calendar representation of an actual minimizing
sequence. Thus T⊆[0,1] is nonempty compact, c=max T, Never is a separate
point after T, and independent laws q_i satisfy q_i({c})=0. The literal
payoffs and complete caps on T∪{Never} are limits of the original finite
profiles and have D_T(q)=D_*. Every cap is attained; the pure-date payoff
function is continuous on T. These are the actual marked-representation
conclusions, not premises about an arbitrary supplied auxiliary game.
Assume

    α_i=q_i(Never)>0 for EVERY player.             (HT1)

Then some player has an earlier finite cap maximizer:

    ∃i∈I, ∃t∈T, t<c: U_i(t,q_{−i})=b_i(q).       (HT2)

This is cardinal-independent. The implication from an original no-UE
table to D_*>0 is not needed for the proof. In the Fin4 application the
counterexample normal form may be chosen FIRST with s=(1,0,0,0), before
selecting the minimizing sequence; no already selected minimum or law
is transported through a reward normalization.

The unregularized source used here is proved in Section35 of
`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. Its weak-* density and
marked-tester construction is the same semantic representation as
(RC9)–(RC10), without requiring entropy convergence. The finite transport
needed here is proved explicitly below and is not inferred from the
finite-atomic-mixture domain (RC11).

### Reduction to the late-only branch

For any profile x on this ordered calendar write

    W_i(x)=U_i(Never,x_{−i}),
    L_i(x)=W_i(x)+s_i∏[j≠i]x_j(Never).

Because q and every reweighting below have no prescribed atom at c,
L_i is exactly the finite pure-c payoff. Since s_i≥0, it is no smaller
than the Never payoff.

Suppose (HT2) fails. By attained caps, every cap must then equal its
late value, and every earlier finite response is strictly smaller:

    b_i(q)=L_i(q),
    U_i(t,q_{−i})<L_i(q) for every t∈T, t<c.       (HT3)

If c=0, all prescribed laws are Never, since they give c zero mass.
Then D_T(q)=S₀, contradicting the known strict inequality D_*<S₀ proved
below. Hence assume c>0.

### One fixed cut: exact scaling of every future tester

Choose any real K<c with K≥0 that carries no atom of the common prescribed
mixture. Define the head/tail masses and conditional laws

    H_i=q_i([0,K]),   S_i=1−H_i≥α_i>0,
    h_i=q_i( · | [0,K]) when H_i>0,
    v_i=q_i( · | (K,c]∪{Never}).

For a player with H_i>0 vary x_i∈[0,1] and set

    q_i^x=(1−x_i)h_i+x_i v_i.                    (HT4)

For H_i=0 leave q_i unchanged and fix x_i=1. The original point is
x_i=S_i; it is an INTERIOR point of the cube of all variable coordinates,
because α_i>0 and H_i>0 there. No independence is lost: each player
independently chooses its mixture component and its conditional clock.

For a player i and any tester t∈T with t>K, including separately Never,
condition on whether one of its opponents selects the head. If so, the
first opponent coalition lies at or before K and its reward is independent
of t. Therefore the exact response identity is

    U_i(t,q^x_{−i})
      =A_i(x_{−i})+X_{−i} U_i(t,v_{−i}),
    X_{−i}=∏[j≠i]x_j,                            (HT5)

where A_i is the early-opponent reward contribution. It is a multi-affine
polynomial in the opponent head/tail probabilities. In particular

    L_i(q^x)=A_i(x_{−i})+X_{−i} L_i(v).

At x=S the factor X_{−i} is strictly positive. Thus (HT3) implies
U_i(t,v_{−i})≤L_i(v) for every future finite test and Never. Equation
(HT5) shows that ALL those inequalities survive for EVERY x in the cube.
More precisely, each future tester's deficit below the late test is
multiplied by X_{−i}. This includes testers arbitrarily close to c;
there is no o(ε) cap leakage to compare with a higher-order decrease.

Head tests t∈T∩[0,K] have a uniform strict gap at x=S: this is a compact
set and its payoff function is continuous and strictly below L_i(q).
If the set is empty there is no head condition. Each pure payoff and
L_i change uniformly continuously under these finite mixing parameters,
by the bounded-reward coupling estimate. Hence in a relative neighborhood
of x=S every head test also remains below the late cap. We have proved
the exact local identity

    D_T(q^x)=F_K(x):=Σ_i L_i(q^x)−Σ_i U_i(q^x).  (HT6)

The function F_K is multi-affine in the variable players' probabilities.
No assertion that (HT6) holds on the WHOLE cube is needed.

### Actual finite transport of this conditional reweighting

Here is why genuine global minimality applies to the neighborhood in
(HT6). Use the fixed finite minimizing sequence that produced q. On its
common quantile domain [0,1], write its bounded player densities r_iⁿ and
interval-collapse maps π_n, with Never separate. The source construction
gives r_iⁿ⇀*r_i in L∞, a uniform bound |I|, retained atom marks, and the
complete finite-response sets T_n→T. It gives a.e. convergence of the
prescribed and moving-response coalition kernels in these coordinates.

Select as the nth head exactly the original dates whose OLD quantile
response locations are at most K. Never is always in the tail. Since K
has zero mixture mass, the head indicators

    1_{π_n(u)≤K} → 1_{π(u)≤K}

converge almost everywhere and in L¹. Here a retained atomic interval is
included as a whole or excluded as a whole according to its midpoint;
it is never split by treating K as a raw density-domain coordinate.
Weak-* convergence and the bounded densities give H_iⁿ→H_i and
S_iⁿ→S_i. For H_i>0, independently reweight that player's ACTUAL finite
conditional head and conditional tail to probabilities 1−x_i and x_i.
For H_i=0 leave its nth law unchanged. For all large n the denominators
H_iⁿ and S_iⁿ needed by the varying players are bounded away from zero.
This gives a literal independent finite profile p^{n,x}; it adds no new
dates, removes no tester and leaves original Never as Never.

On the old quantile domain its new density, for a varying player, is

    r_iⁿ(u)[(1−x_i)1_{head}/H_iⁿ+x_i1_{tail}/S_iⁿ].

The bracketed factors are uniformly bounded and converge a.e. The new
densities therefore converge weak-* to the corresponding reweighted
limit densities. Products converge weak-* by rectangle tests and L¹
density, with a uniform bound. Against the unchanged marked semantic
kernels, split each integral into a moving-kernel L¹ error plus a fixed-
kernel weak-* error. Thus all prescribed coalition probabilities and
payoffs converge to those of q^x.

Exactly the same argument applies to EVERY sequence of pure tester
locations in the old T_n. Retained atoms keep their literal ties; other
limit points are mass-zero cuts; c and Never remain different tests.
Taking convergent maximizing subsequences gives the upper cap bound,
and approximating each fixed T-test and Never gives the lower bound.
Thus every unrestricted cap of p^{n,x} converges to that of q^x on T.
The old calendar is unchanged, so there is no new c-atom or missing c⁺
issue here: c remains empty and its late test remains available.

For EACH fixed x, D(p^{n,x})≥D_* and taking n→∞ proves

    D_T(q^x)≥D_*.                                (HT7)

No common finite approximation is claimed for all x simultaneously.
The chosen cut is fixed before taking the minimizing-sequence limit;
there is no division of its error by a shrinking tail probability.

### Algebraic constancy and the Never limit

Equations (HT6)–(HT7) make x=S a local minimum of F_K at a relative
interior point. A multi-affine polynomial with an interior local minimum
is constant: its lowest nonzero homogeneous Taylor part would have mean
zero and both signs on a symmetric sign cube, and would supply a small
decreasing direction. This also covers several coordinates per block,
although (HT4) uses only one. Therefore

    F_K(x)=D_* on the entire parameter cube.      (HT8)

At its all-tail vertex, (HT8) says ONLY that

    Σ_i L_i(v)−Σ_i U_i(v)=D_*.                   (HT9)

It does NOT assert that the actual debt of v equals D_*: early tests may
overtake the late branch away from the local neighborhood. This is why
the polynomial is kept separate from the complete-cap objective.

Choose K approaching c through mixture-continuity points. There are at
most countably many excluded atom locations, so such cuts exist. Since
q_i({c})=0 and α_i>0, S_i(K)→α_i and the conditional tail law v_i has
finite mass (S_i(K)−α_i)/S_i(K)→0. Hence v_i tends in total variation to
Never. Uniform bounded-payoff coupling gives U_i(v)→0 and W_i(v)→0,
while the product of conditional opponent Never masses tends to1.
Thus L_i(v)→s_i. Taking limits in (HT9) yields D_*=S₀.

But the literal all-Never profile has payoff0 and debts s_i. Choose j
with s_j>0. The existing theorem
`exists_exactRoot_terminalExploitability_le_and_debtSum_descent` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`
prepends an internally produced finite-game Nash row and lowers its total
debt strictly: both terms of its minimum decrease are positive. The
resulting profile is still a finite law. Hence D_*<S₀, a contradiction.
This proves (HT2). ∎

### Exact scope and next surviving branch

The proof uses the attained complete-cap function, actual finite transport
and positive Never masses. It does not assume common-support likelihood
bounds or entropy convergence. If some α_i=0, its conditional tail need
not approach Never and the last step fails. If S₀=0, the all-Never profile
already has zero debt and the strict prefix comparison is unavailable.
Both hypotheses are used, not presented as removable technicalities.

The new move differs from changing only a Never atom: it independently
reweights every old conditional head against its ENTIRE tail. Preserving
each conditional tail is precisely what makes all near-late cap deficits
scale exactly. Merely moving selected head mass to Never would not have
that property.

Together with (LR6) and the positive singleton social sum supplied by the
Fin4 no-UE Q source, this says that a positive-Never minimizing source
cannot hide all its strategic constraints at the empty final cut. An
earlier finite cap attains the maximum. It may be an empty response cut
or a prescribed atomic date; it need not be shared by players, and it
need not be the earliest support point. Nothing here removes that binding
response, proves its owner has zero debt, or produces a uniform equilibrium.
The next question is how an earlier binding cap and the late-binding
constraints can be consumed together without deleting either response.

## Signed extension of the earlier-cap source consumer

Status: ordinary mathematical extension, not independently reviewed or
Lean-checked. The preceding reviewed section is unchanged. This statement
does not require reward normalization or transport of a selected minimum.

Retain its arbitrary finite player set, bounded original reward table,
actual finite-law infimum D_*, marked ordered-calendar global minimizer q,
empty final cut c, complete attained caps, and positive Never masses α_i.
The own singleton rewards s_i may now have arbitrary signs. If

    S₊=Σ_i max(s_i,0)>0,

then some finite test t<c attains some player's complete cap. In particular
this applies to every no-UE table: if all s_i≤0, all-Never itself is an exact
terminal equilibrium, since its unilateral pure finite-date payoffs are
s_i and its Never payoff is0.

The correct endpoint branch is

    E_i(x)=W_i(x)+max(s_i,0)∏[j≠i]x_j(Never).

It is the maximum of the pure-c and Never payoffs whenever no prescribed
law has an atom at c. No reward coordinate has been altered. If every
finite t<c is strictly suboptimal, attained caps give b_i(q)=E_i(q).

For the same fixed continuity cut K and the same independently reweighted
conditional head/tail laws q^x in (HT4), conditioning on an opponent head
gives EXACTLY

    E_i(q^x)=A_i(x_{−i})+X_{−i}E_i(v),
    U_i(t,q^x_{−i})=A_i(x_{−i})+X_{−i}U_i(t,v_{−i})

for every future test, including Never. Thus all future deficits relative
to E_i retain their signs on the entire parameter cube. The compact head
has a strict uniform cap gap at the original point. The actual finite
transport in (HT7) is unchanged and uses no reward sign. Consequently
the local complete debt equals the multi-affine polynomial

    F_K^+(x)=Σ_i E_i(q^x)−Σ_i U_i(q^x).

Its interior local minimum forces this polynomial to be constant. Evaluating
the polynomial at the all-tail vertex and then letting K↑c gives

    D_*=lim_K [Σ_i E_i(v)−Σ_i U_i(v)]=S₊.

As before, this extrapolated polynomial value is NOT asserted to equal the
complete debt of each all-tail profile. Total-variation convergence of each
conditional tail to Never is enough for the displayed limit.

Finally all-Never has exactly total debt S₊. Choose j with s_j>0 and apply
`exists_exactRoot_terminalExploitability_le_and_debtSum_descent` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean` with
continuation all-Never, gap=s_j, and a finite reward bound M>0. Its j-debt
is s_j, so the produced finite root prefix decreases total debt by at least

    min(s_j²/(8M),s_j/2)>0.

This contradicts D_*=S₊. The signed extension is proved. It changes neither
the requirement α_i>0 for every player nor the remaining earlier-binding
cap branch. If S₊=0, the all-Never equilibrium disposes of the original
game instead of supplying this contradiction argument.

## Spreading original clocks: collision or a genuinely missing response cut

Status: complete ordinary mathematical finite-law estimate and source
consequence, not independently reviewed or Lean-checked. This is internal
research, not another proposed export. The move changes actual independent
laws and measures ALL cap leakage; it does not assume an auxiliary Nash
selector or preservation of caps under arbitrary clock refinement.

### Exact finite-data question

Fix any nonempty finite player set I of size n, bounded real rewards
|r_i(S)|≤M with M>0, original Never payoff0, and an arbitrary independent
finite stopping-law profile p. Let χ(p) be the probability that its FIRST
quitting coalition has size at least2. For each i, let χ_{−i}(p) be the
probability that the first coalition among its opponents has size at least2;
if every opponent chooses Never this event is false. Set χ_{−i}=0 for a
one-player game. These are different probabilities.

Stretch the original calendar by placing every old date k at date2k+1.
Date2k is now an empty available test immediately before that old date.
Write p̂ for this ACTUAL stretched profile and

    Λ(p)=Σ_i[b_i(p̂)−b_i(p)]≥0.                    (SD1)

All old tests and Never remain, with their old values, and the prescribed
coalition law is unchanged. Thus Λ is exactly D(p̂)−D(p), not a supplied
cap bound. It prices the otherwise missing before/after cuts. It need not
vanish, even when χ=0.

For any integer L≥1, construct p^{[L]} as follows. If player i's original
independent clock equals a finite k, it independently selects a uniform
subdate ℓ∈{1,…,L} and quits at

    (L+1)k+ℓ.

Original Never remains Never. All players' added random choices are private
and independent. Original order between DIFFERENT dates is preserved;
simultaneous old draws may now be separated. Every gap and subdate is a
literal natural-number test. No compact-clock realization is required.

The claim is the complete estimate

    D(p^{[L]})
      ≤D(p)+Λ(p)+2Mnχ(p)+2MΣ_iχ_{−i}(p),          (SD2)

while every singleton stage of p^{[L]} is at most1/L and all Never masses
are unchanged. The bound is independent of L and of the original deadline.

### Prescribed payoffs and every pure response

Couple the old and new laws by the original clocks and their independent
subdate draws. If the old first coalition is a singleton, its unique owner
still precedes every other old block and remains the first quitter. The
all-Never outcome is also unchanged. Only an old nonsingleton FIRST
coalition can change its reward. Therefore

    |U_i(p^{[L]})−U_i(p)|≤2Mχ(p) for every i.     (SD3)

Fix a responder i and a new pure time in block k, at subdate ℓ. Compare
with the three ACTUAL stretched-calendar tests immediately before old k,
at old k, and immediately after old k. Their payoffs are denoted
Q_i^−(k), Q_i^0(k), Q_i^+(k), all bounded by b_i(p̂).

On the event that the original opponents' first finite coalition is a
singleton, the conditional new test payoff, averaged over the private
subdates, agrees with the convex combination

    [(L−ℓ)/L] Q_i^−(k)
      +(1/L) Q_i^0(k)+[(ℓ−1)/L] Q_i^+(k).        (SD4)

Here equality means equality of the expected kernels RESTRICTED to that
event, with the same coefficients. If the unique opponent first quits
before k or after k, all three comparison outcomes agree with the new
outcome. If it first quits at k, its uniform subdate is later than ℓ,
equal to ℓ, or earlier than ℓ with exactly the displayed probabilities.
Those probabilities do not depend on which opponent is the sole quitter.
All-opponent-Never gives the same own singleton in all four tests.

On the exceptional event of an original opponent collision, the difference
between the new payoff and this convex combination has absolute value at
most2M. Thus the full pure payoff is at most

    b_i(p̂)+2Mχ_{−i}(p).

An empty new gap corresponds to an old stretched cut and has the same
bound. Never uses the passive first-opponent coalition: it is unchanged
off the same exceptional collision event, so obeys the bound too. This
exhausts EVERY pure natural date and Never. Taking the supremum, or any
behavioral mixture of those tests, proves

    b_i(p^{[L]})≤b_i(p̂)+2Mχ_{−i}(p).            (SD5)

Combining (SD3) and (SD5) yields (SD2). Also the new marginal probability
at a single date is p_i({k})/L≤1/L. Multiplying by opponent survival can
only decrease it, so every new singleton stage probability is at most1/L.

### A consumed restriction at the actual positive infimum

Assume δ=inf D>0 for this fixed ORIGINAL table, and fix η>0. For a profile
with all α_i=p_i(Never)≥η, the independence identity gives

    χ(p)≥α_iχ_{−i}(p),

because on the event that i Never stops, an opponent collision is also
the original first collision. Consequently (SD2) implies

    D(p^{[L]})≤D(p)+Λ(p)+2Mn(1+1/η)χ(p).        (SD6)

Apply the established original-stage restriction in
[POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md](../exports/POSITIVE_NEVER_NEAR_MINIMA_FORCE_SINGLETON_STAGE_ATOMS.md).
It gives ε_A,γ_A>0 for this table and η, such that every actual law with
D≤δ+ε_A and these Never bounds has some singleton stage≥γ_A. Choose L
with 1/L<γ_A. Equation (SD6) therefore forces

    D(p)−δ+Λ(p)+2Mn(1+1/η)χ(p)>ε_A.            (SD7)

In particular all finite profiles with D(p)≤δ+ε_A/2 and α_i≥η satisfy

    Λ(p)+2Mn(1+1/η)χ(p)>ε_A/2.                 (SD8)

This is an actual complete-law source restriction. A near-minimum sequence
with a fixed positive Never lower bound cannot have BOTH vanishing first-
collision probability and vanishing complete-cap cost of clock stretching.
It is stronger than merely knowing that a marginal or singleton stage atom
exists. The displayed argument uses no root normality, reward normalization,
entropy, bounded response menu, or assumed favorable reselection.

For an arbitrary infinite original law the same conclusion follows from
finite censoring if needed. Both its original and stretched complete caps
are approximated uniformly by censoring sufficiently late finite mass;
the collision probabilities converge by coupling, and Never masses can
only increase. The actual infinite stretched law is the independent image
k↦2k+1, with Never unchanged. Thus (SD8), with a weak inequality if taking
a boundary limit, also gives a positive uniform collision-or-stretch floor
for sufficiently near-minimal arbitrary laws.

### Exact boundary and the unresolved consuming move

The missing-cut term cannot be discarded. Take two players with own
singleton1, passive singleton0 and joint reward−10 for both. Player0
quits at date0 with probability1/2 and otherwise Never. Player1 quits at
date1 with probability1/2 and otherwise Never. There are NO on-path
collisions. Direct calculation gives

    U=(1/2,1/4),   b=(1,1/2),   D=3/4.

Stretching exposes the empty first date, where player1 can quit alone.
Its cap becomes1; player0's cap stays1. Hence Λ=1/2. In the L-spread
profile, player1's test at the first subdate of block0 earns

    1−11/(2L),

approaching1. Targets are unchanged. Thus collision-free spreading can
raise debt by a fixed amount if the newly exposed test is ignored. This
is a solved-table method boundary, not a positive-global-minimum example:
player0 quitting surely with player1 Never is already an exact equilibrium.

The bounded source lookup used the existing nonsingleton anti-diffusion
and literal endpoint descriptions in `docs/TOOLKIT.md`, together with
`QuittingStageAtomConcentratedPacketAdapter` in
`Research/Quitting/PositiveStageAtomConcentratedPacket.lean` and
`FinFourStrongConcentratedPacketConsumerResult` in
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.
Those adapters alter a selected action and do not bound all other caps
or retain whole-profile minimality. The current estimate instead produces
a complete actual refinement and charges its entire cap effect. No blanket
absence-of-overlap claim is made.

The remaining question is NOT whether an original singleton stage can be
found; that is settled by the cited restriction. It is whether true global
minimality can consume the collision arm of (SD8), or the positive price of
an unavailable response cut, by a coupled alteration of old stopping mass.
Neither arm is excluded by (SD8). In particular it would be circular to
assume Λ small just because inserting empty dates is strategically useful
to a deviator. This checkpoint changes the candidate move and quantifies
its exact failure modes; it does not establish another raw UE class.

The missing-cut arm has a concrete continuation meaning. At an old date k
write A_i(k) for the passive contribution from opponents who quit before k,
R_i(k) for their probability of all surviving to k, and B_i(k) for their
complete conditional cap on the old calendar beginning AT k. If R_i(k)>0,
the old full cap is at least A_i(k)+R_i(k)B_i(k), whereas a newly inserted
empty date immediately before k pays A_i(k)+R_i(k)s_i. Thus a profitable
new cut necessarily has

    B_i(k)<s_i.                                  (SD9)

If R_i(k)=0 no such gain is possible. This is a genuine conditional cap,
not a prescribed-payoff annotation. Global minimality of the WHOLE law
does not say that this conditional suffix is itself a minimum.

A tempting canonical shortcut is invalid: the exact declaration
`singlePivotSingletonTable_punishment_le_solo` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotCanonicalConsequences.lean`
supplies only P_i≤s_i, not P_i=s_i or P_i≥s_i. The explicit punishment
transport in `FinFourSinglePivotNormalization` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
does not change that direction. Hence the fact B_i(k)≥P_i does NOT rule
out(SD9), even for a zero-singleton nonpivot row. The remaining move must
alter the old head as well as the deficient suffix, or genuinely consume
the collision arm. No free cap-preserving clock stretching is inferred.

## First-root consumption: a genuine minimum cannot start with a solo root

Status: complete ordinary algebraic consequence of an ACTUAL prefix minimum
and the inspected strict minimum cap margin. Not independently reviewed or
Lean-checked. It is not a new raw-table UE class. Unlike a best-endpoint
adapter, the calculation retains the full Bellman maximum for every cap.

Let (u⁺,b⁺) be a point in the original terminal semantic carrier, and let
q∈[0,1]^I be a literal independent first root. Let (u,b) be its semantic
prefix, assumed to be a GLOBAL sum-debt minimum with value δ>0. Set

    a=∏_i(1−q_i),    d⁺=Σ_i(b_i⁺−u_i⁺).

The exact prefix formulas are those in `quittingTerminalSemanticPrefix`
in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. In the
finite Boolean stage game whose all-Continue annotation is b⁺, let Q_i
be the pure-Quit endpoint, C_i the pure-Continue endpoint, and

    g_i=q_iQ_i+(1−q_i)C_i,
    e_i=max(Q_i,C_i)−g_i≥0.

These are actual cap-annotated STAGE regrets; no stage Nash assumption is
made. The full prefix cap is b_i=max(Q_i,C_i). The prescribed prefix payoff
uses u⁺ instead of b⁺ ONLY on the all-Continue event, so

    u_i=g_i−a(b_i⁺−u_i⁺),
    δ=Σ_i e_i+a d⁺.                               (FR1)

Every tail carrier point has d⁺≥δ by global minimality. Consequently

    Σ_i e_i≤δ(1−a).                               (FR2)

The tracked strict margins supply ξ>0 with b_i−s_i≥δ+ξ for EVERY i.
For arbitrary signed Fin4 tables this is the exact declaration
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
For arbitrary finite players with nonnegative own singletons it is
`positive_minimum_nonnegativeOwner_quadraticMargins` in the same file.
One may take ξ=δ²/(8M) for a common M>0 reward bound. The source is the
prefix pair (u,b), not the conditional tail; no tail-minimum assumption
is hidden in this use.

For each coordinate, regardless of which Bellman branch is maximal,

    e_i≥q_i(b_i−Q_i).

Combining this with(FR2) proves the forced participant-premium charge

    Σ_i q_i(Q_i−s_i)
      ≥δ[Σ_iq_i−(1−a)]+ξΣ_iq_i.                 (FR3)

The bracket is nonnegative by the union bound. If q has precisely one
positive coordinate j, then Q_j=s_j and every other summand on the left
vanishes, whereas the right side is ξq_j>0. This is impossible. Thus every
NONTRIVIAL first product root of such an actual minimum has at least TWO
positive quitter coordinates and a positive first-stage collision mass.

Equivalently, if S is the root's random quitting coalition, the left side
of(FR3) is

    E[Σ_{i∈S}(r_i(S)−s_i)],

and the bracket is E[(|S|−1)^+]. Singletons contribute zero to the left.
This states which actual simultaneous-quitting payoff mass must finance
the stage regrets; it does not infer that the root itself is Nash.

The applicability to a represented FIRST occupied atom needs the actual
first-root decomposition. If that source has already been produced,
its original pre-atom mass tends to zero; the first root rates converge,
and a subsequence of the actual post-date semantic pairs gives the tail
carrier point. Earlier empty tests pay s_i and are strictly below the
source cap, so dropping those empty tests changes no limiting cap. The
continuous prefix formulas then give(FR1). This paragraph does not supply
the missing first-atom producer by itself. It does NOT apply unchanged to
an arbitrary later atom, whose earlier cap tests must remain in a larger
maximum and whose prescribed payoff has a nontrivial old-head term.

For overlap, `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
requires at least one low-premium ACTIVE coordinate at every absorbing
product root. It is not the weighted-sum statement(FR3). No new whole-table
coverage follows merely from this comparison. The next substantive task
is to consume the forced first COLLISION root with its actual tail and
complete cap equations, rather than replacing it by a favorable auxiliary
Nash root or assuming its tail is another minimum.

## A finite same-tail selector exposes a responsive cap cycle

Status: complete internal finite-dimensional reduction, ordinary mathematics
not independently reviewed or Lean-checked. It is not a new UE class or
an export candidate. Its intended use is to focus an actual consuming
variation on complete-cap switches; no such variation is proved here.

### Actual data and question

Let a bounded quitting table have actual global sum-debt infimum δ>0.
Let v=(u⁺,b⁺) belong to its original closed terminal semantic carrier.
Suppose some nonzero product row p has T_p(v) an actual GLOBAL minimum
of value δ. Here T is the literal semantic prefix, with all unilateral
behavioral caps, defined by `quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. Assume the
strict all-owner source margin, available for arbitrary signed Fin4 or
nonnegative own singletons at arbitrary finite cardinality, from
`positive_minimum_fourPlayer_allOwner_quadraticMargins` or
`positive_minimum_nonnegativeOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.

Can one reselect only the FIRST row, retaining this actual continuation
source, so that every genuinely mixed coordinate is obstructed by an
actual switch in ANOTHER player's full cap?

The answer is yes. For x∈[0,1]^I let Q_j(x₋ⱼ) be first-row Quit value,
C_j(x₋ⱼ) its Continue value priced at the actual tail cap b_j⁺, and put

    F(x)=Σ_j max(Q_j(x₋ⱼ),C_j(x₋ⱼ))−Σ_j U_j(T_x(v)),
    Δ_j(x)=Q_j(x₋ⱼ)−C_j(x₋ⱼ).

Both Q_j and C_j are multiaffine and independent of x_j. The second
statement is important: the owner's complete cap never depends on its
own first-row mixing rate. The full payoff vector is multiaffine in x.
Every T_x(v) remains in the original carrier, by the actual-prefix
closure statement `quittingTerminalSemanticPrefix_mem_carrier` in the
same source file. Thus F(x)≥δ for EVERY x, with equality at p.

### Compact selector and exact conclusion

Let K={x∈[0,1]^I:F(x)=δ}. This is a nonempty compact set. Choose x*∈K
maximizing Σ_i x_i². Its norm is at least that of the supplied nonzero p,
so x* is nonzero. The full-prefix minimum and strict source rule out a
solo support, as in(FR1)–(FR3). Thus x* still has a collision row. Neither
the tail's debt nor its individual continuation levels are asserted to be
minimal.

For every mixed coordinate i with 0<x_i*<1, there is some j≠i such that

    Δ_j(x*)=0,          ∂_i Δ_j(x*)≠0.             (CG1)

To prove this, hold all other coordinates fixed. Each Δ_j is affine in
x_i. If no j satisfies(CG1), every strict cap branch retains its sign
in a neighborhood, and each cap tied at x* is either independent of x_i
or has zero slope, hence remains exactly tied on that whole line. The
owner's cap is independent of x_i as well. Therefore F is locally affine
in x_i. Since x_i* is interior and F has a global minimum there, this
affine function is constant locally. Moving x_i slightly in one of the
two directions strictly increases Σ_j x_j² while remaining in K. This
contradicts the selection of x*. The argument includes all current cap
ties; it does not choose favorable branches separately for different
variations.

Draw i→j whenever(CG1) holds. Every mixed vertex has an outgoing edge,
and no edge is a self-loop. Consequently at this selected actual minimum
one of the following holds:

- every first-row rate is pure, so the row is a pure collision coalition;
- a player with rate zero or one has a tied Quit/Continue cap;
- there is a directed cycle of at least two genuinely mixed players,
  every member having a tied complete cap and responding nontrivially
  to its preceding mover's first-row rate.

Indeed, if there is a mixed vertex, follow its edges. Either the path
reaches a pure-rate vertex, which is a tied cap owner by construction,
or it repeats a mixed vertex and yields such a cycle. In particular a
fully mixed selected row has at least TWO distinct tied cap owners, not
merely one arbitrary cap equality.

### Source and scope boundaries

The input is a literal first-row prefix decomposition of a true minimum.
For a produced marked first atom, such a tail carrier can be obtained
from the same original finite profiles: remove their vanishing pre-mark
mass, take their actual post-row behavior profiles and pass to a compact
semantic-pair subsequence. If a finite row coordinate quits surely,
choose an arbitrary continuation for that owner's null event; do not
call it a conditional law. The prefix identities remain exact, since
its arbitrary own continuation is multiplied by zero in every affected
prescribed or opponent-cap term. Other owners' positive-survival tails
are their ordinary conditional laws. If two or more owners quit surely,
all continuation terms in current caps vanish. Continuity of T gives
the represented first-row decomposition. This construction never assigns
a conditional probability to a zero-probability event.

Reselecting x* is a new ACTUAL carrier minimum with the same actual tail;
it is not the unmodified original law. Thus the statement does not retain
the exact original marked stage probability promised by the stage-source
theorem. The current mathematical goal only needs an actual minimum for
a legal consuming variation, so this distinction is explicit rather than
silently hidden.

The responsive cap graph is not a best-response or quitting-influence
graph for the whole table. Its edges depend on this selected row and the
actual continuation cap vector. It is not enough that Δ_j=0: a zero-slope
tie cannot obstruct coordinate motion and is excluded in(CG1). No sign
for these slopes, auxiliary Nash property, collision erasure, or strict
debt decrease follows from the compact selector.

The concrete next question is whether the finite-amplitude geometry of
these responsive cap cycles, together with actual global minimality
under changes of the OLD conditional tail laws, forces a descent. Root
variation alone only supplies F≥δ and the tight branches; treating that
local inequality as a complete no-UE source would repeat the already
refuted orbit-minimum shortcut. The sure-rate and pure-rate-tie branches
remain literal alternatives, not conditions to be discarded.

## A joint row–tail repair escapes two separate local barriers

Status: exact ordinary-mathematical test and variation calculation, not
Lean-checked or a new existence class. The game below already has a pure
terminal Nash profile. The question being tested is narrower: can an
actual coupled change of a responsive cap-tie row and its OLD tail lower
complete debt when both separate blocks oppose local changes?

The answer is yes. This retires alternating local row/tail minimization
as a sufficient search rule, but not the genuinely joint variation.
The final derivative calculation retains the extra requirement needed
to use this mechanism at a TRUE global minimum.

### Full table and all response values

There are four players. For every nonempty coalition S, set

    r_i(S)=10                         if i∉S;
    r_i({i})=1;
    r_i(S)=2,18,10                    if i∈S and |S|=2,3,4 respectively.

These rules specify all sixty coordinates, with Never reward zero.
Let each player put mass 1/2 at date 0 and 1/2 at Never. Its prescribed
payoff and complete cap are

    U_i=141/16,       B_i=71/8,       D=1/4.        (JT1)

The date-0 response pays 71/8; EVERY positive finite date also pays
71/8; Never pays 35/4. Thus the row is fully mixed with all four
first-row Quit/Continue caps tied, and no late tester is omitted.

The true global infimum on this table is zero: player 0 sure at date 0,
all others Never is terminal Nash. Player 0 receives 1 rather than 0
from Never; every other player receives passive 10 rather than pair
reward 2 from joining. No positive-minimum conclusion is claimed from
(JT1), even though its numerical own-floor margins are very large.

### Every nonzero sufficiently small root-only change raises debt

Keep the all-Never tail fixed and vary the first row x. Its tail cap is
the own-singleton vector 1. Write Δ_i(x)=Q_i(x)−C_i(x). Exactly,

    Δ_i(x)=8[P(exactly two opponents quit)
                 −P(exactly one opponent quits)].

At x₀=(1/2,1/2,1/2,1/2), Δ=0 and its Jacobian J has diagonal zero and
every off-diagonal entry 4. For h→0 the exact full debt has expansion

    D(x₀+h)−1/4
       = (1/2)‖Jh‖₁−(1/2)Σ_i h_i+O(‖h‖₁²).    (JT2)

Indeed stage regret is Σ(Δ_i⁺−x_iΔ_i) and the surviving all-Never debt
is 4∏(1−x_i). These expressions give (JT2) directly, including all cap
switches. Since J⁻¹=(−Id+(1/3)11ᵀ)/4 has induced ℓ¹ norm 5/12,
‖Jh‖₁≥(12/5)‖h‖₁. The leading term is therefore at least
(7/10)‖h‖₁. A genuine punctured neighborhood of this row has strictly
larger debt. This is local, not a global root-minimum claim: the pure
singleton root already supplies a distant zero-debt alternative.

### Every small unrestricted tail-only release also raises debt

Keep the first-row rates equal to 1/2. Replace the old all-Never
continuation by ANY four independent stopping laws after that row,
with conditional finite probabilities η_i and η=Ση_i. The laws may be
infinitely supported and need not share a calendar or a response time.
Let u_i and b_i be their actual prescribed payoffs and COMPLETE caps.

Because every passive reward is 10, the limiting late-finite response
gives the exact lower bound

    b_i≥1+9[1−∏_{j≠i}(1−η_j)]≥1.

The current Continue branch therefore weakly dominates its old tied
Quit branch. Direct Bellman subtraction gives the exact identity

    D_new−1/4=(1/8)Σ_i(b_i−1)−(1/16)Σ_i u_i.    (JT3)

Bonferroni and independence give

    Σ_i(b_i−1)≥27η−9η².

The total reward of a singleton coalition is 31; the totals of pairs,
triples and the grand coalition are 24,64,40. A joint first coalition
requires at least two players to choose finite clocks. Consequently

    Σ_i u_i≤31η+33Σ_{i<j}η_iη_j
            ≤31η+(33/2)η².

Inserting these two estimates into (JT3) proves

    D_new−1/4≥23η/16−69η²/32>0   for 0<η<2/3.   (JT4)

This tests ALL small tail-only changes, not merely another symmetric
row. It uses the complete late-finite cap rather than Never, whose value
is lower. The coefficient is only a convenient exact certificate; no
sharpness claim or optimization is intended.

In fact the fixed-row assertion is global, by the following stronger
account communicated by CODEX_MORSE and checked directly here. Let a₁ be
the probability that exactly one tail clock is finite, and a₂ the
probability that at least two are finite. Summing the same late-test
bound gives Σ(b_i−1)≥9(3a₁+4a₂): exactly one finite clock is visible to
three deleted-player opponent tuples, whereas two or more are visible
to all four. The first coalition has total reward 31 on the first event
and at most 64 on the second. Hence Σu_i≤31a₁+64a₂ and

    2Σ(b_i−1)−Σu_i≥23a₁+8a₂≥0.

Together with (JT3), this proves that the all-Never continuation is a
GLOBAL minimizer over every actual tail at this fixed root. The inequality
extends to the actual semantic carrier by continuity. The coupled decrease
below therefore escapes even global fixed-root tail optimization, not
merely a locally optimized continuation. Global root optimization is a
different premise and fails here because of the pure singleton exit.

### A legal simultaneous two-date change strictly lowers debt

For t∈(0,1/2), give each player's old continuation conditional mass t
at date 1 and 1−t at Never, while replacing the original date-0 rate
by x. These are independent laws

    p_i(0)=x,   p_i(1)=(1−x)t,   p_i(Never)=(1−x)(1−t).

The conditional continuation has complete cap and prescribed payoff

    b(t)=10−9(1−t)³,
    Δ(t)=24t(1−t)(2t−1)<0,
    u(t)=b(t)+tΔ(t)−(1−t)⁴.

Here the tail Quit test pays b(t)+Δ(t); its later finite test pays b(t);
its Never test pays 10[1−(1−t)³]. These exhaust its pure-response menu.
The full two-date profile has the four response types

    Q₀=10−9(1−x)³+24x(1−x)(2x−1),
    Q₁=10[1−(1−x)³]+(1−x)³[b(t)+Δ(t)],
    Q_late=10[1−(1−x)³]+(1−x)³b(t),
    Q_Never=10[1−((1−x)(1−t))³].

Every date at least 2 gives Q_late. Thus the complete cap is
max(Q₀,Q_late); Q₁ and Q_Never are strictly smaller than Q_late.
Prescribed payoff is

    U=xQ₀+(1−x){10[1−(1−x)³]+(1−x)³u(t)}.

The cap equality Q₀=Q_late is

    24x(1−x)(2x−1)−(1−x)³[b(t)−1]=0.            (JT5)

At (x,t)=(1/2,0), its x derivative is 12 and its t derivative is −27/8.
The implicit-function branch therefore has x(0)=1/2 and x′(0)=9/32.
Along this actual branch all first-row caps remain tied and

    D(t)=(1−x(t))⁴ ·4[(1−t)⁴−tΔ(t)],
    D′(0)=−25/16<0.                              (JT6)

This supplies actual strict decreases for every sufficiently small
positive t. No correlated draw or favorable selection of a new finite
Nash equilibrium is used: the actual row rates compensate the change
of the old COMPLETE continuation caps.

For a fully rational finite-amplitude check, take x=65/128 and t=1/36.
The first-row cap equality need not hold exactly at this rational point.
The exact four response values are

    Q₀=18917657/2097152,
    Q₁=1200026075/134217728,
    Q_late=1209822155/134217728,
    Q_Never=597558015/67108864.

Q₀ is the complete cap: its differences from Q₁ and Q_late are
10703973/134217728 and 907893/134217728, respectively, while
Q_late−Q_Never=14706125/134217728>0. The prescribed value is
615993422355/68719476736. Hence

    D=3900362221/17179869184
      =1/4−394605075/17179869184<1/4.             (JT7)

The finite arithmetic was checked exactly with rational enumeration of
all product outcomes and each response type, and agrees with the displayed
closed formulas. Behavioral deviations are mixtures of these pure tests,
so (JT7) is the unrestricted terminal debt, not a truncated-menu value.

### What the successful coupling would require at a true minimum

There is a precise local calculation behind this test. Let an actual
first root p have all rates in (0,1), with EVERY complete first-row cap
tied. Let v=(u,b) be its actual carrier tail, d=Σ(b_i−u_i),
a=∏(1−p_i), α_i=∏_{j≠i}(1−p_j), and let J be the Jacobian with entries
J_ij=∂_j(Q_i−C_i) at this row and this actual cap annotation. Suppose
J is nonsingular. Consider a PRODUCED actual tail path with expansions

    b(t)=b+tβ+o(t),       u(t)=u+tυ+o(t).

The vectors β and υ must come from those same laws and ALL their cap
maximizers. They are not free coordinates of a semantic annotation.
The implicit-function theorem then selects actual independent first-row
rates maintaining every tie, with

    p′(0)=J⁻¹ diag(α_i) β.

The full Bellman identity gives the exact directional formula

    d/dt D(T_{p(t)}(v(t))) at 0
      =a{Σ_i(β_i−υ_i)
            −d Σ_i [J⁻¹ diag(α_j)β]_i/(1−p_i)}.  (JT8)

The example (JT1)–(JT7) constructs the laws, β,υ and the favorable sign;
it does not merely assume them. At a TRUE global minimum, every such
legal path must instead make the bracket in (JT8) nonnegative. Proving
that some actual conditional-law change violates that inequality is the
remaining task. A responsive cycle by itself does not produce the path,
does not ensure J is nonsingular, and may involve fewer than all cap
owners. These literal boundary cases remain open in the current approach.

The existing exact `minimumTerminalSemantic_auxiliaryNash_budget` and
`minimumTerminalSemantic_auxiliaryNash_eq_allContinue` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
were inspected for comparison. They assume an exact Nash root against a
specified shifted cap of a GLOBAL minimum. They cannot be applied to v
merely because its prefix is minimal, nor do they supply the actual path
in (JT8). Likewise a local adjoint inequality from (JT8) is not a global
weighted-minimum declaration. No such promotion is made here.

## A responsive collision can be an unrestricted strict local debt minimum

Status: complete internal countertest to a LOCAL consuming mechanism,
ordinary mathematics and not Lean-checked. It is not a positive global
minimum, an equilibrium counterexample, or a new existence class. In
particular it does not falsify the actual first-collision source question.
It shows why that question must use global minimality rather than only
responsive cap ties, an invertible cap Jacobian, and numerical own-floor
margins, even when all old-tail variations and all pure responses are kept.

### Full game and literal cap menu

For four players, specify all sixty reward entries by

    r_i(S)=100                       if i∉S;
    r_i({i})=1;
    r_i(S)=108,92,100                if i∈S and |S|=2,3,4 respectively.

Never pays zero and M=108 bounds the absolute rewards. Let p⁰ give
every player mass 1/2 at date 0 and 1/2 at Never. Exact product enumeration
gives

    U_i(p⁰)=1401/16,       B_i(p⁰)=701/8,
    U_i(Never,p⁰_{−i})=175/2,       D(p⁰)=1/4.    (JL1)

Both date 0 and EVERY later finite response attain B_i; Never is smaller
by 1/8. At the first row all four caps are tied and all rates are mixed.
The cap-gap Jacobian has zero diagonal and every off-diagonal entry −4.
Thus all directed mixed-cap influences are nonzero. The values in (JL1)
also exceed the numerical own-floor bounds obtained by substituting
D=1/4 into the true-minimum inequalities, by a large strict margin.

Nevertheless any pure pair quitting surely at date 0 is exact terminal
Nash: its two members get 108 rather than passive 100 on withdrawal,
and each outsider gets 100 rather than triple reward 92 on joining.
The actual global infimum is zero. In particular p⁰ is not even a
GLOBAL minimum over its fixed all-Never-tail first roots.

### Uniform control of arbitrary independent conditional tails

Retain the distinguished first date, change its rates to x_i=1/2+h_i,
and permit each conditional continuation to be ANY independent stopping
law on the remaining dates and Never. Let η_i be its probability of a
finite clock, η=Ση_i, and write its actual semantic values as (u,b).
Set w_i=b_i−1. All following estimates are uniform in the number, order,
and spacing of occupied tail dates, including infinite supports.

The limiting late-finite response gives

    b_i≥1+99[1−∏_{j≠i}(1−η_j)]≥1,
    Σw_i≥297η−99η².                               (JL2)

The supremum is enough; no finite last response is assumed to attain
this limit. Coupling each tail with all-Never also gives 0≤w_i≤2Mη,
so ‖w‖₁ is bounded by a constant times η independently of the calendar.
Every pure test is coupled with the SAME test against all-Never, and
taking their supremum preserves this estimate.

The coalition welfare is 301 for a singleton, 416 for a pair, 376 for
a triple, and 400 for the grand coalition. A first coalition of size
at least two requires two or more finite clocks. Consequently

    Σu_i≤301η+115Σ_{i<j}η_iη_j
          ≤301η+(115/2)η².                        (JL3)

These are actual full-law estimates, not menu regrets or a supplied cap
relaxation. Prescribed values also satisfy ‖u‖₁≤4Mη by coupling.

### The full nonsmooth debt expansion has a strictly positive linear part

Put a(x)=∏(1−x_i), α_i(x)=∏_{j≠i}(1−x_j). For all-Never continuation
cap 1, the exact first-row gap is

    Δ_i⁰(x)=−8[P(exactly two opponents quit)
                   −P(exactly one opponent quits)].

Its Jacobian at x₀=(1/2)1 is J=−4(11ᵀ−Id). With the actual tail the
gap is g_i=Δ_i⁰(x)−α_i(x)w_i. The complete Bellman identity is

    D=Σ(g_i⁺−x_i g_i)+a(x)[4+Σw_i−Σu_i].         (JL4)

Define z=Jh−w/8. Taylor expansion of the fixed root polynomials, using
the Lipschitz inequality for the positive-part function, gives uniformly
over all the tails just described

    D−1/4=(1/2)‖z‖₁−(1/2)Σh_i
             +(1/16)(Σw_i−Σu_i)
             +O((‖h‖₁+η)²).                    (JL5)

No cap differentiability is used. For clarity, the linear contribution
of a(x)·4 is −Σh_i/2. In the regret term, g=z+O(‖h‖₁²+‖h‖₁η)
and g_i⁺−g_i/2=|g_i|/2. The remaining factors h_i g_i and the products
of a(x)−1/16 with Σ(w_i−u_i) are uniformly quadratic.

Since ΣJh=−12Σh, the two linear terms involving h,w become

    D−1/4=(1/2)‖z‖₁+(1/24)Σz_i
             +(13/192)Σw_i−(1/16)Σu_i
             +O((‖h‖₁+η)²).

Equations (JL2) and (JL3) therefore imply

    D−1/4≥(11/24)‖z‖₁+(83/64)η
                 −C(‖h‖₁+η)²                 (JL6)

for one constant C depending only on this table. The coefficient check is
(13·297−12·301)/192=83/64. Moreover J is invertible with induced ℓ¹
inverse norm 5/12. The identity Jh=z+w/8 and the uniform bound on w
show that ‖h‖₁+η≤C₁(‖z‖₁+η). Thus there exist r,c>0, independent
of the tail calendar, such that

    0<‖h‖₁+η<r  ⇒  D≥1/4+c(‖h‖₁+η)>1/4.     (JL7)

This is strict local minimality against ALL simultaneous independent
law changes on the original date and its entire future, with unrestricted
behavioral deviations tested. The parameter ‖h‖₁+η is comparable to
the total-variation distance from p⁰ in a sufficiently small neighborhood.

### Small refinements before the old date do not escape the local minimum

The conclusion is also stable when the old date is retained as an anchor
and arbitrary earlier dates are inserted. Allow player i head probability
ℓ_i before the anchor, with H=Σℓ_i small. Conditional on not using the
head, its law is a suffix q close to p⁰ as in (JL7). Conditional head
laws may be different and may use any finite number of earlier dates;
their time geometry is not replaced by one common atom.

Keep those conditional laws fixed and vary ℓ. For each player retain
ALL tests at or after the anchor. Their supremum is the expected passive
head payoff plus the opponents' head-survival product times B_i(q).
Subtracting the actual prescribed payoffs gives a multiaffine polynomial
P(ℓ). The actual complete debt is at least P(ℓ), because adding earlier
response tests can only raise caps. At the all-head-off vertex,
P(0)=D(q). With only owner i's head turned on, it quits alone whenever
used, so cancellation of every other recipient's passive payoff gives

    P(ℓ_i e_i)=D(q)+ℓ_i[B_i(q)−s_i−D(q)].         (JL8)

This is an exact axis identity, not a Taylor approximation to an invented
response. At p⁰ the coefficient equals 691/8>0. By the same uniform
coupling bounds, all four coefficients stay bounded below by a positive
constant for q sufficiently close to p⁰. Every coefficient of degree
at least two is uniformly bounded in terms of M and four players only:
its vertex payoffs are bounded actual conditional expectations, and the
finite multilinear coefficient inversion has a fixed size. Therefore

    D(full law)≥P(ℓ)≥D(q)+c₂H−C₂H².

Together with (JL7), this is a strict local barrier under arbitrary small
earlier refinements as well. The proof only needs the future-test lower
bound; it does not discard the new early maximizing branches. No horizon,
late-response, or off-path test is suppressed.

### Retired implication and next mathematical question

A responsive mixed-cap cycle, nonsingular J and even strong numerical
own-floor margins do NOT force an infinitesimal full-law debt decrease.
The countertest includes simultaneous old-tail changes and newly inserted
earlier clocks, rather than merely stationary or fixed-menu variations.
The positive test (JT1)–(JT8) shows that coupling can succeed; (JL1)–(JL8)
shows it is not universally forced by this local information.

The actual source remains strictly stronger: it minimizes over ALL
independent profiles, hence over every first root AND every actual tail,
jointly. The pure pair here violates that indispensable premise. The
next question is a finite-amplitude consuming move that uses both global
inequalities, not a weaker derivative assertion or a favorable root
selected independently of its complete tail caps. No additional static
example or optimization of these constants is proposed.

## Two global block minima still admit an actual coupled finite escape

Status: complete exact ordinary mathematics, not Lean-checked or independently
reviewed. This falsifies alternating GLOBAL root/tail optimization, not a
positive global debt minimum or a new existence class. Both separate blocks
are globally optimized; their joint domain contains the explicitly lower-debt
product law below. All responses, including arbitrary late dates and Never,
are retained.

### Full table and the original collision

Put s=1/100, P=1 and H=P−s=99/100. Core players 0,1,2 have cyclic
prev(i)=i−1 and next(i)=i+1 modulo 3. Every passive reward is P and every
own singleton is s. For core i and nonempty opponent coalition T, set

    r_i(T∪{i})=P−1_{prev(i)∈T}
                  +2·1_{next(i)∈T}(1−1_{prev(i)∈T})+2·1_{3∈T}.

For every coalition containing 3 and another player, set r_3(S)=P−16=−15.
These rules specify all sixty coordinates; Never pays zero and M=15 bounds
absolute rewards. Use q=(1/2,1/2,1/2,0) with all-Never continuation. Exactly,

    U_i=601/800, B_i=301/400 (i<3),
    U_3=7/8, B_3=701/800,       D_0=1/200.                (GB1)

Every debt is s/8. The three core root caps are tied; player 3's Continue
cap is strictly maximal. All numerical all-owner margins obtained by
inserting D_0 and M in the true-minimum inequalities hold, but D_0 is NOT
the whole-profile infimum.

### Global minimization over every first root

For any first row x with all-Never continuation, put

    c_3=∏[i<3](1−x_i),       c=c_3(1−x_3),
    f_i=2x_next(i)(1−x_prev(i))−x_prev(i),
    g_i=f_i+2x_3 (i<3),       g_3=−16(1−c_3).

The exact complete debt is

    D(x)=4s c+Σ[i<3](g_i^+−x_i g_i)+16x_3(1−c_3).        (GB2)

The three-cycle regret R=Σ[i<3](f_i^+−x_i f_i) satisfies

    R≥(1/3)(1/8−c_3)       if c_3<1/8.                  (GB3)

Indeed let m=max(x_0,x_1,x_2)>1/2 and rotate so x_0=m,x_1=y,x_2=z.
Then f_1≤−m(2m−1). If y≥1/4, its regret is at least (2m−1)/8.
If y<1/4, f_2≥(6m−1)/4≥1/2. For z≤3/4 the regret of player 2
is at least 1/8; for z≥3/4, f_0≤2y−z≤−1/4 and player 0's regret
is at least 1/8. Thus always R≥(2m−1)/8. Finally c_3≥(1−m)^3 and
1/8−(1−m)^3≤(3/4)(m−1/2), proving (GB3).

Increasing f_i by 2x_3 lowers its regret by at most 2x_i x_3. Therefore
when c_3≤1/2, (GB2) implies

    D(x)≥4s c_3+R+x_3[16(1−c_3)−6−4s c_3]
         ≥4s c_3+R.                                    (GB4)

The bracket is strictly positive. For c_3≥1/8 the survival term suffices;
for c_3<1/8 use (GB3) and 4s=1/25<1/3. If c_3>1/2 and c≥1/8,
the survival term again suffices. In the remaining case x_3>3/4 and
every core x_i<1/2. Since f_i≥−1, every g_i>1/2, and the core regret
sum exceeds 3/4. These cases prove D(x)≥D_0 for EVERY x∈[0,1]^4.
Thus no pure coalition or other first-row mixture escapes (GB1).

### Global minimization over every actual tail

Fix q. For ANY four independent conditional tail laws, let (u,b) be their
actual payoff/complete-cap pair; let a_1 be the probability exactly one
clock is finite and a_2 the probability at least two are finite. Infinite
supports and arbitrary timing are allowed. The late-finite cap gives

    b_i≥s+H·P(some opponent tail clock is finite)≥s.

Continue therefore dominates the old tied Quit branch of every core
player, and player 3's smaller Quit branch. Exact subtraction gives

    D_new−D_0=(1/8){2Σ[i<3](b_i−s)+(b_3−s)−Σ_i u_i}.    (GB5)

The deleted-opponent weights (2,2,2,1) total seven. One finite clock is
seen with weight at least five; two or more are seen with weight seven.
The positive cap term is at least H(5a_1+7a_2). Singleton total reward
is s+3P. Nonsingleton totals are 4P+1 for a core pair, 4P−3 for the
core triple, 4P−14 for a pair with 3, 4P−11 for a triple with 3,
and 4P−13 for the grand coalition. Consequently

    Σ_i u_i≤(s+3P)a_1+(4P+1)a_2,
    D_new−D_0≥(1/8){(2P−6s)a_1+(3P−7s−1)a_2}≥0.       (GB6)

This GLOBAL fixed-root assertion covers all actual tails and extends to
their semantic carrier by continuity. It does not price only Never or
a bounded response menu.

### Screen all joining responses, then change the root

Release only core player 0's conditional Never mass. Give it finite mass t
with conditional geometric parameter 1/4:

    p_0(j)=t(1/4)(3/4)^{j−1},       j=1,2,… .

Other tail laws remain Never. Player 2 can join 0 for P+2: a single new
atom would create an excessive cap. The displayed distribution instead
controls EVERY join test. At date j its excess above s is
H·P(0 before j)+(H+2)p_0(j), which is at most Ht because
2p_0(j)≤H·P(0 after j), using 2/3≤H. Its late supremum is Ht.
Player 1 loses one on joining and player 3 loses sixteen; their tests
are also bounded by the late supremum. Thus the actual tail values are

    u=(st,Pt,Pt,Pt),
    b=(s,s+Ht,s+Ht,s+Ht),       D_tail=4s(1−t).           (GB7)

Never remains separate and is below the late test. No last response is
assumed to attain that supremum.

For rational l<1 near one, set

    W=3+4l−l²,
    λ_0=l(l+5)/W,       λ_1=l,       λ_2=2l/(1+l),
    x_i=λ_i/(1+λ_i),       x_3=0,
    Ht=7l(1−l)/W.

The core cap equalities, checked by substitution, are

    2λ_1−λ_2(1+λ_1)=0,
    2λ_2−λ_0(1+λ_2)=Ht,
    2λ_0−λ_1(1+λ_0)=Ht.

Player 3 still has its full Continue cap. Joint root survival is
a=W/[3(1+3l)²]; the full debt is D_∞=4s a(1−t). It is below D_0
exactly when 3H/(8−5H)<l<1. Taking l=99/100 gives

    x=(19767/39700,99/199,198/397,0),
    t=700/59799,       a=19933/157609,
    D_∞=59099/11820675,
    D_0−D_∞=7/18913080>0.                                (GB8)

These are actual independent infinite laws. The next calculation makes
the entire change finite while retaining every cap branch.

### Exact finite implementation

Keep x from (GB8). Retain geometric atoms j=1,…,L and send the remaining
conditional mass Δ=t(3/4)^L to Never. Put t_L=t−Δ. Tail utilities are
(s t_L,P t_L,P t_L,P t_L), and complete caps are

    b_0=s,       b_1=b_3=s+H t_L,
    b_2=s+H t_L+(2/3)Δ.                                 (GB9)

Player 2's last retained atom maximizes its finite join test. The excess
over the late test at j is
t[(2−3H)(3/4)^{j−1}/4+H(3/4)^L], increasing with j; at L it is
twice the last atom, (2/3)Δ. Empty dates after L give the late test,
and Never gives less. Player 1's losing join and player 3's negative
join tests are dominated by late responses. Player 0's tail opponents
are all Never, so every finite test pays s.

Because H>2/3, every tail cap in (GB9) is weakly SMALLER than in (GB7).
At the prefix all three core caps are therefore their date-0 Quit values,
including the original tied branches. Player 3's Continue cap stays
strictly maximal. Total prescribed payoff loses a(s+3P)Δ, while the
sum of caps loses aHΔ. Hence, exactly,

    D_L=D_∞+2a(P+s)t(3/4)^L.                             (GB10)

For L=32, D_L<D_0 is equivalent to 622160·3^32<77·4^32; the two
integers are 1152875040696061396560 and 1420399293675635474432.
Direct rational evaluation gives

    D_32=545124816137918351766667/
              109026483251748327024230400<1/200.         (GB11)

The actual profile uses the new date-0 rates x. Only player 0 has later
atoms, with unconditional masses (1−x_0)t(1/4)(3/4)^{j−1} at j=1,…,32.
All remaining mass of every player is Never. This is a legal finite
product law with every finite response and Never accounted for. Arithmetic
was checked using Python `fractions.Fraction`, without file output or Lean
changes; (GB11) is ordinary mathematics, not a Lean declaration.
An independent calculation within this session enumerated the full raw
table on all actual product outcomes, then every pure response 0,…,33
and Never. It reproduced (GB11) exactly. Player 0's maximizers are every
finite date; players 1 and 2 maximize only at date 0; player 3 maximizes
at the late date 33. Every date after 33 has that same late response
value. This is a separate arithmetic check, not an independent author review.

### The true infimum and the next question

The true infimum is zero by an explicit profile: use the geometric clock
of parameter 1/4 with TOTAL finite mass one for player 0, and leave all
others at Never. Player 0 gets and is capped by s. Every outsider gets
P; the same screening inequalities in (GB7) with t=1 bound every pure
finite response by P, and Never attains P. This is an exact terminal Nash
profile. Truncating its geometric law after L dates gives exact full debt
(4s+2/3)(3/4)^L, hence literal finite-law approximate Nash profiles.

There is also a source-compatible check using the existing small-player
producer. The deleted three-player core has terminal approximate Nash
profiles at every error. For an actual core profile let
N be its joint-Never probability. Adding player 3 at Never preserves all
core utilities and caps. For player 3, joining is worse than remaining
passive, and quitting alone before a later finite core coalition pays
s≤P. Every pure finite response has gain over Never at most sN, and
arbitrarily late responses converge to that bound. Its added debt is
exactly sN. Each core debt is at least sN by moving only its own Never
mass to arbitrarily late dates. Thus full debt is at most twice core
total debt and tends to zero.

The bounded source lookup inspected:

- `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` in
  `UniformEquilibrium/Quitting/Classification/SmallPlayerExistence.lean`;
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`;
- `quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockPositiveSingleton`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMultipleOutsiderDebt.lean`;
- the finite future/joining rows in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.

That positive-child-singleton machinery already covers this deletion adapter:
the test gives no new UE class. The simpler continue-floor theorem does NOT
apply, because `quittingContinueFloor` in
`UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean` includes zero
while this owner has positive singleton. Exact statements were read under
their imports; no Lean build or fresh check was run.

The direct geometric producer explains an additional scope limit: every
singleton column in this test is above every outsider's own singleton.
Thus it does not satisfy the stronger canonical no-UE source restrictions
in the earlier matrix section. Its purpose is precisely to isolate the
failure of separate GLOBAL block minimization; it is not a hard raw-table
candidate that survives every known existence screen.

The newly falsified implication is: global root-block optimality together
with global whole-tail-block optimality implies global whole-profile
optimality. The actual finite escape also shows an operational requirement:
a joining premium must be screened by a produced complete clock law before
its cap can be used in root balancing. Root equations alone miss this cost.

The arbitrary true-minimum consumer remains open. Root balancing can be
singular or leave the cube; an arbitrary old continuation need not admit
the screened release; the resulting cap changes need not satisfy (GB8).
The next question is to extract a finite-amplitude screened replacement
from genuine joint whole-profile minimality, or identify a rigid source
class that prevents it. Further strengthening solved-table optimization
traps is not the next mechanism.

## Why a minimum-preserving root homotopy does not follow from globality

Status: a substantive failed mechanism, with its exact obstruction proved
below. This is a direct consequence of the existing all-owner margin and
prefix ledger, not a new conjecture-facing reduction or claimed result.

After (GB1)–(GB11), the attempted global mechanism was to transport the
collision root along cap-balanced continuations until it reached an empty
root or a sure boundary, while projecting every intermediate profile back
onto the TRUE minimum δ. The first alternative fails for a precise reason:
the minimum set itself has a neighborhood excluding every nonempty prefix
over tails close to any actual semantic minimum. Connectedness of the
whole carrier does not give connectedness of this minimum fiber.

Let w=(u,b) be a true global minimum, D(w)=δ>0, and use the supplied
strict margin b_i−s_i≥δ+γ. By continuity there is a carrier neighborhood
V of w such that every z=(a,c)∈V satisfies

    c_i−s_i≥D(z)+γ/2 for every i.

Uniform continuity of the finitely many root polynomials supplies a
neighborhood X of the all-Continue root such that for every x∈X and
z∈V the Continue branch is strictly maximal and

    C_i(x;z)−Q_i(x)≥D(z)+γ/4.

The exact ledger, with A(x)=∏(1−x_i), then gives

    D(T_x(z))=A(x)D(z)+Σ_i x_i[C_i(x;z)−Q_i(x)]
              ≥D(z)+(γ/4)Σ_i x_i
              ≥δ+(γ/4)Σ_i x_i.                           (HM1)

The first inequality uses 1−A(x)≤Σ_i x_i and D(z)≥0. It retains all
Quit/Continue branches, since the strict inequalities prove rather than
assume the common Continue branch on this neighborhood. Tail membership
in V is semantic closeness of actual carrier points; no unrealizable
conditional law is introduced. Thus even simultaneously changing the OLD
tail cannot preserve minimum debt when the tail approaches w and a fresh
nonzero root approaches all Continue.

Consequently a continuous path (x(t),z(t)) of minimizing decompositions
with endpoint (0,w) must have x(t)=0 near that endpoint. There is no
automatic minimum-preserving continuation from the supplied nonzero
collision decomposition to that endpoint. A proposed cap-equation
homotopy must either leave the minimum set, end at a different boundary,
or supply an independent global comparison that crosses the barrier.
Following a locally invertible cap Jacobian is not that comparison.

This is consistent with the exact finite escape above: its path crosses
the separate block barriers and compares a distant actual product law.
For a true minimum, such a distant comparison must be produced from its
whole old conditional laws. The unresolved next question is a finite
replacement of old finite stopping mass, with its complete response
switches calculated, that crosses the barrier and lowers total debt.

## Existing-atom reweighting excludes unique on-support complete caps

**Status.** Candidate proved below in ordinary mathematics under the exact
marked-source hypotheses. An independent check passed; this
is not Lean-checked, not exported, and does not settle the multi-cap or
zero-own-point-mass branches. It changes existing finite stopping mass, rather
than adding a fresh root or merely releasing Never. The source-specific
isolation and signed finite transport are essential, not optional
regularity assumptions inferred from generic unique attainment.

### Self-contained question and inspected dependencies

Let I be a nonempty finite player set, with |I|=n (in the live application
n=4). Let r_i(S) be arbitrary signed rewards for each nonempty coalition
S⊆I, bounded in absolute value by M. The all-Never outcome pays zero.
Each player samples its stopping time independently. A deviator may
replace its complete stopping law; hence its cap is the supremum over
ALL pure finite dates and Never, including arbitrary late dates.

Let δ be the infimum of the sum of unrestricted terminal debts over
actual independent finite stopping-law profiles on ℕ∪{Never}. Suppose
δ>0, and take the produced marked minimum (T,q) from Section 2 of
`POSITIVE_MINIMUM_EARLY_ORIGINAL_COLLISION_STAGE.md`: T⊆[0,c] is compact,
c=max T, Never is a separate isolated label, and

    D_T(q)=Σ_i[b_i^T(q)−U_i(q)]=δ.               (UA1)

The source has a fixed ORIGINAL finite minimizing sequence p^k, old
quantile interval maps π_k, bounded densities r_i^k⇀*r_i, and complete
finite test sets T_k→T. Each positive finite atom of q is the midpoint
τ of one retained open interval J=(a,b); its corresponding original
interval J_k=(a_k,b_k) has a_k→a and b_k→b, and

    T∩J={τ},  τ=(a+b)/2.                        (UA2)

The original outcome and moving-response kernels converge almost
everywhere and in L¹ on these old charts. The complete pure-response
payoffs V_i(t,q_-i) are continuous on the compact disjoint union
X=T⊔{Never}. These are the actual hypotheses produced by that reviewed
source, not properties of an arbitrary payoff/cap annotation in K.

The narrow nearby lookup was
`TerminalSemanticStoppingLawDebtConvexity.lean` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/`: the one-law outcome/payoff
affinity and other-player cap convexity are compatible with, but do not
prove, this simultaneous old-law exclusion. The previous strict-late
multiaffine failure and fixed-cut repair in this notebook were also
checked. `CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md`
records why the product Jensen identity alone does not consume global
minimality. No outer-infimum envelope differentiation is used here.

**Candidate exclusion.** It is impossible that, for EVERY i∈I, there is
a UNIQUE complete maximizing clock τ_i∈X and

    V_i(τ_i,q_-i)=b_i^T(q),  q_i({τ_i})=m_i>0.  (UA3)

Uniqueness means a unique POINT of X, not uniqueness after identifying
distinct response clocks that happen to have the same outcome function.
If distinct clocks attain the cap, (UA3) fails even if their payoffs are
outcome-equivalent at q. Never is permitted as τ_i only when its original
own mass is positive. No Nash root, minimizing continuation, common
Never floor, reward sign, or cap selector is additionally assumed.

### The source-specific cap-stability lemma

Positive OWN mass at a finite τ_i implies positive mixture mass there,
so (UA2) applies. The open interval

    (τ_i−(b−a)/2, τ_i+(b−a)/2)∩T={τ_i}

isolates this test. Never is isolated by the stated disjoint-union
topology. Thus X\{τ_i} is compact. By continuity and UNIQUE point
attainment,

    g_i:=b_i^T(q)−max_{t∈X\{τ_i}}V_i(t,q_-i)>0. (UA4)

Own mass is not being used to control opponent payoffs. It is being
used solely to isolate the maximizing point in the ACTUAL marked test
space. In an ordinary compact calendar, uniqueness at an accumulation
point does not imply (UA4). On ℕ alone, a unique finite maximizer can
also have arbitrarily late near-maximizers. Neither invalid generic
implication is used.

For a vector λ near zero, independently set

    q_i^λ=(1−λ_i)q_i+λ_iδ_{τ_i}.                (UA5)

Both signs are legal: if −m_i/4<λ_i<1, the mass at τ_i is
m_i+λ_i(1−m_i)>0 and all other masses are multiplied by the positive
factor 1−λ_i. When m_i=1 the coordinate direction is simply zero.
Total variation between q_i^λ and q_i is at most |λ_i|. The bounded
payoff coupling estimate gives, uniformly over ALL t∈X,

    |V_i(t,q_-i^λ)−V_i(t,q_-i)|
       ≤2MΣ_{j≠i}|λ_j|.                        (UA6)

Choose an open box about zero so small that
4MΣ_j|λ_j|<min_i g_i and all signed laws are legal. Equations
(UA4)–(UA6) then show that EVERY complete cap stays uniquely at its
displayed τ_i throughout that box. This covers ALL marked finite tests,
the last finite test c, and Never. No late-response branch is dropped.

To compare with the source's extended test space T⁺=T∪{c⁺}, observe
that τ_i≠c for every i, since q_i({c})=0 whereas m_i>0. Equation
(UA5) therefore gives q_i^λ({c})=0 throughout the signed box (and
indeed throughout every legal λ). No prescribed finite mass lies
strictly above c, and no mass is inserted at c⁺. Thus a deviator at c
and one at c⁺ face exactly the same outcomes: any finite opponent
exit occurs strictly earlier, and on the remaining all-opponent-Never
event the deviator is the sole quitter. Consequently, for arbitrary
signed rewards and even when some chosen τ_j is Never,

    V_i(c⁺,q_-i^λ)=V_i(c,q_-i^λ).              (UA6a)

The extra DISTINCT test c⁺ cannot be maximizing: the unique supported
τ_i is not c and (UA4) places c strictly below it. Hence the cap and
the uniform cap gap are unchanged on the COMPLETE extended compact
test space X⁺=T⊔{c⁺,Never}. This argument proves, rather than assumes,
that the last finite response is harmless; it never identifies either
finite test with Never.

### Signed transport on the original actual finite witnesses

The source's finite-atomic variation theorem states λ_i∈[0,1]; it is
NOT sufficient by itself to authorize the negative λ_i in (UA5).
Here is a separate transport using the existing retained own atoms.

If τ_i is finite, let τ_i^k be the unique original date whose old
interval is J_{i,k}→J_i of positive length. If τ_i=Never, let
J_{i,k}=(c_k,1) and J_i=(c,1). Positive m_i at Never ensures 1−c>0.
Weak-* convergence and the constant retained-atom densities give

    p_i^k({τ_i^k})=m_i^k→m_i>0.                (UA7)

Here τ_i^k is Never in its own case, not a late finite substitute. For
all sufficiently large k, m_i^k≥m_i/2. For any fixed λ in the above
box with λ_i≥−m_i/4, the literal old-calendar laws

    p_i^{k,λ}=(1−λ_i)p_i^k+λ_iδ_{τ_i^k}        (UA8)

are probabilities: away from τ_i^k they remain nonnegative, and at
that date their mass is at least m_i/2−m_i/4=m_i/4. They have finite
support, remain independent, add no clock, delete no tester, and retain
original Never. This is an actual finite-law move of old stopping mass.

On the OLD common quantile domain their densities are

    r_i^{k,λ}=(1−λ_i)r_i^k
                  +λ_i 1_{J_{i,k}}/|J_{i,k}|.  (UA9)

The normalized interval indicators converge strongly in L¹ because
their endpoints converge and their limiting lengths are positive.
Consequently these nonnegative densities have a uniform L∞ bound
(for example |1−λ_i|n+2|λ_i|/|J_i| for all sufficiently large k),
and converge weak-*
to the corresponding density of q_i^λ. Their product and every opponent
product converge weak-* by the same rectangle-test argument as the
source. The ORIGINAL maps π_k and their kernels are unchanged, so their
a.e./L¹ outcome and moving-response convergence is still valid. The
split into fixed-kernel weak-* convergence plus moving-kernel L¹ error
therefore proves

    U_i(p^{k,λ})→U_i(q^λ),
    b_i(p^{k,λ})→b_i^T(q^λ).                    (UA10)

For the cap upper bound take any original maximizing test sequence and
extract a convergent OLD location in T, or the separate Never label;
the unchanged moving-kernel proof applies. For the lower bound retain
the source's approximations to each fixed T-test and Never. In fact,
within the cap-stable box, every maximizing sequence eventually uses
the displayed τ_i^k: any other limiting location contradicts (UA4),
and convergence to a retained midpoint forces the unique original
midpoint by (UA2). None of these modifications puts mass at the
non-atomic last finite test c, so no extra c⁺ response is needed.
Equivalently their limiting complete caps also equal those on X⁺,
by the explicitly proved duplication (UA6a).

For EVERY fixed λ in that open box, (UA8) is actual and hence has
D(p^{k,λ})≥δ. Taking the limits in (UA10) yields

    D_T(q^λ)≥δ.                                (UA11)

This explicitly uses the original finite witnessing sequence. It does
not claim arbitrary signed changes of an annotated carrier pair are
realizable, or that one finite profile realizes all counterfactual laws.

### A multiaffine branch cannot carry positive global debt

Because all complete caps stay at τ_i in the open box,

    D_T(q^λ)=F(λ)
      :=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)].          (UA12)

F is a multiaffine polynomial in λ_1,…,λ_n. Each fixed-response
payoff is affine separately in every opponent law; each prescribed
payoff is affine separately in every law. Thus each λ variable occurs
with degree at most one in every monomial, and total degree is at most n.
Equations (UA1),(UA11),(UA12) make zero an INTERIOR local minimum of F,
with F(0)=δ.

An interior local minimum of a multiaffine polynomial is constant.
Indeed, if F−F(0) is not zero, let H_k be its lowest nonzero homogeneous
Taylor part, 1≤k≤n. Its nonconstant square-free monomials have average
zero over the independent sign cube {−1,+1}^n and are linearly
independent there. Hence H_k has a strictly negative value at some
sign vector h. For sufficiently small ε>0,

    F(εh)−F(0)=ε^k H_k(h)+O(ε^(k+1))<0,       (UA13)

contradicting the local minimum. This argument permits identically
zero coordinate directions and does not require a nonzero first
derivative or a nonsingular cap Jacobian.

But the polynomial F has the exact algebraic endpoint

    F(1,…,1)=0.                                (UA14)

At that endpoint every displayed prescribed law is the pure clock
δ_{τ_i}; each displayed response τ_i is identical to its prescribed
own law, so V_i(τ_i,q_-i^1)=U_i(q^1). This identity includes ties,
Never, and the all-Never payoff zero.

IMPORTANT: (UA14) does NOT assert D_T(q^1)=0, nor that the τ_i remain
complete caps at this distant endpoint. Only the globally defined
POLYNOMIAL selected in (UA12) is evaluated there. It would be constant
if it had an interior local minimum; its endpoint zero would then
contradict F(0)=δ>0. Thus a nonconstant leading part exists and (UA13)
actually applies inside the cap-stable neighborhood.

Choose ε and let η=δ−D_T(q^{εh})>0. By (UA10), for large enough k the
literal finite profile (UA8) satisfies

    D(p^{k,εh})<δ−η/2.                         (UA15)

This contradicts the TRUE actual global infimum. It is an actual
finite-amplitude coupled change of existing finite/Never mass, not a
formal directional inequality with unmeasured cap leakage. Therefore
(UA3) is excluded. ∎

### Surviving source geometry and precise next question

At every positive represented global minimum, SOME player's cap is
either attained at more than one distinct clock, or has no unique
maximizing clock carrying positive mass in its owner's prescribed law.
The latter includes a unique zero-mass accumulation cut and a unique
finite/Never response outside the point-atom support. A zero-mass cut
may still belong to the TOPOLOGICAL support of the owner's law.
The exclusion does not say every
owner's debt is zero, and does not eliminate responsive multi-cap cycles.

The minimal failed generalization is replacing (UA3) by mere unique
attainment: without isolation, (UA4) need not hold and an o(ε) cap
switch can dominate an ε^k polynomial decrease. Another invalid
generalization identifies equivalent responses at q without showing
their payoff FUNCTIONS coincide throughout the signed neighborhood.

The next substantive question is whether the genuine all-law minimum
forces a joint reweighting inside a multi-cap active face, or forces one
active response onto a non-isolated/off-support boundary that a separate
actual calendar operation consumes. A first-root responsive cycle alone
does not supply either implication. The requested independent check is
the isolation/complete-cap lemma (UA2)–(UA6), signed actual transport
(UA7)–(UA11), and the distinction between polynomial endpoint (UA14)
and actual cap debt at that endpoint.

Independent initial stress-test: CODEX_NOETHER checked the actual
marked-clock isolation, complete c/c⁺ comparison, retained-atom signed
density transport, and the algebraic endpoint distinction. The review
agreed with those steps under the unique-POINT/on-support hypothesis.
This is an internal candidate checkpoint, not authorization to export
or a claim of full source consumption.

## Response-faithful triple exchange: one law may change, not two

**Status.** Exact ordinary-mathematics whole-law constraint, not a debt
consumer or export candidate. It was derived while trying to turn
NOETHER's sharp same-profile triple inequality into a comparison involving
actual complete cap responses. The coefficient CHANGES under a unilateral
law replacement; applying the old quarter coefficient to response copies
is false. This is a new obstruction to that proposed paid-cap inference,
not another optimization trap or claimed equilibrium class.

The narrow source search in `MathUE/PMFProduct/`, together with
`Quitting/Paths/StoppingLawOperationalDistance.lean` and
`Quitting/Paths/FiniteCalendarRawPredicates.lean`, found no declaration
for cross-profile triple coordinate exchange. The actual full-cap and
one-law payoff semantics already inspected above remain the input. No
outer infimum differentiation is used.

### The one-coordinate cross-profile inequality

Let P,Q be independent complete stopping-law profiles on ℕ∪{Never},
differing ONLY in player m's law. Finite mass need not have finite
support. Put t_a(P)=P(first coalition I\{a}) and

    e(P)=P(finite first coalition of size 1, 2, or 4).

Define the same coordinates for Q. For ANY distinct a,b∈I,

    t_a(P)t_b(Q)≤e(P)e(Q).                       (RC1)

In particular Q may replace the entire law of m by a pure finite cap
clock or Never. This is about the SAME unchanged opponent laws, not
two independently selected payoff or response witnesses.

Write I={a,b,c,d}, choosing c in the two shared participants so that
c≠m. Sample ordered independent copies X∼P, Y∼Q. On the domain that
X first triple I\{a} occurs at u and Y first triple I\{b} at v,
the finite dates and inequalities are

    X_b=X_c=X_d=u<X_a,
    Y_a=Y_c=Y_d=v<Y_b.

For u<v, swap c's two clocks: the output first coalitions are
({b,d},{c}). For u>v, the SAME swap gives ({c},{a,d}). Since P_c=Q_c,
this is a measure-preserving involution of P×Q, not merely a
coordinate permutation of two different laws.

For u=v, if b≠m swap b, giving ({c,d},I); if b=m, swap a instead,
giving (I,{c,d}). The chosen unshared player is not m, so its
marginals also agree and this swap preserves P×Q. The three branch
images have respectively (pair,singleton), (singleton,pair), and
either (pair,grand) or (grand,pair). They are disjoint ORDERED outcome
categories. Each branch map is injective, with fixed involutive inverse
once its category is read. Consequently the entire domain, of measure
t_a(P)t_b(Q), injects measure-preservingly into the event that BOTH
outputs are exceptional finite nontriples. Its measure is e(P)e(Q),
proving (RC1). Never may be any absent clock, but u,v are finite; the
strict inequalities and all equal-date cases above remain literal.

The same proof works on a compact marked calendar with an isolated
Never label: all clock comparisons and swaps are measurable, and a
triple has one actual earliest finite date. Alternatively, actual
same-opponent-law finite witness pairs transport the finite outcome
coordinates and (RC1) passes to their limit. This observation does
not authorize arbitrary unrelated annotated carrier pairs.

### Coefficient one is sharp, even for a pure unilateral response

Fix c,d surely at date zero and b half at zero, half at Never. Let
P_a=Never and Q_a=date zero surely, leaving every opponent unchanged.
Then P has first triple I\{a} with probability1/2 and pair {c,d}
with probability1/2. Q has first triple I\{b} with probability1/2
and grand coalition with probability1/2. Thus

    t_a(P)t_b(Q)=1/4=e(P)e(Q).                   (RC2)

There is no universal smaller coefficient in (RC1). In particular,
the same-profile e²/4 inequality must NOT be applied across this
prescribed/cap-response pair. If a payoff realization is desired,
give a payoff1 when a belongs to the quitting coalition and0
otherwise; pure date zero is a complete cap response to these
opponents. This is an exact response-mode falsifier, not a positive
global-gap example.

For two response copies changing DIFFERENT players, even coefficient
one with only their exceptional masses can fail. Start all four clocks
surely at zero. Let Q withdraw a to Never and R withdraw b to Never.
They realize distinct pure triples, so t_a(Q)t_b(R)=1 although
e(Q)=e(R)=0. The coupled two-owner withdrawal profile realizes the
pair {c,d}; the base realizes the grand coalition. The missing equal-
date swap transfers its product measure to these TWO HYBRID profiles,
not to Q×R. NOETHER independently owns the resulting common-source
two-coordinate cap-family identity; it is not duplicated here.

### Genuine global use and the remaining unpaid step

At the actual produced marked global minimum q with D(q)=δ>0,
let τ be any complete cap response of m and let q^{m,τ} replace only
that player's full law. The source finite-atomic transport produces
actual witnesses with ALL T⁺ finite tests and Never retained. Its
own cap is unchanged because its opponents are unchanged; its own
prescribed payoff equals the displayed response payoff. Thus

    d_m(q^{m,τ})=0,
    Σ_{j≠m}d_j(q^{m,τ})=D(q^{m,τ})≥δ.          (RC3)

The last inequality is TRUE whole-profile global minimality, not a
fixed-root floor. Alongside (RC3), (RC1) constrains prescribed q
versus THAT same-opponents response profile. For example, if
t_a(q)>0 and e(q)>0, then every b≠a satisfies

    t_b(q^{m,τ})≤e(q)e(q^{m,τ})/t_a(q).        (RC4)

A response that tries to put substantial mass on an incompatible
triple must pay exceptional finite outcome mass. That is a genuine
response-law constraint, but exceptional OUTCOME mass is not by
itself a summed-DEBT payment. Arbitrary signed rewards allow that
mass to be profitable or cap-raising. I have not obtained a universal
inequality converting (RC4) into a lower actual cap bill than the
original δ, and no response arrow has been temporalized into a
private-law correlation mechanism.

The finite active-clock Nash bootstrap also fails at this exact
boundary. If all current cap maximizers are supported isolated atoms,
their set is finite (otherwise its accumulation point would be a
zero-own-point-mass maximizer). A finite game using those pure clocks
and the old complete law as actions has a Nash profile. But it only
annuls regret against that finite action set; a previously nonmaximizing
empty or late T-test can become maximizing at the distant endpoint.
The local uniform gap from (UA4) does not control that endpoint.
Adding every current test to the action set is not a cure: if its
last empty c becomes prescribed, c⁺ no longer duplicates c.

This is the already tracked finite-menu/full-cap boundary, not a new
producer. I inspected
`quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
and
`quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le`
in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`.
They express the exact missing late candidate as Never payoff plus
opponent-Never product times the own singleton. The nearby
`FiniteDeadlineBoundaryResponseCollision.lean` preserves a
counterfactual collision cylinder, not a profitable prescribed repair.
Therefore I am not claiming that Nash on the present active clocks
consumes the surviving source.

The next concrete question is to couple (RC1)–(RC4) with an ACTUAL
joint old-law change and its complete cap ledger, rather than with
the same-profile quarter coefficient or finite restricted regret.
Any such repair must control the newly exceptional response outcomes
and the hybrid two-owner profile; neither is furnished by the law
inequality alone.

## Better-reply security: a global obstruction, not cap-degeneracy consumption

**Status.** A substantive failed existence route, with an exact minimal
test and a true-minimum obstruction. The marked source is locally a
FULL weak-continuity point, even in its surviving multiple-cap and
zero-own-point-mass branches. That local fact does not supply the global
payoff-graph security hypothesis of a discontinuous-game existence
theorem. On the project's ordinary compact stopping-law space, a positive
true minimum with nonnegative own singletons actually supplies a
better-reply-security FAILURE. This is a direction change, not a new
conditional existence interface or a claim that the UE conjecture is false.

### The exact theorem inspected

The literature lane has no Reny transcription. I read the original
Philip J. Reny, “On the Existence of Pure and Mixed Strategy Nash
Equilibria in Discontinuous Games”, Econometrica 67(5), 1999,
1029–1056, Sections 2–3, especially Theorem 3.1. Original-paper locator:
<https://kylewoodward.com/blog-data/pdfs/references/reny-econometrica-1999A.pdf>.
The author's publication list identifies this paper and the 2022
corrigendum; I also checked the latter at
<https://ewerhart.net/files/2022%20Ewerhart%20Reny%20Etrica.pdf>.
It leaves Theorem 3.1 unchanged; no symmetric-equilibrium corollary is
being used here.

The needed theorem is: a compact convex strategy game with bounded
payoffs, quasiconcave in each own strategy, has an equilibrium if it is
better-reply secure. That condition quantifies the ENTIRE closure of
the vector-payoff graph. At a nonequilibrium profile x and any associated
graph-limit payoff u, one owner must have a FIXED allowed strategy
whose payoff remains strictly above u_i on some opponent neighborhood
of x_-i. This is not merely ordinary better-response existence at x,
and not security on the actual minimum set alone.

The strategy sets contemplated here are complete probability laws with
their weak topology; own terminal payoff is affine, hence quasiconcave.
The missing condition is global graph security, not convexity.

Narrow Lean lookup read
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, especially
`CompactStoppingTime`, `CompactStoppingLaw`,
`compactStoppingLawEquivPMF`,
`compactStoppingTime_finiteSingleton_isClopen`, and
`CompactStoppingLaw.tendsto_realMass_of_isClopen`.
`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawProfile.lean`
supplies `quittingCompactStoppingLawProfile` and its exact own-law
identity. `CompactStoppingLawCapUpperBound.lean` supplies
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`:
late finite is Never payoff PLUS the surviving-opponents singleton
term, not Never itself. The nearby
`minimumRealizingSequence_purify_or_offMinimum` in
`Diagnostics/Quitting/StoppingLaw/ArbitraryClockMinimumPurification.lean`
explicitly retains an off-minimum alternative; it is not the needed
global security theorem. No Reny existence theorem is silently imported
from those declarations.

### Ordinary compact laws: the all-Never graph fiber is too large

Let C=ℕ∪{Never} with the one-point compact topology: each finite date
is isolated, and finite dates tending to infinity approach Never.
Let L=Prob(C) with weak convergence, and take the product L^4.
This is the actual strategy space represented by CompactStoppingLaw;
its probability data are exactly all ordinary complete stopping laws.

Given ANY finite-support profile p, shift all its finite dates by k,
retaining its original Never masses. Call this p[k]. First-coalition
probabilities and prescribed terminal payoffs are EXACTLY unchanged,
while every marginal p_i[k] converges weakly to δ_Never. Thus

    (allNever,U(p)) belongs to the payoff-graph closure. (BS1)

For an actual finite sequence p^k with U(p^k)→u, shift its kth profile
by k as well. All finite mass is then at dates at least k, so the same
weak convergence proves (BS1) with the limiting u. This argument uses
actual finite laws; it is not an annotation or correlated law.

Shifting may ADD profitable early empty responses, so caps need not
be unchanged. That is immaterial to (BS1), which concerns prescribed
PAYOFF graph closure. It would be false to call the delayed profiles
full-debt near-minima without a separate cap calculation.

For a FIXED own stopping law z_i, against literal all-Never opponents,

    U_i(z_i,allNever_-i)
        =(1−z_i({Never}))s_i≤max(s_i,0).         (BS2)

Every neighborhood of all-Never opponents contains that opponent
profile itself. Consequently NO own strategy can secure a payoff
strictly above max(s_i,0) there, regardless of its randomization or
unbounded finite support. This is a point evaluation, not an estimate
that loses arbitrarily late responses.

Now suppose δ>0 is the TRUE Fin4 summed-debt minimum and s_i≥0 for
every owner. The inspected declaration
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
gives for its actual payoff/cap carrier minimum

    u_i≥s_i+δ−d_i+δ²/(8M)>s_i,                 (BS3)

since all d_i≥0 and Σ_i d_i=δ. Its actual realizing profiles may be
finitely censored while preserving payoffs and full caps, as already
proved/cited above. Delaying that finite realizing sequence produces
the graph point (allNever,u) in (BS1).

Positive δ also forces some s_j>0 in this nonnegative-singleton branch:
if every s_i=0, literal all Never has payoff0 and caps0, hence δ=0.
Therefore all Never is NOT a Nash profile. But (BS2),(BS3) show that
NO player secures anything strictly above its graph-limit u_i there.
Thus

    δ>0 and all s_i≥0 ⇒ the ordinary compact-law
    game is NOT better-reply secure.             (BS4)

This is the reverse of the proposed use of Reny's theorem. The actual
true-minimum margin does not verify its security hypothesis; together
with the compactification it supplies an exact failure point. In the
signed-own case the same argument excludes security whenever the
realizing payoff has u_i>max(s_i,0) for EVERY owner. The signed margin
u_i>s_i alone does not justify that stronger inequality.

Minimal exact test, reusing the earlier four-player boundary table:
r_i(S)=1 when i∈S and0 otherwise. Shift the pure grand-coalition
profile to dates k. Its payoff is always (1,1,1,1), and its weak limit
is all Never. All Never is nonequilibrium (any owner can quit for1),
but no payoff can exceed1. Better-reply security fails at this graph
point although the table has exact terminal Nash at every pure grand
date and true δ=0. Thus the issue is not an unknown positive-gap table
or a stronger solved optimization trap.

### The marked minimum itself is a full weak-continuity point

Now keep the actual produced compact marked X=T⊔{Never}, where Never
is isolated and every positive finite MIXTURE atom is isolated in T.
Consider ALL independent laws on X, not merely laws dominated by the
original mixture or densities bounded by a fixed constant.

**Lemma.** If p^k→q marginally weakly on this FIXED X, then

    U_i(p^k)→U_i(q),  b_i^T(p^k)→b_i^T(q).     (BS5)

Moreover, for every moving complete pure-test sequence t_k→t∈X,

    V_i(t_k,p_-i^k)→V_i(t,q_-i).               (BS6)

Here q is the original marked minimum, not an arbitrary law on X.

Proof. The bounded first-coalition kernel on X^4 is continuous at any
clock tuple whose finite ties occur only at isolated points. For an
isolated common clock, sufficiently close finite coordinates equal it
exactly, so its tie is retained. With distinct finite clocks the
ordering is stable. Never is an isolated label and is not approached
by finite clocks. The remaining possible discontinuities have at
least two independent coordinates equal at a NON-isolated finite
point. That event has q-product probability zero: a tie has positive
mass only when both laws have an atom there, which would make it a
positive mixture atom, hence isolated. Weak convergence of the product
measures and the bounded almost-everywhere-continuous integration
criterion give prescribed outcome and payoff convergence.

For (BS6), the analogous response kernel has its possible bad set at
an opponent coordinate equal to the fixed finite t if t is non-isolated.
Every q_j has zero atom there. If t is isolated, t_k=t eventually,
so any actual tie remains exact. A tuple with earliest opponents
ties away from t again has only the null non-isolated tie set just
described. A coupling/Skorokhod realization of the weakly convergent
laws on the compact metric X, followed by bounded convergence, proves
the moving-test identity. Equivalently use the same product/kernel
argument with the deterministic response coordinate δ_{t_k}.

Each p^k cap is a supremum, not assumed attained. Choose tests within
1/k of it and extract a convergent subsequence by compactness of X.
(BS6) proves the limsup bound. Retain one actual maximizing test at q
for the liminf bound. This proves full cap convergence (BS5), including
all late marked finite tests and Never. ∎

For the extra finite c⁺, q_i({c})=0 makes its original value duplicate
c, and (BS6) handles that fixed extra test as well. The conclusion
does not say a nearby profile with newly inserted c mass has those
two response functions identical.

In particular, every displayed complete cap response of q is locally
secure against unrestricted weak opponent-law perturbations. Some
owner has d_i≥δ/4>0, and its maximizing pure test secures a payoff
strictly above U_i(q) in a weak neighborhood. This holds when the cap
has MULTIPLE maximizing clocks and when its unique maximizing clock
has ZERO own point mass. Forced cap degeneracy is not a discontinuity
of the payoff or full-cap map at the original marked minimum.

### Why this does not yield an equilibrium producer

Reny's graph-closure condition is global. (BS5)–(BS6) prove it only
at the source q and profiles with the same isolated-atom property;
arbitrary other laws on X can put new atoms at non-isolated original
zero-mass cuts. The complete payoff game can then have discontinuities.
The same-profile cap gap cannot control every graph point of that game.

Keeping a fixed dominated-density strategy set makes all integral
payoffs continuous and its weak-* law cube compact. A Nash equilibrium
there need not control excluded clocks: at an atomless point, an
arbitrarily narrow approximation to a pure test may require density
far ABOVE the imposed bound, particularly when opponents' own densities
concentrate at that bound. Increasing the bound does not provide a
uniform full-cap error, and new limiting atoms again appear at those
cuts. An equilibrium of that restricted cube is therefore not an
actual epsilon-Nash producer. No excluded response is discarded here.

Re-marking EACH new limiting atom would restore the local continuity
property (BS5), but the common quantile calendar depends on ALL players'
laws. It is not a product of four fixed convex strategy spaces with
independent unilateral agency. Hence compactness of the marked source
carrier cannot be substituted for the Cartesian compactness premise
of the existence theorem. This is an actual topology/agency mismatch,
not a missing continuity convention.

The next mechanism must therefore use a GLOBAL joint law comparison
and its summed-cap ledger, or a genuinely response-complete approximation
whose compactness survives the new atoms. Neither the ordinary compact
law security theorem nor a dominated-density Nash gives that consumer.
The forced multiple-cap/zero-own-point-mass alternative remains open.

## Independent MORSE45 gate, then return to full-law existence

I independently falsified MORSE's complete H1–H12 support-local
UPPER-or-CHARGE raw-class candidate at frozen whole-notebook SHA256
`6a32c34b7c6d4da99abc197598d06dc386755f9e5420e6ee963d966122020220`.
The complete review is retained in my existing
`feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BROUWER.md`.
No counterpart review was read. Verdict: PASS, including quiet, partly
sure and all-sure roots, ONE common reward box, the actual fixed-target
uniform-payoff consumer, and complete selections of the compared raw
producers. Exact rational recomputation confirms the sixty-entry fixture,
all five traps, all charge coefficients and the actual stationary
profile with every own payoff above its singleton. This is a genuine
raw reward-class adapter, not a universal Fin4 consumer.

The newly inspected declarations and files are recorded in that review;
in particular the selected-return consumer really accepts arbitrary
boxed continuation annotations, so it does not require actual law
realization of each finite Nash root. That source-level mode differs
from our genuine debt minimum, whose cap geometry remains unresolved.
The next owned question is a response-complete full-law approximation
that avoids both the allNever graph defect (BS1–BS4) and the fixed-density
exclusion (BS6), or a joint-law comparison using the marked source.

## Increasing density bounds and bounded entropic Nash: exact failed producer

Status: ordinary-mathematical falsifier of a specific approximation
mechanism, not a new game counterexample or a supplied-interface export.
This uses ONLY the existing participant-indicator boundary table,
r_i(S)=1 if i∈S and 0 otherwise, whose true infimum is zero. It does
not introduce another local-optimization trap. The target mechanism
was Nash existence on an increasing bounded-density cube, followed
by full-cap realization, possibly after a bounded common-mixture
relative-entropy penalty. The excluded-clock error is exactly visible.

### DR1. Restricted density Nash at every scale

Fix L≥1. Every controller chooses a finite-clock density f_i on [0,1]
with 0≤f_i≤L and integral at most one; the remainder is Never. Pure
unrestricted tests retain every t∈[0,1] and Never. Against three copies
of g_L=L·1_[0,1/L], the pure test payoff is

    V_i(t)= (1−Lt)^3     for 0≤t≤1/L,
            0           for 1/L≤t≤1,
    V_i(Never)=0.

Opponent finite ties have probability zero. The first display is
strictly decreasing on its positive interval. Among EVERY density
bounded by L, moving all allowed mass to that earliest interval
therefore maximizes expected payoff. Formally,
∫(g_L−f)V=∫_[0,1/L](L−f)V≥0; omitted outside mass and Never contribute
zero. Thus (g_L,g_L,g_L,g_L) is an EXACT Nash equilibrium of this
restricted compact game. Each U_i=∫_0^1 (1−x)^3 dx=1/4.

But the unrestricted pure clock 0 has payoff 1. Its FOUR complete
debts sum to 3, at EVERY L. Increasing the density bound does not
give a full-response error tending to zero, even when the chosen
restricted equilibria converge weakly to a perfectly good pure Nash
profile at zero. Their payoff graph does not converge to that profile's
actual simultaneous-coalition payoff.

### DR2. The actual finite-law discrepancy is retained

To realize the same atomless order law, let every player independently
choose uniformly from m consecutive finite dates. Never mass is zero.
Under this table, player i is paid one exactly when its date is one
of the minimum-date quitters. Therefore

    U_i= m^(−4)·∑_(k=1)^m k^3 = (m+1)^2/(4m²),
    B_i=1,
    D=3−2/m−1/m² →3.

The first available date is itself a full-cap test, so this calculation
does not need an illegally inserted earlier date. All actual finite
witnesses retain the discrepancy. Clock compression or weak collapse
to a tied atom instead changes the prescribed payoff; it is not a
payoff/full-cap approximation of the restricted density equilibrium.

### DR3. A bounded relative-entropy penalty leaves the failed producer intact

For a complete law profile put μ=(p_0+p_1+p_2+p_3)/4 and
I_i=KL(p_i∥μ). This is well-defined in every probability mode because
p_i≤4μ, and 0≤I_i≤log4. Replacing the finite or continuous payoff by
U_i−τ I_i, τ≥0, keeps the full-law regularization cost bounded.

At the density profile of DR1 all four laws agree, so I_i=0. Against
the other three copies, EVERY legal bounded-density replacement f_i
has U_i(f_i)≤1/4 and I_i(f_i)≥0. Consequently the same profile is
an exact Nash equilibrium of the ENTROPIC restricted game at every
L and every τ≥0, still with original full debt 3. A common-mixture
penalty encourages likelihood overlap, not chronological dispersion
or response completeness. It cannot repair this approximation gate.

This does not assert that the FULL regularized game has no equilibrium.
Indeed any full Nash profile for this bounded-cost game would give
original unilateral gains at most τ log4, directly from its Nash
inequality and I_i≥0. Producing such profiles is the substantive
unrestricted existence problem; the increasing restricted-density
equilibria above do not produce them.

### DR4. Bounded nonnegative penalties also preserve the escape-to-Never defect

In the positive-global-gap branch with s_i≥0, write γ>0 for the
checked true-minimum slack from BS3, so the source payoff u_i>s_i+γ.
Consider ANY nonnegative law-dependent penalty bounded by η, with
η<γ, and a sequence of actual minimizing payoffs tending to u.
Delay every finite date of the kth profile beyond k. Payoffs still
tend to u, and the penalized payoff sequence has a subsequential
limit at least u_i−η>s_i in every coordinate. All laws tend weakly
to Never. At literal allNever opponents, every fixed own strategy's
original payoff is ≤s_i; subtracting a nonnegative penalty cannot
raise that bound. Hence no strategy secures above the displayed
graph-limit payoffs. If additionally η<max_i s_i, the allNever profile
remains nonequilibrium (the positive owner may quit alone). This
extends the BS graph defect to bounded penalties, including the
common-mixture entropy with τ log4<min(γ,max_i s_i).

Thus bounded entropic perturbation does NOT furnish the missing global
better-reply security. An unbounded absolute-time cost might furnish
ordinary compactness but no longer gives a uniformly small bound for
all original clock deviations, so it is outside this proposed producer.

### DR5. Mechanism retired; actual frontier remains the response seam

The restricted-density Nash mechanism, with or without bounded identity
entropy, is retired. The independent full-goal question is now a joint
law/response construction that keeps all clocks as actual deviations.
The owned entropy-minimum compactness result remains valid, but it is
not upgraded to Nash existence by DR1–DR4. No new theorem premise,
state field, export or uniform-equilibrium claim is added here.

### DR6. Whole atomless-clock class excluded, not just the symmetric selector

The coordinator's scope question has a complete affirmative answer.
For the same participant-indicator table, let EACH independent law
have an arbitrary atomless finite-clock part on an ordered real
calendar bounded below, and arbitrary Never mass n_i. No symmetry,
density bound, common support or regularization is assumed. Independent
finite ties have probability zero: for i≠j, integrate p_j({t})=0
against p_i. The first finite coalition is therefore a singleton
almost surely. Since only its members are paid one,

    ∑_i U_i = P(some finite stop)=1−∏_i n_i≤1.

Every complete finite-clock cap is 1. If the calendar has an earliest
point, quitting there is a pure payoff-one response; no opponent has
an atom there and none is earlier. If only a finite lower infimum is
available, tests approaching it have payoff tending to one, which
still gives cap1 without claiming attainment. All table rewards are
at most one. Consequently

    D=4−∑_i U_i =3+∏_i n_i≥3.                         (DR6)

Thus EVERY purely atomless independent-clock profile misses terminal
epsilon-Nash for epsilon below 3/4 in maximum individual gain (and
has sum debt at least3). There is no favorable existential restricted
density-Nash selector hiding behind DR1: the WHOLE atomless strategy
class is incapable of approaching the original game's debt-zero
target, despite the actual pure grand coalition being exact Nash.

For original nonnegative integer clocks in this table, pure date zero
always gives payoff1, EVEN with opponent atoms. More generally,

    D=4−E|S_first|,

where S_first=∅ on perpetual continuation. If D≤ε then
P(S_first=I)≥1−ε, because 4−|S_first|≥1 whenever the first coalition is
not grand. So approximate equilibrium for this table REQUIRES almost
sure simultaneous grand absorption, not an atomless order limit.
Any actual finite approximation claiming prescribed-payoff AND full-cap
convergence to an atomless law retains the lower bound in (DR6); adding
large tied mass instead is a material payoff change, not that realization.

This is an exclusion of an approximation CLASS on a solved boundary
game. It is not a positive-global-gap example and cannot be inserted
inside the genuine first-collision source as a contradiction. The
next route must actively retain and change collision atoms; neither
bounded-density tuning nor an atomless continuum replacement is used.

## One exceptional latest cap: conditional old-mass transport and a sure-clock reduction

Status: a COMPLETE ordinary-mathematical source restriction, with a
focused independent NOETHER PASS of LC1–LC5 and the earlier-own-mass
consequence in LC6. No full export gate or export is requested; this is
not a whole Fin4 consumer. The review checked the exact positive
rescaling of the exceptional cap, the moving retained-atom cutoff,
the two-sided signed original-law transport, and the distinction
between the algebraic endpoint and its actual unrestricted debt.
It uses the TRUE global sum minimum and preserves every full response.
No root Nash, minimizing old tail, nonnegative reward, or atomless
approximation is assumed. Its source is precisely the produced marked
calendar and laws of UA1–UA15; Never is isolated and ordered after every
finite clock. The extra late test c⁺ is retained as an outcome-equivalent
copy of c for these old-chart changes, not discarded.

### LC1. Self-contained claim

Let bounded signed Fin4 rewards satisfy |r_i(S)|≤M. Let q be a
produced marked global minimum with full sum debt δ>0, on compact
finite-clock set T and isolated Never, with q_i(c)=0 at c=max T.
The prescribed laws have bounded old quantile-chart densities, every
positive finite mixture atom is an isolated retained midpoint, and
old-chart finite realizing sequences preserve prescribed payoffs and
ALL pure-response caps as in UA1–UA15. Suppose every owner's complete
cap has a unique POINT maximizer τ_i on X=T⊔Never. For one owner m,

    q_m({τ_m})=0,
    q_j({τ_j})>0 for every j≠m,
    τ_j<τ_m for every j≠m.                             (LC1)

Put t₀=min_(j≠m)τ_j; all three nonexceptional τ_j are finite, since
Never is the last point. Then necessarily

    q_m({t:t>t₀}∪{Never})=0,
    τ_j=t₀ for all j≠m,
    q_m({t₀})>0,
    δ=r_m(I∖{m})−r_m(I)>0.                            (LC2)

The first line strictly excludes every source geometry in (LC1) with
positive own mass later than the earliest other maximizing clock.
The remaining geometry is a sure-by-t₀ exceptional owner and three
common supported cap atoms. The numerical final identity is a selected-
response polynomial evaluation, NOT an assertion that the pure-grand
endpoint has actual full debt δ or belongs to the minimum fibre.

### LC2. Ordered unique-cap stability without isolated exceptional clock

Let h=max_(j≠m)τ_j. Reweight each nonexceptional law only toward its
EXISTING supported cap atom:

    q_j^λ=(1−λ_j)q_j+λ_jδ_(τ_j),       j≠m.

These are probabilities for a two-sided open box around zero, because
their own point masses are positive. The mixture factors 1−λ_j are
strictly positive there. For a finite exceptional maximizer τ_m>h,
choose a strictly between h and τ_m. For EVERY response clock t>a,
including Never, expand the opponent product:

    V_m(t,q_{−m}^λ)
       = [∏_(j≠m)(1−λ_j)]·V_m(t,q_{−m})+C(λ),       (LC3)

where C(λ) is independent of t. Each nonempty replacement subset
has at least one sure finite opponent clock τ_j≤h<a; that opponent
has absorbed before t, even if other opponents stop still earlier.
The prescribed first-coalition payoff in that summand is independent
of the response time. This reasoning also covers signed expansion
coefficients: only the coefficient of the original term needs to
be positive to preserve its maximizing order.

The compact lower-clock set T∩[0,a] does not contain τ_m. Original
response continuity and unique maximization give a strict uniform gap
on that set. The standard 2M∑|λ_j| response-change bound preserves
this gap for a smaller two-sided box. Formula (LC3) preserves the
unique maximizer on all clocks above a. Thus τ_m remains the complete
cap maximizer, even when it is a NONISOLATED zero-mass point. If τ_m
is Never, its isolation gives the ordinary uniform-gap argument
directly. Every other τ_j is isolated and has its original uniform
gap, so all their maximizers remain fixed under sufficiently small
simultaneous changes of the other laws as well.

This is not the false generic implication “unique nonisolated max
gives a uniform gap”. The order of the OPPONENT replacement atoms
below the exceptional response yields the exact affine rescaling
(LC3) near that maximum.

### LC3. Signed conditional transport of existing mass after t₀

Assume e=q_m({t:t>t₀}∪{Never})>0, and define the conditional OLD law
ν=q_m(· | t>t₀), including Never in the event. Vary the exceptional law
by

    q_m^λ=(1−λ_m)q_m+λ_mν.                            (LC4)

On the event's complement its likelihood multiplier is 1−λ_m; on
the event it is 1+λ_m(1/e−1). Hence |λ_m|<min(1/4,e/8) is a legal
two-sided box. If e=1 this simply leaves q_m unchanged and still
causes no difficulty. Together with LC2, ALL caps are fixed on the
product box. The own-law change (LC4) does not affect m's response
values; it affects other owners continuously in total variation,
whose supported unique cap points are isolated.

The actual finite witnesses are not supplied as a new interface.
In the original realizing sequence, t₀ is the retained positive
mixture atom. Let its original date be t₀^k and its old quantile
interval have right endpoint b_k→b. These intervals have positive
limiting length because one nonexceptional owner has positive mass
at t₀. The event “strictly after t₀^k, including original Never”
is exactly the old-chart region u>b_k. Write e_k for its m-marginal
mass. The bounded old densities and convergence of the retained
interval give e_k→e>0. For large k, e_k≥e/2. The literal law

    p_m^{k,λ}=(1−λ_m)p_m^k+
                λ_m·p_m^k(· | original clock>t₀^k)               (LC5)

is an actual probability even for negative λ_m in the chosen box:
its two multipliers are positive. Its old-chart density is

    r_m^{k,λ}(u)=r_m^k(u)·[(1−λ_m)+
                              (λ_m/e_k)1_{u>b_k}].               (LC6)

The indicators converge in L¹ to 1_{u>b}; the bracket multipliers
are uniformly bounded. Testing (LC6) against any L¹ function proves
weak-* convergence to its displayed limiting density: the moving
indicator error vanishes by absolute continuity of its test integral,
and the fixed multiplier uses original weak-* convergence. The
nonexceptional signed atom reweightings use the direct UA old-chart
formula. No new atom, calendar refinement, or clock consolidation
is introduced. All modified densities stay nonnegative and uniformly
bounded, so the original product-rectangle and moving-response-kernel
arguments give complete payoff and cap convergence.

Original q_i(c)=0 remains true for every changed law: all targets are
existing finite atoms or conditional old mass. Thus the late c⁺ test
has exactly the c response value, including the original Never
event. ALL actual finite tests are accounted for. The true global
floor therefore applies to these signed changes on a TWO-SIDED box.

### LC4. First polynomial endpoint and exclusion of later own mass

With all displayed responses fixed there,

    D(q^λ)=F(λ)=∑_i[V_i(τ_i,q_{−i}^λ)−U_i(q^λ)].                (LC7)

F is multiaffine in the four law-mixture parameters. True global
minimality gives F(λ)≥F(0)=δ on an open box. The multiaffine interior-
minimum argument from UA forces F to be algebraically constant:
the first nonzero homogeneous squarefree term would have zero sign-
cube mean and a negative direction. This remains valid if one
parameter is redundant (e=1).

Algebraically set every parameter to one. Nonexceptional players
now prescribe δ_(τ_j), so their displayed response payoff equals
their prescribed payoff. Owner m prescribes ν, wholly STRICTLY
after t₀. The earliest opponents stop surely at t₀, and m's displayed
response τ_m also lies after t₀. Both therefore receive the same
passive payoff. Every summand of (LC7) is zero. Thus F(1,1,1,1)=0,
contradicting constant δ>0. This is the actual signed global-minimum
contradiction for e>0. As in UA, the endpoint evaluation does NOT
identify actual endpoint caps; only a sufficiently small negative
polynomial direction has to be transported to actual finite witnesses.

### LC5. The surviving sure-clock geometry and exact grand withdrawal

Hence q_m stops no later than t₀ almost surely. If some τ_j>t₀,
opponent m has surely stopped before j's response; responding at
τ_j or Never gives identical payoff. This contradicts UNIQUE point
maximization. Therefore all three τ_j=t₀. If q_m({t₀})=0, m stops
strictly before t₀ almost surely and the same equality contradicts
unique maximization at t₀ for each other player. Thus q_m({t₀})>0.

Now ALL owners have positive prescribed mass at t₀. Reweight every
old law, including m's, toward δ_(t₀) with both signs. Nonexceptional
caps stay fixed by isolation; the exceptional later cap stays fixed
by the exact rescaling LC3, since all opponent targets are t₀<τ_m.
Actual signed transport is exactly the retained-atom UA transport.
The new selected-response polynomial is again constant δ.

At its all-one endpoint, all four prescribed clocks are t₀. For
every j≠m the displayed response t₀ is the prescribed action, giving
zero selected-response debt. The exceptional response is later,
so its payoff is r_m(I∖{m}), while prescribed payoff is r_m(I).
The constant polynomial identity gives the final equality in (LC2).

This is a universal SOURCE restriction, not a favorable-minimizer
selection or root-level Nash conclusion. The remaining last-sure
geometry can have a genuine local/operation-only barrier, so no
infinitesimal descent or actual pure-grand minimum is inferred. The
next question is whether finite-amplitude changes of that sure owner's
OLD finite mass and the three common-cap laws consume this remaining
case; its pure-grand polynomial endpoint alone cannot do so.

### LC6. Further selected-response identities, including earlier own mass

The constant polynomial from LC5 can be evaluated with any subset of
the four reweighting parameters equal to one. This is an algebraic
identity of the displayed responses, NOT a claim that these endpoints
still have those actual caps or minimize actual debt. Let

    a_m=q_m({t₀})>0,       e_m⁻=q_m({t<t₀})=1−a_m.

Set the three nonexceptional parameters to one and leave m's parameter
zero. If m stops at t₀, the selected-response debt is the withdrawal
gap δ. If m stops earlier, its prescribed payoff is s_m and its late
response gets r_m(I\{m}); every other owner prescribes its displayed
response t₀ and contributes zero. Therefore

    δ=a_mδ+e_m⁻[r_m(I\{m})−s_m].                   (LC8)

Combined with δ=r_m(I\{m})−r_m(I), this proves the exact implication

    e_m⁻>0  ⇒  r_m(I)=s_m.                         (LC9)

This is the additional consequence independently checked by NOETHER.
It does not hold merely from a local debt minimum or the source's
coordinate margin. It uses the constant two-sided selected-response
polynomial. If e_m⁻=0, no equality to s_m is inferred.

For completeness, fix a nonexceptional owner i and let
e_i⁻,a_i,e_i⁺ be its probabilities of stopping before, at, or after
t₀, with Never included in the last event. Set every OTHER law,
including m's, to the pure clock t₀ and leave i's original law.
Writing J=I\{m,i}, the same polynomial gives

    δ=a_iδ+e_i⁻[r_i(I)−s_i]
       +e_i⁺[r_m(J)−r_m(I\{i})
                         +r_i(I)−r_i(I\{i})].     (LC10)

The early case makes i prescribe its singleton but display a grand
response. The late case makes m display the passive payoff from J,
while m and i's prescribed values come from I\{i}; i's displayed
response joins the grand coalition. This explicitly retains both
changed owners in the endpoint ledger.

### LC7. Singleton-pressure containment is automatic on this residual

Let μ({i}) be the prescribed probability that i is the first SOLO
quitter. For the chosen unique cap response τ_i, let θ_i be its
probability of quitting SOLO against the three unchanged opponent
laws; Never has θ_i=0. The LC residual satisfies, pointwise,

    θ_j=0 for every j≠m,
    θ_m≤μ({m})≤∑_i μ({i}).                        (LC11)

For j≠m the displayed response is t₀. Its opponent m stops no later
than t₀ surely, so j can never quit alone at that response. If τ_m
is finite, its solo-response event requires all three opponents to
stop strictly after τ_m>t₀. On that SAME opponent event the prescribed
m clock is at most t₀ surely, hence m is the actual first solo
quitter. Independence permits the event containment without any
new profile, response coupling, or temporalization assumption. If
τ_m=Never, its θ_m is already zero.

Consequently the extra selected-family singleton-pressure inequality
∑_i θ_i≤∑_i μ({i}), obtained on MORSE's worst-table line, does not by
itself dispatch this geometry: it already holds by literal event
inclusion. This is not a contradiction from combining two necessary
conditions. The containment was sent to MORSE and the coordinator;
the open problem remains a full-cap finite-amplitude repair.

### LC8. Actual global tail graft forces the exceptional punishment value

Status: complete ordinary-mathematical derivation from the same LC
source, not independently reviewed and not a UE consumer. This is a
GLOBAL law replacement, not an assumed minimum-tail property of the
first-collision row. It concerns the counterfactual opponent tail seen
when m delays; actual prescribed play has already stopped by t₀.

Let C=I\{m}. Define

    b=b_m(q),
    H=max_{t∈T, t≤t₀}V_m(t,q_{−m}),
    α=∏_{j∈C}q_j(clock>t₀),
    A=E[r_m(S_first(opponents)); first opponent stop≤t₀],
    P=inf_w cap_m(w).

The infimum defining P ranges over ALL actual independent behavioral
opponent plans, equivalently complete stopping laws on ℕ⊔Never. Own
m's strategy is overwritten by each response. Thus P is the actual
unrestricted punishment value, not a child equilibrium value or a
finite-response value. All-Never contributes zero in the definition
of A; its first-stop event here is finite. Never is included in α.

The unique maximizing response τ_m>t₀ gives H<b. Also α>0. If α=0,
all opponents have stopped by t₀ surely, so every later response equals
Never. A finite τ_m then ties Never; a Never τ_m ties the distinct
finite c>t₀. Both violate uniqueness. Let z be the limiting full cap
of the opponents' original conditional laws strictly after t₀. The
literal head/tail response decomposition, justified below, gives

    b=A+αz,        z=(b−A)/α.

Claim:

    z=P,           b=A+αP.                       (LC12)

No assertion of attainment by a stationary plan is made. The source's
original marked conditional tail does attain this scalar value in
the payoff/cap closure, which is what (LC12) says.

#### Literal finite-witness seam

Use the ORIGINAL finite minimizing sequence pᵏ. The retained positive
mixture atom t₀ has an original date a_k=t₀^k. Let

    η_k=p_mᵏ(clock>a_k),
    l_j^k=p_jᵏ(clock>a_k),
    α_k=∏_{j∈C}l_j^k,
    A_k=E[r_m(first opponent coalition); first opponent stop≤a_k],
    H_k=max_{0≤t≤a_k}V_m(t,p_{−m}ᵏ).

The same retained-interval cutoff as LC3 proves η_k→0 and
l_j^k→q_j(clock>t₀), hence α_k→α>0. The original complete-test kernel
convergence gives A_k→A and H_k→H. The H_k restriction does not lose
moving empty tests: the positive-length retained interval separates
the finite dates at or before a_k from those strictly after it in
the old chart. All original tests on the early side have limits in
T≤t₀; all such limiting tests have original witnesses on that side.

Let w be ANY actual independent opponent-tail law with full m-cap
κ. Replace ONLY p_jᵏ's conditional mass strictly after a_k, for each
j∈C, by w_j shifted to begin at a_k+1. Keep its entire earlier law
and its late probability l_j^k. Keep p_mᵏ unchanged. Write pᵏ[w]
for this actual independent profile. This is legal finite-amplitude
replacement, with no external randomization or inferred tail Nash.

For prescribed play, couple the unchanged heads and m's old clock.
If m≤a_k, every changed opponent clock is strictly later than an
already terminating m clock unless an unchanged opponent head stops
still earlier. The prescribed first coalition is unchanged. Hence
EVERY coordinate's payoff changes by at most 2Mη_k.

For a response of j≠m, the unchanged opponent m is still sure-early
except on an event of probability η_k. On that event only can its
response payoff depend on the grafted tails. The bound 2Mη_k is
UNIFORM over all its finite clocks and Never. Consequently its FULL
cap changes by at most 2Mη_k as well. This explicitly retains the
prelimit late leakage of m; it is not treated as literally zero.

For owner m itself the own law is overwritten. Responses at or before
a_k are exactly unchanged. Every response strictly after a_k has
payoff A_k+α_k times its corresponding full response against w.
All relative finite clocks and Never are available, so EXACTLY

    B_m(pᵏ[w])=max(H_k,A_k+α_kκ).                 (LC13)

The accounting error outside this one cap is at most 14Mη_k in the
SUM debt: four prescribed-payoff errors and three other-cap errors.
Thus all terms used in the global comparison converge with no
unpaid observer cap or late finite response.

#### Taking the infimum without assuming attainment

Apply the same literal decomposition to the ORIGINAL post-a_k
conditional opponent law. Its complete cap κ_k is at least P, and

    B_m(pᵏ)=max(H_k,A_k+α_kκ_k).

Since B_m(pᵏ)→b>H and α_k→α>0, necessarily
κ_k→z=(b−A)/α. Therefore P≤z.

Conversely, for every ε>0 choose an ACTUAL opponent plan w with
κ<P+ε. Use it in (LC13). Since pᵏ[w] is in the unrestricted domain,
true global minimality and η_k→0 give

    b≤max(H,A+ακ)≤max(H,A+α(P+ε)).

Let ε decrease to zero. H<b forces b≤A+αP, so z≤P. This proves
(LC12). No derivative of an outer infimum, no compact attainment,
and no favorable maximizing selector is used.

If the initial infimum is taken over finite laws, choose w finite
by censoring a near-punishment law. The named checked cap stability
`abs_replacementCap_censorLateFiniteStoppingLaws_sub_le` and payoff
stability `abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le` in
`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`
show that all coordinate caps/payoffs converge under this operation.
Together with `exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`,
this aligns the finite-law and all-behavioral SUM infima. The former
declaration bounds each cap, not merely maximum exploitability; the
sum comparison uses those individual bounds. The actual witnesses
may therefore all be chosen finite while retaining unrestricted caps.

The exact checked scalar producer
`quittingPunishmentValue_eq_stationaryPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` lets w instead
be a constant-row opponent plan with cap within ε of P, followed
by the same finite censor. Its adjacent declaration
`quittingPunishmentValue_le_max_solo` gives P≤max(s_m,0); all-player
punishment normality, when independently supplied by the no-UE
Fin4 reduction, strengthens this to P≤s_m. Neither infimum is
asserted attained in that file. No extra sign hypothesis is used
in the graft proof itself.

### LC9. What the global graft does and does not supply

Choose finite ε-near-punishment tails and diagonal original indices.
The graft then approaches EXACTLY the source's original payoff/full-
cap vector: its m-cap tends to A+αP=b, the other cap changes vanish,
and all prescribed-payoff changes vanish. Thus one may change the
ENTIRE unreachable post-t₀ opponent behavior while staying arbitrarily
close to the genuine minimum in debt and payoff/cap coordinates.
This is an actual source-preserving modification, not a certificate
requiring unknown minimizing-tail data. If a repeated stationary
near-punishment plan is chosen, its finite realization retains all
finite responses and Never. No claim is made that a single stationary
tail attains P, has the original unique selector, or is child Nash.

I read `questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md` and the
deletion setup in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`.
That question requires a compiler relating separately selected proper-
face equilibria. LC12 supplies only a scalar m-punishment optimum on
ONE counterfactual face. Its three players' incentives are invisible
to prescribed play precisely because m is sure-early. They have not
become equilibrium incentives of a child game. The quiet-lift source
preserves surviving players' payoffs and full deviations, but does
not force the outsider cap to equal its minimum over all opponent
plans. No child selector is silently attached to (LC12).

A minimal exact failed implication makes this separation unavoidable.
Consider two players m,j with complete reward vectors in that order:

    r({m})=(0,0),       r({j})=(1,1),       r({m,j})=(2,1).

Player m's punishment value is 0: opponent j Never gives every
m response payoff0, and all m rewards are nonnegative. The one-player
child obtained by deleting m has singleton payoff1. Any terminal
ε-Nash child law with 0<ε<1 stops finitely with probability at least
1−ε, because pure finite Quit yields1. Against that law m's Never
response already pays at least1−ε. Hence NO ε-Nash child tail can
have m-cap within ε of P=0 for ε<1/2. Punishment-optimal opponent
behavior and even approximate child Nash are genuinely different
selection tasks. The parent table itself has a pure joint-Quit Nash
profile, so this is only a falsifier of the proposed splice, not a
positive-gap example or a counterexample to LC12 under its source
hypotheses. It is not a new optimization trap.

Thus the attempted next step “graft a child equilibrium which also
punishes m optimally” is retired. Any use of smaller-game existence
must PAY the difference of its outsider cap from P and the observer
caps created when releasing m's existing finite mass. LC12 does not
provide that price. The live next question is a coupled finite-
amplitude release whose summed unrestricted-cap ledger pays this
scalar difference, or a different global comparison consuming the
earliest unsupported cap geometry. No supplied-tail interface or
uniform-equilibrium assertion is proposed.

### LC10. Coupled early/late old laws exclude earlier exceptional mass

Status: COMPLETE ordinary-mathematical strict source-restriction proof,
not independently reviewed and not a UE producer. It uses the GLOBAL
punishment equality LC12, not a new supplied tail condition. Assume
the LC source and e_m⁻=q_m(clock<t₀)>0. Every opponent has late mass
l_j=q_j(clock>t₀)>0 because α>0 in LC8. Let

    ν_m⁻=q_m(·|clock<t₀),
    ν_j⁺=q_j(·|clock>t₀),       j≠m,
    q_m^λ=(1−λ_m)q_m+λ_mν_m⁻,
    q_j^λ=(1−λ_j)q_j+λ_jν_j⁺.                    (LC14)

ALL four variations are legal on a TWO-SIDED open parameter box.
For a conditional event of probability e>0, their two likelihood
multipliers are 1−λ outside it and 1+λ(1/e−1) inside it; the same
small signed bounds as LC3 keep both positive. Own m's earlier
conditional law is finite surely, never containing Never or t₀.
The other conditional laws include their original Never probabilities.

#### Complete cap stability, not only a selected response lower bound

For every j≠m put E_j=q_j restricted to clocks≤t₀ and
c_j(λ_j)=1+λ_j(1/l_j−1). Then

    q_j^λ=c_j(λ_j)q_j−(λ_j/l_j)E_j.

For ANY m-response t>t₀, every non-original opponent-product term
contains a finite clock at or before t₀. It absorbs before t, making
that term independent of t, including t=Never. Hence EXACTLY

    V_m(t,q_{−m}^λ)=k(λ)V_m(t,q_{−m})+C(λ),
    k(λ)=∏_{j≠m}c_j(λ_j)>0,      t>t₀.           (LC15)

This preserves the unique later maximizing point over the ENTIRE
late region, even if it is nonisolated or is Never. The earlier
compact region T≤t₀ has strict gap H<b_m, preserved by uniform
total-variation control. The own m variation does not change its
response values. Each other owner's unique cap t₀ is an isolated
retained midpoint, so its uniform complement gap survives ALL four
signed changes. Therefore all four FULL caps stay at their original
displayed response points on a common two-sided box.

#### Direct signed transport of BOTH original cutoff sides

In the original minimizing sequence let the t₀ atom's retained
quantile interval be (d_k,b_k), with d_k→d and b_k→b and b>d.
Strictly BEFORE its original date a_k corresponds to u<d_k;
strictly AFTER it, including Never, corresponds to u>b_k.
The limiting m early probability e_k⁻ tends to e_m⁻>0, and each
j late probability l_j^k tends to l_j>0. Define literal actual laws

    p_m^{k,λ}=(1−λ_m)p_mᵏ
                      +λ_m p_mᵏ(·|clock<a_k),
    p_j^{k,λ}=(1−λ_j)p_jᵏ
                      +λ_j p_jᵏ(·|clock>a_k),    j≠m.

For large k the same signed parameter box makes these probabilities.
Their old-chart densities are r_m^k times

    (1−λ_m)+(λ_m/e_k⁻)1_(u<d_k),

and r_j^k times

    (1−λ_j)+(λ_j/l_j^k)1_(u>b_k), respectively.

Both moving indicators converge strongly in L¹. All multipliers and
densities are uniformly bounded and nonnegative. For every L¹ test
function, absolute continuity removes the moving-cut error, after
which original weak-* convergence applies. The rectangle-product
and unchanged outcome/moving-response kernel arguments give all
prescribed-payoff and unrestricted-cap limits. These are original
finite independent laws, with negative coefficients justified directly,
not by the frozen nonnegative-mixture declaration. All changed laws
retain zero c mass; c⁺ still duplicates c, and Never remains separate.
Thus the true δ floor applies on the full signed box.

#### Constant polynomial and its exact endpoint

The selected-response sum F(λ)=D(q^λ) on that box is multiaffine.
True globality forces F constant δ. At the algebraic all-one endpoint,
m prescribes a finite clock STRICTLY before t₀, and every opponent
prescribes a clock STRICTLY after t₀. Prescribed absorption is m's
singleton, so U_m=s_m and U_j=r_j({m}). Each j's displayed response
t₀ also follows m's sure earlier singleton, and its selected debt
is zero. The m displayed response τ_m>t₀ faces the original joint
conditional opponent tail. Its value is z=P_m by LC12: originally
the same response gave b_m=A+αz and was a full maximizer. Therefore

    δ=F(1,1,1,1)=P_m−s_m.                       (LC16)

No actual cap at this distant endpoint is claimed. In particular an
earlier m response could now pay s_m rather than P_m; that does NOT
affect the selected polynomial evaluation or the local contradiction.

This proves the sign-free implication e_m⁻>0 ⇒ P_m>s_m at a positive
LC source: its exceptional player would be punishment-ABNORMAL.
For genuine Fin4 no-UE data that possibility is excluded by the
CHECKED same-table reduction, not by a guessed reward sign. I inspected
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`
and `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
The latter's `all_punishmentNormal` field means EXACTLY P_i≤s_i,
as defined by `IsQuittingNormalPlayer` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.
Finite-law/all-behavioral infima are aligned by LC8's individual
cap-censor comparison. Hence LC16 contradicts δ>0 and proves

    q_m=δ_(t₀)                                  (LC17)

for EVERY surviving LC source of a hypothetical Fin4 counterexample.
The earlier-mass equality r_m(I)=s_m is retained in LC6 but is not
needed to infer LC17. This is a strict genuine-source exclusion,
not Nash of the other three conditional tails or a full consumer.

### LC11. An actual finite-amplitude path reaches a multiple-cap minimum

The following is an EXISTENTIAL minimum reselection, not a pointwise
exclusion of every LC source. Start from any LC source, before or
after LC17, and use the legal forward OLD-atom path

    q_i^x=(1−x)q_i+xδ_(t₀),       0≤x≤1.

Its selected-response polynomial is identically δ by LC5, although
its actual full caps need not stay selected all the way. Every point
has actual finite realization on the retained old t₀ intervals;
the forward coefficients are probabilities and all modified densities
are bounded. All q_i^x(c)=0, so c⁺ still adds only the existing c value.
The produced marked response functions and their compact full caps
depend UNIFORMLY continuously on x by total variation.

Let Z be the closed set of x where all four original displayed
responses remain full maximizers. It contains an initial interval.
On Z the actual full debt is δ, because the selected polynomial is
δ and now its responses ARE full maximizers. Let x* be the end of
its maximal initial interval. If x*<1 and all caps were still unique
there, the three t₀ selectors would have their isolated-point uniform
gaps. For m, the ordered old-atom expansion above t₀ has positive
coefficient (1−x*)³; its unique late selector and the compact earlier
gap would likewise persist in a neighborhood of x*. That would
contradict maximality. Thus some cap has at least two maximizing
POINTS at a genuine actual global minimum q^{x*}.

If x*=1, the endpoint still has the selected responses as full caps
by closedness. All prescribed laws are pure t₀. Owner m's selected
late response is r_m(I\{m}), and BOTH the distinct finite c>t₀ and
Never have that same passive value. They are therefore two genuine
maximizing POINTS. This again gives a marked global minimum with
multiple cap maximizers. No actual cap claim at x=1 is made unless
x=1 belongs to Z; that condition is exactly the distinction required
for this argument.

Consequently an LC minimum can be moved by a finite-amplitude change
of EXISTING finite mass to a genuine multiple-cap minimum, with no
increase of debt along the initial path. It does NOT give debt below
δ, and it does NOT say every minimum already has multiple caps. The
new proof must consume that multiple-cap geometry, not suppress it
through a favorable selector or treat the selected-grand identity as
an actual equilibrium. The zero-own-mass EARLIEST-cap alternative
from NOETHER's SLC10–SLC12 remains a different unresolved branch.

### LC12. Own-law path bypasses a nonisolated earliest-cap obstruction

Status: complete ordinary-mathematical EXISTENTIAL minimum reselection,
unreviewed. It is not a pointwise unsupported-cap exclusion or a full
UE consumer. The unsupported earliest cap itself need NOT be isolated.
This is different from stabilizing it under changes of its opponents:
only its OWN law changes, so its entire full-cap function is unchanged.

Let q be the same produced global minimum δ>0, with all four caps
unique. Suppose one owner m has zero own mass at its EARLIEST cap
τ_m, and the other three have supported cap clocks τ_j>τ_m. Put
t₀=min_{j≠m}τ_j and suppose

    e=q_m(clock<t₀)>0.

Condition only m's old law on this event, calling it ν, and follow
the literal old-law path

    q_m^x=(1−x)q_m+xν,       0≤x≤1,
    q_j^x=q_j,              j≠m.                 (LC18)

The same change is legal on a two-sided open interval near x=0:
its likelihood multipliers are 1−x and 1+x(1/e−1). All three
non-m caps are unique supported points, hence isolated and uniformly
gapped. They remain fixed locally by total-variation control. The
whole m cap function and its unique maximizer remain EXACTLY fixed
for every x, including a nonisolated τ_m, because its opponents
never change. Thus the selected sum

    F(x)=b_m(q)+Σ_{j≠m}V_j(τ_j,q_{−j}^x)−Σ_iU_i(q^x)

is affine, equals the actual full debt near zero, and has an interior
minimum there. It follows that F(x)≡δ algebraically on the entire
path. Actual full debt is not asserted equal to F outside that
initial stable region.

Literal finite realization: if t₀ is finite, it is a positive retained
mixture atom because some j owns mass at its supported cap there.
Condition p_mᵏ on clock BEFORE the corresponding original date; its
old-chart indicator lies before the converging LEFT endpoint. If
t₀=Never, condition on the original finite-clock region before c_k;
its endpoint tends to c and its m mass tends to e. The same L¹
indicator/weak-* bounded-density argument as LC10 applies. Negative
x near zero is justified by direct likelihood positivity. Forward
0≤x≤1 needs no extrapolated probability. All modified laws retain
zero c mass; every actual moving response and original Never remains
priced. The complete payoffs/caps along (LC18) belong to the actual
carrier and vary continuously in x by uniform total-variation bounds.

Let x* end the maximal initial interval where the three displayed
non-m responses are still complete maximizers. Throughout that
interval D(q^x)=δ. If x*<1, uniqueness of ALL three supported cap
points at x* would give complement gaps and an extension beyond x*.
Hence some non-m cap has at least two maximizing POINTS at the
actual global minimum q^{x*}. No gap for τ_m is used in this step.

If x*=1, m now stops STRICTLY before every other displayed cap surely.
For any finite τ_j, that response and Never give the same payoff;
if τ_j=Never, its payoff equals that at finite c because m stops
strictly below c surely. The relevant selected responses really are
full maximizers at x=1 by closedness. Thus again another cap has
multiple maximizing POINTS at a genuine global minimum.

Therefore an earliest unsupported owner with any old mass before
the first supported opponent cap can be moved to a multiple-cap
minimum even when its own unique maximizer is NONISOLATED. This is
not NOETHER's stronger isolated-cap pointwise contradiction: here
we select another actual minimum, and the old unique-cap source may
still exist. If e=0, the earlier-law direction does not exist and
the argument says nothing. Nor does it cover several unsupported
opponent caps, whose own maximizers may move without a uniform gap.

The immediate full-goal target is now the multiple-cap minimum reached
by LC11 or LC12. A proof must handle simultaneous ACTIVE responses
and upper-bound their cap changes; choosing one branch and reusing
the interior multiaffine argument would discard the very boundary
price that these finite-amplitude paths expose. No further density,
entropy, or fixed-child Nash approximation is being proposed.

## Endogenous sharing loses the independent payoff carrier

Status: exact mechanism falsifier, ordinary mathematics. This changes
the attempted general discontinuous-game existence route; it is NOT a
counterexample to UE or a source exclusion inside δ>0. The example is
solved by actual all-Never. It falsifies even PAYOFF realization of an
allowed endogenous-sharing equilibrium, before unrestricted cap
transport is attempted. No further sharing-rule interface is proposed.

### ES1. The literature theorem actually inspected

The original Simon–Zame working paper is available as the scanned
Berkeley paper [Discontinuous Games and Endogenous Sharing Rules](https://escholarship.org/content/qt8n46v2wv/qt8n46v2wv.pdf)
(1987; published in Econometrica, 1990). Its scan was not successfully
extracted here, so no exact assertion is attributed to an unread
theorem in it. The independently authored primary source actually read
is Erik Balder, [An equilibrium closure result for discontinuous games](https://webspace.science.uu.nl/~balde101/baet11.pdf),
Economic Theory 48 (2011), Theorems 1 and 2 and Section 4.1.

Balder's Theorem 2 assumes compact metric action spaces and an upper
semicontinuous nonempty compact convex-valued payoff correspondence.
It produces a bounded measurable selection of that correspondence
and an independent mixed Nash equilibrium for the SELECTED payoff
function. Section 4.1 permits the correspondence obtained by taking
the convex hull of each fiber of the closed original payoff graph.
Theorem 1 retains a sequence's equilibrium payoffs and relates the
selected payoff graph to limiting graphs, but it does not identify
the selected payoff with the original literal collision payoff.

Narrow Lean lookup found no Simon–Zame declaration in the toolkit or
paper filenames. Two nearby actual-law facts were inspected instead:
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`
requires a ONE-coordinate endpoint that is ALREADY another true
minimum; it gives coordinate debt affinity, not an endogenous-sharing
producer. `QuittingCapBandFiniteCut` and
`QuittingCapBandFiniteCut.target_terminalSemanticDebt_le`
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`
move a supplied actual law's bad mass to an actual near-cap receiver.
They do not synthesize jointly independent laws from a convexified
coalition lottery. No Lean result is asserted for ES2–ES5.

### ES2. Complete Fin4 table and legal compact strategy topology

Let I={0,1,2,3} and specify ALL sixty reward coordinates by

    r_i(S)=1 if |S|=3 and i∈S; otherwise r_i(S)=0.

Never pays zero. In the literal terminal game each player chooses
an independent complete stopping law on X=ℕ⊔{Never}. Endow X with
the one-point compactification topology: each finite clock is
isolated, and finite clocks tending to infinity converge to Never.
This is a compact metric pure-strategy space. The pure payoff map
u:X⁴→[0,1]⁴ is continuous everywhere except possibly the all-Never
point n. Indeed, if a profile has a finite first clock, then in a
neighborhood all coordinates at or before that clock are fixed and
every other coordinate remains strictly later, so its first coalition
is unchanged.

For every a∈I, let three clocks in I\{a} equal k and let a's clock
equal k+1. These pure profiles converge to n and their payoff vector
is v^a, which has coordinate a zero and each other coordinate one.
Thus the closed payoff graph at n contains 0 and all four v^a. Its
convex hull contains

    v=(v^0+v^1+v^2+v^3)/4=(3/4,3/4,3/4,3/4).

Define the bounded measurable selection u* to equal literal u at
every profile except n, and set u*(n)=v. It belongs pointwise to
the convexified closed payoff graph. The pure all-Never profile is
an exact Nash equilibrium for u*: changing one's own clock to ANY
finite date yields a singleton, hence own payoff zero, while Never
yields 3/4. All unilateral mixed deviations are averages of these
pure payoffs. This is precisely the independent-mixed equilibrium
notion allowed by the inspected theorem; no public correlation is
needed to make it an equilibrium of the MODIFIED payoff function.

### ES3. Its equilibrium payoff is outside every actual product-law closure

For an arbitrary actual independent profile, finite or infinite
support, let t_a be the probability of first coalition I\{a}, let
T=Σ_a t_a, and let e=1−T count ALL other outcomes, including Never.
The displayed table gives the exact identity

    U_i=T−t_i,       Σ_i U_i=3T.

Consequently any sequence with U→v would have T→1, e→0 and every
t_a→1/4. This is impossible for independent clocks. The following
simple ordered-two-copy proof suffices; the stronger sharp inequality
retained in NOETHER's TC2–TC3 also implies it.

Fix distinct a,b and write I={a,b,c,d}. Sample two independent
copies X,Y of the entire product profile. On the event that X first
realizes I\{a} at u and Y first realizes I\{b} at w, split into the
three cases u<w, u>w, u=w. Swapping the two copies' c coordinates
is a measure-preserving involution because they have the same
marginal law. In the first case it changes the ordered first outcomes
to ({b,d},{c}); in the second to ({c},{a,d}). Each event therefore has
probability at most e, since its indicated singleton has probability
at most e in the appropriate copy. In the equal-time case, swap the
b coordinates instead. The ordered outcomes become ({c,d},I), so
this event too has probability at most e. No bounded date, finite
support, or no-Never hypothesis is used: the omitted coordinate is
strictly later than a finite first clock, with Never allowed there.
Adding the three disjoint DOMAIN cases gives

    t_a t_b≤3e.

The argument does not demand injectivity BETWEEN its three images,
because each case is bounded separately and only their domain
probabilities are added. The exact inequality passes to payoff/law
closure. In the alleged limit it would give 1/16≤0. Therefore v is
not even in the closure of the literal prescribed payoff vectors,
and a fortiori not in the closure of actual payoff/FULL-cap pairs.

### ES4. What is falsified, and what survives

The false implication is: an independent mixed equilibrium of a
measurable selection of the convexified closed payoff graph has an
actual independent stopping-law approximation preserving its payoff,
and hence can supply terminal approximate Nash of the original game.
The selection above has an exact equilibrium payoff not approximable
by ANY actual profile, regardless of its debts. This is stronger
than merely noticing that a particular pure collision reward changed.

The convexified all-Never fiber silently admits a correlated lottery
on the four triple omissions. Actual quitting laws have independent
private clock randomization and a deterministic all-Continue public
history before absorption. The omitted-player correlation is not an
available public device. Matching its four payoff coordinates in
this table forces that forbidden outcome lottery, so it cannot be
hidden by a different independent payoff realization.

This does NOT refute existence of a FAVORABLE endogenous-sharing
equilibrium selection with an actual adapter. For this table the
literal all-Never payoff zero itself is an actual exact equilibrium.
Nor does it refute the literature theorem, whose payoff indeterminacy
is explicit. It retires the general theorem as a black-box producer
from the closed payoff graph: an additional independent-law and
all-response realization theorem would be genuinely load-bearing,
not a continuity detail. No such theorem has been supplied.

### ES5. Direction after the falsifier

The multiple-cap boundary must be analyzed inside the actual complete
product-law carrier, not its convexified payoff graph. The surviving
useful facts are literal coordinate convexity of total debt and
debt-vector affinity on ONE-coordinate chords whose two endpoints
are already minima. The next question is whether a true minimum's
simultaneously active response branches force an actual
minimum-preserving law extension or a lower-debt product profile.
Neither endogenous payoff choices nor the previously retired
atomless density controls may supply that missing global step.

## Earliest active zero-mixture cap: simultaneous conditioning exclusion

Status: COMPLETE ordinary-mathematical candidate, independently passed
by NOETHER for EA1–EA5 and exact boundary EA6 in the existing feedback.
It is a
genuine positive-global-minimum restriction, not a supplied local
interface. It handles ALL simultaneously active cap responses rather
than assuming four unique caps. It strengthens the common-zero-cap
consumer by retaining distinct later cap maximizers. No UE theorem
or export is claimed.

### EA1. Exact statement on the produced source

Use the actual marked source X=T⊔{Never}, original finite sequence
and bounded signed reward table from UA, LC and ES above. Let

    A_i={t∈X: V_i(t,q_-i)=B_i(q)},
    τ=min(⋃_i A_i),       μ=Σ_i q_i/4.

Each A_i is nonempty compact because the COMPLETE response function
is continuous on compact X. The minimum is in the ordered compact
finite calendar, unless it is Never. Suppose τ is FINITE and

    μ({τ})=0,       e_i=q_i(clock>τ)>0 for ALL i.       (EA1)

Claim: these hypotheses are IMPOSSIBLE at δ=Δ(r)>0. No uniqueness,
own cap support, punishment normality, root Nash, minimal conditional
tail or response attainment among original ℕ deadlines is assumed.
The displayed compact cap attainment is produced, not posited for
the original countable clocks.

Consequently, at any positive produced minimum with a finite earliest
active zero-mixture point, SOME owner stops STRICTLY before τ surely.
For all three OTHER owners, τ, finite c and Never are full maximizing
points; if τ=c there are two distinct points, otherwise three. In
particular a source with ALL FOUR caps unique CANNOT have a
zero-mixture earliest cap, including the nonisolated residual of the
reviewed worst-SUM source reduction.

### EA2. Why the signed variation preserves every active branch

If τ is the first finite tester, q_i({τ})=0 and the supports of all
opponents are after τ, so every V_i(τ)=s_i. For an owner m with
τ∈A_m, the checked global minimum margin δ≤B_m−s_m immediately
contradicts δ>0. Thus assume there is a finite tester below τ.

Take real ordered cuts u_n<τ increasing to τ and set

    e_i^n=q_i(clock>u_n)≥e_i>0,
    ν_i^n=q_i(·|clock>u_n).

For fixed n independently change each EXISTING complete law by
q_i^λ=(1−λ_i)q_i+λ_iν_i^n. This is legal on an open two-sided
box about zero. Its old likelihood factors are 1−λ_i on clock≤u_n
and c_i=1+λ_i(1/e_i^n−1)>0 on clock>u_n. Equivalently,

    q_i^λ=c_i q_i−(λ_i/e_i^n)E_i^n,
    E_i^n=q_i|_(clock≤u_n).

EVERY nonoriginal term in an opponent product contains an early
finite submeasure E_j^n. For ANY response t>u_n that term has
absorbed before t, so its payoff is independent of t. Therefore,
simultaneously for EVERY recipient and EVERY upper test,

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i(λ)=∏[j≠i]c_j>0,       t>u_n.                (EA2)

Choose a real a_n with u_n<a_n<τ. The compact lower test set
T∩[0,a_n] contains NO maximizing point for ANY owner, because τ
is the earliest point of the UNION of all four active sets. Each
owner has a positive uniform gap on that set. Uniform total-variation
payoff bounds preserve those lower gaps on a smaller signed box.
All A_i lie strictly above a_n, and positive rescaling (EA2) keeps
EVERY original member of A_i tied at the upper cap. Hence ALL full
caps equal k_i B_i+C_i there. Arbitrarily many active points, active
Never, and nonisolated active points cause no branch switch: their
entire upper response family is transformed by the SAME positive
affine map. This is not the false assertion that an arbitrary
selected branch of a changing maximum controls the cap.

Choose once any τ_i∈A_i, with τ_m=τ for one earliest owner m.
All τ_i≥τ. The multiaffine selected sum

    F_n(λ)=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)]

equals ACTUAL debt on this signed box. Literal old-cut transport
below gives F_n≥δ there and F_n(0)=δ, so the sign-cube polynomial
argument gives F_n≡δ. Its distant all-one value is INITIALLY only

    Σ_i[V_i(τ_i,ν_-i^n)−U_i(ν^n)]=δ.               (EA3)

No actual endpoint cap assertion has yet been made.

### EA3. Direct old finite realization, including all moving responses

The needed cut transport is the same proved mechanism as UA's signed
old-law density transport and NOETHER's CC4, not a theorem about
negative convex coefficients. For any fixed cut, the monotone old
chart maps its initial segment to an interval. If a retained atom is
removed, its RIGHT endpoint is the late-conditioning boundary; if
the boundary has zero mixture mass, its raw preimage is null and
old endpoint cuts converge to it. Cuts outside T merely specify the
same initial segment as the corresponding endpoint of the retained
interval or tester gap. These are chronological unions of WHOLE old
atom intervals, not a newly inserted nonisolated clock.

For the corresponding old finite cuts and positive masses e_i^{k,n}
the literal modified probability laws have old-chart densities

    f_i^k[(1−λ_i)+(λ_i/e_i^{k,n})1_(old clock>cut)].

The cut indicators converge in L¹, the normalizers converge to
e_i^n>0, and a small fixed signed box keeps all likelihood factors
nonnegative and bounded. Against any L¹ test the moving-indicator
error is bounded by the integral of its absolute value over a set
of vanishing measure; the remaining fixed multiplier is a weak-*
test. Thus the modified densities converge weak-* on the UNCHANGED
old chart. Independent product tests and the original prescribed
and arbitrary-moving-response kernels give payoff and FULL-cap
convergence. Never is retained and zero c mass remains zero; c⁺
therefore continues to duplicate c. This supplies the actual global
floor for the signed box used in EA2.

Also μ({τ})=0, so all q_i({τ})=0 and ν_i^n→ν_i=q_i(·|clock>τ)
in TOTAL VARIATION. Normalizers remain bounded away from zero.
The final ν has the SAME direct old-cut realization, now using the
null raw boundary at τ; the modified density bound is at most the
old bound divided by min_i e_i. Its complete (U,B) pair belongs to
the ORIGINAL actual carrier. Uniform total-variation response
estimates pass (EA3) to

    Σ_i[V_i(τ_i,ν_-i)−U_i(ν)]=δ.                   (EA4)

This passage does not identify the selected cap with the full cap.
The required identification is proved next.

### EA4. The final conditioned profile has actual full caps

Put E_j=q_j|_(clock<τ). Zero mass at τ ensures
ν_j=(q_j−E_j)/e_j. For EVERY response t≥τ, INCLUDING τ itself,
each nonoriginal term in the opponent expansion has a finite exit
STRICTLY before t. Consequently the SAME constant works on the
entire closed upper response set:

    V_i(t,ν_-i)=k_i V_i(t,q_-i)+C_i,
    k_i=∏[j≠i]e_j⁻¹>0,       t≥τ.                 (EA5)

Since each original τ_i is an actual global maximizer and τ_i≥τ,
positive scaling gives V_i(t,ν_-i)≤V_i(τ_i,ν_-i) for EVERY upper
test. At τ, all conditioned opponents stop strictly later, so
V_i(τ,ν_-i)=s_i; therefore V_i(τ_i,ν_-i)≥s_i. Every finite test
t<τ also has payoff exactly s_i. Never is in the upper set, and
c⁺ duplicates c. Thus the ALL-response upper bound is proved:

    B_i(ν)=V_i(τ_i,ν_-i) for EVERY i,
    B_m(ν)=V_m(τ,ν_-m)=s_m.                         (EA6)

Equations (EA4),(EA6) give ACTUAL D(ν)=δ. Its pair lies in the
original carrier by EA3, so it is another true global minimum.
The checked `minimumTerminalSemantic_singletonMargin` applied to
owner m at this actual pair yields δ≤B_m(ν)−s_m=0, contradiction.
This is the missing global consumer: distinct later caps can be
larger than their singleton levels; only the EARLIEST owner must
have equality. It is unnecessary to assert B_i(ν)=s_i for all i.

### EA5. The sure-early obstruction is an exact output

If (EA1) fails through e_h=0, then q_h(clock≤τ)=1 and zero mixture
mass gives q_h(clock<τ)=1. For any recipient i≠h and EVERY response
t≥τ, that sure early opponent makes the prescribed first coalition
independent of t. Some τ_i∈A_i is ≥τ by the definition of earliest
active point; hence ALL these upper responses are full maximizers.
In particular τ,c,Never are maximizing POINTS for all i≠h. This
does not declare their prescribed laws Nash or permit replacement
of h's complete early law by a pure clock.

If an alleged earliest active point were Never with zero mixture
mass, every law is finite surely and the distinct finite c would
tie each Never cap. That contradicts earliestness directly. Thus
the zero-mixture case never hides an omitted terminal boundary.

More generally, an earliest active Never would force ALL four active
sets to be the singleton {Never}. If some own Never mass were zero,
the other recipients would again have the distinct finite c tied
with Never. If all own Never masses were positive, the reviewed
all-supported unique-cap exclusion UA would apply. Hence the
earliest active point is finite at ANY produced positive minimum,
not only under zero mixture mass.

For four UNIQUE caps, an e_h=0 sure-early owner is impossible since
each of the other three caps would have distinct c and Never
maximizers. Therefore ALL-UNIQUE produced positive minima have a
POSITIVE MIXTURE ATOM at their earliest cap; it is finite and
isolated by the source producer. In particular the sole unsupported
strictly earliest NONISOLATED alternative in the reviewed fresh-table
reduction is excluded if EA1–EA5 survives independent falsification.
This does not exclude a zero-OWN-mass earliest cap at an atom supplied
by some OTHER player's prescribed law, nor multiple-cap sure-early
sources. Those are the genuine remaining branches.

The source lookup for this new implication was narrow: the exact
`minimumTerminalSemantic_singletonMargin` declaration and imports in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
the original carrier definition in `Quitting/Root/TerminalSemanticPair.lean`,
and the stopping-law minimum-fiber declarations identified in ES1.
NOETHER's common-zero proof CC3–CC5 supplies the nearby comparison:
the new point is replacing common cap τ by the EARLIEST member of
the union of ALL active sets, then bounding later caps by (EA5) and
using the singleton equality for only ONE owner. No Lean build ran.

Boundary checks: positivity is indispensable. With all reward entries
zero, actual all-Never has zero debt, zero mixture mass at first finite
tester c=0, all caps are tied there and at Never, and all late masses
are positive. No positive-margin contradiction follows. With the
participant-indicator table and purely atomless finite laws, the
earliest finite cap also has zero mass and singleton equality, but
their large positive debt is NOT the true all-law infimum: all-pure
date-zero play has debt zero. This is the exact existing DR6 guardrail
against replacing global δ by a restricted profile debt.

### EA6. Exact no-strict-late boundary and its collapsing normalizer

This validates the EXCEPTION in EA5; it does not weaken the positive-
global-floor hypothesis or claim another solved-table optimization trap.
Set all own singletons zero. Give recipient i≠0 payoff1 on singleton
{0}, give recipient0 payoff1 on singleton{1}, and set EVERY other
reward coordinate zero. For N≥1 choose player0's uniform law on
{0,…,N−1}, player1's uniform law on {N,…,2N−1}, and players2,3
pure Never. The first outcome is {0} surely, so

    U=(0,1,1,1),       B=(1,1,1,1),       D=1.

For each i≠0 EVERY finite response ≥N and Never gives cap1; before
N the response payoff is the chance that0 has already stopped, and
at its last possible clock the join payoff remains0. Player0's cap1
is achieved by every finite response ≥2N and Never. These exact full
caps include every finite clock, not only the prescribed menu.

The common quantile charts have c=1/2 and limiting finite calendar
T=[0,1/2]. Player0 is uniform on [0,1/4], player1 uniform on
[1/4,1/2], and players2,3 are Never. The earliest active point is
τ=1/4, which is NONISOLATED with zero mixture mass. Player0 stops
STRICTLY before τ surely, so e_0=0. The other three caps have every
point in [τ,c] and Never as maximizers, exactly the EA5 output.

For cuts u_n↑τ, e_0^n remains positive but tends to ZERO. Conditioning
player0 after u_n concentrates its law into the collapsing interval
(u_n,τ), and the likelihood bound1/e_0^n diverges. Its limit would
insert a positive atom at the old NONISOLATED point τ, which is NOT
covered by bounded old-chart transport. Thus the positivity of each
FINAL e_i in EA1 cannot be replaced by positivity at every preceding
cut. The obstruction has exact finite witnesses and is not repaired
by treating a moving cut as an automatically permissible new atom.

The true all-law gap of this table is zero: actual all-Never is exact
Nash since every own singleton is zero. The source values D=1 here
therefore cannot be substituted for δ. This boundary tests both the
several-active-branch cap ledger and the zero-normalizer seam without
claiming a positive-minimum counterexample.

### EA7. Global late-tail graft sharpens the sure-early exception

Status: COMPLETE UNREVIEWED ordinary derivation, separate from the
frozen combined source-reduction artifact and not a dependency of it.
The source assumptions are the same actual produced true minimum,
τ the earliest member of the UNION of all cap-maximizer sets, zero
mixture mass at τ, and the actual Fin4 no-UE punishment normality
P_i≤s_i. EA5 supplies an owner h with q_h(clock<τ)=1.

Claim: τ is a maximizing response for ALL FOUR owners. The three
non-h recipients were already covered by EA5; the new global graft
shows τ also maximizes h's own cap. This is a common ACTIVE point,
not unique caps, not the common-unique finite spectrum, and not UE.

If there are two sure-strictly-early owners, each recipient has one
as an opponent. Every response≥τ then gives that recipient the same
payoff, so the claim is immediate. Assume h is the only such owner.
Thus l_j=q_j(clock>τ)>0 for all j≠h and α=∏[j≠h]l_j>0.
Let A be h's passive payoff ledger on the event some opponent exits
before τ, and let H=max_(t∈T,t≤τ)V_h(t,q_-h). This is attained
on a compact set of finite tests and

    H≥V_h(τ)=A+αs_h.

An arbitrary replacement of ONLY each opponent's old conditional
tail after τ is invisible to EVERY prescribed payoff and EVERY
non-h full-response payoff. Under prescribed h play its sure exit
is before τ. If a non-h pure response is earlier, all changed draws
remain later than that response; if it is≥τ or Never, h has already
exited. Thus no changed tail can affect the first coalition in
either case. This prices unrestricted caps, not merely the displayed
late maximizers.

Literal finite seam: choose original finite reply dates a_k tending
to the zero-mixture τ boundary. Their own and opponent atom masses
there tend to zero. Then η_k=p_h^k(clock>a_k)→0, l_j^k→l_j,
α_k→α, A_k→A, and H_k→H, where H_k is the largest original h
response payoff at finite dates≤a_k. For H_k's upper bound extract
arbitrary moving head-maximizing replies; their limits are≤τ.
For its lower bound approximate every strict earlier tester, and
use reply a_k itself for τ. Null mixture mass prices its vanished
tie and yields V_h(a_k)→V_h(τ). Hence the truncated-head cap limit
does not require isolated τ or a uniform gap below τ.

For ANY actual independent opponent-tail laws w, preserve every old
opponent head and its late probability, replacing its conditional
tail by w shifted to start at a_k+1. Keep h's entire old law.
On the event h≤a_k all prescribed first coalitions and every non-h
deviation outcome remain unchanged by the preceding argument. Thus
all four prescribed payoff errors are≤2Mη_k and every non-h full
cap error is≤2Mη_k, UNIFORMLY over all finite/Never responses.
The total debt error outside h's new cap is≤14Mη_k.

For h, every test≤a_k is unchanged; every later test or Never has
exact payoff A_k+α_k times the corresponding w response. Therefore
its ACTUAL new full cap is exactly

    max(H_k,A_k+α_k cap_h(w)).

Since the literal modified law has D≥δ, taking k→∞ gives

    B_h(q)≤max(H,A+α cap_h(w)) for EVERY actual w.      (EA7)

The true punishment value is the infimum of cap_h(w) over actual
independent opponent laws, without attainment. Normality P_h≤s_h
permits w with cap_h(w)≤s_h+ε. Hence (EA7) gives

    B_h(q)≤max(H,A+α(s_h+ε))≤H+αε.

Let ε↓0. Since B_h≥H, equality follows. The compact H maximum
cannot occur strictly before τ by earliestness of the UNION of
active sets. It therefore occurs at τ, proving τ∈A_h. No old
conditional tail is assumed punishment-optimal, and no child Nash
is inserted. If P_h is unattained or negative, the same finite
ε argument applies; H already includes the solo payoff at τ.

The source of true normality at the SAME reward table is
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`,
whose returned `all_punishmentNormal` field has no reward change.
The literal punishment infimum and the stationary equality are in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`; exact attainment
is NOT inferred. These declarations and the already inspected
stopping-law correspondences were checked narrowly, with no build.

Thus the zero-mixture earliest branch in a hypothetical Fin4
counterexample has a common ACTIVE cap point with no own mass there,
at least one sure-strictly-earlier prescribed owner, and three
recipients with an entire maximizing late plateau. The unique-cap
join/withdrawal spectrum does not consume these MULTIPLE branches.
The next genuine question is an all-response coupled release of
that early owner, not another punishment-optimal child-Nash splice.

## Head concentration globally reselects a multiple-cap minimum

Status: COMPLETE UNREVIEWED ordinary-mathematical candidate HP1–HP6,
separate from the frozen strengthened source-reduction packet. This
is a finite-amplitude actual MINIMUM RESELECTION, not a pointwise
exclusion of all-unique minima, an automatically consumed rank or
UE. Its endpoint alternatives have a full cap ledger; no endpoint
is declared minimizing from a selected polynomial alone.

### HP1. Exact target and supplied source facts

Let q be ANY produced true positive SUM minimum of a bounded signed
Fin4 reward table with same-table true punishment normality P_i≤s_i.
Assume all four caps have UNIQUE maximizing points τ_i and they
are NOT ALL equal. By reviewed EA, their earliest point τ=min_iτ_i
is finite and has positive mixture mass, hence is ISOLATED in T.
The exact target is an ACTUAL profile pair in the same original
carrier with debt δ and some cap having at least two maximizing
TEST POINTS. No proper-game child equilibrium is supplied.

This applies in particular to every all-unique source of the ONE
fresh table produced in the frozen strengthened packet. Its ordinary
proof of non-common unique caps and reviewed EA supply the two
source facts; no old minimizing law is transported across table
variation. True normality holds for that SAME fresh table by the
checked no-UE source used in LC10 and EA7.

### HP2. Concentrate existing HEAD mass, not cap atoms

Put B={i:e_i=q_i(clock≤τ)>0}. This set is nonempty because τ has
positive mixture mass. For i∈B let ν_i=q_i(·|clock≤τ); for i∉B
let ν_i=q_i, a redundant direction. Independently vary

    q_i^λ=(1−λ_i)q_i+λ_iν_i.

For i∈B the head and late likelihood factors are respectively
1+λ_i(1/e_i−1) and 1−λ_i; both are positive on a two-sided box.
Its density is a positive multiple (1−λ_i) of the old law plus
an early signed term (λ_i/e_i)q_i|_(clock≤τ). An e_i=1 direction
is redundant and causes no difficulty. Directions for i∉B are
IDENTICALLY unchanged, not conditioning on a vanishing old event.

Every earliest selector τ is isolated and unique, so it has a
uniform compact-complement gap and stays fixed locally. For any
later selector σ_i=τ_i>τ choose a real a_i with τ<a_i<σ_i; when
σ_i=Never use τ<a_i<c, possible since a positive finite atom lies
strictly before c. For EVERY test t>a_i, expanding its opponent
product gives

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i(λ)=∏[j∈B,j≠i](1−λ_j)>0.                (HP1)

Every nonoriginal term contains a finite head exit≤τ, so C_i is
independent of t, including Never. The lower compact set t≤a_i
excludes the unique σ_i and has a uniform gap. Thus ALL later
caps stay fixed locally, even at nonisolated points. This is a
whole-upper-family identity, not uniqueness-as-uniform-gap.

The selected sum F(λ)=Σ_i[V_i(τ_i,q_-i^λ)−U_i(q^λ)] is multiaffine
and equals actual D≥δ on the signed box, with F(0)=δ. Therefore
F is algebraically constant δ. No supported OWN cap mass is needed:
the target is each owner's OLD head conditional, not its cap point.

### HP3. Complete actual finite transport and continuous path

Including τ in the conditioning event uses the RIGHT endpoint of
its positive old retained interval as the HEAD boundary. For each
i∈B, original head masses e_i^k tend to e_i>0 and the literal law
conditional on original clock≤τ^k has old density

    f_i^k[(1−λ_i)+(λ_i/e_i^k)1_(u<right endpoint)].

The interval endpoint converges, its indicator converges in L¹,
the signed likelihoods remain nonnegative and bounded, and the fixed
multiplier weak-* test gives the desired limiting density. Unchanged
independent rectangle products and prescribed/ALL-moving-response
kernels give BOTH U and full B convergence, exactly as EA3. Never
is in the complement; no new calendar point is inserted; zero c
mass is retained and c⁺ duplicates c. The global floor is therefore
the true actual floor for this signed family.

Follow the legal forward diagonal path q_i^x=(1−x)q_i+xν_i,
0≤x≤1. Every point has bounded old density and actual carrier
realization. Uniform total-variation estimates make all caps and
payoffs continuous in x. The selected sum stays δ ALGEBRAICALLY
as the same polynomial, but it is actual D only when the old
selectors remain full caps.

### HP4. A first cap wall is an actual multiple-cap minimum

Let Z be the closed set where ALL old τ_i remain full maximizing
responses. It contains an initial interval. Let x* end its maximal
initial interval. On that interval and at x*, actual D=δ.

If x*<1 and all caps were still unique there, every τ selector
would have its isolated complement gap. For each later σ_i, the
coefficient k_i(x*) in (HP1) is positive. Its original upper ordering
is preserved along the whole path near x*, and the compact lower
set has a gap from uniqueness at x*. Thus every old selector would
remain full in a neighborhood beyond x*, contradiction. Hence some
cap has multiple maximizing POINTS at q^{x*}. This argument prices
nonisolated later caps without suppressing their nearby replies.

It remains to check x*=1; actual endpoint membership in Z is now
justified by closedness, not polynomial extrapolation.

### HP5. All but one endpoint configuration directly have multiple caps

At x=1 every owner in B stops no later than τ surely; each owner
outside B continues strictly after τ. There is at least one later
cap owner i because the original cap dates were not all equal.
If there is ANY h∈B\{i}, that sure opponent makes every response
strictly after τ and Never outcome-equivalent for recipient i.
Since its old selector τ_i>τ is a full cap at this endpoint,
the distinct finite c and Never are full maximizing points.

In particular |B|≥2 always yields multiple caps. If |B|=1 and
some later cap owner differs from its sole member, the same applies.
The only remaining configuration is

    B={h},       τ_h>τ,
    τ_j=τ and q_j(clock≤τ)=0 for ALL j≠h.         (HP2)

The endpoint changes ONLY h's OWN law. Thus its entire full-response
function and old cap B_h are unchanged. All three opponents originally
and finally stop strictly after τ, so V_h(τ)=s_h. Uniqueness of the
different maximizing point τ_h gives B_h>s_h.

### HP6. The exceptional endpoint has a genuine global debt decrease

At (HP2)'s endpoint, h stops≤τ surely and ALL opponents stop>τ.
Prescribed play is the singleton h, regardless of which head date
h selects. Arbitrary changes of the three opponents' conditional
tails after τ do not change any prescribed payoff or ANY non-h
full cap. A non-h test before τ sees only unchanged h or its own
early exit; one at τ sees h's unchanged atom there; a later test
or Never is screened by h's sure exit≤τ. This is the complete
deviation ledger, not child Nash or a favorable cap selector.

Literal witnesses make the comparison rigorous even at a marked
endpoint. HP3 makes h's old finite law conditional on clock≤τ^k,
so its late leakage is EXACTLY zero. The other old finite head
masses tend to zero. Preserve those heads and their late probabilities
and graft ANY actual opponent punishment law w starting at τ^k+1.
All prescribed payoffs and non-h full caps are EXACTLY unchanged
by the sure-by-cut h law. For h the new full cap is exactly

    max(H_k,A_k+α_k cap_h(w)),

with H_k→s_h, A_k→0 and α_k→1. The head cap convergence is
uniform: while all opponents have total head mass tending to zero,
every finite head response is within 2M times that mass of s_h.
The response at τ^k supplies the matching lower bound. No original
finite cap attainment, uniform nonisolated gap or attained punishment
minimum is assumed.

Choose actual w with cap_h(w)≤P_h+ε≤s_h+ε. The limiting modified
debt is at most δ−B_h+s_h+ε. Choose 0<ε<B_h−s_h. It is STRICTLY
below δ, contradicting the true global floor. Thus x*=1 cannot
remain in the exceptional configuration; the path must already
produce an actual multiple-cap minimum as in HP4 or HP5.

We have derived an ACTUAL finite-amplitude existing-head law producer:
ANY all-unique positive minimum with non-common cap dates can be
reselected, at the SAME table, to a multiple-cap true minimum under
same-table Fin4 punishment normality. Applied after the reviewed
worst-SUM source reduction, it means the counterexample search may
select a multiple-cap minimum without retaining an all-unique
multi-unsupported fallback. This is EXISTENTIAL and does not assert
that every produced minimum was already multiple, exclude all-unique
sources pointwise, or consume the resulting simultaneous-cap wall.

No step is added to the frozen 920-line artifact. A complete full
consumer must now operate on the actual multiple-cap minimum, not
reuse the fixed-selector polynomial beyond its cap-stable path.

### HP7. Exact same-table strategic input and the remaining value gap

The tracked input is
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
Its hypotheses are a literal reward table on NONEMPTY coalitions of
Fin4, a supplied real coordinate bound with |r(S)_i|≤bound for EVERY
coalition and recipient, and NO uniform-equilibrium payoff for THAT
SAME reward table at initial state none. Its produced field
`FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal`
is ∀i, `IsQuittingNormalPlayer reward i`.
`IsQuittingNormalPlayer` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
means `quittingPunishmentValue reward i ≤ quittingSoloSelfPayoff reward i`.
The punishment definition in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` is the infimum
over actual independent behavioral opponent plans of the supremum
over ALL behavioral responses. Thus its sole use in HP6 is the
existence, for EVERY ε>0, of an ACTUAL opponent law w with cap≤s_i+ε;
no infimum attainment or stationary child Nash is supplied. The
same-table no-UE hypothesis follows from that table's positive true
terminal-debt infimum by
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
its player type is finite and inhabited, as Fin4 is. For
the fresh table, apply the declaration afresh. Nothing transports
normality from the old reward table or singleton normalization.

There is a genuine kernel distinction when HP4 ends at x*<1. The
new equal-valued test and old unique test were NOT outcome-equivalent
at x=0, or the old cap would not have been unique. For two ordered
reply clocks t<s, under a COMMON opponent sample, player i's
membership in the absorbing coalition can only decrease when its
reply is delayed, while each opponent's membership can only increase.
The same holds for s=Never, with the empty Never outcome assigned
the empty membership vector. Hence different coalition kernels
force a strictly different membership marginal for some recipient:
if all those monotone marginal changes vanished, the two coalition
sets would be equal almost surely. At x*<1, the opponent product
law retains at least (1−x*)³ times its original product law. The
strict monotone marginal change therefore remains positive. Thus an
INTERIOR wall has at least two full maximizing tests with genuinely
different absorbing-outcome kernels, not merely c/Never copies behind
a sure owner.

However HP5 at x*=1 can supply ONLY outcome-equivalent c/Never
plateau points behind a sure head owner. The proof does not eliminate
this alternative. It supplies an explicit original-law head endpoint
and some zero-debt recipients when their prescribed laws stay strictly
late, but it does NOT prove that a previously positive debt is killed,
lower cardinal-minimal debt support, or price release of the final
sure owner. There is currently no complete consumer of that endpoint
which receives strictly stronger sufficient data than the already-open
multiple-cap branch. Therefore HP is retained as a global-path
mechanism in this notebook, NOT an export request or a claimed strict
counterexample-class reduction. The next line must distinguish or
consume the endpoint plateau instead of counting duplicate TEST POINTS
as strategic progress.

Nearby tracked geometry inspected for this question:
`quittingTerminalSemanticDebt_responseChord_eq_of_minimum_sameDebtSum`
and `response_support_nonempty_and_card_le_three_finFour` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticMinimumResponseChord.lean`.
Those exact results need TWO same-minimum endpoints differing in ONE
complete stopping law, and an actually killed source-positive debt
coordinate for the cardinal drop. HP's diagonal path alone does not
supply either premise. The all-observer cap convexity facts in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
do not change that gap.

## Generic raw-kernel rigidity excludes an all-isolated unique-cap minimum

Status: COMPLETE UNREVIEWED ordinary-mathematical source-consumer
candidate KR1–KR8. This is a genuine additional fresh-table restriction,
not an HP endpoint multiplicity count. It uses the ALL-minimum debt
rigidity proved and independently checked in MORSE Section49. The
full UE goal remains open: multiple caps and nonisolated later caps
are not consumed here. No export request or Lean claim is made.

### KR1. Exact target and a compatible generic fresh table

Write O for the sixteen outcomes, comprising fifteen nonempty finite
coalitions and Never, and set r_i(Never)=0. Impose the following
finite raw reward condition, separately for each recipient i:

    (A,B) ↦ r_i(A)−r_i(B), A,B∈O, A≠B,
    is injective and NEVER equals zero.                    (KR1)

This is compatible with an arbitrarily small perturbation of ANY
unit-cube table: each excluded equality is a proper affine hyperplane
in its fifteen row coordinates. Distinct ordered pairs have distinct
coefficient vectors e_A−e_B, where e_Never=0. First move an arbitrarily
small distance into the open unit cube, then avoid the finite union
of proper hyperplanes in a still smaller open ball. No strategic
equivalence or normalization is claimed for this full perturbation.

Starting from the canonical positive table, choose the perturbation
small enough to keep the positive true SUM gap and ALL 82 labelled
no-contact inequalities. These are open conditions by the eight-times
reward bound and finite coefficient bounds. Next select positive
recipient scales arbitrarily close to one, using the fixed-carrier
concave objective W(θ)=min_a θ·a. At coordinate-regular θ, all θ-
minimizing old debt vectors equal the coordinate derivative of W,
and all new scaled SUM minima have one common vector d*. This follows
from the positive/negative supporting inequalities, not outer Danskin.
Positive recipient scales preserve (KR1), because they multiply every
difference WITHIN one recipient row by the SAME positive number.

Fix this ONE fresh table BEFORE any minimizing sequence. It has
positive true δ, all canonical no-contact gaps, raw condition (KR1),
and one debt vector for EVERY carrier minimum. Its same-table no-UE
branch supplies true P_i≤s_i by the exact declaration recorded in
HP7; normality is applied anew after BOTH table operations.

The target is: NONE of its produced marked minima can have ALL four
caps both UNIQUE and ISOLATED. Equivalently, each all-unique minimum
has at least one NONISOLATED maximizing point, necessarily LATER than
the atomic earliest cap and with zero OWN point mass. This is not
an assertion that all later caps are nonisolated or pairwise distinct.

### KR2. All-old-law signed reweighting is actually realizable

Suppose q is such an all-unique all-isolated true minimum, with fixed
selectors σ_i. For each owner j choose ANY nonnegative continuous
weight w_j on the compact marked finite-clock space plus the isolated
Never point, with 0≤w_j≤1 and e_j=∫w_j dq_j>0. Define the old-law
target ν_j=(w_j/e_j)q_j and the independent signed family

    q_j^λ=(1−λ_j)q_j+λ_jν_j.

Both signs near zero are probability laws: the likelihood is
1+λ_j(w_j/e_j−1), bounded and positive on a two-sided box. The
weights are not new prescribed clocks or publicly shared lotteries.

For the ORIGINAL finite witnesses, let m_k(u) be the midpoint of
the original aggregate interval containing u, with the original
Never interval treated separately. Assign each original stopping
date its mass multiplied by w_j(m_k) and renormalize by e_j^k.
Extend w_j from the compact finite test subset to the surrounding
real interval by linear interpolation in its complementary gaps
and constant continuation at the two ends; Never stays separate.
This elementary extension preserves continuity and the range[0,1].
This is a literal stopping law: its multiplier is CONSTANT on each
original date interval. The marked producer gives m_k→π almost
everywhere; on retained positive intervals π is the old midpoint,
and elsewhere π(u)=u almost everywhere. Continuity and boundedness
give w_j(m_k)→w_j(π) in L¹. The original density bound and weak-*
convergence then give e_j^k→e_j and the intended new densities.
The signed multipliers remain uniformly bounded and nonnegative.

Thus prescribed rectangle-product kernels and EVERY fixed or moving
finite tester kernel converge under the same old-calendar proof.
Never is unchanged as a calendar point; c retains zero mass and its
late duplicate is still exact. Every small signed family pair is
in the ORIGINAL carrier. This does not invoke continuity of a new
atom at a zero-mass nonisolated point.

### KR3. Individual multiaffine debt kernels are constant

Each σ_i is unique and isolated in the compact complete test space.
The complement is compact and has a positive response gap. Uniform
total-variation bounds for the small independent signed reweightings
therefore keep EVERY full cap at its old selector. Its own law is
irrelevant to its cap; all other response values are controlled
uniformly over ALL deadlines, not just the four selected tests.

The actual SUM on this box is the multiaffine fixed-selector sum,
has an interior global minimum δ and is algebraically constant.
Every box point is consequently an ACTUAL global minimum. Debt
rigidity makes EACH coordinate equal its original d_i*. Therefore
the INDIVIDUAL multiaffine branch polynomials

    F_i(λ)=V_i(σ_i,q_-i^λ)−U_i(q^λ)

are constant d_i*, first on the open box and hence identically as
polynomials. At λ=(1,1,1,1) we conclude ONLY the selected-response
identity

    ∫[∏ν_j] [r_i(R_i(t_-i;σ_i))−r_i(S(t))]=d_i*.       (KR2)

No actual endpoint-cap or endpoint-minimum assertion is used. Here
S(t) is the actual first coalition (Never if all clocks are Never)
and R_i is its counterpart with ONLY i's clock replaced by σ_i.

### KR4. Rectangle tests yield an almost-sure raw regret identity

Multiply (KR2) by ∏e_j. It holds for EVERY product of nonnegative
continuous old-clock weights with positive integrals; zero-integral
weights contribute zero automatically. Products of these weights
determine signed measures on the compact product clock space: they
form a separating algebra containing constants, or equivalently
approximate the indicator rectangles in the product-law measure.
Thus the finite-valued measurable raw regret kernel satisfies

    r_i(R_i(t_-i;σ_i))−r_i(S(t))=d_i*
    for ∏q_j-almost EVERY clock tuple t.                    (KR3)

This does not just state prescribed expected payoff-flatness. It
retains the actual coalition pair of each pure tuple. Since δ>0,
choose i with d_i*>0. Such a pair cannot have R_i=S. Condition
(KR1) gives ONE unique ordered pair with this difference. Hence
BOTH R_i and the common actual coalition S are deterministic almost
surely. In particular the prescribed terminal outcome itself is
ONE fixed S∈O, not merely one constant expected payoff vector.

### KR5. Never and deterministic collision coalitions are impossible

If S=Never, every owner prescribes Never surely. Every full cap is
max(s_i,0), so positive total debt supplies some s_i>0. For that
owner the reviewed global singleton margin δ≤B_i−s_i gives δ≤0,
contradiction. All-negative own singletons would instead give debt0.

If |S|≥2, independence forces all members' clocks to equal ONE
deterministic finite date t₀, and every outsider's clock is strictly
later. Indeed two independent clocks equal almost surely can only
have a common Dirac law; no correlated simultaneous clock is used.
There is NO prescribed mixture mass before t₀. In an all-unique
minimum, EA forces the earliest cap to have positive mixture mass;
therefore no maximizing selector lies before t₀. For every recipient,
some OTHER member of S is sure at t₀. A maximizing selector strictly
later than t₀ would consequently tie the outcome-equivalent distinct
finite c and Never tests, violating uniqueness. ALL selectors must
equal t₀. The canonical no-common-cap exclusion, preserved by KR1's
table construction, contradicts this. This argument does not assume
that S is a pure Nash coalition or that its participants have positive
debt.

### KR6. A deterministic singleton is ruled out by a global tail graft

Let S={h}. Then h is finite surely and every opponent's clock is
strictly later than h almost surely. Thus U_h=s_h. The true global
singleton margin gives B_h−s_h≥δ>0, so h is genuinely a debtor.

Independence gives ordered separation of supports: their common
boundary b may be nonisolated, but there are cuts approaching b
for which h's late mass tends to zero and the opponents' total
head mass tends to zero. If h has a boundary atom, include it;
opponents cannot have an atom there. If h has no boundary atom,
approach b from below. Never mass of h is zero. This also covers
b=c and arbitrarily late original deadlines. Apply the marked cut
transport and a diagonal selection to the ORIGINAL finite witnesses
to obtain literal integer cuts a_k with

    p_h^k(clock>a_k)→0,
    Σ[j≠h]p_j^k(clock≤a_k)→0.                            (KR4)

Keep every opponent head and its late probability, but replace each
conditional tail by ANY actual independent punishment plan w shifted
to start at a_k+1. If h's original late leakage is η_k, coupling
shows that each prescribed payoff changes≤2Mη_k, each non-h FULL
cap changes uniformly≤2Mη_k, and the resulting non-h-cap/total-payoff
SUM error is≤14Mη_k. No early responder or Never test is omitted.

The modified h cap is EXACTLY

    max(H_k,A_k+α_k cap_h(w)).                              (KR5)

H_k is its best head response, A_k its passive head payoff and α_k
the probability that all three opponents survive the cut. By the
second condition in (KR4), every head response is uniformly within
2M times that small head probability of s_h. Hence H_k→s_h,
A_k→0 and α_k→1. Choose an ACTUAL w with cap_h(w)≤P_h+ε≤s_h+ε,
using SAME-table true normality and no attainment hypothesis. The
limiting modified debt is at most δ−B_h+s_h+ε. Taking
0<ε<B_h−s_h gives an actual debt strictly below δ, contradiction.

This is a complete original finite-law comparison, not a child Nash,
renamed punishment verifier or payoff-only endpoint extrapolation.
It excludes the final deterministic-outcome case in KR4.

### KR7. Exact scope tests and the residual

Raw difference injectivity is indispensable in KR4. Embed the
following two-owner calculation in Fin4 with two dummy Never owners.
Set recipient0's own singleton−1, joint01 payoff1, passive singleton1
payoff2, and ALL unspecified rewards and other recipient rewards0.
Owner0 stops at date0; owner1 is half date0/half Never. The actual
coalition is half01 and half0. Replacing owner0 by Never produces
half1 and halfNever. BOTH raw regrets are1, since

    r_0(1)−r_0(01)=2−1=1=0−r_0(0).

Thus a positive constant raw regret alone does NOT make S constant.
Its repeated row difference is exactly forbidden by (KR1). Actual
U_0=0; date0 pays0, every later finite test pays1/2, Never pays1,
so this is an exact full-cap calculation, but not a true positive
minimum: literal AllNever is debt-zero. It is only the minimal failed
genericity implication, not a new counterexample or optimization trap.

Isolation is also a REAL hypothesis in KR3. On a compact continuous
test interval, V(t,u)=−t²+2ut is affine in u for each fixed t, yet
its unique nonisolated maximum moves from0 to u and the cap is u².
Uniqueness does not make the selected branch stay affine nearby.
This is an abstract cap-family test, not a quitting-game construction.

Consequently the complete result removes the ALL-isolated all-unique
arm at ONE produced fresh table. Its remaining all-unique arm MUST
have a nonisolated LATER cap point, whose OWN prescribed point mass
is zero; supported positive points are retained isolated atoms. Its
multiple-cap arm is not consumed. No pointwise claim about an arbitrary
original reward table, no payoff/cap/profile rigidity, and no UE is
inferred. No previously frozen packet is modified by this addition.

### KR8. Concrete next question

The decisive new data are an almost-sure raw regret identity, not an
equivalent c/Never tie. Its proof currently uses exact cap stability
at ALL isolated unique points. Can the nonisolated LATER maximizer's
known positive-rescaling family supply enough of this rectangle
rigidity without falsely treating arbitrary earlier law changes as
cap-stable? Or can genuine multiple active kernels be priced by the
same generic-difference table and all-minimum debt-vector rigidity?
Those are the surviving global consumer questions. A directional
cap derivative or a pure endpoint debt estimate alone cannot replace
the exact all-moving-response step KR3.

## Head-box debt rigidity excludes EVERY all-unique minimum

Status: COMPLETE ordinary-mathematical candidate HR1–HR6, with
NOETHER's independent focused falsification PASS and no unresolved
objection. The complete self-contained artifact is
[DEBT_RIGID_MULTIPLE_CAP_SOURCE_REDUCTION.md](CODEX_BROUWER__DEBT_RIGID_MULTIPLE_CAP_SOURCE_REDUCTION.md);
its separate whole-proof gate remains.
This supersedes KR's ALL-isolated/generic-difference arm.
It does NOT use full-law rectangle weights, generic payoff differences
or isolated LATER caps. It uses only OLD head conditioning before
the earliest atomic cap, fixed-cap debt rigidity and an ACTUAL global
punishment graft. No new packet, export or UE conclusion is claimed.

### HR1. Exact fresh-table and same-table inputs

Use the canonical fresh positive table, with all 82 no-contact gaps,
then the arbitrarily small positive recipient scaling of the new
ordinary DR proof to produce ONE fresh table r. The finite gaps and
δ>0 persist. Every global original-carrier minimum has one COMMON
nonnegative debt vector d*. The producer of this rigidity is the
fixed-carrier concavity/coordinate-derivative/Fubini argument reviewed
in MORSE Section49, NOT a checked Lean declaration or a theorem
in the frozen 920-line artifact. The scaling changes the entire
minimizing family; no old minimizing law is transferred.

At this SAME table, positive true SUM infimum gives no UE, and the
checked same-table declaration/hypotheses in HP7 give P_i≤s_i for
ALL owners. The singleton margin is δ≤B_i−s_i at EVERY actual
carrier SUM minimum. The canonical source proof supplies: if ALL
four caps are unique, their earliest point τ is FINITE, a positive
MIXTURE atom and ISOLATED, and their dates are NOT ALL equal.
The ordinary DR5 supported-earliest reset additionally proves that
EVERY owner whose maximizing point equals τ has zero OWN mass there.
These are fresh-table source facts, not a favorable selection of a
special minimizing law.

Fix ANY such hypothetical all-unique source q, with selectors σ_i.
Let B={i:e_i=q_i(clock≤τ)>0}. It is nonempty. Some supplier h has
q_h({τ})>0; the supported-earliest exclusion forces σ_h>τ. Therefore
d_h*>0: its old atom at τ has strictly positive regret from the
unique different full maximizer. The target is a contradiction for
this ORIGINAL source, not merely minimum reselection to cap copies.

### HR2. The full head-box and its actual finite transport

For i∈B put ν_i=q_i(·|clock≤τ); for i∉B leave the law unchanged.
Use independent parameters q_i^λ=(1−λ_i)q_i+λ_iν_i. The old HEAD
and LATE likelihood factors are 1+λ_i(1/e_i−1) and 1−λ_i, positive
and bounded on a two-sided box. A redundant e_i=1 is harmless.

Original finite witnesses use the retained date n_k corresponding
to τ and conditioning on clock≤n_k. The boundary is the RIGHT end
of the retained positive mixture interval, so its initial indicator
converges in L¹; the e_i^k tend to the positive e_i. The literal
signed likelihoods stay bounded and nonnegative and converge weak-*
after multiplication by that moving indicator. Prescribed products
and ALL moving finite-test kernels therefore converge on the old
calendar. Never remains outside the head, c has no new mass and
the late duplicate c⁺ remains EXACT. Every small signed family pair
is in the original carrier, not just a selected polynomial fiber.

Each earliest selector τ has its isolated uniform complement gap.
For each later selector σ_i>τ choose τ<a_i<σ_i (for Never use
τ<a_i<c). Expanding the opponent product shows that EVERY test
t>a_i has value k_i(λ)V_i(t,q_-i)+C_i(λ), with
k_i=∏[j∈B,j≠i](1−λ_j)>0 and the SAME t-independent C_i.
Each additional term contains a head exit≤τ. Thus the WHOLE upper
ordering is preserved, even for a nonisolated later maximizer; a
compact lower gap keeps it full locally. ALL four caps consequently
stay at their selectors on a two-sided box.

The SUM fixed-response polynomial is multiaffine, actual D≥δ in
that box and equalδ at its interior. Hence it is constant and every
box point is an actual minimum. Debt rigidity forces EACH individual
fixed-response polynomial

    F_i(λ)=V_i(σ_i,q_-i^λ)−U_i(q^λ)

to be constant d_i*, first on the box and then ALGEBRAICALLY for
every parameter vector. Its endpoint evaluations below are selected
regrets only. No modified endpoint full cap or actual minimum is
inferred by extrapolation.

### HR3. If there is only one old head owner, the debt ledger contradicts margin

Suppose B={h}. All opponents stop strictly AFTER τ. Every old head
response by h, and h's prescribed conditional head law, pays exactly
its singleton s_h. Its full cap is independent of its own law. On
the small signed head mixture, constant individual debt therefore
forces U_h=s_h, including the redundant e_h=1 case. Consequently

    d_h*=B_h−s_h≥δ.

There is at least one earliest maximizing owner j≠h. Its cap is
unique at τ and its prescribed own mass at τ is zero, so d_j*>0.
This strict mean-regret statement needs no uniform gap on its OWN
law: a bounded nonnegative integrand positive at every prescribed
clock has strictly positive integral. Therefore
δ=Σ_i d_i*≥d_h*+d_j*>d_h*, contradiction. The head owner was not
assumed to be a Nash row or a minimizing tail.

### HR4. With two head owners, rigidity makes the supplier originally sure

Suppose |B|≥2 and retain a supplier h with σ_h>τ and d_h*>0.
In the fixed-response polynomial set ALL other B parameters to1.
At least one OTHER owner now stops≤τ surely, so if h uses its
original conditional LATE law (>τ), BOTH that prescribed clock
and its selected later reply σ_h>τ are screened by the same old
head coalition. Their raw regret is EXACTLY zero; outside-B owners
also stop>τ and cannot alter this screening.

With h itself conditioned to HEAD, F_h equals d_h* by HR2's
polynomial identity. With h left ORIGINAL, its head weight is e_h
and its late weight1−e_h, so the SAME identity gives

    d_h*=F_h(own parameter0,others1)=e_h d_h*.

Since d_h*>0, e_h=1. This asserts ORIGINAL q_h(clock≤τ)=1,
not endpoint purity or an endpoint-minimum claim. Any OTHER later
maximizing selector would now tie distinct c/Never responses behind
h's sure exit, violating uniqueness. Hence σ_j=τ for EVERY j≠h.
The supported-earliest exclusion gives q_j({τ})=0 for all j≠h.
Each of these opponents has strictly positive probability AFTER τ:
an opponent sure≤τ would screen h's own later cap and likewise make
it tie c/Never. This is an actual sure-head source geometry, not a
child-game equilibrium premise.

### HR5. The actual complete tail graft contradicts the unique later cap

Let H be the FULL supremum over finite source tests≤τ for recipient
h. Compactness and unique maximization at σ_h>τ give H<B_h.
Let α=∏[j≠h]q_j(clock>τ)>0 and A be h's passive payoff from
opponent absorption strictly before τ. Because EVERY opponent has
ZERO root point mass, the ACTUAL root test satisfies

    V_h(τ)=A+αs_h≤H.                                  (HR1)

At the ORIGINAL finite root n_k, h's late leakage η_k→0. Preserve
each opponent head, root probability and late probability and graft
ANY actual independent punishment law w after n_k. For all prescribed
payoffs and all non-h FULL caps the only discrepant coupled outcomes
require the ORIGINAL h to survive past the cut: payoff/cap errors
are≤2Mη_k each, and the non-h-cap/total-payoff SUM error is≤14Mη_k.
This is uniform over ALL finite replies and Never, including early
tests and joining the unchanged root. No cap of a nonmover is silently
replaced by a favorable selected response.

h's cap in the modified actual profile is EXACTLY

    max(H_k,A_k+α_k cap_h(w)).                         (HR2)

The head cutoff is the retained original atom date. All fixed/moving
head tests extract into the compact finite source set≤τ, and every
source head test has original head witnesses. Thus H_k→H by the
complete head-kernel argument, not an assumed maximum response gap
on a nonisolated cap. Also A_k→A and α_k→α; vanishing opponent
root atoms make strict-before versus through-root head payoff limits
agree. Head payoffs are unchanged by the graft.

True SAME-table normality supplies w with cap_h(w)≤P_h+ε≤s_h+ε.
If finite literal witnesses are desired, move each finite tail beyond
a sufficiently large truncation to Never; its total moved mass tends
to zero and uniform response coupling preserves this bound with an
arbitrarily smaller initial ε. This leaves an ACTUAL independent
finite-support/Never punishment law. It is not an attained infimum
or a correlated/publicly chosen coalition.

Using (HR1), the limiting modified h cap is≤H+αε≤H+ε. All other
errors vanish, so its actual SUM debt has limsup≤δ−B_h+H+ε.
Choose 0<ε<B_h−H. Literal modified debts are eventually STRICTLY
below δ, contradiction to the true global infimum. This consumes
the original sure-head geometry, not the multiplicity at a reselected
endpoint.

### HR6. Exact new restriction and what is still open

Both possibilities for the nonempty head set B contradict the all-
unique source. Therefore ONE produced fresh table can have NO
produced marked global minimum with all four caps unique. EVERY
such minimum has multiple maximizing TEST POINTS for some owner.
This is pointwise over ALL freshly produced minima, unlike HP's
existential reselection. No generic ordered reward differences or
isolated later caps are needed; KR remains a valid but subsumed
supporting route if this proof passes independent falsification.

The multiple-cap points may nevertheless be outcome-equivalent late
plateau tests. HR does not consume those kernels, prove a strict
positive-debt rank drop, or produce UE. Its genuine increment is
removal of the ENTIRE all-unique branch at the rigid fresh table,
not a claim that point multiplicity alone is an equilibrium consumer.
No frozen source, DR packet or export is changed. The next question
is a full global repair of simultaneous active kernels at a debt-rigid
minimum, with the late plateau alternative retained explicitly.

## Strict pre-active heads at a debt-rigid multiple-cap minimum

Status: COMPLETE supporting extension MH1–MH3; NOETHER's focused
independent proof check found no mathematical issue, with the cut
clarification incorporated in MH2. It is not a consumer of the final
sure-owner release or a whole-artifact gate. No genericity, uniqueness
or supported-active-point hypothesis is used. This is a concrete
description of one remaining outcome-equivalent plateau, not another
cap-point multiplicity count.

### MH1. Any fixed cut strictly before ALL active tests is cap-stable

At a produced true positive minimum with one common debt vector
for ALL carrier minima, let τ be the EARLIEST point in the union
of the four complete cap sets, allowing multiple caps. Fix u<a<τ
and B_u={i:q_i(clock≤u)>0}. Each old target q_i(·|clock≤u) has
bounded two-sided likelihood transport when its event has positive
mass. Choose a cut not splitting a retained atom; include the whole
old atom whenever needed. Every upper response t>a transforms by
the SAME positive affine rule, because any new term has a head exit
≤u. Therefore ALL active tests, not merely chosen representatives,
retain their relative order and equalities. The compact lower tester
set≤a contains no active point and has a uniform gap. Full cap
stability follows even when every active set has accumulating points.

As in HR2, the actual SUM and then EACH fixed-representative regret
polynomial are constant on the signed box and algebraically for all
head parameters. For each i∈B_u its old head lies STRICTLY before
every full maximizer, so d_i>0. If |B_u|≥2, condition all other
B_u owners to head and compare i's old law to its own head target.
Its late branch and its selected cap (both>u) are screened by another
sure head, so d_i=e_i d_i and e_i=q_i(clock≤u)=1 for EVERY i∈B_u.

If B_u={h}, the conditional head pays s_h because all opponents
are>u. Constant own debt gives U_h=s_h, and singleton margin gives
δ≤d_h. Hence ALL other debts are zero. In particular B_u cannot
be singleton whenever ANY other owner has positive old probability
strictly before τ: that old strictly-suboptimal mass gives positive
debt for the other owner.

### MH2. Two pre-active owners force a pure common coalition

Suppose A={i:q_i(clock<τ)>0} has at least two members. The above
conclusions hold for ANY regular cut u<τ. First take u high enough
to capture positive old head mass from every member of A; all of
them are then originally sure≤u. Let t₀ be their smallest essential
support endpoint. If exactly one owner had that smallest endpoint,
cuts just above it would have singleton B_u, impossible by MH1.
At least two owners therefore share it. Use CALENDAR events clock≤u,
not raw-chart cuts through a retained interval. At an isolated t₀,
one whole-date event at the RIGHT end of its retained interval
already gives clock≤t₀; cuts within its following calendar gap are
the same event. At a nonisolated t₀, choose decreasing regular
calendar cuts u>t₀ with whole retained atoms included; their raw
pullbacks use retained right endpoints or null boundaries. Whenever
these two heads are present, MH1 makes them sure≤u, and taking the
decreasing calendar events makes them both PURE at t₀. Every other owner with the SAME lower
support endpoint is present in these decreasing cuts as well, so
MH1 also makes it pure at t₀. An additional pre-active owner with
a STRICTLY HIGHER lower endpoint would be screened by the earlier
sure players: both its prescribed law and every active response≥τ
see the same coalition, giving debt0, incompatible with its positive
strictly-suboptimal pre-active mass. Thus EVERY member of A is pure at ONE common
finite t₀<τ, and outsiders stop≥τ>t₀.

The actual terminal outcome is deterministically A. ALL active
responses are later passive plateau tests, and the individual debts
are exactly

    d_i=r_i(A∖{i})−r_i(A)>0 for i∈A,
    d_i=0 for i∉A,
    δ=Σ[i∈A](r_i(A∖{i})−r_i(A)).                     (MH1)

Here |A|≥2, so no empty withdrawal reward is needed. A may have
two, three or four members. No pure Nash claim is made: on the
contrary, EVERY member strictly benefits by withdrawing. The entire
head comparison is actual/source-global, but it does not yet remove
the last sure finite owner or control that release's new late caps.

### MH3. What this exposes rather than consumes

The remaining multiple-cap geometry with two strict pre-active owners
is not an arbitrary diffuse clock family: it is an exact pure unhappy
coalition and one of eleven finite withdrawal sums. To avoid these
contacts by a NEW whole-table proof, one cannot append the canonical
endpoint target without checking its signs. Its participant-pair and
participant-triple values are+1 while passive singleton/pair values
are−1; consequently pair withdrawal sums target−4, not a value above
the positive minimum. The anti-membership endpoint would raise every
withdrawal sum to2|A|, but lowers canonical singleton/pair join
contacts. No simultaneous-contact separator or new worst-table
comparison is supplied here. Thus (MH1) is retained as exact source
data for a genuine last-sure release, not an unproved finite-spectrum
consumer or new export. The sole strict-head-owner arm is excluded
by the stronger SAME-table checked input
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
Its hypotheses are original-carrier membership and global SUM
minimality, exactly four players, a positive reward bound M covering
all entries, and positive total debt δ. It gives

    U_i−s_i≥δ−d_i+δ²/(8M)>0 for EVERY i.

The strict final inequality uses nonnegative debts and d_i≤δ.
Hence MH1's U_h=s_h is impossible; no second debtor is needed.
This theorem and `exists_minimumTerminalSemanticDebt_le_sqrt_of_fourPlayer`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPayoffEnvelope.lean`
were narrowly inspected. No change to the frozen HR artifact follows.

## A random minimum forces a root-to-later active payoff-kernel bridge

Status: COMPLETE ordinary-mathematical candidate BG1–BG6 with two
independent focused mathematical PASSes. The combined standalone
integration gate is separate. It is a source restriction at one compatible
generic debt-rigid positive table, not an equilibrium consumer. It
strictly distinguishes root-to-later active kernels from late/Never
plateau aliases. No conclusion that the bridging owner has positive
debt is made. Deterministic outcomes are retained as a separate
alternative; no unreviewed deterministic-outcome exclusion is used.

### BG1. Exact data and compatible fresh-table selection

Take the intermediate positive-gap unit-cube table with the 82
strict no-contact gaps from the complete source/table construction,
then, BEFORE selecting new minima, make its recipient rows generic:

    r_i(S)≠r_i(S′) for every i and distinct nonempty S,S′.

This selection is legal. First contract the whole table by a common
factor arbitrarily close to1 so that every entry is strictly inside
the unit cube. Every homogeneous contact value and the true SUM
infimum contract by the SAME factor, so all contact gaps and the
positive gap persist. Next take a sufficiently small perturbation
inside this open cube outside the finitely many row-equality
hyperplanes. Their complement is dense. If the perturbation size is
β, the full-law SUM infimum changes by at most8β and each contact
by at most6β; choose β below the positive-gap and contact margins.
This retains Δ>0 and all 82 strict gaps. Now perform the ordinary
positive recipient-scale selection DR on THIS fixed carrier. Positive
row scales preserve all within-row inequalities, and arbitrarily
small scales preserve the contact gaps. This produces ONE fixed
table with generic recipient rows and ALL-minimum debt-vector
rigidity. No old minimizing law, cap family or normality datum is
transferred.

At that table fix ANY produced marked TRUE global minimum q.
Use its complete independent laws on X=T⊔{Never}, full continuous
response functions and all original finite/Never response witnesses.
Put δ=Δ(r)>0, d_i=B_i−U_i, and let τ be the earliest point in the
union of ALL active cap sets. It is finite by EA. “Deterministic
outcome” means that the prescribed terminal outcome law, including
Never, is a point mass, not merely that its payoff is constant.

Claim: either the prescribed terminal outcome is deterministic,
or there exist an owner i and a later compact test σ>τ such that

    V_i(τ,q_-i)=V_i(σ,q_-i)=B_i,

where τ is a finite isolated positive mixture atom, no prescribed
owner stops before τ, and the TWO actual response PAYOFF KERNELS
differ on a positive-probability set of opponent draws. Their
EXPECTED payoffs are equal maxima; the pointwise kernel distinction
does not mean their cap values differ. In particular a genuinely
random minimum cannot have ONLY late/Never outcome-equivalent cap
multiplicity.

### BG2. Randomness eliminates all strict pre-active heads

Let A={i:q_i(clock<τ)>0}. The signed old-head argument MH applies
without uniqueness or an isolated τ. At a whole-date cut u<τ,
every response above a slightly larger cut a<τ has one positive
affine rescaling under each conditional old-head change. The
compact lower test set has no active point and has a strict gap.
All full active upper sets therefore remain active together on a
legal two-sided box. Actual original finite witnesses use WHOLE
retained dates/right-end cuts or null boundaries; they never split
an old atomic interval. The SUM polynomial is constant by global
minimality and each individual polynomial is constant by debt rigidity.

If A is nonempty and exactly one owner has any mass before τ,
the single-head argument gives its U_h=s_h. This contradicts the
checked SAME-table all-owner quadratic payoff margin stated in MH3,
under original carrier membership, global SUM minimality, a positive
reward bound, four players and δ>0:

    U_h−s_h≥δ−d_h+δ²/(8M)>0.

If A has at least two members, MH2's cut descent makes ALL of them
pure at one common t₀<τ, and every outsider stops≥τ. For precision,
these are decreasing CALENDAR events, not decreasing raw coordinates
through an isolated midpoint. At an isolated t₀ the whole-date
event at its retained right endpoint already suffices; in the
nonisolated case regular whole-atom/null-boundary cuts decrease
to t₀. This prescribed terminal outcome is the deterministic
coalition A.

Thus a NONDETERMINISTIC minimum has A empty. If its earliest active
point had zero mixture mass, EA's actual all-response result would
supply an owner stopping strictly before it surely, contradicting
A empty. Hence τ has positive mixture mass and is isolated. Every
prescribed law is on clocks≥τ, and its mass on clocks≤τ is precisely
its own atom at τ. This excludes no deterministic arm by assumption.

### BG3. If no cap bridges the root, the complete root box is stable

Assume the nondeterministic minimum has NO owner maximizing both
at τ and at a later compact point. Let

    R={j:a_j=q_j({τ})>0}.

R is nonempty. Every owner whose cap contains τ has cap set EXACTLY
{τ}. This is not an assumption that the other owners' caps are
unique: they may have arbitrary compact later maximizing sets,
including equivalent finite/Never plateaus.

For j∈R independently use the existing supported-atom reset

    q_j^λ=(1−λ_j)q_j+λ_jδ_τ.

The original retained positive interval supplies actual finite
targets at its retained date n_k. Its own atom mass tends to a_j>0,
so small parameters of BOTH signs are legal. The old-chart density

    (1−λ_j)f_j^k+λ_j 1_(J_k)/|J_k|

is uniformly bounded and nonnegative; interval indicators converge
in L¹, yielding weak-* convergence, product/payoff convergence and
ALL moving-cap convergence. Unit mass gives a redundant direction,
not an illicit negative probability. Never stays separate and c⁺
duplicates c exactly; no new mass is inserted at a nonisolated point.

A root-only cap has the isolated compact complement gap. For an
owner with ALL its active points later, compactness and isolation
of τ permit one cut a>τ strictly below its entire active set; when
the only active point is Never choose τ<a<c. Each product term
containing a reset opponent quits at τ, before EVERY response t>a.
Consequently on the WHOLE upper family,

    V_i(t,q_-i^λ)=k_i(λ)V_i(t,q_-i)+C_i(λ),
    k_i=∏_(j∈R,j≠i)(1−λ_j)>0.

This preserves ALL maximizing equalities and upper orderings, not
just one selector. The compact lower set contains no active point
and remains below the upper maximum locally. Thus EVERY full cap
stays represented by its original active set on one signed box,
even if every later cap set is multiple and nonisolated.

Select any original maximizer σ_i for each owner. The selected
summed-regret polynomial is the ACTUAL debt throughout this box.
It is multiaffine, has interior global minimum δ, and hence is
constant. Every box pair is a true original-carrier minimum. ALL-
minimum rigidity now makes EACH individual polynomial identically
d_i, algebraically at distant parameter endpoints too. Those far
evaluations remain SELECTED regrets, not actual endpoint cap claims.

### BG4. This forces a deterministic original root cohort

If R={h}, every opponent is strictly after τ. The reset target
pays s_h to h. Its cap is independent of its own law. Individual
constancy forces U_h=s_h when a_h<1; if a_h=1 the same equality
is immediate. The all-owner quadratic payoff margin contradicts
this. Thus |R|≥2.

Consider any h∈R. If its cap is root-only, its own reset toward
its maximizing root has

    d_h(q^λ)=(1−λ_h)d_h(q)

on the actual box. Rigidity forces d_h=0. The ONLY maximizing
point is τ, so zero expected regret implies the ORIGINAL q_h
is pure at τ. This is actual original purity, not a polynomial
endpoint inference.

If all its cap points are later, its positive prescribed atom at
the strictly suboptimal root gives d_h>0. In the polynomial identity
condition all OTHER members of R to the root. There is another
sure root owner. With h on its old conditional late law (>τ),
both its prescribed clock and any selected σ_h>τ are screened
by the same other-owner root coalition, so the raw regret is zero.
With h conditioned to the root, its selected regret is d_h by
individual polynomial constancy. Leaving h original gives

    d_h=a_h d_h+(1−a_h)·0,

forcing a_h=1. If a_h=1 already, no late conditional is defined
or needed. Again this is ORIGINAL purity. All outside-R laws are
strictly after τ by BG2 and their zero root masses.

Every member of R is therefore originally pure at τ, and every
other owner is later. The actual prescribed terminal coalition is
deterministically R, contradicting nondeterminism. This proves that
a nondeterministic positive minimum MUST have a root-to-later bridge,
not merely some pair of abstract maximizing point labels.

### BG5. The bridge really distinguishes payoff kernels

Choose the bridging owner i and any later active σ. The root
response is its full cap, so the singleton margin gives

    V_i(τ)=B_i≥s_i+δ>s_i.

If no opponent had positive root mass, its response at τ would
be its own singleton s_i, impossible. Thus with positive probability
at least one opponent exits at τ. On that event let S≠∅ be the
opponents' tied root coalition. Because there are no earlier draws,
the response at τ gives coalition S∪{i}, while the response at
ANY σ>τ, including Never, gives coalition S. These are different
coalitions on a set of positive probability. At least one such
nonempty S has positive event probability, since there are finitely
many possible S.

The fresh row genericity gives

    r_i(S∪{i})≠r_i(S).

Thus the two FULL response payoff kernels differ on that positive
probability set of the ORIGINAL opponent laws. This is not merely
a c/Never alias behind a sure old owner. Equality of their expectations
is the genuine active tie that remains to be priced. No claim about
a sign of the pointwise differences, a positive debt of i, or a
root Nash condition is made.

This distinction has literal finite witnesses as well. Retain the
original root date n_k and one original moving response σ_k for σ
(or literal Never). Since τ is isolated and σ>τ, σ_k>n_k eventually.
For a nonempty root coalition S with positive limiting opponent
probability, the event that EXACTLY its members stop at n_k and
all other opponents are later has probability tending to that
positive value. Root masses and through-root masses converge by
the retained interval's endpoint density tests. On this event the
two actual finite responses give respectively S∪{i} and S. The
SAME fixed generic reward difference is nonzero for every k. No
new nonisolated insertion or asymptotic tester alias supplies the
kernel distinction.

### BG6. Exact boundaries, source comparison and the remaining consumer

The participant-indicator table from the earlier cap-atom boundary
test, r_i(S)=1 if i∈S and0 otherwise, has each owner half root/half
Never. Its terminal outcome is genuinely random, every cap is
root-only, and D=2. Resetting the root masses legally decreases D.
Its true δ is0. Thus a random PROFILE with positive debt cannot
replace a genuine global positive minimum in BG3–BG4.

Within-row genericity is needed ONLY for the PAYOFF-kernel upgrade,
not for the coalition-kernel bridge. For the complete table
r_i(S)=1 for every i,S, let owner0 be pure at date0 and every
other owner be half date0/half Never. The prescribed coalition is
random, U_i=B_i=1 and δ=0. For any owner j≠0, date0 and Never
are both maximizing responses. Their first-coalition kernels differ:
the former joins owner0 and the latter does not. Their payoff
kernels are nevertheless identically1 against these opponents.
This exact table shows why different test or coalition labels
alone cannot be upgraded to different payoff kernels without
checking the reward data.

One attempted finite-amplitude consumer of the bridge was repeated
root prefixing. Its precise all-branch ledger, with no pre-root
mass and a fixed actual old tail (u,b), is

    Q_i(a)=root-Quit reward,
    A_i(a)=opponent root-absorption reward,
    c_-i=∏_(j≠i)(1−a_j), c=∏_j(1−a_j),
    B_i(a,u,b)=max(Q_i,A_i+c_-i b_i),
    U_i(a,u)=a_i Q_i+(1−a_i)A_i+c u_i.

If EVERY Q_i ties its later cap, the root is exact Nash AGAINST
the tail CAP vector b; the debt cancellation is D=cΣ_i(b_i−u_i).
It is NOT exact Nash against u or the global root cap vector.
Prefixing the SAME row again changes its continuation caps and
can break all these ties; no repeated-root contraction follows.

The exact declarations
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
`quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
and `exists_quittingCapNashRootStack` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` were
inspected under their imports. They require each chosen root to be
exact Nash against its executable suffix's COMPLETE cap. They
produce finite cap-Nash stacks, not absorption of those stacks,
a debt-minimizing old tail, or preservation of the SAME root's Nash
property after another prefix. The global positive-minimum auxiliary
budget in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
was also inspected; it constrains prefixed auxiliary Nash roots,
not this original first row. No false Nash hypothesis is inserted
to close the repeated-root route.

The new source restriction concerns genuinely RANDOM atomic earliest
outcomes, independently of any proposed finite-contact elimination
of deterministic outcomes. Even if such an elimination is later
proved, BG alone supplies no debt decrease. The next consumer must
price a real root-versus-later max tie, possibly carried by a
ZERO-debt owner, while permitting changes to the independent old
tails and controlling every moving finite response and Never.
A late-plateau-only multiplicity argument or a locally linear
selector cannot settle that remaining branch.

## The genuine marked bridge as an actual finite-prefix source

Status: complete ordinary-mathematical adapter of the already accepted
canonical source theorem, not an additional class exclusion or export.
It does not require an attained minimizing tail, a tail deadline
attaining its limiting cap, or a Nash first row. The strategic inputs
are precisely the same fixed-table marked source and ALL-minimum debt
rigidity used in BG. The purpose is to let a consumer work with the
existing finite-prefix interface without naming a whole calendar.

### NF1. Exact finite statement delivered by the canonical source

Write r for the ONE final selected table, K for its original closed
payoff/full-cap carrier, δ=min_K D>0, s_i=r_i({i}), and d* for its
common nonnegative debt vector at ALL unweighted SUM minima. Its
row-genericity means r_i(S)≠r_i(T) for distinct nonempty coalitions.
There exist a∈[0,1]⁴ and v=(u,b)∈K with the following properties.

For S⊆I\{i}, set

    p_-i(S)=∏[j∈S]a_j ∏[j∉S,j≠i](1−a_j),
    α_i=∏[j≠i](1−a_j), c=∏[j∈I](1−a_j),
    A_i=∑[∅≠S⊆I\{i}]p_-i(S)r_i(S),
    Q_i=∑[S⊆I\{i}]p_-i(S)r_i(S∪{i}),
    C_i=A_i+α_i b_i.

The literal prefix map is

    T_a(v)_U,i=a_i Q_i+(1−a_i)A_i+c u_i,
    T_a(v)_B,i=max(Q_i,C_i).

It satisfies D(T_a(v))=δ and T_a(v)_B−T_a(v)_U=d*.
At least two a_j are positive and at least one a_j is STRICTLY
between0 and1. The nonempty root-coalition law has at least two
distinct coalitions of positive probability; its collision mass
is positive. For at least one owner i,

    Q_i=C_i=T_a(v)_B,i.                         (NF1)

There is a nonempty S⊆I\{i} with p_-i(S)>0 and

    r_i(S∪{i})≠r_i(S).                         (NF2)

Root Quit and Continue followed by ANY tail response have precisely
these two different payoffs on that root event. Its owner may have
d*_i=0; neither sign of (NF2) is asserted. Zero and sure rates are
permitted, including α_i=0. No division by α_i is made in the statement.

Every T_x(w), x∈[0,1]⁴,w∈K, lies in K. Consequently

    D(T_x(w))≥δ,
    D(T_x(w))=δ ⇒ T_x(w)_B−T_x(w)_U=d*.         (NF3)

In particular v minimizes G_a(w)=D(T_a(w)) over ALL of K; only
D(v)≥δ, not D(v)=δ, is automatic. These are actual-carrier facts,
not a prescription to execute an unattained pair at an infinite date.

### NF2. Delete only vanishing ORIGINAL strict pre-date mass

Take ANY one of the canonical theorem's produced marked minima q,
with its first active retained atom τ and original retained finite
dates n_k. Its actual finite independent laws p_i^k satisfy

    p_i^k({n_k})→a_i=q_i({τ}),
    h_i^k=p_i^k({t<n_k})→q_i({t<τ})=0.

The second convergence is an old-chart interval-endpoint test: the
left endpoints of the retained intervals converge and their density
likelihoods are uniformly bounded. It is NOT a raw cut inserted
inside the retained atom. The accepted source supplies its zero limit.

For large k, condition p_i^k on {clock≥n_k}, retaining Never, and
call the law z_i^k. This conditions on positive mass1−h_i^k→1,
not on the eventual probability of joint continuation through τ.
It removes the earlier mass and rescales the entire remainder by
1/(1−h_i^k). In total variation TV(p_i^k,z_i^k)=h_i^k.
Independent coupling therefore gives, for every recipient i,

    |U_i(p^k)−U_i(z^k)|≤2M∑_j h_j^k,
    |B_i(p^k)−B_i(z^k)|≤2M∑_(j≠i)h_j^k.       (NF4)

The cap estimate is uniform over EVERY actual finite deadline and
Never, hence remains valid after taking the unrestricted supremum.
It also applies to each particular MOVING original response. Thus
z^k has the SAME limiting prescribed payoff, full cap and terminal
outcome law as p^k. Its normalized root rate is

    a_i^k=z_i^k({n_k})
         =p_i^k({n_k})/(1−h_i^k)→a_i.

The operational estimates agree with
`abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents`
and `abs_quittingContinuationBestResponseValue_sub_le_opponentStoppingLaws`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
Their operational distance is twice TV; (NF4) uses TV. The corresponding
prescribed-law/outcome bound and stopping-law/full behavioral cap
identities in that same file were inspected under their imports.

### NF3. Renumbering does not silently discard a profitable early test

Shift every finite z_i^k date t≥n_k to t−n_k, keeping Never literal.
Call the resulting actual finite profile y^k. Terminal coalitions
and prescribed payoffs are unchanged. An original finite test t≥n_k
corresponds exactly to translated test t−n_k, and Never to Never.

When n_k>0, the extra tests t<n_k against z_-i^k give EXACTLY s_i:
all opponents are at or after n_k. Thus

    B_i(z^k)=max(s_i,B_i(y^k))                  (NF5)

when n_k>0, and equals B_i(y^k) if n_k=0. This equality exposes the
one possible cap difference caused by translating to an initial date.
It is not legal to declare complete-cap invariance from order alone.

The canonical root is maximizing for the bridge owner, but not for
EVERY owner. For a non-root-maximizing owner its later selected cap
has actual moving witnesses strictly beyond n_k; for a root-maximizing
owner root response itself has payoff converging to its cap. More
uniformly, choose an original compact maximizing point of EACH owner.
All are at or later than τ by definition of the earliest active point.
If the selected point is τ its retained witness is n_k. If it is later,
its original moving witness is eventually strictly later than n_k
(or literal Never). By (NF4), their z^k payoffs still tend to the
original B_i, and they are all retained in the translated y^k menu.
Consequently liminf B_i(y^k)≥B_i. Together with (NF5) and (NF4),

    B_i(y^k)→B_i, U_i(y^k)→U_i.                (NF6)

The strict singleton margin B_i−s_i≥δ>0 additionally shows that,
eventually, B_i(y^k)>s_i and (NF5) discards ONLY strictly dominated
early singleton tests. This proof works for a moving retained date
with n_k→∞ and for n_k=0. Arbitrarily late and Never witnesses have
not been cut off. No claim of simultaneous exact finite attainment
of all limiting maximizing points is made.

### NF4. Actual old tails even if some owners stop surely at the root

The profile y^k has root a^k at date0. If e_i^k=1−a_i^k>0,
take its independent own conditional law on {clock>0}, including
Never, and shift each finite t>0 to t−1. If e_i^k=0, choose ANY
actual own tail law, for example pure Never. Let w^k be the resulting
four actual independent tail laws, and v_k=(u^k,b^k) their FULL pair.

There is an exact literal identity, for EVERY k,

    pair(y^k)=T_(a^k)(v_k).                    (NF7)

Indeed each marginal equals a_i^k δ₀ plus1−a_i^k times its shifted
tail; a zero tail coefficient makes the chosen filler irrelevant.
The full cap is max(Q_i(a^k),A_i(a^k)+α_i(a^k)b_i^k): choosing
Continue at0 permits an unrestricted complete tail response, including
all finite dates and Never, not just the prescribed tail clock.

All v_k are ACTUAL pairs at this SAME table and belong to the compact
original carrier K. Extract one common further subsequence v_k→v∈K.
No uniform density bound on a conditional law whose own normalization
tends to0 is needed: this extraction is in the already bounded
eight-dimensional actual pair carrier, not weak-* convergence of those
conditional law densities. By the explicit finite sums and max,
T_(a^k)(v_k)→T_a(v). Equation (NF6) identifies this with the SAME
original minimum pair, not just another small-debt point.

If a_i=1, the original prescribed tail of i is never executed. If it
is the ONLY sure owner, its complete Continue response still depends
on its opponents' genuine conditional tails and is represented by
b_i. Its own conditional tail filler does not determine its own cap.
If another owner is sure then α_i=0 and C_i=A_i, independently of b_i.
With two sure owners ALL α_i=0; one may still extract v, but no
continuation coordinate enters any root cap. All these cases use
actual v_k rather than conditioning a limiting zero-survival event.

The named exact splicing identity
`quittingTerminalSemanticPair_rootThenContinuation`, the definition
`quittingTerminalSemanticPrefix`, and
`continuous_quittingTerminalSemanticPrefix` were inspected in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
`quittingTerminalSemanticPrefix_mem_carrier` in that file supplies
prefix closure for ALL w∈K. Joint a,v continuity used here also follows
directly from the displayed polynomial/max formula; the cited fixed-root
continuity theorem alone is not mislabeled as a joint theorem.

### NF5. A later marked maximum is exactly the complete Continue cap

Take the canonical bridging owner i with maximizing τ and σ>τ.
Root response in y^k has payoff Q_i(a^k)→B_i. Its later original
moving witness at σ has, after (NF4) and translation, payoff
tending to B_i and a date strictly after0, or literal Never.
Write its shifted tail payoff as V_i(t_k,w_-i^k). The exact prefix
response value is

    A_i(a^k)+α_i(a^k)V_i(t_k,w_-i^k)
       ≤A_i(a^k)+α_i(a^k)b_i^k.

The right side tends to C_i; hence C_i≥B_i. But (NF7) and
(NF6) give max(Q_i,C_i)=B_i, and Q_i=B_i. Therefore C_i=B_i
and (NF1) follows without division by α_i, even if α_i=0.

Conversely one may use actual ε_k-best tail replies to w_-i^k,
ε_k→0. Their literal post-root values converge to C_i=B_i;
root values converge to Q_i=B_i as well. Finite-law tails have a
finite reply menu plus Never and in fact admit maximizing pure
replies, but approximate selection already suffices. No SINGLE
tail deadline must attain b_i at the limiting unattained pair v.
No late cap born only in a new limit is selected and silently
identified with an original finite clock.

The singleton margin Q_i=B_i>s_i implies a nonempty opponent
root event with positive probability: with no opponent root mass
Q_i would equal s_i. Choose one such S. On that event root Quit
creates S∪{i}; every Continue-then-tail response, finite or Never,
sees S already absorbing. Row genericity proves (NF2). On the
original finite witnesses the same event probabilities tend to
p_-i(S)>0, and the same fixed nonzero table difference appears.
This retains the genuine PAYOFF-kernel distinction, not only a
numerical expectation equality or an abstract deadline alias.

### NF6. Randomness forces a strictly mixed FIRST root rate

At least two a_j>0 are already supplied by the canonical collision
source. If every a_j belonged to {0,1}, the nonempty set
R={j:a_j=1} would quit surely at τ, all other owners would be
strictly later, and the ORIGINAL prescribed terminal outcome would
be the point mass on R. This contradicts the canonical random law.
Thus some j has0<a_j<1; this conclusion does not depend on whether
the selected tail v retains a particular terminal law.

In fact there are TWO positive nonempty root-coalition probabilities.
Let H={j:a_j=1} and F={j:0<a_j<1}. If H≠∅, choose any j∈F:
H and H∪{j} both have positive probability when all other mixed
owners continue. If H=∅, there are at least two mixed suppliers
j,k, and {j} and {j,k} both have positive probability when the
remaining mixed owners continue. Hence the actual FIRST root law,
not only the entire root/tail outcome law, is random.

No claim that ALL rates are strictly mixed, that c>0, that every
owner is a root supplier, or that the bridging owner itself has
positive root mass follows. The bridge event uses opponents,
so it remains meaningful when a_i=0 or1 and d*_i=0.

### NF7. Exact open finite consumer and a useful nonconsumer identity

The existing finite consumer can now be attacked with a genuine
root bridge (NF1), a strictly mixed rate, the nonzero payoff-kernel
event (NF2), and common d* at EVERY true carrier minimum. To finish
one must construct an actual same-table profile with D<δ or derive
inconsistency. Since every root/tail splice is in K, any strict
inequality D(T_x(w))<δ already gives a literal actual finite/profile
repair after approximating w by realizing laws. The required strict
gap must dominate the approximation error. A changed full pair w
is not automatically the result of a specified playerwise graft of v.

When c>0 (ALL a_i<1), put t_i=(Q_i−A_i)/α_i and
κ_i=a_i/(1−a_i). The global fixed-root objective is exactly

    G_a(w)/c=D(w)+∑_i[(t_i−b_i(w))⁺
                         +κ_i(b_i(w)−t_i)⁺].  (NF8)

It is a CAP-penalized global debt minimum over K, not a weighted
ordinary-debt minimum. At a bridge b_i=t_i. No positive weighted
Nash/quad singleton margin may be applied to v merely by treating
the two hinge slopes as recipient weights: K is not convex, and
the upper-cap coefficient differs from the prescribed-payoff
coefficient away from the hinge. This is an exact objective
re-expression, not a consumer or a new supporting-field request.

The unreviewed next attempt is to exploit this ALL-tail constrained
minimum together with actual response laws. It must avoid replacing
K by its convex hull, promising only cap-control for one recipient,
or transporting normality from an earlier table. The α_i=0 sure-root
arm remains distinct from this c>0 expression.

### NF8. UNIVERSAL finite-prefix bridge at the SAME selected table

The compact NF1 data alone describe ONE supplied minimum. Common d*
and within-row distinct rewards do NOT logically recreate the canonical
theorem's random-law/bridge conclusion at another minimum. For example
a punishment-graft argument that preserves the pair and removes its
sole bridge needs that conclusion again at the NEW source. The following
universal statement is what the ENTIRE canonical table theorem supplies;
it is not inferred merely from the one NF1 witness.

Fix the ONE canonical final table r, its K, δ and d*. Then

    FOR EVERY x∈[0,1]⁴ and w∈K:
      Σ_i x_i>0 and D(T_x(w))=δ
      ⇒ |{j:x_j>0}|≥2, some0<x_j<1,
         and some i satisfies
           Q_i(x)=A_i(x)+α_i(x)b_i(w)=B_i(T_x(w)).  (NF9)

The nonempty root-coalition law is random, and for that i some
nonempty S⊆I\{i} has p_-i(S;x)>0 with different fixed rewards
r_i(S∪{i}) and r_i(S). Root Quit and ANY Continue-then-tail reply
therefore have genuinely different PAYOFF kernels. As before i
may have zero debt, x_i may be0 or1, and α_i may vanish. ALL
minimum pairs—not only the pairs in (NF9)—have debt d*.

**Proof.** Fix x,w AFTER selecting the canonical table. Because w∈K,
choose actual finite-support tail profiles h^k with pairs w_k→w.
Such finite approximants exist for ANY carrier pair: first approximate
by an actual profile, then TV-truncate its finite clock tails to Never,
using the uniform complete-cap estimates in NF2. No old marked source
law must be reconstructed. Prefix the EXACT same fixed x to h^k at
date0, shifting each finite h^k date one step forward. The resulting
actual finite profiles y^k have pairs exactly T_x(w_k), hence
D(y^k)→D(T_x(w))=δ. Thus they are genuine globally minimizing
sequences at the SAME final table, not merely constrained minima.

Their FIRST mixture atom is date0 with fixed positive length

    m=Σ_i x_i/4>0.

In the quantile producer its whole raw interval is [0,m], its
retained midpoint is τ₀=m/2, and its own limiting masses are x_i.
It is the first retained prescribed point in EVERY subsequence with
the producer's convergences. The finite-tail chart may otherwise
vary arbitrarily; none of that affects this fixed positive interval.
It follows in particular that no likelihood normalization tending
to zero or moving retention convention can dissolve the root atom.

Apply the canonical EVERY-produced-minimum theorem to any such
produced marked source q. Its earliest active point τ is its
FIRST prescribed stage with no prescribed mass before it. The
fixed τ₀ atom gives prescribed mass>0 there; there is no prescribed
point before τ₀. Therefore τ=τ₀. An alleged τ>τ₀ would contradict
the no-preactive-mass conclusion, and τ<τ₀ would contradict the
theorem's requirement that τ itself be a prescribed positive atom.
This step uses the canonical UNIVERSAL source property, not the
earlier one-witness finite statement.

The theorem supplies at least two own positive atoms at τ₀, hence
at least two positive x_j, and a random ORIGINAL terminal law.
If all x_j were bits, a nonempty sure root coalition would be the
deterministic prescribed terminal outcome, impossible. The two
positive root-law labels follow by the same H/F case split as NF6.

BG supplies some recipient i and an original compact later cap
point σ>τ₀. Its root response gives Q_i(x)=B_i(T_x(w)). Original
finite moving witnesses for σ are eventually strictly after date0
or literal Never: the retained [0,m] atom is uniformly isolated,
so a different later compact point cannot be represented by date0.
Their full prefix values tend to that SAME cap. Every such response
has the exact value

    A_i(x)+α_i(x)V_i(t_k,h_-i^k)
       ≤A_i(x)+α_i(x)b_i(w_k),

including the literal Never response. Therefore C_i(x;w)≥B_i′.
Exact splicing and w_k→w give B_i′=max(Q_i(x),C_i(x;w)); hence
C_i=Q_i=B_i′. The proof does not divide by α_i or suppose that
the limiting b_i is attained by one tail deadline.

Since the true minimum cap satisfies B_i′−s_i≥δ>0, Q_i(x)>s_i.
Some nonempty opponent root coalition has positive probability;
otherwise Q_i(x)=s_i. Its two response kernels give S∪{i} and S,
and row genericity supplies the nonzero fixed payoff difference.
The same positive event has the SAME probability p_-i(S;x) on
EVERY finite prefixed witness, because x is fixed exactly. Finally,
ALL-minimum debt rigidity supplies d* directly at T_x(w). ∎

**Boundary and consumption scope.** The nonzero-root condition is
essential. For x=0 and ANY true minimum w=(u,b), singleton margin
gives b_i>s_i, so T_0(w)=w but Q_i(0)=s_i<C_i(0;w)=b_i for
every i. There is no root bridge in this all-Continue presentation.
This does not contradict NF9 or the first prescribed-stage theorem.

NF9 can be invoked at EVERY NEW minimum-preserving actual graft
whose first root remains nonzero, without storing its whole calendar.
An actual tail graft supplies a pair w′∈K, or a proven actual sequence
supplies its closure pair; then D(T_x(w′))=δ triggers NF9. A new
tail offered only as unattained numerical values, without carrier
membership, cannot be used. If the root is also changed, use its new
nonzero x′, not the old root's bridge. Mere near-minimality does not
give the exact equality in NF9.

The canonical table's typed93 no-contact/sign facts are NOT recovered
from NF9, row genericity and debt rigidity. They remain separate
inputs if a later argument changes reward tables. A finite consumer
for arbitrary tables satisfying these displayed UNIVERSAL minimum
constraints would be sufficient for UE, since the canonical selection
produces them from any no-UE table. No pointwise preservation of an
arbitrary earlier game's minimizing laws or normality is asserted.

## Exact finite-common-menu Nash selection fails for a whole solved table

### FN1. Complete game, probability mode and claim

This is a COMPLETE ordinary-mathematical falsifier of one candidate
producer, not a positive-gap game or a Fin4 source reduction. There
are THREE players I=ℤ/3ℤ. A player loves its predecessor ℓ(i)=i−1.
For every nonempty quitter coalition S, define

    r_i(S)=1                 if i∈S,
           3                 if i∉S and i−1∈S,
           0                 otherwise.

Never pays0. The complete twenty-one terminal entries are

    S        r(S)
    {0}      (1,3,0)
    {1}      (0,1,3)
    {2}      (3,0,1)
    {0,1}    (1,1,3)
    {0,2}    (1,3,1)
    {1,2}    (3,1,1)
    {0,1,2}  (1,1,1).

For ANY nonempty finite COMMON menu F⊆ℕ, consider the normal-form
terminal game whose pure actions are F∪{Never}, mixed independently.
The payoff is the original first-quitter terminal payoff, NOT a
finite-horizon average. The claim is that this game has exactly ONE
Nash LAW profile: everybody puts mass1/3 at n=max F and mass2/3 at
Never. Its unrestricted full debt is4/3, irrespective of |F| or
the calendar gaps. Therefore EVERY exact Nash selector from EVERY
such finite common menu fails to approximate unrestricted terminal
Nash. Approximate menu Nash selection is NOT excluded.

### FN2. No sure root at any continuation

At any allowed date write p_i for the conditional own Quit probability.
Let u_i be its own conditional continuation payoff. Since every
participant reward is1, the root Quit value is Q_i=1. With
j=i−1 and k=i+1, its prescribed Continue value is

    C_i=3p_j+(1−p_j)(1−p_k)u_i.

Any root Nash has p_i<1 for EVERY i, regardless of u. Indeed, if
p_i=1, player i+1 loves that sure quitter, so its Continue value
is3 and its Quit value1. Thus p_(i+1)=0. Player i−1 dislikes
the sure quitter i while its loved opponent i+1 is quiet, so
its Continue value is0 and its Quit value1. Thus p_(i−1)=1.
But player i then loves the sure quitter i−1, so its own Continue
value is3, contradicting p_i=1.

This handles arbitrary off-path own continuation laws at a sure
coordinate; all relevant Continue comparisons have opponent survival
factor0, and do not rely on the own continuation choice.

### FN3. The last menu date has one Nash row

At the last allowed date the only continuation is Never, so u=0 and

    Q_i−C_i=1−3p_(i−1).

By FN2 no rate is sure. If p_i=0, its Continue optimality forces
p_(i−1)≥1/3. That predecessor is strictly mixed and hence forces
p_(i+1)=1/3. The latter owner is now strictly mixed and forces
p_i=1/3, a contradiction. All rates are strictly mixed and the
three indifference equations give p_i=1/3.

Conversely that row is Nash, since each player's Quit and Continue
values are1. Its prescribed payoff vector is u=(1,1,1).

### FN4. Every earlier date is quiet

Suppose the conditional tail Nash payoff is (1,1,1). Then

    G_i=Q_i−C_i=p_(i+1)−2p_(i−1)−p_(i−1)p_(i+1).

FN2 again rules out sure rates. Any positive rate is strictly mixed
and has G_i=0; a zero rate has p_iG_i=0 as well. Consequently

    0=Σ_i p_iG_i
      =−(p₀p₁+p₁p₂+p₂p₀)−3p₀p₁p₂.

Every term on the right is nonpositive, so at most one rate is
positive. If only p_i>0, the quiet player i−1 has G_(i−1)=p_i>0
and strictly prefers Quit. Thus all rates must be0. Conversely,
with all rates0 both root choices give1, so the quiet row is Nash
and preserves the tail payoff (1,1,1).

Here backward induction applies to NORMAL-FORM Nash on complete
independent stopping laws, not an assumed subgame-perfect selection.
Any such Nash induces a root Nash, by unilateral changes to the
own root mixture with the old own conditional tail retained.
FN2 gives c=∏(1−p_i)>0. Keeping the root fixed and changing only
one conditional tail changes its total payoff by c times the tail
payoff change. Therefore the prescribed tail must itself be a
restricted Nash. Conversely a root Nash over the old tail Nash
payoffs, together with that tail Nash, bounds every complete own
law through the exact root max(Q,C) formula.

Induction through the ordered allowed dates therefore gives the
unique law in FN1. Missing natural-number dates are irrelevant to
the restricted game; the argument applies to ANY finite common F.
The all-quiet earlier choices are uniquely forced even though each
individual is indifferent when all three are quiet.

### FN5. Its COMPLETE unrestricted caps

For the unique law, the prescribed payoff is

    U_i=(1/3)·1+(2/3)·[3·(1/3)]=1.

A pure finite reply before n gives own solo1. A reply at n always
participates and gives1. Any finite reply after n receives3 if
its loved opponent quits at n, and receives own solo1 when both
opponents chose Never. Hence its payoff is

    3·(1/3)+(2/3)²=13/9.

A Never reply receives3 with probability1/3 and otherwise0, so
it gives1. These cases exhaust ALL finite deadlines and Never;
affinity of the actual complete-law payoff bounds arbitrary own
behavioral deviations by their pure sup. Thus

    B_i=13/9,        d_i=4/9,        D=4/3.

The original joint-Never mass is8/27 for every menu. Enlarging the
menu only moves the unique finite mass to its new maximum; the
omitted response is always a still later finite deadline. For the
empty menu, the only law is all Never and its full debt is3.

### FN6. Explicit ACTUAL unrestricted exact equilibrium

At natural date3k+j only player j has Quit hazard1/2; the other two
Continue. The resulting independent complete laws are

    q_i(3k+i)=2^(−k−1),       q_i(Never)=0.

A full period has solo outcome masses1/2,1/4,1/8 and survival1/8.
Consequently its complete first-quitter distribution is
(4/7,2/7,1/7) on the singleton labels, and

    U=(1,2,1).

To verify EVERY behavioral deviation, define the live-phase
potential v_i(j)=2 if i=j+1, and1 otherwise. A Quit response pays1
even if the scheduled opponent also quits, so it is≤v_i(j).
For Continue:

    i=j:    next-phase potential1 equals current potential1;
    i=j+1:  (1/2)·3+(1/2)·1=2;
    i=j−1:  (1/2)·0+(1/2)·2=1.

Every own action therefore satisfies the one-step potential bound,
and the prescribed own action attains equality. Against an arbitrary
behavioral deviator, its TWO opponents each face one independent
half-Quit chance per period. Their joint survival probability is
at most4^(−K) after K periods, regardless of the own reply.
The bounded remaining live potential contributes at most2·4^(−K),
which vanishes. Iterating the one-step bound therefore proves
ALL actual unilateral terminal payoffs≤v_i(0). The prescribed law
attains this vector, either by the displayed singleton distribution
or by equality and its own joint-survival decay. Thus

    B=U=(1,2,1),       D=0.

This exact terminal equilibrium suffices to show the TRUE global
gap is0. TV-truncating each geometric finite law to Never after
K periods also gives actual finite-menu profiles with full debt→0
and payoff→(1,2,1), uniformly over ALL finite/Never replies. FN4
shows those profiles cannot be exact restricted Nash. Hence this
example does NOT obstruct finite-law approximation or an
approximately-Nash producer with a separately proved full-cap bound.

### FN7. Narrow source/overlap audit and direction change

The named unconditional theorem
QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff in
UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean
already consumes this table's singleton matrix with coefficient
sequence γ=(0,−1,2), arbitrary nonsingleton rewards. The balance
equation −1+2s=0 gives s=1/2. The definition
CyclicSingletonTailData.coarse in
UniformEquilibrium/Quitting/Cycles/CyclicSingletonTailProducer.lean
agrees with the displayed cyclic payoff. The inspected
quittingSingletonMatrix in
UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean
is exactly r_i({j})−r_i({i}). No new UE class or producer is claimed;
FN6 is an independent elementary full-response verification.

This is NOT the literal FTV1996 Example2: example2Data in
Literature/future/FleschThuijsmanAndVrieze1996.lean is a TWO-player
3×2 absorbing action table, with one live entry and the recorded
reward matrices. This test shares the singleton rows of the
FTV1997 three-player table, but its nonsingleton rows DIFFER:
terminalReward in
UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/Credibility.lean
has pair01=(1,0,1), pair02=(0,1,1), pair12=(1,1,0) and grand0,
rather than the four collision rows in FN1. Literature's paper
transcription is evidence about the published table, not an adapter
claim for the modified collision completion. This bounded comparison
does NOT assert global bibliographic novelty for finite-menu selection.

The chosen finite-menu neighborhood was also checked:
exists_exactFiniteDeadlineTimingNash in
UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean
is unconditional exact menu existence, not full-cap control.
The existing SinglePivotFiniteMenuRegression in
UniformEquilibrium/Diagnostics/Quitting gives ONE bad menu Nash,
whereas FN1–FN5 rule out EVERY exact selector for this ONE complete
table over ALL finite common menus. No matching whole-selector
statement was found by the narrow menu/deadline search in that
diagnostics subtree and the cyclic three-player example subtree.
No Lean check or whole-tree novelty audit was performed here.

The retired implication is therefore precise: increasing common
finite pure-deadline menus plus selecting exact terminal Nash laws
does not by itself produce unrestricted small debt, even when
exact unrestricted Nash exists. Approximate menu equilibria,
player-specific menus, completion mechanisms and actual global
minimum comparisons remain unexcluded. No dummy lift of this
three-player table to Fin4 is claimed: a fourth player's Quit can
absorb, so a zero recipient row alone is not a transparent dummy.

The next active question returns to the c>0 TRUE-carrier objective
in NF7 and the UNIVERSAL minimum-prefix constraint NF9. Any
successful repair must price all old and new response caps, not
merely enlarge a Nash menu whose continuation omits later finite
responses.

## Unsupported-root recipient pricing: a complete fixed-source price and its obstruction

### CP1. The tempting global-row consumer

Fix the SAME canonical unit-cube table, true global minimum δ>0,
common minimum debt a, and a nonzero minimum prefix T_q(v).
Suppose owner i has q_i=0 and a root cap, so Q_i=B_i′; in particular
this covers the surviving c>0 unsupported sole-bridge mode.
Let γ=δ²/8. In recipient row i define the unit-cube endpoint

    h_i(S)=+1 if i∈S, and−1 otherwise,

leaving Never0. Interpolate that row toward h, leaving all other
recipient rows unchanged. This is a globally legal reward-table
direction; it is not a law change at the old table.

There is a COMPLETE fixed-source price, not merely a response
derivative. Against the old independent laws the h-root response
pays1. Since i has no root mass, the h-prescribed payoff satisfies

    U_i^h≤−(1−α_i)+α_i·1=2α_i−1.

The old root response satisfies

    Q_i−s_i
      =Σ_(S≠∅)p_-i(S)[r_i(S∪{i})−s_i]
      ≤2(1−α_i).

The actual quadratic minimum margin gives
2(1−α_i)≥δ+γ. Since a_i≤δ, the h-selected root regret is therefore

    1−U_i^h≥2(1−α_i)≥a_i+γ.

For EVERY interpolation parameter η∈[0,1], recomputing the new
FULL cap and merely lower-bounding it by this legal root response
gives

    d_i^η(old laws)≥(1−η)a_i+η(1−U_i^h)
                  ≥a_i+ηγ,
    D^η(old laws)≥δ+ηγ.

The same calculation holds at the marked source using its literal
original finite witnesses and limiting kernels; it does not need
cap attainment at a tail clock. The direction stays in the reward
cube, and the margin is from the FINAL same table. This calculation
is complete ordinary mathematics, not a new consumer or an export.

### CP2. Why it cannot uniformly price the active face

The desired next implication would be that NEW moving minimizers
must pay this source price. That implication is unproved and cannot
follow from the fixed-source calculation alone.

The zero-debt boundary supplies a concrete ACTUAL obstruction to
any single-recipient ALL-active-branch version. For an arbitrary
bounded recipient reward direction k, retain the old source and
write the selected regret slope at test t as

    L_i(t)=V_i^k(t,q_-i)−U_i^k(q).

If a_i=0, the old prescribed law q_i is supported, up to null
sets, on its FULL old maximizing test set: its expected nonnegative
old regret is0. Reward affinity and independence give EXACTLY

    ∫L_i(t)dq_i(t)=0.

Hence one cannot have L_i(t)>0 uniformly on that whole active
set. For the CP1 direction its unsupported ROOT branch has a
strictly positive slope, while some OWN-supported later active
branches necessarily have nonpositive slopes. Never is included
if it has prescribed mass; finite calendar endpoint mass remains
separate. No hypothesis of unique response attainment, finite
support, or positive prescribed mass at the root is being made.

The bridging owner can have zero debt in the genuine canonical
source, so this is not a removable boundary. A positive fixed-source
MAX slope is not a positive price of EVERY branch which a moving
law can select. CP1 did recompute the new cap at FIXED laws, but
does not control the law movement before taking the infimum.

### CP3. Minimal exact envelope falsifier

For clarity, the failed optimization implication already has the
two-branch finite algebraic model

    F(t,η)=δ+max(t+η,−t−η)=δ+|t+η|.

At η=0 the unique current minimizing t is0; at that FIXED point
F(0,η)=δ+η. Nevertheless, for every small η>0 the legal moving
point t=−η has F=δ. Both branch expressions are affine. A rigid
unique old minimum does not repair the inference.

This model is NOT an actual positive-gap quitting table and does
not refute a statement using all of the genuine source geometry.
Its role is only to falsify the attempted envelope step from CP1
and cap affinity. CP2 supplies the actual zero-debt active-face
reason that mixed-sign branch slopes cannot simply be discarded.

### CP4. Surviving statement and changed mechanism

The fixed-source unit-row price CP1 is valid. A source-neighborhood
or worst-table consumer would additionally have to control the
NEW maximizing branch and simultaneous old-law movement, or
derive a positive aggregate price over the full cap-selection
face. Neither is produced by CP1–CP3. The sole-bridge mixed-own-rate
fiber reduction and nonlinear-wall no-go already recorded in
NOETHER RM2–RM4 were checked before pursuing this direction; they
are not new findings here.

No new export or paid-port claim follows. The single-row envelope
route is retired in this form. The next investigation is genuinely
global: whether an existing positive recursive/absorbing/quitting
equilibrium theorem can consume the compatible positive-table
normal form, with its original independent behavioral and uniform
payoff semantics. Merely making rewards nearly constant cannot
itself shrink original exploitability after inverting the scales.

## Positive near-constant rewards: primary theorem scope and an exact missing-hypothesis test

### PL1. Standalone question and probability mode

Suppose a Boolean Fin4 quitting table has, for every nonempty coalition,

    |r_i(S)−1/2|≤ρ<1/2,       r_i({i})=1/2,

and Never pays0. Each player still has exactly ONE observed Continue
action and ONE Quit action. Players independently randomize their own
complete behavioral strategies. Does a primary positive recursive,
absorbing or quitting-game existence theorem produce unrestricted
terminal ε-Nash profiles at every ε>0 in THIS game, hence one fixed
uniform payoff by the tracked semantic selection theorem?

This section assumes the displayed normal form only conditionally.
It neither proves nor duplicates the independently investigated
counterexample-preserving normalization. It is a bounded primary-source
scope check, not a claim that no other theorem exists in the literature.

### PL2. The applicable ordinary quitting theorem still requires payoff order

Solan–Vieille, *Quitting Games* (2001), Theorem1.2 assumes positive
own singleton rewards, normalized to1, and participant rewards no larger
than own singleton. It produces cyclic subgame-perfect approximate
equilibria. Proposition2.2 permits a broader hypothesis: at EVERY
continuation in its specified compact low-coordinate set, select a
one-stage Nash root which is allContinue, or has a positive quitter
whose root payoff is at most its own singleton. Positivity alone is not
that root-selection hypothesis. See the
[primary paper, Theorem1.2 and Proposition2.2](https://www.math.tau.ac.il/~eilons/quitting19.pdf).

The exact tracked conditions are QuittingUnitSoloExit,
QuittingCappedJointExit and QuittingWeakSoloExitPreference in
UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean.
The ordinary production declaration
exists_uniformEquilibriumPayoff_of_soloExitPreference and its upstream
exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference are in
UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean.
Their statements and the delegation from Literature/SolanAndVieille2001.lean,
theorem1_2, were inspected under the displayed imports, without a Lean
build. In particular this existence result is already implemented;
reidentifying its payoff condition is not a new consumer.

For a positive row affine transformation r_i′(S)=θ_i r_i(S)+β_i,
θ_i>0, one has the exact finite-coalition identity

    r_i′(S)−r_i′({i})=θ_i[r_i(S)−r_i({i})].

Thus making these numbers small does not change an above-own
participant reward into the required below-own reward. This finite
identity makes no strategic assertion about a transformation leaving
Never0 rather than translating Never as well.

### PL3. Arbitrarily near-constant positive tables can fail even the broader root criterion

Here is a complete Fin4 table, not a positive-gap example. Fix
0<η<ρ<1/2 and put, for EVERY i and nonempty S,

    r_i(S)=1/2+η if i∈S and |S|≥2;
           1/2 otherwise.

All60 finite rewards lie withinρ of1/2 and all own singletons
equal1/2. In the one-stage game with continuation
w_i=1/2−ζ for every i, where 0<ζ<1/2, fix arbitrary independent
opponent root rates and write α_i=P(no opponent quits). Then

    Quit_i=1/2+η(1−α_i),
    Continue_i=(1/2)(1−α_i)+(1/2−ζ)α_i,
    Quit_i−Continue_i=η(1−α_i)+ζα_i>0.

Quit is strictly dominant for every player. Consequently the sole
one-stage Nash root is allQuit, and EVERY positive quitter's payoff
is1/2+η>r_i({i}). Scaling all finite rewards and w by2 puts
own singletons at1 and this w inside the compact set in
Proposition2.2, but there is still no low-paid active quitter and
allContinue is not Nash. Thus the displayed positive near-constant
normal form does NOT by itself supply that proposition's complete
root-selection input.

This is a sharp missing-hypothesis test, not failure of equilibrium
existence: allQuit is an exact unrestricted equilibrium of this same
table. If a player continues instead of joining the other three
date-zero quitters, it receives1/2 rather than1/2+η; later behavior
cannot undo their absorption. Hence its true gap is0. The test is
not asserted to satisfy the canonical typed93 no-contact screens.

### PL4. Positive general quitting results require unavailable information or actions

Solan–Solan, *Sunspot Equilibrium in Positive Recursive General
Quitting Games*, arXiv1803.00878, Definition2.3 and Theorem2.5,
give approximate equilibria with an independent public signal at
each date. Their Theorem2.6 for Boolean positive quitting games
leaves either such a low-hazard sunspot construction or a uniformly
absorbing limit of stationary discounted equilibria; Lemma2.7
consumes an absorbing limit. Neither positivity nor the displayed
reward radius supplies that absorbing alternative. See the
[primary preprint, Section2](https://arxiv.org/pdf/1803.00878).

Solan–Solan–Solan, *Jointly Controlled Lotteries with Biased Coins*
(2020), Theorem3.1 removes the public correlation for positive
recursive general quitting games when TWO players each have at
least TWO continuing actions. Section3 uses those observed continuing
actions for its pre-absorption lotteries. Its footnote states the
uniform conclusion too. See the
[primary paper, Section3](https://www.math.tau.ac.il/~eilons/JointlyPublished.pdf).
The Boolean game fails the action-cardinality hypothesis for
every player. Merely giving Continue two observable names changes
the public information and is not a strategy-preserving padding.

The corresponding Literature/future/SolanAndSolan201819.lean
and Literature/future/JointlyControlledLotteriesWithBiasedCoins.lean
were inspected: they are empty source-audit namespaces, not checked
versions of these theorems. No producer is borrowed from those files.

The exact agency obstruction to THIS lottery adapter is elementary.
At a fixed date t, on the event that the original Boolean game is
still alive, its observed past is the ONE deterministic word
(Continue,Continue,Continue,Continue) repeated t times. Every
publicly history-measurable variable is therefore constant on
that event. A common lottery output announced at a deterministic
date before absorption cannot have two values of positive
conditional probability. A public-history stopping rule for ending
a communication block also has a deterministic first live date:
its test receives the same sole live word at every date. Private
coins are not public observations, and a revealed Quit absorbs
before any later living continuation. This rules out simply
compiling the inspected public-signal construction by duplicate
Continue labels; it does NOT rule out a different ordinary producer
which avoids those signals altogether.

### PL5. A recent ordinary positive-absorbing theorem excludes the Boolean absorption graph

Solan–Vieille, *Undiscounted Equilibrium in Positive Recursive
Absorbing Games with Non-Rectangular Absorption Structure*,
arXiv2512.04306, Definition2.6 and Theorem2.8, give an ordinary
equilibrium payoff when EVERY connected component of nonabsorbing
pure action profiles is nonrectangular. Remark2.9 gives the uniform
version. See the
[primary preprint, Section2.3](https://arxiv.org/pdf/2512.04306).

In our original Boolean game the set of nonabsorbing pure profiles
is the singleton {allContinue}=∏[i] {Continue_i}. Its sole
component is rectangular. Changing finite rewards, their signs or
their radius leaves this absorption graph unchanged. Thus this
ordinary theorem does not consume the proposed normal form.
The adjacent Literature/future/SolanAndVieille2025.lean and
Literature/future/SolanAndVieille2025b.lean were inspected and are
empty audit namespaces. No Lean theorem or acceptance status is
inferred from their names or from the preprint.

### PL6. The LCP alternative and inverse-accuracy bookkeeping are unchanged

The accepted May2018 manuscript of Solan–Solan,
*Quitting Games and Linear Complementarity Problems* (2020),
Theorem2.13 gives ordinary ε-equilibria in its non-Q branch and
sunspot ε-equilibria in its Q branch, with the stated normal-player
and zero-LCP hypotheses. The accepted text, rather than arXiv v1's
different numbering and normal-player definition, was inspected in
the [primary manuscript](https://econ.biu.ac.il/sites/econ/files/seminars/sunspot11.pdf).
Theorem2_13_nonQ in Literature/SolanAndSolan2020.lean states the
ordinary branch under SoloExitNormalized, TablePayoffsBounded,
HasNormalPlayers, no nontrivial zero projective-LCP solution and
non-Q. Its implementation and imports were inspected narrowly.

For the standard singleton-difference matrix Γ_ij=r_i({j})−s_i,
the above row change gives Γ′=diag(θ)Γ. Standard Q is invariant
under this positive row scaling: for EVERY offset q′, the same z
solves q′+diag(θ)Γz≥0 and complementary iff it solves
diag(θ)⁻¹q′+Γz≥0 and complementary, because each coordinate
residual has been multiplied by a positive number. This ordinary
one-line argument uses the EXACT definitions StandardLCPSolution
and IsStandardQMatrix in
UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean,
which were inspected. It does not import the paper's normal-player
set from an unnormalized table. In particular no inference
“all finite rewards positive, so the old hard Q matrix disappears”
is valid. The normalized differences, not their uncentered signs,
enter the criterion.

Finally suppose one bounds debt at orderρ by choosing a simple
profile in a near-constant table. To transport a recipient's error
back through scaleθ_i one must divide that error byθ_i; an O(ρ)
bound need not be o(θ_i). As a transparent finite-law test, apply
r_i′(S)=1/2+θ_i[r_i(S)−s_i] to a prescribed profile and to a
unilateral deviation BOTH absorbing almost surely. Their exact
payoff difference is θ_i times the old difference; the common
1/2 cancels. Therefore a positive old gain g_i appears as a small
new gain θ_i g_i, not as a gain tending to0 after inversion.
This statement deliberately restricts both laws to a.s. absorption:
for laws with Never mass, the row translation has an additional
absorption-probability term and cannot silently be treated as a
strategic affine equivalence.

### PL7. Decision and concrete next question

The inspected primary theorems do not produce ordinary equilibrium
from the displayed Boolean positive near-constant hypothesis alone.
The exact missing inputs are, respectively, payoff order or a
complete low-paid active-root selector; public correlation;
two observable continuing actions at each of two players;
a nonrectangular absorption graph; or a non-Q singleton matrix.
PL3 is an exact falsifier of the most plausible automatic-selector
shortcut. No full literature census, new equilibrium class,
counterexample to Fin4 UE or export is claimed.

The research returns to the SAME-table c>0 carrier comparison in
NF7, retaining the universal minimum-prefix constraint. The next
concrete question is whether all-minimum debt rigidity imposes
an actual product-law restriction on the ENTIRE simultaneous
root/later active face, beyond one selected bridge and the
fixed-source row price retired in CP2. A single favorable selected
cap price cannot stand in for that face.
