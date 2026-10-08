# Nonbijective singleton sources beyond a column-sign cone

Author: CODEX_BROUWER. Ordinary mathematics, not Lean-checked.

## Current full-goal status

The full Fin4 uniform-equilibrium conjecture is OPEN. The strongest
accepted source used here is
[FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE.md](../exports/FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE.md).
It selects ONE fresh table from any counterexample: its unrestricted
SUM-debt minimum is positive, its absorbing infimum is strictly larger,
all minimum debts and original Never masses are positive, and a random
nonsure first collision has a paid root-to-later-finite PAYOFF-kernel
bridge. No row Nash, minimum tail or attained tail deadline is assumed.
The earlier canonical
[random-collision](../exports/RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md)
and [four-finite](../exports/FOUR_FINITE_CLOCKS_AT_ORIGINAL_MINIMA.md)
source results remain distinct; their tables are not silently identified.

The exact missing consumer is an ACTUAL independent stopping-law
competitor with lower full debt, controlling EVERY finite deadline and
Never, or another global contradiction. Completed comparison ledgers
and exact architecture falsifiers below have not supplied one. SG's
actual end-Never graft has an independent focused PASS; the other live
supporting derivations retain their explicit ordinary/unreviewed status.

The retained independent global source is RS: the native ZERO-OWN
ABSORPTIVE infimum, not the native unrestricted gap (AllNever already
has zero debt). At a positive Euclidean-ball maximum, source-switching
comparison yields a radial convex combination of at most57 complete
response-minus-prescribed probability ledgers from SAME-table minima.
Its averaged prescribed law contains every singleton and cannot consist
entirely of deterministic minima. Existing SAME-table completion permits
finite-support, all-four-finite realizing laws at each index. RS is
COMPLETE ORDINARY, UNREVIEWED supporting mathematics, not a UE theorem
or an independently reviewed counterexample-class elimination.

RS11 now uses the genuine native absorbing floor: an occupied-prefix
comparison forces positive ORIGINAL terminal collision probability in
EVERY selected all-four-finite realizing sequence, at that SAME table.
Its full arbitrary-root, negative-cap and sure-row argument is COMPLETE
ORDINARY, UNREVIEWED. It supplies no paid owner, atom floor or legal
debt improvement. The next step is to change that actual collision mass
while upper-pricing all born caps, not to refine its lower bound.

The subsequent boundary-penalty producer test BP is COMPLETE ORDINARY,
UNREVIEWED. It falsifies EVERY exact finite-calendar Nash selector with
arbitrary strictly negative terminal payments tending to zero, followed
by private independent repetition, on the already-solved RZ table.
All repeated finite/Never caps are evaluated exactly. Thus absolute
disappearance of the terminal perturbation is not sufficient; the next
construction must control its deleted-player, absorption-relative seam.
This is an architecture falsifier, not an original positive-gap example
or an additional reduction of the RS source.

These ledgers are not one playable profile or a public signal. RS10
retires pure-coalition and single-owner-geometric consumption of balance
plus positive deliveries alone; its exact test is solved and violates
the genuine minimum cap margin. The live next question is whether the
ALL-law floor and that strict margin force a legal independent
whole-law substitution with all born caps priced. No radial identity,
count balance or selected response lower ledger is used as a cap upper
bound. The live boundary question now permits nonvanishing terminal
payments but must actually produce negligible deleted-player seam
charges, not assume a favorable Nash selector. All older unique proofs,
tests and objections are retained below.


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

### PL8. The 2026 APS extension does not supply the missing atomic selection

Ashkenazi-Golan, Krasikov, Rainer and Solan, *The APS approach for
undiscounted quitting games* (2026), defines Flesch paths with only
one continuously active quitter. Definition2.9 requires its payoff
at that quitter to be0. Theorem2.11 realizes sequentially perfect
paths; it does not produce their nonemptiness. Theorem4.10 adds a
circuit hypothesis to the characterization. The introduction explicitly
restricts the path class; simultaneous atomic exits are not included.
See the [primary article, Sections2 and4](https://link.springer.com/article/10.1007/s00182-026-00982-6).

The paper's own-zero normalization subtracts the own reward ALSO
from Never; it is not ZE's native table, which keeps Never0. At the
native zero-excess source the original strict margins give
u_i=B_i−s_i>0 for ALL i. Such a vector cannot itself be the starting
payoff of the paper's sequentially perfect Flesch path, by its stated
zero-coordinate condition. A different attainable payoff or a produced
atomic path would still be needed. No new ordinary existence theorem
or completeness claim is imported.

## Proper finite-menu Nash is not an all-four-finite approximation producer

### PF1. Question and exact scope

The four-finite source theorem permits a new original minimum realizing
sequence in which every prescribed clock is finite almost surely, and even
has finite support at each index. Does selecting an EXACT Nash equilibrium
of a common finite deadline game, with Never EXCLUDED, approximate the
unrestricted full debt infimum in that class?

No. The following exact Fin4 example satisfies positive own singletons
and every completion row witness, has all-four-finite full-debt infimum0,
but EVERY exact Nash selection in EVERY nonempty common finite deadline
menu has unrestricted debt8. This is a supporting architecture failure,
not a new counterexample-class reduction or UE claim. The earlier FN
failure already retired the corresponding finite-menu architecture with
Never included; this test prevents reintroducing exact Nash selection
merely because the new source has four proper clocks. It is not an
obstruction to approximate Nash selections or direct whole-law minimization.

### PF2. Complete sixty-entry table and proper approximation

Core owners are 0,1,2 modulo3, with love(i)=i−1. For i in the core set

    r_i(S)=1 if i∈S;
           3 if i∉S and love(i)∈S;
           0 otherwise.

For the fourth recipient set

    r_3(S)=1 if 3∈S;
           0 if S={0};
           3 otherwise.

These rules specify every nonempty coalition and all sixty rewards.
All own singletons are1. Each core row has a distinct passive singleton
with reward0, and row3 has witness r_3({0})=0. Thus every recipient
has the actual row condition r_m({j})≤s_m. All rewards are nonnegative.

There is an explicit unrestricted exact terminal Nash profile: schedule
core owners 0,1,2 repeatedly, with ONLY the scheduled owner quitting
with hazard1/2 at each date; owner3 uses Never. The core calculation
is the FN cyclic calculation: phase payoffs to a core recipient are
2 when its loved owner is scheduled and1 at its other phases. Each
scheduled owner is indifferent between quitting and continuing; every
other core owner weakly prefers continuing. The vanishing geometric
opponent survival bounds every unrestricted response, including Never.

The first core singleton probabilities, starting at phase0, are
(4/7,2/7,1/7). Row3's Never values in phases0,1,2 are respectively

    (9/7,18/7,15/7).

They satisfy the literal one-step Continue recurrences: at phase0,
V=V(next)/2; at the other phases, V=3/2+V(next)/2. Any Quit reply
pays1, below all these phase values. The same geometric survival
argument bounds EVERY finite and Never reply by its initial Never
value. Thus this is a full four-player terminal Nash profile with
payoff (1,2,1,9/7) and debt0.

It has THREE unchanged proper core anchors. Move owner3's Never law
to a sufficiently late finite date. Every prescribed payoff and each
full cap is screened by an unchanged proper opponent; the error tends
to0 uniformly over all replies. Hence the entire pair is approached
by four-proper profiles and the four-finite debt infimum is0. Truncate
the core finite tails to late FINITE dates for finite-support versions.
This is a solved table, not a genuine positive-gap source.

### PF3. No absorbing root Nash exists for any nonnegative continuation

Write core root rates q_i and dummy rate y. All member rewards are1,
so each core Quit payoff is1. If a core owner k quits surely, its
successor has Continue payoff3 and must have rate0. Its predecessor
then has Continue payoff0, because its loved successor is absent and
k screens all later outcomes, so that predecessor must quit surely.
But k then has Continue payoff3 and cannot quit surely. Thus no core
coordinate can be sure at a root Nash, independently of continuation.

If owner3 is sure, a zero core rate forces its successor to quit
surely: with no loved quitter and a sure dummy, its Continue payoff
is0 while Quit pays1. Hence all core rates must be strictly between0
and1. Their indifference equations become 1=3q_love, forcing all
three rates1/3. On this core law, dummy Continue pays3 on every
nonempty core coalition except singleton{0}, which pays0. The former
event has probability15/27. Its Continue payoff is therefore at least
5/3 for ANY nonnegative continuation, above its Quit payoff1. This
contradicts sure dummy. No root coordinate is sure at any root Nash
with nonnegative continuation.

This observation permits backward conditional-Nash reasoning for a
finite-menu equilibrium: the joint continuation probability at each
nonterminal menu date is positive. The induced conditional suffix
must itself be a Nash profile. No subgame-perfection hypothesis has
been assumed.

### PF4. At continuation vector1 the only root Nash is allContinue

For core i, put a=q_love(i), b=the other opponent core rate. Its
Quit-minus-Continue incentive is

    G_i=1−3a−(1−a)(1−b)(1−y).

If y=0, the identity

    Σ_(core i) q_i G_i
      =−Σ_(core pairs{i,j})q_iq_j−3q_0q_1q_2

and the Nash signs force at most one positive core rate. A sole
positive rate is impossible: its predecessor has no loved quitter
and strictly prefers Quit. Thus all core rates are0.

Suppose y>0. By PF3 all rates are less than1. A zero core rate
would give its successor G≥y>0 and force a sure rate, so all core
rates are positive and mixed. Indifference gives, cyclically,

    b=f_y(a)=((2+y)a−y)/((1−y)(1−a)).

The map f_y is strictly increasing wherever these rates lie, with
derivative 2/((1−y)(1−a)²). An increasing real map cannot have a
nonconstant finite cycle: choose its least cycle member and iterate
the strict inequality if its successor differs. Hence all core
rates equal some t>0. Dummy Continue, at continuation1, then pays

    3−(1−t)²(2+t)=1+3t−t³>1.

It strictly prefers Continue, contradicting y>0 at Nash. Therefore
y=0 and all core rates are0. Conversely allContinue is a root Nash
at vector1 since every singleton pays1. It is the unique root Nash.

### PF5. Every common finite-menu exact equilibrium has full debt8

Fix ANY nonempty finite F⊆ℕ and let each strategy law be supported
on F only. At its final menu date T=max F the continuation game has
only Quit available, so all four owners quit and all four payoffs
are1. At each preceding menu date, PF3 rules out any sure root;
its positive continuation probability makes the conditional suffix
Nash. Induct backwards. PF4 at suffix vector1 forces allContinue
at EVERY preceding date. Thus the UNIQUE exact finite-game Nash
profile has all four owners pure at T.

Its prescribed payoff is1 in every row. Responding strictly after T
or Never is passive at the other-three coalition and pays3 in every
row. Earlier finite replies and root joins pay1. The full cap vector
is therefore(3,3,3,3), the debt vector is(2,2,2,2), and D=8 for
EVERY F. This includes singleton menus and arbitrarily sparse or
late finite menus. There is no favorable exact finite-game selector.

### PF6. Source check and mechanism decision

The narrow lookup of QuittingCyclicSingletonOpenSignData and its
isUniformEquilibriumPayoff theorem in
UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean
confirms that cyclic singleton producers already consume the core
open-sign pattern, with arbitrary collision rewards. This record
makes no new existence-class or literature-priority claim. The
proper completion and cap checks above are direct literal-law tests.

The conclusion is only that complete finite clocks and their
finite-support approximations do not make exact restricted Nash
selection response-complete. Four-finite approximation itself is
NOT falsified: PF2 supplies approximate full Nash finite clocks.
The next route must change the COMPLETE laws using the unrestricted
debt objective, rather than optimize an exact restricted Nash menu.

## A paid Never source has no finite prescribed tail after its last cap

### PC1. Exact restriction and status

COMPLETE ORDINARY PROOF, UNREVIEWED. Fix a bounded signed Fin4 table
with s_i>0, ORIGINAL full payoff/cap carrier K, and true positive
unweighted SUM-debt minimum δ. Suppose ALL K minima share ONE debt
vector d*. Let q be ANY old-quantile marked minimum produced from
actual finite-law approximants. Its full compact response space is
X=T⊔{Never}, with last finite point c and q_i({c})=0. Assume

    n_i=q_i(Never)>0 for EVERY i.

No root Nash, minimum tail, raw-date tightness or new nonisolated
insertion is assumed. The exact final finite response has value
V_i(c)=V_i(Never)+s_i∏_(j≠i)n_j, so Never is strictly suboptimal.
Put A_i=argmax_X V_i and L=max(⋃_i A_i), a FINITE compact test.

Claim: q_i({finite clocks>L})=0 for every i. Moreover either L=c,
or L is an isolated positive-mixture atom, the LAST retained finite
atom, and its retained interval ends at c. This is a pointwise source
restriction, not a raw-calendar last-date assertion or a UE consumer.
The NP separated-gap producer supplies all these hypotheses at ONE
table. Row genericity and93 contact exclusions are not used here.

### PC2. Literal two-sided finite-tail-to-Never transport

Fix a regular ordered cut a>L, respecting whole retained dates;
a nonisolated boundary has zero mixture mass. Put

    e_i=q_i({finite clocks>a}), J={i:e_i>0}.

Independently for i∈J use the OLD-law variation

    q_i^λ=q_i+λ_i[e_i δ_Never−q_i restricted to finite clocks>a].

Early mass stays fixed, late finite mass has factor1−λ_i, and
Never mass is n_i+λ_i e_i. A small common two-sided box is legal
because n_i,e_i>0. Owners outside J stay fixed.

On the ORIGINAL finite sequence, take whole-date finite tail events
A_i^k with convergent raw cut boundaries and e_i^k→e_i. Their
indicators converge in L¹, including the finite boundary c_k→c.
The retained Never interval has positive limiting length, and
n_i^k→n_i>0. The literal actual laws are

    p_i^{k,λ}=p_i^k+λ_i[e_i^k δ_Never−p_i^k restricted to A_i^k].

Their signed OLD-chart density is

    f_i^k−λ_i f_i^k 1_(A_i^k)
        +λ_i e_i^k 1_(Never interval)/|Never interval|.

It is nonnegative and uniformly bounded on the same small box.
Strong interval/cut indicators plus marginal weak-* convergence give
the stated limit. All old prescribed and moving-response kernels
remain unchanged, so the rectangle/L¹ product argument gives BOTH
prescribed and FULL-cap convergence for every fixed parameter vector.
Never is separate; c⁺ duplicates c because no new mass is put at c.
Every small-box pair lies in original K and has actual debt≥δ.

### PC3. Entire caps stay fixed, and individual payoff polynomials are constant

For EVERY test t≤a the changed opponent clocks were finite>a
and become Never, or conversely; both are later than the responding
owner. Its first-coalition response kernel is EXACTLY unchanged.
Every old active point lies≤L<a and retains its old cap value.

The compact upper tester set {t∈X:t≥a} has NO maximizer and has a
strict uniform gap from the old cap. Product coupling bounds every
response change uniformly by2M times changed opponent marginal
masses. Shrink the signed box to preserve this gap. Thus EVERY
full cap B_i stays exactly its old value, with no unique-response
or favorable-selector assumption.

Each U_i(λ) is multiaffine. The summed regret equals actual debt
on the box and has a true interior minimum, hence is constant.
Every box pair is a global minimum. All-minimum rigidity yields
U_i(λ)=B_i−d*_i individually. Therefore EACH payoff polynomial is
IDENTICALLY constant, also at algebraic distant endpoints. No
far-endpoint full-cap constancy or minimality follows from this.

### PC4. A singleton cylinder contradicts any positive finite tail

Suppose J is nonempty and choose i∈J. Set every other λ_j=1.
All finite opponent draws now lie≤a; each opponent's former late
finite mass was moved to its OLD positive Never atom. Changing
λ_i from0 to1 moves e_i of its own finite clocks>a to Never,
leaving early mass unchanged.

Any finite opponent exits before a and screens both own choices,
so gives the SAME passive reward. On the all-opponent-Never
cylinder the finite own draw instead pays s_i and Never pays0.
Independence gives the exact prescribed-payoff difference

    U_i(λ_i=0,λ_-i=1)−U_i(all λ=1)
        =e_i s_i∏_(j≠i)(n_j+e_j)>0,

with e_j=0 outside J. This contradicts individual polynomial
constancy. The endpoints are legal laws, but only their prescribed
payoff identity is used; born endpoint caps are not omitted.

Thus every e_i=0 for every regular a>L. Cuts approach L from above
(or one cut suffices in an isolated gap), yielding no prescribed
finite mass strictly after L. If L=c this is vacuous but exact.

If L<c and all own masses at L were0, every finite opponent would
be strictly earlier than L. An owner active at L would have
V_i(L)=V_i(c)=V_i(Never)+s_i∏_(j≠i)n_j, making c active, a
contradiction. Hence L has positive mixture mass and is isolated
by the retained-atom construction. With no finite mass after L,
its retained interval ends at c: any positive raw length between
its right endpoint and c would collapse to a later finite clock.
It is the LAST retained finite atom, not necessarily the last
support date at each original approximating index. Vanishing
later original finite mass is allowed.

### PC5. Boundary, increment and open consumer

True global minimum cannot be replaced by positive profile debt.
In the participant-indicator table r_i(S)=1 if i∈S and0 otherwise,
let every owner have probability1/2 at date0,1/4 at date2,1/4 Never.
Every cap is1 at date0 only, but finite prescribed mass lies after
the latest active point. Moving small Never mass to the OLD date2
keeps all caps1 and raises that owner's payoff by at least the mass
times(1/4)³; other payoffs cannot decrease. This legally lowers debt.
The true global gap is0, so it is not a counterexample to PC1.

Together with NP's no-pre-active-head theorem, this brackets all
prescribed finite clocks between the first and last full active
times. It excludes a post-active prescribed tail, not an alias of
two response labels. It does NOT imply every prescribed clock is
its owner's maximizer, L<c, a paid temporal charge or a renewal law.
The zero-mixture final finite test c remains a live residual.

Source correspondence used: the original carrier, complete moving
kernels and signed old-law bounds in the canonical source proof;
the actual joint-Never debt bound in
UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean;
and NP's ordinary common-debt/positive-Never producer. No new Lean
declaration, independent gate or export is asserted. The next
question is whether the L=c residual, or the final retained
collision when L<c, supplies an ACTUAL whole-law change controlling
all born caps rather than another clock-count refinement.

## Reusing the old symmetric trap: end-Never grafts fail over ALL tails

### EG1. Exact whole-family failure, not a new solved-table trap

This reuses the already recorded positive symmetric table:
own singletons1, EVERY passive reward100, participant pairs108,
participant triples92 and grand rewards100. It specifies all60
coordinates. Give every owner half date0/half Never. Direct enumeration
gives in every row

    Q=B=701/8, R=175/2, U=1401/16,
    n=1/2, h=1/8, ν=1/16, d=1/16, D=1/4.

Root and last empty finite responses tie; Never is strictly below.
The end budgets κ=(B−R)/h are EXACTLY1 for every owner. This is
NOT a true global minimum: pure date0 pair A, with outsiders Never,
has payoff/cap108 for its members and100 for outsiders, so trueΔ0.

Stronger than its previously retained infinitesimal failure, NO
finite-amplitude replacement of ONLY its original Never branches
by ANY actual independent tail can lower this profile's full debt.
All response deadlines/Never and arbitrarily long tail laws are
covered. Thus a consumer confined to that whole-law subclass fails,
not merely one chosen tail or one derivative.

### EG2. Complete unrestricted all-tail inequality

Take ANY actual tail v with marginal Never masses m_i and joint
mass c=∏m_i. Every player's passive reward is100, so its Never
response pays100(1−c_-i). Its arbitrarily late finite reply pays

    1+99(1−c_-i), c_-i=∏_(j≠i)m_j.

Hence its FULL tail cap satisfies b_i−1≥99(1−c_-i)≥0.
On every sample with a finite exit, at least THREE owners have
a finite opponent (four if at least two owners exit finitely).
Taking expectations gives

    Σ_i(1−c_-i)≥3(1−c).

The total reward of the first coalition is at most416: the
singleton/pair/triple/grand totals are301/416/376/400.
Thus Σ_i u_i≤416(1−c). Combining these exact bounds yields

    2Σ_i(b_i−1)−Σ_i u_i≥178(1−c)≥0.

The ledger SG1 then gives for EVERY end-Never graft

    D_graft−1/4
      =(1/16)[2Σ_i(b_i−1)−Σ_i u_i]
      ≥(89/8)(1−c)≥0.

AllNever is the unique tail probability mode with c=1 and the
only way to have zero stated lower bound. Every tail with ANY
finite absorption probability makes the actual debt strictly larger.
Closing, the nonnegativity holds on ALL tail carrier K as well.

### EG3. Mechanism change and exact nonclaim

This is a genuine global failure of a tail-only repair architecture
at an old recorded solved profile, without new constants tuning.
It does not falsify SG's necessary original-minimum inequality:
that inequality is exactly satisfied here. It also does not
falsify NP's TRUE global source, because the unrestricted full
floor atδ=1/4 is absent. A proof may still combine the ALL-tail
budget with that missing full-law floor. The conclusion is that
the budget alone cannot be a consumer: a successful repair may
have to change EXISTING finite stopping mass, not only its old
Never branches. The actual distant pure-pair competitor does so.

The next mechanism must use that full-law/global input and retain
the paid finite bridge; I will not strengthen this solved table
or optimize its constants. This is supporting failure evidence,
not an export or a new equilibrium-class claim.

## Augmented rigidity and globally strict finite-root fibers

### NR1. Self-contained question and exact status

COMPLETE ORDINARY PROOF, UNREVIEWED. Fix a bounded Fin4 table r,
every own singleton s_i>0, and its ORIGINAL full-response infimum
δ=inf_p D_r(p)>0. Suppose δ_abs>δ, where absorbing profiles retain
ALL behavioral response caps. Let ν(p)=∏[i]p_i(Never).

Can a FRESH nearby row-affine table be selected with common joint Never
mass at ALL original minima, compatibly with the complete NP source?
Yes. At ONE final table r* there are a_i*>0 and ν*>0 such that EVERY
actual sequence with D_{r*}(p^k)→δ* satisfies

    d_i^{r*}(p^k)→a_i*,       ν(p^k)→ν*.

The selection precedes ALL sequences and marked sources. No individual
Never mass, payoff, cap, law or calendar is claimed unique. There is no
actual minimum-attainment assumption. At the SAME table this implies
globally strict one-coordinate finite-root fibers and strictly nonminimal
conditional tails. It does not produce a debt descent or UE.

### NR2. Exact signed directions on a fixed augmented carrier

Define the nonempty compact set

    A=closure{(d_0(p),d_1(p),d_2(p),d_3(p),ν(p)):actual p}⊆ℝ⁵.

Debts lie in[0,2M] and ν in[0,1]. The additional coordinate is ACTUAL
joint Never probability; it cannot be inferred from one old (U,B) pair
and must be retained BEFORE closure. For θ_i>0 and τ close to0 define

    r_i^{θ,τ}(S)=θ_i r_i(S)+τ/4  for nonempty S; Never pays0.

Choose the neighborhood so all new own rewards stay positive. Positive
row scaling scales payoff and EVERY response cap. Whole-row addition C
has B_i^{new}=B_i+C and U_i^{new}=U_i+C(1−ν), provided BOTH old and
new own singletons are nonnegative. Every finite pure response absorbs
surely, hence gains C. Its supremum is the FULL cap: delayed finite
values tend to Never payoff+h_i s_i≥Never payoff, before AND after
translation. This proves the signed identity for all finite/Never replies.
Therefore, EXACTLY at every actual profile,

    d_i^{θ,τ}(p)=θ_i d_i(p)+(τ/4)ν(p),
    D_{θ,τ}(p)=∑[i]θ_i d_i(p)+τν(p).                (NR2)

The FINAL UNWEIGHTED infimum is the fixed-carrier concave value

    W(θ,τ)=min[(a,v)∈A](∑[i]θ_i a_i+τv).

There is no convexification of independent laws or selected-law envelope
derivative. The old coefficients remain fixed while the table changes.

### NR3. Select ONE regular coefficient vector before ALL minima

Compact bounded A makes W finite, concave and Lipschitz on ℝ⁵. In every
nonempty open box there is a point with all five two-sided coordinate
partials. On every one-coordinate slice the one-sided slopes of a finite
concave function are monotone, with at most countably many disagreements;
Fubini gives a null exceptional set for each coordinate and their union.

Choose (θ*,τ*) there, arbitrarily near(1,0). For EVERY minimizing (a,v),

    W(θ*+t e_i,τ*)≤W(θ*,τ*)+t a_i,
    W(θ*,τ*+t)≤W(θ*,τ*)+t v.

Dividing separately by positive and negative t forces ALL minimizing
coefficients to be the SAME a_i=∂_{θ_i}W and v=∂_τW. Set

    a_i*=θ_i* a_i+(τ*/4)v,       ν*=v.

For ANY actual final-table minimizing sequence, its old five coefficients
are bounded. Every subsequential cluster belongs to A and minimizes W
by(NR2), hence equals this same (a,v). Thus the ENTIRE coefficient
sequence converges. Applying(NR2) gives exactly NR1, not a favorable
subsequence or uniqueness of underlying pairs.

This is a genuine fifth-coordinate extension of ordinary DR. The generic
declaration `Math.CompactLinearMinimum.exists_mem_open_all_minimizers_eq`
in `MathUE/Analysis/CompactLinearMinimumRigidity.lean` has one fixed compact
coefficient set and a regular weight in every open region; its Rademacher
proof was statically inspected, not checked here. The ordinary
coordinate/Fubini argument above is the mathematical proof used here;
the generic declaration is not a checked whole-NR producer.
The ACTUAL extra ν coefficient and semantic signed table transport are
also ordinary mathematics, not claimed implemented.

### NR4. Compatibility and uniform all-law rigidity

The table change is arbitrarily small. Full and absorbing infima are
8-Lipschitz in reward sup distance, since all payoffs and ALL complete
caps are1-Lipschitz at fixed laws. Thus δ*>0, δ_abs*>δ* and s_i*>0
remain. Within-row distinctness is preserved EXACTLY by positive scaling
and a common row addition.

From ANY actual counterexample, use NP's ordinary interior row-generic
positive-own separated table BEFORE its four-weight regular step, and
replace that step by NR2–NR3. Its marked no-head/root-box proof needs
only the common final debt vector, now a*, and remains applicable to
EVERY original minimum at this SAME final table. No old source or old
table's normality is transported. Reapply actual no-UE inputs to r*.

The actual absorbing completion bound
δ_abs*≤D_{r*}(p)+14M*ν(p)^(1/4) forces ν*>0. The exact joint-Never
singleton bound νs_i*≤d_i gives a_i*≥s_i*ν*>0. For every ε>0 there
is ζ(ε)>0 such that, for EVERY actual profile,

    |ν(p)−ν*|≥ε ⇒ D_{r*}(p)≥δ*+ζ(ε).               (NR4)

Otherwise a sequence would contradict NR3. Equivalently, the compact
coefficient set outside that ν-neighborhood has a strict objective gap.
No constants optimization or actual minimum attainment is used.

### NR5. All nonzero minimum prefixes have strictly nonminimal tails

Fix ANY w in the ORIGINAL final-table carrier K and realize it by actual
finite tails p^k. Prefix EXACT rates x at date0 over those SAME tails.
ALL finite/Never caps converge to T_x(w), and the literal joint Never is

    ν(prefix_x p^k)=c(x)ν(p^k),       c(x)=∏[i](1−x_i).

If q≠0 and D(T_q(w))=δ*, positive ν* excludes any sure rate, so
0<c(q)<1. Applying NR3 to these genuine minimum sequences forces

    ν(p^k)→ν*/c(q)>ν*.                              (NR5)

This holds for EVERY realizing sequence of w, not a chosen attained tail.
If D(w)=δ*, NR3 would instead force ν(p^k)→ν*, a contradiction.
Therefore D(w)>δ*. In the exact prefix identity

    δ*=c(q)D(w)+∑[i](max(g_i(q),0)−q_i g_i(q)),

the nonnegative root term is STRICTLY below(1−c(q))δ*. The tail is
strictly HIGHER in ordinary total debt, not a decreasing rank or Nash.

If x and q are TWO minimum roots over the same w, the same realizing
tails give c(x)ν*/c(q)=ν*, hence c(x)=c(q). This also excludes x=0
when q≠0. The result applies anew after every same-table reconstruction.

### NR6. Every one-coordinate finite-root change is globally strict

Fix the same nonzero minimum prefix and an owner j. Change ONLY x_j to
ANY t∈[0,1] different from q_j. Its full pair lies in original K and
has debt≥δ*. Equality would force c(x)=c(q) by NR5. Every other factor
1−q_i is positive, so this would force t=q_j. Thus

    D(T_x(w))>δ* for EVERY t≠q_j.                   (NR6)

This is a finite-amplitude ALL-response exclusion, not merely failure of
small descent. Any different minimum root over this fixed tail must
change at least TWO rates and preserve the EXACT all-Continue product.

The univariate objective is convex piecewise affine: for i≠j its Q_i,
C_i and U_i are affine in x_j; B_i=max(Q_i,C_i). The cap of j is
independent of its own rate and its payoff is affine. Unique minimization
therefore gives a strictly negative left slope and strictly positive
right slope at every mixed q_j>0; at q_j=0 the right slope is strictly
positive. A zero slope would yield a nonempty constant adjacent interval
because there are only finitely many affine root branches.

In particular EVERY positive supplier j has SOME OTHER owner i with

    Q_i(q)=C_i(q),       ∂_{x_j}(Q_i−C_i)(q)≠0.

Without such a nonzero slope switch the objective would be locally affine
and could not have a strict interior minimum. This assigns a coupled-cap
wall to EACH supplier, but supplies no paid temporal edge or return.

### NR7. Exact boundary tests and failed stronger implications

For the complete table r_i(S)=−1 at all nonempty S, AllNever is exact
full Nash with ν=1. The infimum is identically0 on an open neighborhood
with all own rewards negative. Whole-row cap translation fails there:
Never stays cap0. Differentiability without the OLD AND NEW own-sign
hypotheses cannot imply joint Never rigidity by the NR2 coefficient law.

At the earlier EG table (owns1, passive100, pair participants108,
triple participants92, grand100), half-root/half-Never has D=1/4 and
ν=1/16, while an exact pure-pair full Nash has D=0 and ν=0. Its member
Quit-vs-Continue margin and outsider root-join disadvantage are both8,
so that pair stays exact Nash on a small open reward ball. The true
infimum there is0. NR3 constrains TRUE minimizing sequences, not the
positive-debt half-root profile. This reuses the old solved regression;
it is not a new positive-gap example or a stronger optimization trap.

Common ν is not unique laws, payoffs or kernels. Set r_i(S)=1 for
EVERY recipient and nonempty S except S={2,3}, where EVERY recipient
gets2. This specifies all60 coordinates and all own singletons are1.
Pure date-zero grand Quit is full Nash with U=B=(1,1,1,1): leaving
pays1 at the other-three coalition. Pure date-zero pair{2,3}, outsiders
Never, is also full Nash with U=B=(2,2,2,2): a member leaving pays1,
and an outsider joining pays1 rather than its passive2. Later/Never
outsider responses pay2, and later member responses pay1. Both have
ν=0, but their outcomes, payoff pairs and complete laws differ.

### NR8. Exact increment, narrow dependencies and remaining consumer

The new output is one common ACTUAL joint-Never limit across EVERY
original full-minimum realizing sequence at ONE compatible fresh table.
It is not a supplied state field or a property borrowed at an old table.
Common debt alone did not imply strict old-tail debt or strict root fibers.
No export or UE claim is made.

The bounded source lookup inspected the fixed compact-set declaration
named in NR3, the canonical NP signed translations/full-cap bounds and
source proof, and
`quittingContinuationBestResponseValue_source_sub_stoppingLawMixture_le`
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumTangent.lean`,
plus `quittingSimultaneousStoppingLawMixture_minimumFloor_slopeOrFlat_withUnilateralPassport`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSimultaneousResetMinimumDichotomy.lean`.
Those give unilateral affine debt and minimum-forced transfer, NOT the
extra ν rigidity or joint descent. The nearby
`CommonWitnessPassportRegression.envelope_is_modular_on_vertices` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessPassportRegression.lean`
also rules out assuming a shared active selector from modular cap values.

This does not consume the source. A nontrivial end-Never graft decreases
ν, so cannot even REMAIN exactly minimal here: SG's global budget is
strict when the appended tail has positive absorption probability, by
NR4 and its literal joint-Never product. A successful equal-debt return
would need compensating changes of EXISTING finite mass. Preserving ν
is necessary for such an EQUAL-debt return, not sufficient. NR9 below
tests and rejects a proposed lossless mixing step on that level, and NR10
rules out imposing the fixed-ν restriction on a LOWER-debt competitor.
The consuming question is therefore a ν-changing coupled old-law
comparison, not further tail-only release or counting NR6's walls.

### NR9. Exact full-law fixed-Never optimization still has a collision barrier

This is a COMPLETE EXACT TEST, not a positive unrestricted gap or a
new source theorem. Reuse the participant-indicator table

    r_i(S)=1 if i∈S, and0 otherwise.

It specifies all60 rewards. EVERY actual profile has full B_i=1,
because date-zero Quit surely makes i a participant, and all rewards
are≤1. Let n_i=p_i(Never) and fix ANY joint mass v∈(0,1). For ALL
independent actual laws with ∏[i]n_i=v,

    U_i=P(i belongs to the first finite coalition)≤1−n_i,
    D≥∑[i]n_i≥4v^(1/4).                            (NR9)

The last inequality is AM–GM. Put n=v^(1/4). Equality is attained
by the actual laws p_i=nδ_Never+(1−n)δ_T for ANY common finite date T.
Thus this is the TRUE infimum over the ENTIRE fixed-joint-Never law
class, with all unrestricted deviations, not a bounded-menu optimum.

Its equality cases are exact. AM–GM forces every n_i=n. The other
inequality forces every owner who draws a finite clock to belong to
the first coalition surely. For every pair i,j, on their independent
joint-finite event both conditional finite times must therefore agree
almost surely. Independent probability laws whose product is supported
on the diagonal are Dirac masses at the same date. Since1−n>0, all four
conditional finite laws are the SAME δ_T. These are all actual minimizers.

Take T=0 and T=1. Mix EACH owner's existing finite date independently
half-and-half between the two dates, keeping its Never mass n EXACT.
The joint Never mass remains v. Let p=(1−n)/2 and s=(1+n)/2.
An owner is a participant if it draws date0 (probability p), or draws
date1 and all other owners avoid date0 (probability p s³). Hence

    U_i=p(1+s³),
    D−4n=2(1−n)(1−s³)>0.

ALL response caps remain1; this loss is entirely the destroyed finite
coalition membership. At n=1/2 the old fixed-class minimum is D=2,
the mixed debt is165/64, and the increase is37/64. These are exact
full-law values, not a derivative or a cap-selection artifact.

Indeed no nonconstant continuous PRODUCT-law path in total variation
connects these two endpoints while remaining in the minimizing level:
every minimizer's conditional finite law is a COMMON Dirac δ_T, and
different Dirac dates have positive fixed total-variation separation.
A shared coin choosing one common T would preserve the mixture of
cohorts, but is not the independent private mixture used above.

This does NOT refute NR: the unrestricted table has δ=0, attained at
all date-zero Quit, and its positive-v constrained minima are not full
minima. It also lacks NP's generic paid bridge. The precise failed
implication is that common joint Never restores convexity or supplies
a lossless simultaneous finite-mass chord. NR's concrete role is to
force compensating product survival in an EQUAL-debt reconstruction;
it does not supply the reconstruction. The next mechanism must change
coalition probabilities using the actual table/global-floor information,
not interpolate calendar aliases or share a forbidden cohort coin.

### NR10. Do not impose fixed ν on a LOWER-debt competitor

A sharper whole-law check applies to the earlier EG table, with no new
example or constants tuning. Its half-root/half-Never profile satisfies
d_i=1/16 for every i and ν=1/16. The actual singleton bound gives,
for EVERY independent profile on this table with that SAME joint Never,

    D(p)≥ν∑[i]s_i=4/16=1/4.

Therefore the old profile is already a TRUE GLOBAL minimum over the
ENTIRE fixed-ν strategy class, including all conditional finite laws,
all coupled root/tail changes and all unrestricted response caps.
Unlike NR9 it has actual random atomic coalitions, positive debts,
and distinct maximizing root and late payoff kernels. Its unrestricted
full infimum is nevertheless0 at the distant pure-pair Nash profile,
whose ν=0. This distinguishes the two global optimization problems.

Thus a repair architecture forced to preserve ν is globally falsified
even when it may change ALL existing finite stopping mass. NR's common
ν* constrains an EQUAL-debt return or two minima, not a hypothetical
strictly LOWER-debt competitor: such a competitor need not preserve
ν*. At the genuine source the full-law floor would forbid it by
contradiction, but it cannot be excluded from the search in advance.
This rejects the proposed fixed-ν repair mechanism, not NR's producer.
The next comparison must permit changed ν while controlling the born
caps through the actual unrestricted floor; no more fixed-level mixing
or scalarization is being pursued as a consumer.

## Why an own-threshold payoff-only global screen cannot consume the source

### PS1. Exact question, overlap and status

COMPLETE ORDINARY CONSEQUENCE of the existing singleton source, not a new
UE theorem, counterexample reduction or export candidate. The attempted
different mechanism was to use independent-clock two-copy inequalities
to prove that EVERY actual absorbing profile has some U_i≤s_i. Native
zero-own absorbing minima have strict U_i>0 by the reviewed fixed-bound
BA6 argument, so such a screen would apparently exclude positive native
absorbing gaps. The following actual construction shows that this entire
own-threshold architecture is ALREADY inconsistent with the singleton
source, before any collision inequality is needed.

Let r be a finite signed table, |r_i(S)|≤M, with M>0, and let
Γ_ij=r_i({j})−s_i for j≠i, Γ_ii=0. Suppose λ≥0, Σλ_i=1, and

    ε=min_i(Γλ)_i>0.

Then an ACTUAL independent stationary profile, absorbing almost surely,
has U_i>s_i for EVERY owner. No conclusion about its full debts follows.

### PS2. Complete actual construction and quantitative payoff bound

Choose 0<ρ≤1/2. At every live date player i privately Quits with
probability ρλ_i. One-period total hazard is ρ>0, so its all-Continue
probability is strictly below1 and prescribed play absorbs almost surely.
No public coin, new state or infinite prescribed clock is used.

Let a be its one-period absorption probability and N_i the one-period
absorbing payoff contribution. Then U_i=N_i/a. The total mass of all
singleton events differs from ρ by at most ρ², and the nonsingleton mass
is at most ρ²/2. More explicitly,

    0≤ρλ_j−Pr(first-period coalition={j})
      ≤ρ²λ_j(1−λ_j),
    0≤ρ−a≤ρ²/2,       a≥ρ−ρ²/2≥ρ/2.

The singleton barycenter t_i=Σ_jλ_j r_i({j}) satisfies |t_i|≤M.
Thus |N_i−ρt_i|≤(3M/2)ρ² and

    |U_i−t_i|≤4Mρ,       t_i=s_i+(Γλ)_i.

Taking ρ<ε/(8M) gives U_i>s_i+ε/2 for all i simultaneously.
The constants are only a proof of convergence; no optimization is used.
Zero λ_i is harmless: that owner prescribes Never, while another positive
λ_j still makes the entire profile absorbing.

The exact source inspected is
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`.
It supplies this λ from ANY actual Fin4 no-UE game, with no payoff-sign
or supplied-strategy hypothesis. The tracked direction estimate
`abs_stationaryPayoff_sub_singletonDirectionBarycenter_le` in
`UniformEquilibrium/Quitting/Circulation/DirectionBarycenter.lean` gives
the same limit with bound6Mρ. Its total-hazard contraction declaration
`quittingStationaryContinueMass_lt_one_of_totalHazard_pos` was also read.
These declarations were statically inspected under their imports, not
built in this session; the elementary calculation above is ordinary math.

### PS3. The native zero-own absorbing question has the same obstruction

This does NOT identify a native absorbing minimum with an NP full minimum.
Let z have all own rewards0, bound M>0 and A=Δ_abs(z)>0. For any t>0
add t to EVERY nonempty reward row, leaving AllNever0. Old and new own
rewards are nonnegative, so the exact full-cap translation gives

    D_{z+t}(p)=D_z(p)+4tν(p),       Δ_abs(z+t)=A.

The actual one-marginal absorbing completion bound is
A≤D_z(p)+14Mν(p)^(1/4). Consequently, at EVERY actual profile, either
D_z(p)≥A/2 or ν(p)≥(A/(28M))⁴. Therefore

    Δ_all(z+t)≥min(A/2,4t(A/(28M))⁴)>0.

The terminal exploitability bridge excludes UE for z+t. Its centered
singleton Γ is EXACTLY that of z, so the named Fin4 simplex source yields
Γλ>0 at this SAME native table. PS2 now produces an actual absorbing z
profile with ALL U_i>0. It need not minimize debt; this is consistent with
the strict positivity of every hypothetical native absorbing minimum.
This uses the ordinary normalization/completion argument in the canonical
fully-paid source, not a new normality assumption at z.

Thus a universal test of the form “every actual absorbing profile has
some nonpositive coordinate” can never reach a native positive-gap table
with the required singleton source. Two-copy coalition incompatibilities
remain useful ONLY if they also price full response caps or impose a
stronger, actually supplied quantitative payoff condition. This statement
does not rule out every payoff-dependent argument or inequalities with
thresholds strictly above the own singleton vector.

### PS4. Exact positive-payoff profile still has large complete debt

Set r_i(S)=0 when i∈S and r_i(S)=1 when i∉S, specifying all60 entries.
Owns are0 and Γ has all off-diagonal entries1. At the actual stationary
profile with common hazard q∈(0,1), every owner is finite almost surely and

    U_i=(1−q)[1−(1−q)³]/[1−(1−q)⁴]>0,       B_i=1.

Literal Never attains that cap because the other three eventually Quit.
At q=1/2, U_i=7/15 and D=32/15; as q↓0, U_i→3/4 and D→1, not0.
The table's TRUE absorbing and full infima are nevertheless0: pure solo
date-zero Quit by one owner, others Never, is full Nash. The quitter can
obtain only0, and outsiders lose their passive1 if they join. This solved
test distinguishes payoff delivery from unrestricted deviation control;
it is not an example satisfying the positive native or NP gap hypothesis.

The mechanism decision is to abandon own-threshold payoff-only exclusions,
not to weaken the same copied-outcome inequality. The live consumer must
change existing finite mass while retaining ALL counterfactual caps and
allowing ν to vary. Neither a payoff-positive stationary source nor an
auxiliary Nash root above a minimizing payoff supplies that comparison.

## Global purification prices for the entire existing finite law

### CV1. Exact all-response ledger, not a consuming construction

COMPLETE ORDINARY SUPPORTING CALCULATION, not independently reviewed.
This examines a genuinely ν-changing modification of EXISTING finite
mass, not an appended end-Never tail. It does not produce a descent or
new counterexample-class exclusion. Work at a fixed original NP table
with Δ_all=δ>0 and Δ_abs=δ+g, g>0. For an ACTUAL profile p and owner j
write n=p_j(Never), m=1−n, and suppose 0<n<1. Let f replace ONLY j's
whole law by its conditional FINITE law, and let e replace ONLY j by
literal Never. All other complete laws remain the original independent
ones. These are actual profiles; f is absorbing and e has joint Never
ν(p)/n. The mixing identity p_j=m f_j+n e_j concerns j's private law,
not an observed public lottery between whole game profiles.

Every prescribed payoff is affine on this one-law chord. The cap of j
is unchanged. Every other COMPLETE cap is the supremum of affine pure
reply values, hence convex. Therefore the exact cap-mixing dividend is

    J_j(p)=Σ[i≠j](m B_i(f)+n B_i(e)−B_i(p))≥0,
    J_j(p)=m D(f)+n D(e)−D(p).                 (CV1)

No maximizing clock or common witness is chosen. Arbitrarily late finite
tests, original Never, and every changed maximizing branch remain inside
the three FULL caps in this identity. It follows from the original
floors that

    J_j(p)≥m g−(D(p)−δ).                      (CV2)

Thus whole-law purification is not controlled by the mover's original
gain alone: the true minimum relies on a STRICT cap-mixing dividend
whenever that owner has positive finite mass.

### CV2. Literal original-minimum sequences and the NR strict extra term

Take ANY original finite-law minimizing sequence p^k and a subsequence
with n_j^k→n∈(0,1). Finite conditional laws f_j^k are actual probabilities,
with no conditioning of opponents or zero-probability event. The f^k
pairs belong to K_abs; the e^k pairs belong to K_all. Extract a joint
subsequence of their bounded payoff/FULL-cap pairs. The exact identities
(CV1) pass to these Euclidean limits, giving J_j≥(1−n)g>0.

At the augmented-rigid fresh table of NR1–NR8, original ν(p^k)→ν*>0.
The Never endpoint has ν(e^k)→ν*/n>ν*. NR4's uniform all-law collar
therefore gives some ζ>0 with D(e^k)≥δ+ζ eventually. Consequently

    J_j≥(1−n)g+nζ>0.                          (CV3)

This conclusion uses actual full-cap endpoints of the ENTIRE old finite
law. It does not assume endpoint minimality, atom attainment, tail Nash,
or constancy of the old payoffs/caps. If n=1 there is no finite branch
and no positive dividend conclusion. If n=0 the source is absorbing and
is not a full NP minimum. The two-sided density transports used earlier
are not needed for these literal endpoint comparisons.

There is also a literal uniform incompatible-witness statement. At each
actual p, some i≠j contributes at least J_j/3. For EVERY pure finite or
Never test t, its endpoint response values satisfy

    m[B_i(f)−V_i(t;f_{−i})]+n[B_i(e)−V_i(t;e_{−i})]
      ≥m B_i(f)+n B_i(e)−B_i(p)≥J_j/3.         (CV4)

The first inequality is exact one-law affinity plus V_i(t;p_{−i})≤B_i(p).
Along a minimizing sequence with positive limiting J_j, pass to one fixed
i and a fixed positive lower bound in(CV4). Thus there is NO sequence of
common finite/Never tests approaching BOTH endpoint caps. No attainment
or endpoint calendar identification is required: the witnesses and the
inequality are literal at every original index. This concerns endpoint
responses, not necessarily two current maximizing points at p. Unique
current attainment can coexist with strict Jensen loss; no current
active-face exclusion is asserted.

### CV3. Exact old-table test and the nonconsumed remaining problem

Reuse EG, without a new table: owns1, all passive rewards100, participant
pairs108, triples92, grand100. The half-date-zero/half-Never profile has
D=1/4 and B_i=701/8. Fix j. Its f endpoint has j surely Quit at0 and
all other rates1/2. The other three caps are100 and their debts1; j's
debt is0. Thus D(f)=3. At e, j Never, the other three caps are309/4 and
their debts9/8; j's debt is1/8. Hence D(e)=7/2, and exactly

    J_j=(1/2)·3+(1/2)·(7/2)−1/4=3.

Each nonmover contributes1 to this dividend. The Never endpoint raises
ν from1/16 to1/8; the finite endpoint has ν=0. Every cap here is the
maximum of the literal root response and the complete later/Never
response, not a selected row cap. The table has true gap0 at a pure
pair Nash, so it is NOT an example satisfying the separated-gap premise.
It illustrates the ledger rather than proving (CV2) from profile debt.

The calculation rejects the proposed whole-law inference “purifying a
finite conditional branch preserves other cap prices” even before a
joint calendar construction is attempted. It also shows why convexity
gives no descent: D(p) is BELOW, not above, the endpoint average. A
ν-changing coupled comparison must control changes in these mixing
dividends as well as prescribed payoffs. No bound making that comparison
favorable is proved here; CV is not a gain-to-charge consumer or export.

The narrow source lookup inspected
`quittingContinuationBestResponseValue_source_sub_stoppingLawMixture_le`
and `abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumTangent.lean`,
plus the exact singleton and actual absorbing-completion facts used by
the canonical NP proof. The algebra above uses their ordinary one-law
affinity/convexity principle; it is not a new checked declaration.

## A whole ν-changing diagonal architecture already fails on the old cyclic test

### UD1. Exact scope and complete response ledger

This is an ORDINARY, COMPLETE architecture falsifier, not a genuine
positive-gap example or a new class theorem. It reuses MORSE's already
solved cyclic table rather than strengthening the local test. Its role
is to rule out a uniform acceleration of EVERY existing finite clock
as the missing ν-changing move. Asymmetric calendar changes remain open.

Indices are modulo four. For every nonempty coalition S, the complete
sixty entries are: own singleton 1; at singleton {j}, passive j+1 gets0
and the other two passives100; pairs pay participants69 and passives100;
at a triple omitting m, participant m+1 gets92, the other two participants101,
and passive m100; grand pays99 to all. Never pays0. This is exactly the
previous cyclic regression, not new data.

Let every independent law put probability p at the SAME actual date T
and 1−p at Never, for ANY p∈[0,1] and T∈ℕ. All players have the same
complete quantities

    Q=(1−p)³+207p(1−p)²+294p²(1−p)+99p³,
    A=200p(1−p)²+300p²(1−p)+100p³,
    C=A+(1−p)³,       U=pQ+(1−p)A.

Every pure response strictly before T gives1; the date T gives Q;
EVERY finite response strictly after T gives C; Never gives A. Q≥1
because ALL participant entries are at least1. C≥A. Thus the full
unrestricted cap is EXACTLY max(Q,C), even when T>0, p=0, or p=1.
No response menu has been substituted for the full cap. Put

    G=Q−C=p(2p−1)(6p−7).

Then the exact unrestricted sum debt is

    D(p)=4[(1−p)⁴+G⁺−pG].                     (UD1)

In particular D(1/2)=1/4 and ν(p)=(1−p)⁴ ranges over ALL of[0,1].
This family is not constrained to the old joint Never mass.

### UD2. Global minimum over the entire architecture

Since 6p−7<0, G≥0 on[0,1/2] and G≤0 on[1/2,1]. Expansion gives

    D(p)−1/4=(1−2p)(15+78p−180p²+88p³)/4    if p≤1/2,
    D(p)−1/4=(2p−1)(−88p³+84p²+34p−15)/4   if p≥1/2.

Both cubic factors are STRICTLY positive on their respective intervals.
For a transparent exact certificate: after x=2p in the first factor,
the degree-three Bernstein coefficients on x∈[0,1] are

    (15,28,26,20).

After x=2p−1 in the second factor, they are

    (12,62/3,76/3,15).

Here the Bernstein basis is ((1−x)³,3x(1−x)²,3x²(1−x),x³), all
nonnegative and summing to1. Therefore

    D(p)≥1/4 for EVERY p,T, with equality exactly at p=1/2.   (UD2)

This excludes ALL uniform common-cohort hazard rescalings, not just
small perturbations. Independently taking the earliest of k replicas
of each old half-finite law gives p=1−2⁻ᵏ; taking the latest gives
p=2⁻ᵏ. Both change ν, both modify existing finite mass, and both are
covered by(UD2), as are arbitrary intermediate common rates. Nothing
here excludes asymmetric rates, calendar refinement, or whole-law repair.

### UD3. Why the next mechanism must be asynchronous

The true unrestricted gap of this table is ZERO. After the finite
relabeling i↦−i its singleton matrix has cyclic coefficients
(0,−1,99,99). These meet the hypotheses of
`QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`:
first forward entry negative, the other two nonnegative, and coefficient
sum197>0. The inspected producer permits arbitrary collision rewards.
MORSE's explicit same-table four-block refinement additionally bounds
ALL finite/Never gains by68ρ, and sum debt by272ρ→0. Its original
literal finite-law censoring test also beats1/4. Hence(UD2) is a
whole-architecture obstruction at a SOLVED table, not a no-UE example.

The decision is to drop UNIFORM finite-clock acceleration as a consumer.
This is stronger than NR10's fixed-ν warning but does not answer the
remaining problem: find a genuinely asymmetric ν-changing comparison
whose born caps are paid at a TRUE global minimum. No constants or new
local trapping table are being sought. The old cyclic table's actual
escape already demonstrates the needed change of calendar mechanism.

## A response-complete finite word forces an old finite branch at the c-wall

### TW1. Global finite-word producer and every moving response

COMPLETE ORDINARY DERIVATION, UNREVIEWED. This narrows a source geometry;
it is not a universal repair or a density-based UE producer. Work at the
SAME separated NP table r, with s_i>0 and Γ_ij=r_i({j})−s_i for i≠j,
Γ_ii=0. For ANY simplex λ and ANY ρ∈(0,1], define independent ACTUAL
finite laws

    p_i^N(k)=ρλ_i/N  at k=1,…,N,
    p_i^N(Never)=1−ρλ_i.

Date0 is empty. No public coin, prescribed response cap, or new minimum
is assumed. Let θ∈[0,1] and put

    μ_j=∫₀¹ ρλ_j ∏[ℓ≠j](1−ρλ_ℓ t)dt,
    u_i=Σ_j μ_j r_i({j}),
    F_i(θ)=s_i+∫₀^θ Σ[j≠i] ρλ_j
                    ∏[ℓ≠i,j](1−ρλ_ℓ t) Γ_ij dt,
    b_i=max[θ∈[0,1]]F_i(θ).                    (TW1)

Then the FULL actual pairs(U(p^N),B(p^N)) converge to(u,b)∈K.
The original joint Never is exactly ∏_i(1−ρλ_i), also at the limit.

Here is the full response proof. Couple the finite clocks to independent
uniform grid locations conditional on their own finite draws. A pair
of finite clocks collides with probability at most1/N, so the probability
of ANY prescribed nonsingleton outcome is at most6/N. Conditional on no
tie, singleton-first probabilities are Riemann sums for μ_j. The bounded
reward error vanishes, hence all prescribed payoffs converge to u.

For ANY pure finite tester k, set θ_N=clamp((k−1)/N,0,1). The tester
receives passive singleton rewards from an opponent's earlier first
quit, and its own singleton if all opponents survive until its clock.
The cumulative passive terms are the corresponding Riemann sums. Ties
among opponents cost O(M/N), uniformly through every cutoff. A collision
AT the tester's clock has probability at mostρ/N and costs O(M/N), even
when joining rewards have arbitrary sign or size up to M. Thus uniformly
over ALL finite k, its payoff differs from F_i(θ_N) by O(M/N). This
includes k=0, k>N, and arbitrarily moving deadlines. Every θ is approached
by actual grid testers, including the actual empty date0 and the actual
finite dateN+1 after the whole word. Continuous F_i therefore gives the
maximum in(TW1) as the finite supremum limit. Never has its separate
passive integral; the late finite test adds

    s_i ∏[j≠i](1−ρλ_j)≥0.

Never is dominated by that actual late finite test for every N, not
discarded by a convention. Affinity of complete-law deviations now
identifies these as the FULL behavioral caps. The constants in the
uniform errors are inessential; no bounded response menu or omitted
clock class is used.

This word is only a finite-law REALIZATION of the explicit pair(TW1).
It is not an assertion that an atomless controller suffices for UE;
DR6 already disproves that different architecture.

### TW2. Full finite/Never prices, including simultaneous-response spikes

Write γ_i=(Γλ)_i. Uniformly in θ,

    F_i(θ)=s_i+ρθγ_i+O(Mρ²),
    u_i=ρ(s_i+γ_i)+O(Mρ²),
    b_i=s_i+ργ_i⁺+O(Mρ²).                     (TW2)

These follow directly by expanding the at-most-three survival factors
in(TW1). The singleton probabilities give the second equality because
Σλ_i=1. This is a produced full-cap expansion, not a favorable cap
selector. If γ_i>0, F_i is strictly increasing for all sufficiently
smallρ, since F_i′=ρ(γ_i+O(Mρ)) uniformly on[0,1].

One cannot replace the word by one common quitting date. Reuse the
earlier exact table with owns1, ALL passives2, ALL nonsingleton
participants3. For λ_i=1/4 and ρ=1/2, (TW1) gives

    μ_j=1695/16384,
    u_i=11865/16384,
    b_i=681/512,
    D(u,b)=9927/4096.

Indeed F_i is increasing, its late value is1+[1−(7/8)³], and each
singleton column sums to7. At ONE common date with the same finite
probabilities1/8, the exact cap is instead425/256, with prescribed
payoff201/256 and sum debt7/2. Its joining test, not its late test,
causes the larger cap. This complete sixty-entry table is already
solved by pure grand Nash; it tests the word's response accounting,
not a positive-gap claim or a stronger trapping regression.

### TW3. A derived all-direction constraint at every original minimum

Fix ANY produced marked ORIGINAL full minimum, and retain its actual
limits n_i>0, ν=∏n_i, h_i=ν/n_i, R_i, U_i and B_i. Set

    κ_i=(B_i−R_i)/h_i≥s_i,
    E={i:κ_i=s_i}.

SG proves E nonempty. Its literal finite-block+EMPTY-seam graft puts
EVERY carrier tail w=(u,b) on ONLY the original Never branches and gives

    D(graft)−δ=ν[Σ_i(b_i−κ_i)⁺/n_i−Σ_i u_i].   (TW3)

All old finite masses, original finite/Never tests and moving later
tests are retained as in SG. Apply this to the actually produced(TW1),
for EVERY λ and ρ, and use the TRUE all-law minimum. This gives the
global finite-amplitude inequality

    Σ_i (max_θ F_i(θ)−κ_i)⁺/n_i
       ≥Σ_j μ_j Σ_i r_i({j}).                 (TW4)

For i∉E the clipping term is zero for sufficiently smallρ. Dividing
byρ and using(TW2), without differentiating a selected strategy, gives

    Σ[i∈E] (Γλ)_i⁺/n_i
       ≥Σ_i [s_i+(Γλ)_i]  for EVERY simplex λ. (TW5)

The earlier one-date price included pair-joining spikes. The complete
word suppresses those spikes while retaining ALL actual responses,
so(TW5) contains only the singleton matrix. It does not assert that
the old cap is unchanged, or that any arbitrary positive-payoff tail
is free. Its right side can be negative for some λ.

### TW4. Actual source exclusion: not all c-active owners can play only Never

At THIS SAME no-UE table, the tracked theorem
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
produces λ with γ_i=(Γλ)_i>0 for EVERY i. Its only semantic hypothesis
is no uniform-equilibrium payoff for that literal Fin4 table; no
normality or another reward normalization is transported. The positive
full floor provides that hypothesis, as in NP. The projective matrix
is exactly the receiver-row singleton difference matrix Γ here.

For this produced λ, (TW5) rewrites as

    Σ[i∈E] [(1−n_i)/n_i] γ_i
       ≥Σ_i s_i+Σ[i∉E]γ_i>0.                 (TW6)

Consequently SOME j∈E has n_j<1. Thus EVERY produced original minimum
has a c-active owner with BOTH strictly positive ORIGINAL finite mass
and strictly positive ORIGINAL Never mass. Pure-Never observers cannot
carry the entire c-wall. This is not just an alias-counting statement.

The contradiction is literal. If every j∈E had n_j=1, (TW2) makes
the bracket in(TW3) strictly negative for some sufficiently small fixedρ.
Choose N large, then an old finite-law minimum approximant and the
original empty-seam graft. Full-cap convergence makes that ACTUAL
independent finite law have D<δ. Its joint Never is lower, which is
legal: common-ν rigidity concerns only equality, not a lower competitor.
Thus no cap-control or target-minimum premise was supplied.

### TW5. Surviving claim and concrete next comparison

This is a pointwise source restriction, not a full consumer or an export
request. It uses an end graft only to eliminate the named pure-Never
c-wall geometry. It now PRODUCES an owner j whose ENTIRE old finite
conditional law exists with mass1−n_j>0 AND whose last-empty finite
cap equals R_j+h_j s_j. CV's ν-changing finite/Never conditioning
comparison is therefore applicable at a c-active owner, not merely
some unrelated mover. The all-direction inequality(TW5) is also exact
data for an asymmetric existing-mass comparison.

The selected j need not own the earliest bridge, stop at an atom,
have all its finite clocks maximizing, or be the only c-active owner.
No debt descent is claimed when such a finite branch exists. Both old
solved traps have n_i=1/2 and satisfy the required positive-odds budget,
so they do not falsify(TW6) and do not validate a universal repair.
The remaining task is to couple a change of that produced old finite
branch with another law/calendar change and bound ALL born caps.

## Zero excess debt transfers the live source to a nontrivial native equilibrium

### ZE1. Exact excess decomposition and the useful boundary

This is COMPLETE ORDINARY, UNREVIEWED supporting mathematics. It
does not assert that the boundary must occur, that a native-zero-own
equilibrium is absorbing, or that a paid-clock consumer is available.
Its role is to identify precisely when AP's own-gain term vanishes
at EVERY owner, rather than interpreting every finite branch as useful
payoff slack.

At a produced NP minimum let

    eᵢ=dᵢ−νsᵢ,   hᵢ=∏[j≠i]n_j,   mᵢ=1−nᵢ.

For mᵢ>0, denote by Aᵢ^F the payoff of its original conditional
finite law against the original opponents. Then

    Uᵢ=mᵢ Aᵢ^F+nᵢRᵢ,
    eᵢ=mᵢ(Bᵢ−Aᵢ^F)+nᵢ(Bᵢ−Rᵢ−hᵢsᵢ).               (ZE)

Both summands are nonnegative: the finite conditional strategy is
an actual deviation, and the late finite-response limit is
Rᵢ+hᵢsᵢ≤Bᵢ. The same identities follow on the old marked chart by
bounded original likelihood transport. For mᵢ=0, simply use

    eᵢ=Bᵢ−Rᵢ−hᵢsᵢ,

because nᵢ=1. Thus eᵢ≥0 for every owner, and eᵢ=0 implies BOTH

    Bᵢ=Rᵢ+hᵢsᵢ,
    Aᵢ^F=Bᵢ whenever mᵢ>0.

More explicitly, in the second assertion the finite conditional
prescribed law has zero integral of the nonnegative cap shortfall;
its compact finite clocks are cap-maximizing almost everywhere. No
attained actual ℕ deadline is inferred. At NR's further table both
d and ν are common to all minima, so the numbers eᵢ are likewise
common. This is not payoff or profile uniqueness.

The actual unrestricted lower bound νsᵢ≤dᵢ is also supplied by
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
in `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
The declaration has no cap-attainment, Nash, or sign hypothesis on
the other reward coordinates. Its proof, and the adjacent finite-
response limit declaration, were inspected statically for this step.

### ZE2. ALL-zero excess gives actual native-zero-own near equilibria

Assume now eᵢ=0 for all four owners. Define ONE new raw table

    zᵢ(S)=rᵢ(S)−sᵢ for every nonempty S.

Never remains0, so z has own singletons0. This is a different game,
not a claim that original no-UE, original margins, or an original
minimum automatically survives row translation.

For EVERY actual profile p with joint Never probability ν(p), one
has the exact identities

    Uᵢ^z(p)=Uᵢ^r(p)−sᵢ(1−ν(p)),
    Bᵢ^z(p)=Bᵢ^r(p)−sᵢ,
    dᵢ^z(p)=dᵢ^r(p)−ν(p)sᵢ.                          (ZT)

Here the cap equality has a complete finite/Never check. Every
deterministic finite response absorbs surely, hence its value shifts
by exactly −sᵢ. In r, Never is dominated by the limiting finite
responses because sᵢ≥0. In z, whose own reward is0, delayed finite
responses converge to its Never value itself. Thus the supremum of
finite responses is the full cap in BOTH tables, even if the
supremum is not attained. Behavioral responses are already included
by the pure-clock cap reduction. These facts prove (ZT), not merely
an inequality for a selected old maximizing response.

Use the ORIGINAL actual finite-law minimizing sequence pⁿ.
Its Never products converge to ν>0 and its original debt vector
converges to d. By (ZT) all four native debts converge to0, while

    Uᵢ^z(pⁿ) → Uᵢ−sᵢ(1−ν)=Bᵢ−sᵢ,
    Bᵢ^z(pⁿ) → Bᵢ−sᵢ.

The same sequence retains the original positive first-date mixture,
its random first-root coalition law, and at least two mixed suppliers.
It is not an AllNever realizing sequence. The unchanged finite-root
response payoff differences also retain the original positive-event
root/later kernel distinction. Its native bridger now has ZERO debt;
original paidness must not be transported to z.

Indeed ZE1 and (ZT) give native Never value

    Rᵢ^z=Rᵢ−sᵢ(1−hᵢ)=Bᵢ−sᵢ

for EVERY owner. Native Never and the old finite cap tests all
maximize. Thus this transfer expressly does not create an absorbing
native Nash law. The actual sequence is an unrestricted terminal
ε-Nash sequence as ε→0, with the displayed fixed payoff limit.
The corresponding native uniform-equilibrium payoff follows from
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Its exact hypotheses were inspected: vanishing nonnegative Nash errors,
payoff convergence, and bounded finite game data, all supplied here.
This is an ordinary adapter using a tracked semantic endpoint, not a
claim that ZE's new source inference has been checked in Lean.

### ZE3. Absorbing floor survives; no absorption conclusion follows

On EVERY absorbing actual profile ν(p)=0, (ZT) gives

    D_z(p)=D_r(p).

Consequently the actual absorbing infima and their closed-carrier
debt minima agree:

    Δ_abs(z)=Δ_abs(r)=δ+g>0.

On the native FULL class, by contrast, AllNever is an exact
equilibrium, and the nontrivial sequence in ZE2 also has debt→0.
The full minimum is0, not the old δ. No original positive-minimum
margin or original debt rigidity is asserted in z. The singleton
matrix does remain exactly Γ: its off-diagonal entries are
zᵢ({j})−zᵢ({i})=rᵢ({j})−sᵢ.

Thus the ALL-zero-excess branch supplies stronger native data than
the trivial AllNever equilibrium, but still presents an honest
absorbing-equilibrium problem. An assertion that the same sequence
can be made absorbing with no full-cap cost is precisely unproved.
It would close this branch; merely replaying the native law is not
that proof, because a responder can wait through its earlier blocks.

If some eᵢ>0 instead, AP's strict own-gain applies ONLY when such
an i is also c-active and has mᵢ>0. TW alone has not produced this
intersection. If eᵢ>0 only at other finite or pure-Never owners,
the two-law relocation still requires a genuinely coupled head
comparison, with every changed head cap retained. This is the exact
remaining distinction, not a favorable-member claim.

## Coupled existing-finite-mass relocation with every born cap retained

### AP1. Actual family and current status

This is a COMPLETE ORDINARY, UNREVIEWED comparison ledger, not a
new source theorem or a UE producer. The live question is whether its
finite-amplitude parameters, or a genuinely richer simultaneous calendar
change, can force debt below the true original minimum. No favorable
head payoff, head cap or continuation equilibrium is supplied.

Fix the same NP table, a produced original minimum, and an actual
finite-law realizing sequence pⁿ. Write nᵢ>0 for the limiting marginal
Never masses, ν=∏ᵢnᵢ>0 and mᵢ=1−nᵢ. TW supplies an owner j with

    m_j>0,  B_j=R_j+h_j s_j,  h_j=∏[i≠j] nᵢ.

Choose another owner k≠j with m_k>0. Such an owner exists: the
first collision has at least two positive root suppliers, whether or
not j is one of them. For sufficiently large n, let F_jⁿ,F_kⁿ be the
literal old laws conditioned on stopping at a finite date. All other
old laws remain unchanged. For arbitrary parameters s,x∈[0,1], form
the actual head

    j: s F_jⁿ+(1−s)δ_Never,
    k: x F_kⁿ+(1−x)δ_Never.

Take the fixed original marked source chart. These are bounded old-law
likelihood reweightings: on j's finite mass the ratio is s/m_jⁿ,
on its Never mass (1−s)/n_jⁿ, and similarly for k. The denominators
have positive limits. Thus the same rectangle-product and ALL-moving-
tester argument gives limiting head data Uʰ(s,x),Bʰ(s,x),Rʰ(s,x).
In particular Bʰ is the unrestricted cap, not a restricted finite menu.
This appeal is only to the ordinary source/transport proof already
recorded here; it does not claim a new checked Lean theorem.

After the ENTIRE literal head, insert an actual empty date and N new
dates. Redirect absolute probability ℓ from j's head Never mass to
the uniform law on those N dates, with 0≤ℓ≤1−s. Its residual Never
mass is 1−s−ℓ. If 1−s=0 then ℓ=0 and no conditioning is performed.
First take the original-source limit, then N→∞, or use a diagonal
sequence. Every finite stage is an independent actual stopping-law
profile. No common random calendar selector or payoff sharing is used.

### AP2. Exact full-cap formula and zero-survival boundaries

Put

    h_jʰ=(1−x)∏[r≠j,k]n_r,
    Wᵢʰ=∏[r≠i,j]n_rʰ  for i≠j,
    n_kʰ=1−x,  n_rʰ=n_r for r≠j,k,
    Lᵢʰ=Rᵢʰ+Wᵢʰ(1−s)sᵢ  for i≠j.

The empty date after the whole head is an ACTUAL finite response, so
Lᵢʰ≤Bᵢʰ. The limiting complete new pair is exactly

    Uᵢ′=Uᵢʰ+h_jʰ ℓ rᵢ({j})                           for every i,
    B_j′=B_jʰ,
    Bᵢ′=max(Bᵢʰ, Lᵢʰ+Wᵢʰ ℓ Γᵢⱼ⁺)                  for i≠j,
    ν′=h_jʰ(1−s−ℓ).

These are multiplication formulas; they divide by no survival
probability. They remain valid at s=1, x=1, ℓ=0 and ℓ=1−s.
For j, the full cap is independent of its own stopping law.

Here is the ALL-response upper and lower check for another owner i.
Every actual finite response through the old head has exactly its
head value: j's new late finite branch is still invisible at that test.
The empty seam and every later test have, apart from one joining atom,
value

    Rᵢʰ+Wᵢʰ[(1−s)sᵢ+ℓ θ Γᵢⱼ],  0≤θ≤1.

The joining atom has probability at most ℓ/N and payoff error at most
2Mℓ/N, uniformly over ALL moving test dates. There are no further
opponent finite atoms in the word. The supremum of the displayed
affine values is Lᵢʰ+WᵢʰℓΓᵢⱼ⁺; θ=0 and θ=1 are attained by
actual finite tests before and after the word. A Never response gives

    Rᵢʰ+Wᵢʰℓrᵢ({j});

the θ=1 finite response exceeds it by
Wᵢʰ(1−s−ℓ)sᵢ≥0. This uses the actual same-table nonnegative own
singletons. Consequently Never introduces no omitted cap. Combining
the old-head tests, seam, word, later tests and Never proves both
bounds for Bᵢ′. Behavioral deviations add no larger value, since the
unrestricted cap is the supremum of these pure stopping choices.

Thus the COMPLETE debt comparison is

    D′=Dʰ−h_jʰℓ∑ᵢrᵢ({j})
       +∑[i≠j](Lᵢʰ+WᵢʰℓΓᵢⱼ⁺−Bᵢʰ)⁺.                 (AP)

The head caps in (AP) are actual produced data at the changed head,
not inherited upper bounds from the old minimum. Forgetting that
distinction would incorrectly turn this identity into a consumer.

### AP3. The old c-active finite branch has an exact own-gain ledger

Hold x=m_k and relocate a∈[0,m_j] of j's OLD finite mass:

    s=m_j−a,  ℓ=a.

Its original marginal Never mass is retained. Let A_j^F be j's
payoff against the original opponents when using its literal old
conditional finite law. Then

    U_j=m_j A_j^F+n_jR_j,
    d_j=m_j(B_j−A_j^F)+νs_j.

The new j-payoff increases by exactly

    a(B_j−A_j^F)=a(d_j−νs_j)/m_j ≥0,

and B_j is unchanged. This is an actual relocation of old finite
stopping mass, not an end-Never-only extension. Equality is possible:
the old finite conditional law may already consist of j's cap tests.
Nothing here assigns the other owners a nonpositive cap cost.

Changing x as well gives a genuinely ν-changing coupled comparison:
for x=m_k+b and the same relocation, ν′=n_j(n_k−b)
∏[r≠j,k]n_r. One may also choose ℓ≠a to change j's Never mass.
All admissible choices are covered by (AP), including sure endpoints.
The true floor requires D′≥δ for every such choice; a strict reverse
inequality would give a literal finite witness after choosing large
enough source and word indices. No parameter choice producing that
reverse inequality has been proved.

### AP4. Exact geometric-pivot scope and a minimal hazard countertest

The narrow source route inspected is `exists_geometric_pivot_payoff_eq_and_caps_le`
and `exists_geometric_pivot_payoff_eq_and_exploitability_le`
in `UniformEquilibrium/Quitting/Terminal/GeometricPivotCapDomination.lean`,
with `quittingTerminalPayoff_pivot_late_response_eq`
in `UniformEquilibrium/Quitting/Terminal/FiniteOpponentPivotResponseFormula.lean`
and `geometricPivotStoppingLaw`
in `MathUE/ProbabilityMassFunction/GeometricPivotStoppingLaw.lean`.
The exact declarations and needed definitions were read statically;
no Lean build was run for this note.

Against opponents whose finite choices all precede a deadline, a
pivot's head and Never atom are retained and its finite tail is
replaced by a geometric finite law. Prescribed outcome probabilities
and payoffs are preserved for EVERY positive hazard. The cap-safe
hazard is selected by

    tail mass × hazard = old first positive late atom.

Every new late response is then a convex interpolation of the old
response at that atom and the old limiting late response. The latter
need not be attained. This proves genuine ALL-cap domination for
that selected hazard, including Never. It does not prove domination
for an arbitrarily small hazard, and does not put TW's finite j-mass
beyond all its opponents' finite clocks.

For the hazard issue alone the following THREE-player complete table
is sufficient. Players are h,j,o. The h row is the participant
indicator: r_h(S)=1 iff h∈S, otherwise0. The j row is1 only on
the singleton {j}, and0 on the other six nonempty coalitions.
The o row is1 on {o} and {h}, and0 on the other five coalitions.
Thus all own singletons are1. Prescribe

    h: ½ at date0, ½ Never;
    j: ½ at date1, ½ Never;
    o: Never.

The payoff vector is (½,¼,½). The full caps are (1,½,¾): o's
test at0 pays½, its test at1 or any later finite date pays¾, and
Never pays½. There is no actual gap test between dates0 and1.
For j the first late atom equals its whole finite tail, so the
matched geometric hazard is1. Replacing that tail by hazard½
preserves ALL prescribed payoffs and Never masses but gives o a
date1 response worth7/8. Its full cap is7/8, the other caps remain
1 and½, and total debt rises from1 to9/8. This falsifies the
unrestricted-hazard strengthening, not the named matched producer.

In the same table the existing c-active j branch can instead be
completed in a genuinely ν-changing cap-controlled fashion. Increase
its finite tail from½ to¾, decrease Never to¼, and choose hazard2/3,
so the first atom remains½. All three full caps remain (1,½,¾),
j's prescribed payoff rises from¼ to3/8, and total debt falls from1
to7/8. Every late o-test interpolates the unchanged first value¾
and the new late limit5/8; this checks ALL deadlines and Never.
The regression is already solved: pure singleton {h} at date0 is
an unrestricted Nash profile with D=0. It is neither a positive-gap
example nor a counterexample to the genuine global-minimum floor.

The strongest surviving use is therefore (AP), with actual changed
head caps retained. A matched payoff-preserving geometric compression
alone changes no ν and supplies no descent; its cap-safe hazard does
not remove the coupled-head pricing problem. The next calculation
must change the old head as well and compare its complete caps, rather
than inserting an unproduced empty-gap or free-hazard hypothesis.

## Full reward sensitivity supplies a lower kernel ledger, not a coupled consumer

### GR1. Exact question, source inspection and status

Could differentiability of the GLOBAL full-debt infimum supply an upper
price for all cap branches born after moving existing finite mass to a
maximizing ROOT response? The scalar recipient/constant directions used
in DR and NR do not specify those branches. Here the numerical parameter
is the ENTIRE60-coordinate table, not an old profile, Nash row or supplied
response selector.

The following common-kernel lemma is a COMPLETE ORDINARY, UNREVIEWED
derivation. The proposed upper-pricing implication is exactly FALSE by
GR4. This is supporting mathematics and a mechanism retirement, not a UE
consumer, unrestricted positive-gap example or export request.

Narrow source lookup for this attempt inspected
`lipschitzWith_quittingTerminalDebtSumInf`,
`abs_quittingTerminalDebtSumInf_sub_le_of_reward_close` and
`continuous_quittingTerminalDebtSumInf` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumRewardGeometry.lean`.
Their actual infimum changes by at most8 times the uniform reward error.
The Rademacher application and the distinction between a regular value
and unique underlying minimizers were inspected in
`MathUE/Analysis/CompactLinearMinimumRigidity.lean`, including
`exists_mem_open_all_minimizers_eq`. That LINEAR-infimum declaration is
not invoked as a nonlinear-infimum theorem here. The ordinary marked
source argument used below is the original-chart, rectangle-kernel and
ALL-moving-response proof already retained in this notebook and in the
canonical NP packet. It is not claimed to be fully Lean-integrated.

### GR2. Every marked minimum has one common convexified regret kernel

Let Δ(r)=inf_p D_r(p), with p ranging over ALL actual independent complete
laws and caps ranging over ALL finite responses and Never. At a table r
where Δ is differentiable, write its derivative as

    dΔ_r(H)=Σ_i Σ_[S≠∅] G_i(S) H_i(S).

Fix ANY produced marked minimum q at this table. Let μ(S) be its ORIGINAL
prescribed first-coalition probabilities, so Σ_S μ(S)=1−ν. For each
complete compact test point t let σ_i(t,S) be the first-coalition
probabilities when ONLY owner i replaces its whole law by that pure
test. These are probability coefficients independent of rewards;
Never may leave total mass below1. Put

    M_i={t: Σ_S r_i(S)σ_i(t,S)=B_i(q)}.

The marked kernel proof gives continuity of t↦σ_i(t,·), including
retained ties, zero-mixture cuts, the final finite test c and Never.
It also gives, for EVERY other bounded reward table a at the SAME laws
and SAME old-chart witness sequence,

    F_q(a)=Σ_i max_t Σ_S a_i(S)σ_i(t,S)
                  −Σ_i Σ_S a_i(S)μ(S),
    Δ(a)≤F_q(a),       F_q(r)=Δ(r).                (GR1)

No minima are transported between tables: the inequality follows simply
by reusing that literal actual witness sequence. Finite dimensionality
and the compact complete test menu make the directional derivative of
F_q the maximum of its CURRENT maximizing test slopes. This is an INNER
maximum statement, not the false OUTER fixed-minimizer Danskin formula.
Differentiating only the upper inequality in (GR1) gives, for EVERY H,

    Σ_i H_i·[G_i+μ]≤Σ_i max_[t∈M_i] H_i·σ_i(t).    (GR2)

Finite-dimensional separation now implies

    G_i+μ∈conv{σ_i(t):t∈M_i}  for EVERY owner i.    (GR3)

Indeed a separating row direction, with all other rows zero, would
contradict (GR2). The convex hull is compact. Consequently each owner
has a probability mixture β_i of at most16 maximizing compact tests
whose EXPECTED terminal coefficient vector equals G_i+μ. These tests
need not be outcome-equivalent and their mixture is a mathematical
selector, not a joint public signal. No prescribed strategy is changed.
In the nonsure NP source Never is strictly submaximal; all maximizing
tests are finite and their coefficient sums are1. Thus

    Σ_S G_i(S)=ν,      r_i·G_i=d_i.                (GR4)

The vector G is selected by the TABLE before q. Hence all produced
marked minima at a regular NP table have common d AND common ν without
claiming common prescribed outcomes or response laws.

Every minimum pair in the original closed carrier admits a finite-law
approximating sequence, by the actual finite-law approximation theorem;
the marked producer may be applied to a subsequence of that sequence.
Thus the common d conclusion also covers EVERY carrier minimum pair,
not just a chosen marked realization. Joint Never is not a coordinate
of that carrier pair; its common value is asserted for the produced
realizations and the actual minimizing limits.

The remaining coefficient consequence is

    μ(S)+G_i(S)≥0;
    G_i(S)<0 ⇒ μ(S)>0 at EVERY produced minimum.   (GR5)

This is the strongest pointwise coefficient information proved here.
There is no assertion that G itself is a terminal distribution.

### GR3. Fresh selection is possible; upper cap pricing does not follow

Starting with the reviewed separated table, common-contract slightly if
needed to enter the strict unit cube. Positive own rewards, δ>0 and the
strict full/absorbing separation persist on a nonempty open numerical
neighborhood, by the actual8-Lipschitz estimates for each domain.
Rademacher supplies differentiability points of Δ of full measure in
this finite-dimensional neighborhood. Remove the finitely many row
equality hyperplanes and choose ONE point. This selection is before ALL
new minimizing sequences. At that point (GR4) supplies common minimum
debts directly; the original ordinary NP geometry can then be applied.
No old common-debt or chronology assertion is preserved by fiat. This
is an alternative supporting source selection, not another export.

The hoped-for consumer does NOT follow. For the selectors β chosen at
one minimum define at another actual profile p

    L_β(p)=Σ_i E payoff_i(β_i,p_-i)−Σ_i U_i(p).

By definition of the FULL caps,

    L_β(p)≤D_r(p),       L_β(q)=δ.                (GR6)

The inequality has the wrong direction for proving that a proposed
coupled p has lower debt. A lower value of L_β does not price the changed
maxima from above. Differentiability of the OUTER value does not convert
the selected mixtures into common maximizing responses after law
movement. The exact next test falsifies that inference even at a TRUE
global minimum, with all own rewards positive and an OPEN regular-value
neighborhood. It does not falsify GR2 or a future use of additional NP
hypotheses.

### GR4. Complete actual boundary test: smooth global value, uncontrolled births

Let I={0,1,2,3}. The following formula specifies ALL60 nonempty entries,
with independent private complete laws and AllNever payoff0.

    r_0(S)=1 if 0∈S, and0 otherwise.

For recipient1, if 0∈S set r_1(S)=1 exactly when the membership bits of
1 and2 agree, and0 otherwise. If 0∉S set r_1(S)=1 exactly when 1∈S.
For recipient2, if 0∈S set r_2(S)=1 exactly when those two bits differ,
and0 otherwise. If 0∉S set r_2(S)=1 exactly when 2∈S.
For recipient3, if 0∈S set r_3(S)=1 exactly when 3∉S, and0 otherwise;
if 0∉S set r_3(S)=1 exactly when 3∈S. Every own singleton pays1.

Take p_0=δ_0, p_3=δ_Never, and let owners1,2 quit at0 with rates
q_1=1/2+a, q_2=1/2+b, keeping all remaining mass on Never.
Owner0's full cap and prescribed payoff are1. Owner3's are also1.
Because owner0 stops SURELY at0, EVERY finite response after0 and Never
of owner1 or2 has the same passive outcome; there is no omitted late
solo or joining response. Their exact full ledgers are

    U_1=1/2+2ab,       B_1=1/2+|b|,
    U_2=1/2−2ab,       B_2=1/2+|a|,
    D=|a|+|b|.                                     (GR7)

At a=b=0 this is an ACTUAL terminal Nash profile and true full minimum0.
Fix β_0=δ_0, β_3=δ_1, and β_1=β_2=(δ_0+δ_1)/2. All selected tests are
FINITE and maximize at the original profile. Their response outcome
distributions equal its prescribed distribution μ, so G=0 in (GR3).
Yet for ALL a,b∈[−1/2,1/2], their expected response payoffs for owners1,2
remain1/2, whence

    L_β(p)=0,  while D_r(p)=|a|+|b|.               (GR8)

Thus even an exact common response-kernel selector and a flat complete
selected-regret polynomial leave the born full caps entirely unpaid.
The changed mass is existing finite root mass and Never; this is not an
atomless approximation or a failure caused by an excluded deadline.

The OUTER value Δ really is smooth here. In the full60-coordinate
sup-norm ball of radius1/20 about this table, the two-player root game
between1 and2 still has one interior mixed Nash pair with both rates
in(3/10,7/10): each endpoint action difference has its old sign and
magnitude at least9/10. Anchor0's root payoff is at least19/20, whereas
any later test is at most1/20+(7/10)²; Never is no larger. Dummy3's wait
payoff is at least19/20 and its root join payoff at most1/20. Hence the
same sure anchor and passive dummy extend that mixed pair to a FULL
actual Nash profile throughout the ball. All later finite/Never responses
of1,2 remain exactly their root-Wait action because the anchor is sure.
Consequently Δ=0 on this OPEN full-table neighborhood, so its full
derivative is identically0. The failure cannot be repaired merely by
asking for outer differentiability or regular reward data.

### GR5. Decision and the precise surviving root construction

Do not use GR's convexified selectors as an upper-cap compiler. AP remains
a correct actual comparison, but its fixed conditional-finite library
can omit a root clock of an unsupported bridger. The next finite-mass
construction instead inserts that ACTUAL retained root clock and changes
a second owner's Never/finite balance. Conditional old tails are changed
by literal bounded likelihoods; their full caps must be recomputed, and
the root uses the exact max(Q_i,A_i+α_i b_i) adapter. Original common ν is
not imposed on a lower-debt competitor. No source-forced favorable member
of this new family has yet been proved. GR supplies no missing upper
bound, and a merely formal active-mixture field would not close that gap.

## Actual two-date cohort changes must retain the original intermediate clock

### CS1. The missing calendar seam and the exact repair

The current direct construction moves existing finite mass onto a genuine
root maximizing clock, including an owner whose old root rate is0, and
changes another owner's finite/Never balance. A tempting numerical family
is T_x(T_y(v)), with old source T_q(v), taking x=q,y=0 at the old point.
That last assertion is NOT automatic: T_0(v) inserts an ACTUAL empty date
before the old tail, and its caps are max(s_i,b_i(v)).

Thus a zero-rate stage is not the identity on an arbitrary original
carrier tail. The previous finite-prefix adapter retains exactly this
branch. The repair here is to extract the tail's EXISTING first stage,
not to supply cap domination or ignore an early reply.

This section is COMPLETE ORDINARY, UNREVIEWED supporting mathematics.
It introduces no new source assumption and does not claim that the
resulting family contains a lower-debt member. Its finite realization is
part of the direct construction; the remaining global comparison is open.

### CS2. Exact cap price of an inserted empty date

At an arbitrary original prefix pair T_q(v), write

    B_i^p=max(Q_i(q),A_i(q)+α_i(q)b_i(v)).

Inserting one empty date AFTER its root, while shifting the ENTIRE old
tail one date later, leaves prescribed terminal payoffs unchanged and
gives exactly

    B_i^new=max(B_i^p,A_i(q)+α_i(q)s_i),
    D_new−D_old=Σ_i[A_i(q)+α_i(q)s_i−B_i^p]⁺.       (CS1)

This is a full cap equality: root tests give Q; the new empty-date test
gives A+αs; every shifted old finite tail test and literal Never keeps
its old value. No further date has a new outcome kernel. In particular,
if i is an old root/later bridger and b_i(v)<s_i, its cap rises by

    α_i(q)[s_i−b_i(v)]>0                           (CS2)

at an NP minimum, since α_i(q)>0 there. Strong ORIGINAL margins
B_i^p>s_i do not imply that this intermediate cap is dominated.

A minimal full-Fin4 boundary test specifies all60 entries by
r_i(S)=1 when S={i}, and0 otherwise. The actual tail with ALL four
players sure at date0 has U=B=0 and is full Nash. An inserted empty date
keeps U=0 but gives every owner a solo payoff1 by quitting in that date,
so B_i=1 and D=4. All later finite tests and Never pay0. This is a
zero-gap solved table, not an NP counterexample; it isolates the false
calendar identity without any approximate or missing-response issue.

### CS3. Extract an ACTUAL second root at the same source sequence

Use the literal finite conditional-tail sequence v^k supplied by NF for
the original minimum T_q(v), not a new independently selected tail.
Its own Never masses converge to n_i^v>0 by NP. Let z_i^k be the mass
of its ACTUAL date0. Condition on not stopping at that date, and shift
all later finite dates down by1; keep Never unchanged. Call this actual
independent product tail w^k. For all large k,

    1−z_i^k≥n_i^v/2>0.

Thus the conditional law exists ordinarily for EVERY owner, with a
uniform density multiplier at most2/n_i^v. Both payoffs and complete
caps of w^k are bounded. Pass to ONE subsequence on which z^k→z,
(U(w^k),B(w^k))→w∈K, and its Never masses also converge. The exact
literal prefix formula and its continuity give

    v=T_z(w),       T_q(v)=T_q(T_z(w)),             (CS3)
    z_i<1,     n_i^w=n_i^v/(1−z_i)>0.

All finite/Never responses are included: a tail response at0 is the
second original root response, and a response at a later finite date
or Never is the translated full conditional-tail response. No Nash,
minimum, cap attainment, or sure filler is required for w. At NP source
survival boundaries there are no sure z_i; outside this source the
usual arbitrary law filler at zero survival is harmless in exactly the
same α=0 cases as NF4, not a license to discard the sole-sure owner's
opponent continuation cap.

If b_i(v)<s_i, then the root response Q_i(z)≤b_i(v) and the reward bound
|r|≤M gives

    1−α_i(z)≥[s_i−b_i(v)]/(2M)>0.                 (CS4)

Indeed Q_i(z)=s_i on the all-opponent-Continue event and differs from it
by at most2M on its complement. Hence some OTHER owner has a positive
actual second-stage rate. This is an output, not supplied second-stage
mass. It does not assert two second-stage suppliers or second-stage Nash.

### CS4. Complete finite-amplitude family, with existing mass coordinates

Fix the produced w. For arbitrary x,y∈[0,1]⁴ the actual pair
T_x(T_y(w)) belongs to original K: prefix exact x,y to the SAME finite
w^k witnesses, then take limits. Define

    H_i(t)=t_i Q_i(t)+(1−t_i)A_i(t),
    c_t=∏_j(1−t_j).

Its prescribed payoff and FULL cap are exactly

    U_i'=H_i(x)+c_x H_i(y)+c_x c_y u_i(w),
    B_i'=max{Q_i(x),
             A_i(x)+α_i(x)Q_i(y),
             A_i(x)+α_i(x)A_i(y)+α_i(x)α_i(y)b_i(w)}.   (CS5)

These are respectively root0, root1, and the ENTIRE old conditional
tail cap. In particular the third branch retains all arbitrarily late
finite replies and Never; no named tail maximizer is required. Formula
(CS5) remains valid at every zero/sure rate without dividing by survival.

The affine OWN-law coordinates are absolute masses

    a_i=x_i,       ℓ_i=(1−x_i)y_i,
    t_i=1−a_i−ℓ_i=(1−x_i)(1−y_i).

On the triangle a_i,ℓ_i≥0, a_i+ℓ_i≤1, the literal law puts a_i at
date0, ℓ_i at date1, and t_i on the shifted old law w_i^k. The original
point is a_i=q_i, ℓ_i=(1−q_i)z_i. Moving a_i versus ℓ_i changes EXISTING
finite mass between the two dates. Changing their sum also changes old
tail and Never mass; its joint Never limit is

    ν'=∏_i[t_i n_i^w].                             (CS6)

No common-ν restriction is imposed on a lower-debt competitor. Supported
atoms allow two-sided changes in their positive masses; a zero original
root atom permits only positive insertion there. A negative insertion
is not smuggled into the signed old-law theorem. A single-owner triangle
change has convex D because all its pure response payoffs and prescribed
payoffs are affine in that owner's law; true globality therefore blocks
it. The live attempt changes at least two owners.

The original source point satisfies D'=δ, not just a selected-polynomial
equality. Every point has D'≥δ by the actual global floor. At any point
with D'=δ, common debts and, at the optional NR table, common ν apply;
NF9's same-table first-root constraint applies to every nonzero first
root anew. These facts do not yet force a favorable finite-amplitude
point. The benefit of (CS5) is that this remaining decision is an actual
finite numerical comparison, with no changed-head cap hidden in an
unproduced field and no free-calendar assumption.

## Native equilibrium positivity does not create a nonzero exact prefix

### ZP1. Global source question and the already-known cap obstruction

This is COMPLETE ORDINARY supporting mathematics and an exact
architecture falsifier, not a new counterexample-class reduction.
The proposed route was to close ZE's ALL-zero-excess boundary by
prepending a nonzero one-stage Nash root to its native equilibrium
payoff. That route cannot be used without a genuinely different
strategic operation.

Assume the same NP table r and original minimum as ZE, with

    d_i=νs_i for EVERY i,       ν>0,       s_i>0.

Write S=Σ_i s_i, so δ=νS. At the native table
z_i(A)=r_i(A)−s_i for nonempty A, Never0, ZE gives an ACTUAL
terminal near-Nash sequence pⁿ with caps and payoffs both tending to

    u_i=B_i−s_i>0.

The strict positivity follows from the SAME original all-owner
singleton margin, not normality transported to z. The native
absorbing floor remains Δ_abs(z)=δ+g>0. These are the real source
data; the test in ZP2 does NOT have this absorbing floor.

If x is exact root Nash in z with continuation u, prefix it to pⁿ.
The pure root endpoints and every continuation cap converge, so
the complete cap--Nash cancellation gives native total debt→0.
The joint Never product tends to c(x)ν. The exact ZE row-translation
identity then gives ORIGINAL total debt tending to

    c(x)νS=c(x)δ.

If x is nonzero this is strictly below the ORIGINAL all-law floorδ.
Thus EVERY such exact root is AllContinue. This is also immediate
from the already-known original minimum cap game: root payoffs in
z at continuation u are root payoffs in r at continuation B minus
s_i in EVERY pure action profile, including AllContinue. The two
root games are strategically equivalent.

The precise checked cancellation is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
and its actual-profile total-debt specialization
`quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
The existing architectural no-go
`exactCapPrefix_joint_eq_self_of_unique_allContinue`
in `Research/Quitting/UniqueAllContinueCapStackNoGo.lean` was inspected
under its imports: an exact stack at such a fixed cap state is
allContinue and has zero absorption. This is Research evidence,
not an integrated new consumer. The native reformulation above
does not evade that invariant.

The actual finite-sequence argument matters: z is a different game,
the limiting native marked law need not be an attained ℕ profile,
and no global minimum assertion in z is made. Each prefixed pⁿ is
literal and all finite/Never response caps are retained before
applying the original floor.

### ZP2. A complete actual positive native equilibrium with no nonzero root

The following exact Fin4 table shows that positivity and a nontrivial
terminal Nash source alone do not force an escape from that cap
plateau. All own singletons are0 and Never pays0. Players0,1,2
are core players; player3 is a passive dummy. The following fifteen
rows give ALL60 finite rewards, in recipient order0,1,2,3:

    coalition        reward vector
    {0}              (0,2,2,8/7)
    {1}              (4/3,0,0,8/7)
    {2}              (4/3,0,0,8/7)
    {0,1}            (4/3,5,2,8/7)
    {0,2}            (4/3,2,−1,8/7)
    {1,2}            (4/3,−2,2,8/7)
    {0,1,2}          (4/3,1,3,8/7)
    {3}              (0,0,0,0)
    {0,3}            (0,2,2,−1)
    {1,3}            (4/3,0,0,−1)
    {2,3}            (4/3,0,0,−1)
    {0,1,3}          (4/3,5,2,−1)
    {0,2,3}          (4/3,2,−1,−1)
    {1,2,3}          (4/3,−2,2,−1)
    {0,1,2,3}        (4/3,1,3,−1).

Equivalently, adding3 to a nonempty core coalition leaves every
core reward unchanged; the core rewards at {3} are0. Dummy3
receives8/7 when passive and some core player quits, −1 when it
joins a core coalition, and0 when alone.

Let each core player's actual independent law put mass1/2 at date0
and mass1/2 at Never, while3 plays Never. Then ν=1/8 and EVERY
owner has U_i=B_i=1. A complete pure-clock check is

    owner             Quit0       ANY finite t≥1      Never
      0                  1                1               1
      1                  1                1               1
      2                  1                1               1
      3                −7/8               1               1.

For example Q_1=(0+5−2+1)/4=1 and its Never value is
(0+2+0+2)/4=1. For owner2, Q_2=(0−1+2+3)/4=1 and its Never
value is again1. Owner0's positive passive value occurs with
opponent-exit probability3/4, giving (3/4)(4/3)=1. The dummy
observes a core exit with probability7/8 and hence obtains1.
Since own singletons are0, EVERY late finite deadline is exactly
the Never value. Behavioral deviations are averages of these
pure clocks, so this is an unrestricted terminal Nash profile,
not just a date-zero binary-game equilibrium.

Now form the one-stage game with continuation u=(1,1,1,1).
Claim: its ONLY exact Nash root is AllContinue. This is universal
over all four root rates and includes EVERY quiet, mixed and sure
boundary, not merely the old half-rate root.

First, Continue strictly dominates Quit for dummy3: on a nonempty
core opponent event its advantage is8/7+1, and on the empty event
it is1. Thus every Nash root has x_3=0. Put

    a=x_0,       b=x_1,       c=x_2.

The exact three endpoint differences g_i=Quit_i−Continue_i are

    g_0=−(1−b)(1−c),
    g_1=−1+4a−(1+3a)c,
    g_2=−1−2a+(3+a)b.                           (ZP)

These formulas follow by the actual opponent-coalition expansion,
including the empty event's continuation1. That expansion agrees
with `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`
in `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`,
whose definitions and proof were inspected for this calculation.

If c=1, then g_1=−2+a<0, so b=0; but then g_2=−1−2a<0,
which forbids c=1. If b=1, then g_2=2−a>0, so c=1, already
impossible. Consequently b,c<1 at EVERY Nash root. This makes
g_0<0, hence a=0. Then g_1=−1−c<0 gives b=0; finally
g_2=−1<0 gives c=0. AllContinue is itself strict Nash because
each own singleton0 is below continuation1. This proves the
claim without a numerical equilibrium search.

In particular EVERY finite exact cap--Nash stack over the displayed
actual profile is the identity. Positivity of all four equilibrium
payoffs, independent positive Never masses, a random root outcome,
and supported finite maximizing clocks do not change that fact.

### ZP3. Exact nonclaims and the mechanism decision

This table is solved, not an unrestricted positive-gap example.
The pure date-zero coalition {2} is an absorbing terminal Nash
profile: its payoff vector is (4/3,0,0,8/7); owner2 is indifferent
to continuing, owner0 is indifferent to joining, and the joining
payoffs of owners1 and3 are respectively−2 and−1. Every other
finite/Never response sees the same already-absorbed outcome.
Thus Δ_abs(z)=0, unlike the genuine ZE source's δ+g>0.
The table is neither claimed row-generic nor an NP source.

For a further transparent boundary check, add1 to EVERY nonempty
reward, retaining Never0. The displayed half-rate profile then
has U_i=15/8, B_i=2 and d_i=1/8 for every owner, total debt1/2.
Its one-stage cap game at continuation(2,2,2,2) is exactly the
same game (ZP), up to row translation, so all exact cap prefixes
remain inert. Nevertheless pure{2} is still an exact absorbing
equilibrium and the TRUE debt minimum is0. Positive profile debt
and even an actual fixed-state plateau cannot replace the global
minimum hypothesis.

This falsifier does NOT refute an absorbing-equilibrium theorem
which uses the strict native absorbing gap or other produced data.
It retires the specific automatic nonzero-Nash-prefix inference.
The new APS scope check in PL8 also cannot supply that inference:
its sequential continuous path requires a zero payoff coordinate,
whereas ZE's source has all four native coordinates strictly positive.

The direct construction therefore returns to NONEXACT changes of
existing finite mass, with full root/intermediate/tail maxima kept
in the same ledger. A fixed-state exact-Nash extension is no longer
a live producer. No new export, UE theorem, native absorption
producer or additional positive-gap class exclusion is asserted.

## Negative conditional caps block an unpriced two-owner geometric exclusion

### GC1. The proposed implication and its precise failure

This is a COMPLETE EXACT architecture falsifier, not a new UE result
or positive-gap example. The proposed argument considered ZE's native
boundary with exactly two owners having positive finite mass. Their
supported-clock equations suggest geometric finite tails. If the two
decay rates differ, the slower owner eventually dominates remaining
finite mass. A negative singleton observer was supposed to preempt
that tail and contradict native Nash.

The missing implication was

    native conditional terminal Nash with own0 ⇒ tail cap≥0.

It is FALSE on an occupied first date. A date-zero reply joins
whatever opponents quit there; an empty solo reply BEFORE that
date is not an available clock. Even positivity of every original
equilibrium payoff, positive original Never masses, a random first
collision, and singleton column blockers do not repair the implication.
The full exact test below also gives an explicit cap price for
inserting the missing early test.

### GC2. Complete independent geometric equilibrium

Never pays0. The following fifteen rows specify ALL60 native rewards,
in recipient order0,1,2,3:

    coalition        reward vector
    {0}              (0,4,−1,1/2)
    {1}              (4,0,1/2,−1)
    {2}              (−1,−1,0,4)
    {3}              (−1,−1,4,0)
    {0,1}            (8,12,14,31/2)
    {0,2}            (0,4,−6,1/2)
    {0,3}            (0,4,−1,−6)
    {1,2}            (4,0,−6,−1)
    {1,3}            (4,0,1/2,−6)
    {2,3}            (−1,−1,−6,−6)
    {0,1,2}          (8,12,−6,31/2)
    {0,1,3}          (8,12,14,−6)
    {0,2,3}          (0,4,−6,−6)
    {1,2,3}          (4,0,−6,−6)
    {0,1,2,3}        (8,12,−6,−6).

Let m_0,m_1∈(0,1]. Independently use literal stopping laws

    P(T_0=t)=m_0(1/3)(2/3)^t,    P(T_0=Never)=1−m_0,
    P(T_1=t)=m_1(1/2)(1/2)^t,    P(T_1=Never)=1−m_1,
    T_2=T_3=Never,              t=0,1,2,....

There are NO empty finite dates. Every date has a positive atom
of BOTH finite owners. For any finite reply t of owner0,

    V_0(t)=4m_1[1−(1/2)^t]+8m_1(1/2)(1/2)^t=4m_1.

Every finite reply of owner1 analogously pays4m_0. Their Never
responses have the same values. Thus the two finite laws are
unrestricted exact best replies, for ALL finite probabilities m_0,m_1.

Conditional on BOTH owners drawing finite clocks, the first terminal
coalition is {0}, {1}, or {0,1} with probabilities respectively
1/4, 1/2, 1/4. This follows by summing the geometric series with
common factor(2/3)(1/2)=1/3: the one-date masses are1/6,1/3,1/6.
Consequently the passive Never payoffs are exactly

    R_2(x,y)=−x+(1/2)y+4xy,
    R_3(x,y)=(1/2)x−y+4xy,                         (GC)

where x,y are the conditional finite probabilities of owners0,1
at the current surviving tail. Their immediate Quit probabilities
are x/3 and y/2. Either observer's immediate pure Quit payoff is

    Q(x,y)=−6[x/3+y/2−xy/6]=−2x−3y+xy.

For EVERY x,y∈[0,1],

    R_2−Q=x+(7/2)y+3xy≥0,
    R_3−Q=(5/2)x+2y+3xy≥0.

To check an arbitrary original finite deadline t, split its opponent
law at the earlier dates. The passive payoff already paid on those
earlier exits is identical for this reply and Never. On the positive
opponent-survival event, the displayed inequality compares the
current Quit response to the complete conditional Never value.
Thus EVERY finite response is bounded by original Never; literal
Never attains that value. These calculations control ALL finite
deadlines, arbitrarily late ones and arbitrary behavioral mixtures.
The complete independent profile is therefore terminal Nash for
EVERY m_0,m_1∈(0,1], even when an observer's payoff is negative.

At m_0=m_1=1/2, the joint Never mass is1/4 and the complete
payoff/cap vector is

    U=B=(2,2,3/4,3/4).

All four ORIGINAL payoffs are strictly positive. The unchanged
singleton matrix has a strictly negative entry in EVERY column:

    Γ=[[0,4,−1,−1], [4,0,−1,−1],
       [−1,1/2,0,4], [1/2,−1,4,0]].

For an additional ordinary matrix check, ALL principal minors of
size≥2 are nonzero: the pair determinants are−16,−1,1/2,1/2,−1,−16;
all four triple determinants are2; the full determinant is240.
Together with the negative-column entries this proves R₀ directly:
a nonzero homogeneous complementarity solution cannot have singleton
support, and any larger support would have a singular principal.
The uniform simplex vector has strictly positive image. These
finite matrix facts do not make this solved table a no-UE source.

### GC3. An actual native Nash tail whose cap is strictly negative

Condition both finite owners on surviving all dates0,1,2, shift
the remaining dates down by3, and leave Never intact. At the
above half-finite profile the resulting finite probabilities are

    x=(2/3)^3/[1+(2/3)^3]=8/35,
    y=(1/2)^3/[1+(1/2)^3]=1/9.

The geometric conditional shapes are unchanged. GC2 therefore
gives a literal independent terminal Nash tail with

    U_2=B_2=R_2(8/35,1/9)=−1/14,
    Q_2=−241/315<−1/14,
    U_3=B_3=R_3(8/35,1/9)=11/105.

Its observer2 cap is NEGATIVE although its own singleton is0.
At later tails the slower owner0 increasingly dominates the finite
mass, with negative passive singleton reward to observer2. Nevertheless
the observer cannot preempt that mass for free: every finite reply
joins a positive current atom and pays the specified joining penalty.
Never remains optimal.

More generally, conditioning an actual terminal Nash profile with
positive marginal Never masses on a common old chronological survival
cut preserves exact tail Nash when Never is a maximizing response.
Indeed write the old Never value as H_i+α_i R_i^tail, where H_i
is the passive payoff on earlier opponent exits and α_i>0 their
survival product. Every after-cut reply has the same decomposition.
Old cap optimality gives b_i^tail≤R_i^tail, and tail Never gives
the reverse inequality. Every remaining finite own support clock
was old-cap maximizing, as was Never, so the conditional prescribed
payoff also equals R_i^tail. This argument DOES NOT give its sign.
The actual occupied first date remains part of the tail game.

### GC4. The omitted empty test has an exact positive cap birth

Insert one empty date between old dates2 and3: keep old clocks0,1,2,
and send every old finite clock t≥3 to t+1. Both original laws and
Never masses otherwise stay unchanged. This is an actual calendar
change, not an allowed reply in the old profile. Prescribed terminal
coalitions and EVERY payoff U remain unchanged. Every old finite
reply still has its identical counterpart; Never is unchanged.

The ONLY new response type is the empty date3. For observer2 its
opponent-survival product through old date2 is

    α=(35/54)(9/16)=35/96.

That new reply replaces the conditional Never payoff−1/14 by the
own-singleton payoff0. Its full original value is therefore

    3/4−α(−1/14)=3/4+5/192=149/192.

The other three conditional Never values are positive: they are
4y=4/9 for owner0, 4x=32/35 for owner1, and11/105 for observer3.
Their new empty response is below their old maximizing Never value.
Thus the COMPLETE new total debt is EXACTLY5/192, whereas the
original profile has debt0. A payoff-preserving simultaneous stretch
can create a genuine full-cap loss even at a true zero-gap minimum.

This does not falsify the canonical NP theorem. Taking m_0=m_1=1
in GC2 gives an actual absorbing terminal Nash profile, and already
pure{0,1} at date0 is absorbing Nash. Hence Δ_abs=0 here, not NP's
positive separated floor. No positive-debt profile or conditional
tail is declared a true NP minimum.

The two-owner dominance argument is retired at the exact missing
early-test implication. A future comparison can use the displayed
geometric equations, but must retain occupied atomic dates and price
ALL empty-date births. Neither conditional native Nash nor a column
blocker supplies an unobserved pre-collision opportunity. No export,
full conjecture result or new positive-gap class reduction is claimed.

## Whole-word Bellman barriers and the failure of Never-weighted exact discounting

### BB1. Actual full-cap control problem and status

Question. Can the complete finite-word control problem consume the strict
global source, instead of assuming a local gain or free geometric tail?
Fix any bounded finite quitting table |r|≤M, M>0, and its ORIGINAL closed
attainable payoff/full-cap carrier K. Assume its unrestricted SUM minimum
δ=min_K Σ_i(b_i−u_i)>0. Here all original independent stopping laws,
all finite deadlines and Never are included. No tail Nash or minimum-tail
assumption is added. The following barrier calculation is COMPLETE
ORDINARY, UNREVIEWED supporting mathematics, not a conjecture consumer.

For a product root q write c=∏_i(1−q_i), α_i=∏_(j≠i)(1−q_j),
and use the literal root payoff terms A_i,Q_i from NF. Set

    F_q(B)_i=max(Q_i,A_i+α_i B_i),
    H_i(q)=q_iQ_i+(1−q_i)A_i,
    T_q(u,b)=(H(q)+cu,F_q(b)).                         (BB.1)

Every root and every carrier pair are allowed. Prefix closure follows
by putting q at date0 and shifting actual approximating laws one date;
the same formulas give cap convergence for EVERY finite reply and Never.
Finite-support stopping laws approximate every actual law by moving its
finite tail to Never. Coupling changes U and all responder payoffs by
at most2M times the sum of moved masses, uniformly before taking caps.
Every such finite-support profile is a finite root word ending in the
all-Never pair (0,max(s,0)). Thus the closed carrier is the closure of
the complete finite-word orbit; bounded-word or menu Nash is not used.

Let

    E={B∈[−M,M]^I: some (u,b)∈K has b≤B}.

E is compact and upward closed within the box. Monotonicity of F_q and
prefix closure give F_q(E)⊆E. For any root define the FULL root regret

    R(q,B)=Σ_i F_q(B)_i−Σ_iH_i(q)−cΣ_iB_i
          =Σ_i[(1−q_i)(Q_i−C_i)⁺+q_i(C_i−Q_i)⁺]≥0,
    C_i=A_i+α_iB_i.                                  (BB.2)

R=0 is exactly full root Nash at annotation B, including quiet/sure
owners. For all other roots the quantity remains explicit; it is not
silently discarded as a perturbation error.

### BB2. A continuous barrier with an ALL-root error

Choose L>1 and define on the WHOLE reward box

    V_L(B)=max_(u,b)∈K [Σ_i u_i−LΣ_i(b_i−B_i)⁺],
    W_L(B)=Σ_iB_i−V_L(B),       P_L(B)=W_L(B)−δ.

Compactness gives the maximum; V_L is monotone and L-Lipschitz in ℓ¹.
For every candidate pair,

    Σ_iB_i−[Σ_i u_i−LΣ_i(b_i−B_i)⁺]
      =D(u,b)+Σ_i(B_i−b_i)⁺+(L−1)Σ_i(b_i−B_i)⁺.

Hence W_L≥δ everywhere, P_L≥0 everywhere, and at the cap vector of
ANY true minimum pair W_L=δ. If (u,b) attains V_L(B) and
e_i=(b_i−B_i)⁺, then

    Σ_i e_i≤P_L(B)/(L−1).                           (BB.3)

For B∈E a feasible pair gives V_L(B)≥−|I|M, so W_L(B)≤2|I|M.
These bounds are uniform in L. They do not assume every cap exceeds
its own singleton; GC is a counterexample to that assumption.

For every root, (F_q(b)_i−F_q(B)_i)⁺≤α_i e_i. Insert T_q(u,b)
as a candidate in V_L(F_q(B)). Since α_i−c=q_iα_i, this gives

    W_L(F_q(B))≤cW_L(B)+R(q,B)+LΣ_iq_iα_i e_i.

The probability q_iα_i of the singleton outcome {i} is at most1−c.
Using BB.3 and subtracting δ therefore yields

    P_L(F_q(B))≤P_L(B)+R(q,B)
                   −[δ−P_L(B)/(L−1)](1−c).          (BB.4)

On E, take L−1≥4|I|M/δ. Then P_L(B)/(L−1)≤δ/2, and

    P_L(F_q(B))≤P_L(B)+R(q,B)−(δ/2)(1−c)             (BB.5)

for EVERY root and every B∈E. No cap branches are selected; the max in
BB.1 is the complete response cap throughout. At a true minimum cap
vector P_L=0, BB.5 forces R(q,B)≥(δ/2)(1−c) for every root. This
fixed-cap consequence is already the known minimum/cap-Nash obstruction,
not a favorable whole-law move. Along a word a useful negative comparison
would require the aggregate R error to be less than its absorption charge.
The source has not supplied such a word or a return inside E.

### BB3. Exact discounting by Never mass loses the debt barrier

An apparently cleaner version uses the augmented closed carrier carrying
the original marginal Never probabilities n_i. Define

    V_L^N(B)=max_(u,b,n) [Σ_i u_i−LΣ_i n_i(b_i−B_i)⁺].

The prefix has n′_i=(1−q_i)n_i, so n′_iα_i=cn_i. The same cap
comparison now gives the EXACT supersolution inequality

    V_L^N(F_q(B))≥Σ_iH_i(q)+cV_L^N(B).

This does not give a positive debt barrier. If every n_i=0, ALL cap
penalties vanish. On the actual NP source the produced positive singleton
direction Γλ>0 gives an absorbing profile with EVERY u_i>s_i: first
make λ strictly positive by a sufficiently small perturbation, then use
small stationary independent hazards ρλ_i. Every clock is finite a.s.;
collision probability is O(ρ), and the terminal payoff tends to
s_i+(Γλ)_i>s_i. This is the actual payoff producer already recorded in
PS, not a new strategy completeness assertion. Consequently

    V_L^N(s)≥Σ_i u_i>Σ_i s_i

for EVERY L. The putative barrier ΣB−V_L^N(B) is negative at s.
Strict positive full/absorbing gap cannot repair a potential that has
deleted all absorbing cap penalties.

The failure is structural for diagonal exact-discount weights. For fixed
owner i, the identity w_i((1−q_i)n)α_i=cw_i(n), required for every
n,q_i and any positive opponent survival, says w_i(an)=a w_i(n).
Thus w_i(n)=n w_i(1), including w_i(0)=0. Every such weight discards
precisely the absorbing profiles whose full caps must remain controlled.
The unweighted BB2 retains those caps but pays the explicit root error.

### BB4. Bounded source overlap and the remaining global question

Inspected `exists_quittingRobustChargedRelation_rationalPotential_of_finiteBudget`
in `UniformEquilibrium/Quitting/Projective/RobustChargedRelationPolynomialSeparator.lean`
and `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
The latter, under its exact normality/positive-singleton hypotheses, already
produces a rational polynomial on a FULL fixed box for every robust relative
approximate root-Nash edge. Its domain is stronger than E. BB2 is an
ordinary all-root error ledger from the actual carrier; it is not a claim
of a stronger Nash-edge potential theorem or a new exportable source.

The hard constrained value max_{K,b≤B}Σu need not be continuous merely
because AllNever is strictly cap-feasible: product-law profiles cannot be
convexified by an unproduced common signal. Softening avoids that false
step, but does not solve reachability. The next useful question is whether
the STRICT absorbing gap forces an actual finite word with aggregate
root regret below its physical charge, or forces a closed charged root
return at reachable cap states. A supplied return, fixed annotations or
the existence of an absorbing payoff above s is not such a producer.

## A uniform full-cap calendar compression and a finite whole-table gap test

### QC1. Exact unconditional question and result

Fix I={0,1,2,3}, a finite real reward table |rᵢ(S)|≤M with M>0,
and ANY actual independent behavioral stopping laws pᵢ on ℕ∪{Never}.
Nonabsorption pays0. The original public live history is all Continue,
so all unilateral behavioral deviations are mixtures of complete pure
finite clocks and Never. Write U(p),B(p) for prescribed terminal payoffs
and FULL unrestricted caps, and D(p)=Σᵢ(Bᵢ−Uᵢ).

For EVERY θ∈(0,1] there is an ACTUAL independent profile p′ supported on

    {0,…,N−1,Never},       N=⌈24/θ⌉+1,

such that ALL marginal Never masses are retained EXACTLY and

    |Uᵢ(p′)−Uᵢ(p)|≤12Mθ,
    |Bᵢ(p′)−Bᵢ(p)|≤12Mθ                 for EVERY i.       (QC.1)

No minimum, positive gap, positive own reward, Nash row, actual tail
equilibrium, response attainment or dominated-density condition is needed.
The operation is ONE common deterministic nondecreasing map on finite
clock dates, with Never kept separate. It merges only blocks having small
UNCONDITIONAL clock mass and preserves every large-mass date as a literal
singleton block. It neither inserts an early empty clock nor uses public
randomization. This is a complete ordinary derivation, NOT Lean-checked or
independently reviewed. Its finite whole-table interpretation in QC5 is
already covered by the checked quantile-clock hierarchy and semidecision
program recorded in QC7; this elementary proof makes no novelty claim.

### QC2. The finite ordered partition of the entire original calendar

Put m(t)=Σᵢpᵢ({t}); then Σ_t m(t)≤4. Declare a date LARGE if
m(t)>θ/2. There are at most8/θ such dates. Keep every large date as
a SINGLETON block, including a large original date0. Between successive
large dates, and before the first/after the last, every date has
m(t)≤θ/2. Partition each nonempty such interval greedily into consecutive
blocks with total m-mass≤θ.

The exact existence/count argument includes the infinite final interval.
If an interval's entire remaining mass is≤θ, take its whole remainder
as its final block. Otherwise there is a first finite date at which its
cumulative mass would exceed θ. End the current block just BEFORE that
date. Its mass is>θ/2, since the next individual date has mass≤θ/2.
Continue. There are at most8/θ completed blocks of mass>θ/2 over
ALL intervals, because their total mass is≤4. Each interval has at
most one final block; there are at most8/θ+1 intervals. Thus the whole
partition has at most

    8/θ large singleton blocks
      +8/θ completed small blocks
      +(8/θ+1) final small blocks =24/θ+1.              (QC.2)

Intervals of ZERO mass are NOT silently deleted: if they contain original
dates, they remain one small block. Consecutive large dates have no
intervening block if their original interval is empty. The partition covers
ALL ℕ, including its infinite final small block. Hence no fictitious
clock is inserted before an occupied macro date. The harmless terminal
small block may have zero prescribed finite mass.

Index the nonempty blocks B₀,…,B_{L−1} in their original order,
L≤N. Define f(t)=a for t∈B_a and f(Never)=Never. For each owner
let p′ᵢ=f_*pᵢ. Since f is common and deterministic, the laws remain
independent; their finite support is in0,…,L−1 and all Never atoms are
exactly retained. Unused final dates up to N−1 have zero prescribed
mass, with no change to U or B. This construction does NOT require a
preliminary finite truncation, positive Never mass or a hazard bound.

For a small block let aᵢ(B)=pᵢ(B). Then aᵢ(B)≤θ for every i and
Σ_B aᵢ(B)≤1. These UNCONDITIONAL bounds are the only probability
budget used below. Conditional hazards within the block may be large;
the proof never assumes that they are small.

### QC3. Prescribed payoff and ALL finite/Never response comparisons

Couple each original finite draw Tᵢ with its new draw f(Tᵢ), keeping
Never unchanged. Different players' draws are still independent.
The prescribed first terminal coalition is unchanged unless at least
two owners draw finite clocks in the SAME small block. Large blocks
are single dates, so they preserve all original ties. For any pair i<j,

    Σ_(small B) P(Tᵢ∈B,Tⱼ∈B)
      =Σ_B aᵢ(B)aⱼ(B)≤θΣ_B aᵢ(B)≤θ.

There are six pairs. Therefore the bad event has probability≤6θ;
on its complement the terminal coalition AND nonabsorption are identical.
The rewards differ by at most2M, so

    |Uᵢ(p′)−Uᵢ(p)|≤12Mθ.                            (QC.3)

Fix an owner i and a literal finite OLD response clock τ. Use the NEW
clock f(τ). Among its three opponents the analogous coalition-merging
bad event has probability≤3θ. If τ lies in a small block, the additional
event that ANY opponent draws in that block has probability≤3θ by
the union bound. Outside these two events the responder's before/at/after
relations, the first terminal coalition and nonabsorption are unchanged.
If τ lies in a large block its singleton nature preserves the response
tie exactly and no extra event is needed. Thus, UNIFORMLY over EVERY
finite τ, including arbitrarily late clocks,

    |Vᵢ(τ;p_−i)−Vᵢ(f(τ);p′_−i)|≤12Mθ.              (QC.4)

The literal Never responses are compared using only the opponents'
merging bad event, so their payoff difference is≤6Mθ. These are exact
original/Never couplings; Never is not treated as a finite late clock.

Conversely, for a NEW finite clock a<L choose ANY actual old date τ∈B_a.
The same coupling gives (QC.4). For new clocks a≥L, the opponent laws
are already either stopped or literally Never after L−1; all those
finite tests are outcome-equivalent to clock L. There need not be an
actual finite OLD date after the infinite final block. Handle this seam
by taking old finite responses τ→∞ instead:

    lim_(τ→∞) Vᵢ(τ;p_−i)=Rᵢ(p_−i)+hᵢsᵢ,
    Rᵢ=Vᵢ(Never;p_−i), hᵢ=∏_(j≠i)pⱼ(Never),
    sᵢ=rᵢ({i}).                                      (QC.5)

On a draw with at least one finite opponent clock, this limit receives
the ORIGINAL first-opponent coalition's passive reward. On an all-Never
opponent draw it receives the own singleton. The new clock L has the
same description with the coarsened opponent coalition, so the two
values differ by≤6Mθ, again by the opponents' merging bad event.
The old limit is≤Bᵢ(p) because every old finite test is≤Bᵢ(p).
Hence the NEW terminal late test is≤Bᵢ(p)+6Mθ. New Never is covered
separately as above. This proves the upper comparison for EVERY new
finite/Never test without claiming a nonexistent old finite witness
after the entire infinite block.

Taking suprema in both directions proves the cap part of QC.1.
Mixtures and private-memory behavioral deviations are fully covered by
pure-time extremality on the unique live history. All signs of sᵢ and
passive rewards are allowed. In particular when sᵢ<0 the late limit in
QC.5 may be BELOW the Never response, which was never omitted.

### QC4. Exact tests, including an occupied-clock seam

First complete60-entry test: rᵢ(S)=1 iff i∈S, otherwise0, for every
nonempty S. Owners2,3 use Never. The other independent laws are

    p₀(0)=p₀(2)=1/16,       p₀(Never)=7/8,
    p₁(1)=p₁(3)=1/16,       p₁(Never)=7/8.

At θ=1/4 the four original dates are one small block. The old prescribed
payoffs are (31/256,29/256,0,0), the coarsened payoffs are
(1/8,1/8,0,0), and every original/new cap is1. The coarsening creates
genuine ties and need not preserve payoffs exactly, but the change is
charged by the small block mass as claimed. Never masses are EXACTLY
unchanged. This is a solved boundary test, not a positive-gap source.

Second complete60-entry test: for every nonempty S and every recipient i,

    rᵢ(S)=0 if S={i}, otherwise−1.

Owner0 quits surely at original date0, and the other three use Never.
Then U=B=(0,−1,−1,−1), so D=0. Its occupied date0 is LARGE for any
θ≤1 and remains the FIRST singleton block. The remaining zero-mass
calendar is after it, so compression leaves the full semantics unchanged.
Inserting a FREE empty clock before that large date would instead make
B=(0,0,0,0) while preserving U, hence D=3. This is exactly the forbidden
cap birth: QC2 does not insert that clock. Consecutive occupied large
dates likewise retain their adjacency if their original interval is empty.

I also executed50 independent exact rational tests with80 finite original
dates per owner, arbitrary signed integer rewards in[−5,5], and direct
scans of EVERY pure finite response, the final empty response and Never.
All bound assertions passed. This is experimental regression evidence
only; the proof is QC2–QC3, not these tests or floating-point optimization.

### QC5. A finite semialgebraic certificate for an unrestricted positive gap

For N≥1 define δ_N(r) as the minimum of FULL summed debt over ALL
independent marginal laws on {0,…,N−1,Never}. These are arbitrary actual
controller probabilities, NOT exact Nash equilibria of that menu. The
parameter space is a finite product of compact simplexes. Prescribed
payoffs are degree≤4 polynomials in those probabilities. A complete
reply menu is

    {0,…,N,Never},

because every finite response after N is outcome-equivalent to the first
empty date N. The individual response values are degree≤3 polynomials;
their finite maxima are exactly the FULL behavioral caps. Thus D is
continuous and δ_N is attained and expressible by a finite real
semialgebraic optimization. No tail cap or equilibrium choice is supplied.

Let δ_all(r)=inf_(ALL original behavioral profiles)D. Equivalently this
is the minimum on the closed original payoff/full-cap carrier. From QC.1,
for θ=2⁻ᵏ and N_k=24·2ᵏ+1,

    δ_Nk(r)−96M·2⁻ᵏ ≤ δ_all(r) ≤ δ_Nk(r).             (QC.6)

The left inequality follows by applying the compression to ANY profile:
|D(p′)−D(p)|≤Σ_i(|B′−B|+|U′−U|)≤96Mθ. Take its infimum.
The right inequality is inclusion of the actual finite-controller class.
The estimate is UNIFORM over EVERY table with |r|≤M and every original
behavioral profile; it does not use NP or identify a restricted minimum
with an original one. All Never masses, even zeros and sure-owner
boundaries, remain unchanged during the compression.

Consequently

    δ_all(r)>0 ⇔ ∃k≥1, δ_Nk(r)>96M·2⁻ᵏ.              (QC.7)

The forward direction takes k so the displayed error is below δ_all;
the converse uses QC.6. For a rational table and rational bound M the
right side is a finite exact polynomial inequality certificate: decide
whether there exists any finite-controller probability tuple with
D≤96M2⁻ᵏ. Epigraph variables yᵢ≥EVERY reply polynomial and
Σyᵢ−ΣUᵢ≤96M2⁻ᵏ give an equivalent finite existential real formula.
This is a global optimization over ALL controller laws, not a sampled
law, a local minimum, an exact-menu Nash family, or a chosen root orbit.

For the terminal-to-UE implication use exactly
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
If δ_all>0, every profile has some cap debt≥δ_all/4; pure-time or
behavioral near-attainment supplies an ACTUAL deviation of gain>δ_all/8.
Conversely its uniform actual deviation gapγ forces D≥γ for every
profile. Thus positive SUM infimum is equivalent to no UE without
replacing SUM by MAX or assuming cap attainment. QC.7 is a direct
unrestricted counterexample certificate, not only an absorbing-gap test.
No certificate is claimed to be satisfied by any present example.

### QC6. Whole-table minimax and the exact remaining decision

Positive common scaling permits the reward bound M=1. Set

    E= max_(r∈[−1,1]^60) δ_all(r),
    E_k=max_(r∈[−1,1]^60) δ_Nk(r).

Both maxima exist. For the full value, every fixed-profile payoff and
cap changes by≤‖r−r′‖∞, so D and its infimum change by≤8‖r−r′‖∞.
For the finite value the same bound holds, or use compact parameter
continuity. The UNIFORM QC.6 gives

    E ≤ E_k ≤ E+96·2⁻ᵏ.                               (QC.8)

Hence the full Fin4 conjecture is equivalent to the explicit finite
whole-table inequalities

    ∀k≥1, E_k≤96·2⁻ᵏ.                                (QC.9)

If any real counterexample exists, continuity supplies a rational one
with positive gap, and some finite QC.7 certificate exists. Alternatively
each test E_k>96·2⁻ᵏ is a finite first-order real formula: existentially
choose the60 rewards, universally choose the four finite-controller
simplex points, and compare the finite maximum reply polynomial with
the bound. Exact real quantifier elimination decides each fixed test.
Enumerating k therefore semidecides existence of an unrestricted
counterexample, without a root-Nash potential or a normality source.
The dimensional bounds are very large; no practical computation or
termination when UE holds is asserted.

This identifies a finite WHOLE-table minmax problem with an unrestricted
error bound, but the checked hierarchy already supplies this route. It
does NOT prove QC.9, exhibit a positive E_k certificate, settle UE or
narrow the NP source class. The unresolved step is an actual finite
minimax certificate or a uniform proof of QC.9, not another finite
verification interface. No negative-polynomial witness is supplied.

### QC7. Exact checked overlap and notes-only role

Read `exists_finiteDeadlineTimingProfile_approximation` and
`isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
in `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.
They provide actual finite-menu full-deviation/payoff approximation, with
a cutoff depending on the supplied profile and tolerance; they do not
give the game-independent upper deadline in QC.1/QC.6.

Read `quittingFiniteOpponentAtomGapReplyMenu`,
`quittingAtomGapRepresentative` and its before/after identities in
`UniformEquilibrium/Quitting/Terminal/FiniteOpponentAtomGapReplyMenu.lean`.
Its exact atom/successor/Never menu justifies the finite complete-response
scan, not a claim that naive calendar retiming preserves caps.

Read `exists_elementaryCompressedProfile_terminalSemantics_close` in
`UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`
and the public summary in its `All.lean`. The cutoff-dependent elementary
tail theorem supplies complete cap/payoff density, not this uniform
calendar-length bound. The payoff-only common/sparse calendar summaries
in TOOLKIT explicitly disclaim cap preservation; QC includes the small
tie and empty-clock costs instead.

The existing
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
already gives a different robust full-Nash polynomial certificate under
its actual normality/positive-singleton hypotheses. QC is not a claim
that negative semidecidability has never been accessible by that route.
The initial search above missed the relevant integrated producer. Read
`HasEscapeAwareQuantileClockPayoffTransportAtBound`,
`hasEscapeAwareQuantileClockPayoffTransportAtBound`,
`hasEscapeAwareQuantileClockCompressionAtBound` and
`hasEscapeAwareQuantileClockCompression_of_normalized` in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`.
They produce a common monotone finite-clock quotient for EVERY actual
profile, preserve EACH Never mass exactly, compare EVERY old and new
pure finite/Never response in BOTH directions, and give full (U,B)
error12M/j on a calendar of size8j+1. Their hypotheses are an explicit
bounded reward table and j>0, not supplied Nash roots or cap control.
Thus the full strategy-class content of QC.1 is already checked, with
a smaller support bound.

Read `escapeAwareQuantileClock_normalized_quantitative_bracket` and
its Fin4 specialization in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockApproximation.lean`.
The general continuous-score infimum API applies to SUM debt, which
is8-Lipschitz in semantic sup distance; its96M/j SUM bracket is the
direct same-source counterpart of QC.6. The production global search
is stronger than a supplied finite verifier: read
`finFourCounterexampleStep_sound` and
`exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` in
`Research/Quitting/FinFourCounterexampleSemidecision.lean`. The latter
equates an actual finite positive certificate emitted by the recursive
search with existence of a real Fin4 positive-exploitability-gap table.
Nontermination or failure of bounded search proves nothing.

The prior mathematical and production records are
`formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`,
`formalized/EXACT_FIN4_SCALE_RESOLUTION_AND_COUNTEREXAMPLE_SEMIDECISION.md`
and `Experiments/fin4_exact_search/README.md`. Their unrestricted finite
certificate/minimax program predates this derivation. The distinct
total-unconditional-mass greedy partition in QC2 may be useful as an
elementary proof, but is no strategic coverage increment. NOETHER
independently verified this exact source overlap before a QC audit.
No redundant full gate or export is requested; retain the exact proof,
infinite-final-block seam and signed boundary tests as supporting notes.

## A native absorbing spherical maximum and full response-distribution duality

### RS1. Exact global question, domain and counterexample adapter

Status: COMPLETE ORDINARY, UNREVIEWED source-switching-safe dual proof;
the global consumer is OPEN. This is notes-only supporting mathematics.
The independently selected passive-tax maximum in NOETHER's RM40 is not
identified with the spherical table below. No old NP minimum, genericity,
common debt vector or common Never mass is transported through this maximum.

Let I={0,1,2,3}. A native table z assigns a real reward z_i(S) to every
nonempty S⊆I and recipient i, with z_i({i})=0 and AllNever payoff0.
Each prescribed player independently samples T_i∈ℕ∪{Never}. For a profile
p, let U_i(z,p) be its expected terminal reward and B_i(z,p) the supremum
over COMPLETE unilateral behavioral replacements. Pure-clock extremality
identifies B_i with the supremum over all finite deadlines and Never.
Write D_z(p)=Σ_i(B_i−U_i), and FIX the actual absorbing domain

    P_abs={p:∏_i p_i(Never)=0},
    A(z)=inf[p∈P_abs]D_z(p).                         (RS.1)

The responses in B are NOT restricted to remain absorbing. The prescribed
domain is fixed before reward changes; it has an actual finite-a.s. owner,
not a common prescribed absorption date. Full native infimum is always0
because AllNever is terminal Nash. Nothing below asserts that full gap
is positive.

The no-UE→A>0 adapter is literal. The accepted paid-source initialization
produces a bounded counterexample r with all own s_i>0 and full SUM gap
δ>0. Define z_i(S)=r_i(S)−s_i for every nonempty coalition. Against fixed
opponents, late finite tests converge to the Never payoff plus h_i s_i,
where h_i is the opponents' Never product. Thus both r and z have their
full caps equal to the finite-response supremum; every finite response
absorbs and its payoff translation is exactly s_i. Consequently, at
EVERY actual profile,

    B_i(r,p)=B_i(z,p)+s_i,
    U_i(r,p)=U_i(z,p)+s_i(1−ν),
    d_i(r,p)=d_i(z,p)+s_iν,   ν=∏_j p_j(Never).       (RS.2)

In particular D_r=D_z on P_abs, so A(z)≥δ>0. This does not turn native z
into a full counterexample. Equivalently the accepted single-pivot source
subtracts its lone positive own from that recipient row and preserves its
absorbing gap by the same identity. No native theorem is being inferred
from a stationary affine-invariance claim.

### RS2. A genuinely global spherical maximum

Let E be the56-dimensional Euclidean space of all native tables; its
coordinates are (i,S) with S≠{i}. For two tables at sup distance e, EVERY
prescribed payoff and EVERY finite/Never response payoff at the SAME laws
changes by at most e. Thus each full cap changes by at most e and

    |A(z)−A(z′)|≤8‖z−z′‖_∞,
    A(tz)=tA(z) for t≥0.                              (RS.3)

Both facts use the SAME domain P_abs. No minimum attainment, clock
tightness, response attainment or fixed optimizing profile is needed.
Nonnegativity follows from complete best-response domination of prescribed
play. The compact Euclidean unit ball therefore has a maximizing table r.
If some A(z)>0, the maximum a=A(r)>0 and ‖r‖₂=1, since otherwise positive
rescaling increases A. For EVERY u∈E and ε>0,

    A(r+εu)≤a‖r+εu‖₂.                                (RS.4)

The maximizer is not assumed differentiable. In particular no generic
recipient scaling or reward perturbation is performed after choosing it.

### RS3. Compact limiting ledgers of actual old-table minima

For an absorbing p let μ(p) be its distribution on the15 nonempty terminal
coalitions, so Σ_S μ(S)=1. For owner i choose an ACTUAL finite response
τ_i; let μ_i(p,τ_i) be the distribution after its replacement. That profile
also absorbs because τ_i is finite, even if replacing the unique anchor
by Never would not absorb. Put

    g_i(S)=μ_i(p,τ_i)(S)−μ(p)(S) for S≠{i},
    g_i({i})=0.                                      (RS.5)

The coordinate-zero operation is only the orthogonal projection to E;
it does not alter any native payoff identity. Each full raw row is a
difference of probability distributions and has Euclidean norm≤√2, so
‖g‖₂≤√8.

Finite old-cap approximants ALWAYS exist at native owns0, including when
Never maximizes. Indeed bounded convergence along actual deadlines gives
V_i(t)→V_i(Never)+h_i·0=V_i(Never). Complete behavioral replacements
average pure-clock values. Hence the finite supremum is the full cap.

Let Z be the compact set of ALL cluster ledgers of actual p_k∈P_abs with
D_r(p_k)→a, and chosen finite tests whose old full-cap gaps tend0. This
can be defined without raw clock limits: take the nested closures of
the bounded (μ,μ_i,U,B,g) ledgers having D_r≤a+1/k and each test gap≤1/k,
then project their compact intersection. It is nonempty because actual
infimum approximants and finite cap approximants exist. Every element
retains one actual SAME-table absorbing minimizing sequence, its complete
cap limit and its selected response distributions. It does not assert a
limiting finite raw deadline or a named maximizing response atom.

For EVERY g∈Z the native linear payoff identity gives

    ⟨r,g⟩=a.                                       (RS.6)

More precisely if the response gaps are at most e per owner then
D_r(p)−4e≤⟨r,g⟩≤D_r(p). This also explains why the construction is
about FULL cap ledgers rather than arbitrarily picked responses.

### RS4. Follow new minimizing laws before separating old ledgers

Fix ANY u∈E. For ε↓0 choose ACTUAL absorbing ε²-minimizers p_ε at the
NEW table r+εu. At these same laws choose OLD-table finite tests within
ε² of each OLD full cap, and let g_ε be(RS.5). No response is required
to be maximizing at the new table. The new cap is at least its value
on each selected old test. Thus

    D_new(p_ε)≥D_old(p_ε)+ε⟨u,g_ε⟩−4ε²,
    D_old(p_ε)≥a,
    D_new(p_ε)≤a‖r+εu‖₂+ε².                          (RS.7)

The old and new payoff/cap moduli in(RS.3) also show D_old(p_ε)→a.
Extract only the finite-dimensional probability/semantic ledgers. Their
limit g belongs to Z, and(RS.7) gives

    ⟨u,g⟩≤a⟨u,r⟩.                                  (RS.8)

This is SOME old limiting ledger for this direction. Neither EVERY active
test nor ONE prescribed source works for every direction. For example,
the abstract fixed-profile envelope κ+|x+λ| has unique old minimizing
law x=0 but its new minimizer x=−λ changes the selected old maximizing
branch. Compact attainment does not remove that compensation.

If ar were outside conv Z, strict finite-dimensional separation would
give u with ⟨u,g⟩>⟨u,ar⟩ for ALL g∈Z, contradicting(RS.8). Therefore

    ar∈conv Z.
    ar=Σ[a=1..k]α_a g^a,   k≤57, α_a≥0, Σ_aα_a=1.    (RS.9)

Every g^a comes from ONE actual minimizing sequence at this SAME r.
The chosen table precedes all these sequences. Carathéodory is only
finite-dimensional bookkeeping: the α-average is NOT an independent
stopping-law profile, public randomization, or legal common calendar.

For each component let d_i^a be its limiting actual full debt. Since
native own coordinates are zero, (RS.9) also gives the exact row identity

    Σ_aα_a d_i^a=a‖r_i‖₂².                            (RS.10)

This is an AVERAGE identity, not all-minimum debt rigidity or equality
of the individual source debt vectors.

### RS5. An exact response-difference table rejects a pure-coalition shortcut

The unproduced consumer cannot simply say that a self-consistent
response-minus-prescribed table with positive deliveries has a pure
absorbing Nash coalition. Here is an exact FULL-response test, not a
positive-gap example or an application of(RS.9).

Use independent laws on dates0,1,2 (no Never):

    p₀=(3/11,4/11,4/11), p₁=(5/9,0,4/9),
    p₂=(3/7,0,4/7),     p₃=(4/7,3/7,0),
    chosen tests τ=(1,2,1,0).                          (RS.11)

Let μ be their actual first-coalition law, let μ_i be its law after
replacing i by τ_i, and DEFINE ALL60 reward entries by

    z_i({i})=0,  z_i(S)=μ_i(S)−μ(S) for S≠{i}.          (RS.12)

Thus this is a complete signed native table specified by rational finite
data, not an incomplete singleton matrix. For arbitrary finite deadline
t≥3 and Never, all opponents have already stopped and the payoff is the
same passive value. Therefore tests0,1,2,3 exhaust EVERY full cap here.
Exact selected maxima and prescribed deliveries are

    U=(114557/7844067,248035/23532201,
       29635/2614689,43081/7844067)>0,
    B=(21529/713097,289565/2614689,
       18883/373527,55369/1120581),
    D=4681256/23532201>0.                              (RS.13)

For each i, its selected τ_i REALLY attains this full cap under z.
In particular d_i=‖z_i‖₂², as predicted by the single-ledger identity.
Nevertheless ALL15 pure date-zero coalitions are strictly escapable.
For a mask S, toggle owner i; its deviation gain is z_i(S△{i})−z_i(S).
Here is one strict witness per mask, writing coalitions in binary masks:

    S: 1    2     3    4    5    6    7    8    9     10
    i: 3    3     0    3    0    1    0    0    2      1
    g:32/1617,320/1617,40/539,64/539,24/539,80/539,
      30/539,16/539,80/1617,1520/4851;
    S:11    12    13    14     15
    i: 0     2     0     1      0
    g:160/1617,80/1617,32/539,320/1617,40/539.           (RS.14)

This is NOT an absorbing-gap barrier. Its singleton column3 is

    (z₀({3}),z₁({3}),z₂({3}),z₃({3}))
       =(0,80/441,64/1617,0)≥0.                        (RS.15)

Let only owner3 use a geometric finite clock with hazard θ and let the
others Never. It absorbs a.s. and delivers EXACTLY this column. With
M=max|z_i(S)|, every other owner's pure finite reply differs from its
passive singleton value by at most Mθ from a same-date joining spike;
the remaining preemption term is nonpositive because(RS.15) is
nonnegative. Its full cap is at most that passive value plus Mθ; owner3
has payoff and cap0. Hence D≤3Mθ→0 and A(z)=0. The tested p in(RS.11)
is NOT globally minimizing. This explicitly prevents using positive
profile debt in place of the true all-law floor in the dual consumer.

### RS6. Current global seam and narrow source record

The stable output is(RS.9), not a UE proof or counterexample-class
exclusion. The next mathematical question is: does the ALL-law minimum
floor at r consume this finite mixture by an actual independent absorbing
profile? Neither mixing entire source profiles nor selecting one ledger
from their convex combination is justified. A one-source radial identity
would require an additional proof; it is not recovered by genericity or
by differentiability of nearby, rather than maximizing, tables.

Sources inspected in this attempt, with their scope kept separate:

- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` gives
  the original behavioral gap endpoint, not the native ABS objective.
- `abs_quittingTerminalDebtSum_sub_le_of_reward_close`,
  `abs_quittingTerminalDebtSumInf_sub_le_of_reward_close`, and
  `quittingTerminalDebtSumInf_scaleQuittingReward` in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumRewardGeometry.lean`
  establish the FULL-domain geometry. (RS.3) proves its fixed ABS-domain
  version directly from the same actual response comparisons.
- `exists_positive_maximum_sum_source_of_not_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWorstSumRewardSource.lean`
  selects a FULL unit-cube maximum. It does not state(RS.2),(RS.9) or
  authorize treating that maximum as our native spherical one.
- `quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`
  is the actual late-response limit used to dominate Never.

Narrow source searches covered those terminal and terminal-semantic
neighborhoods. NOETHER's independently derived RM39/PT5–PT6 supplies a
parallel tax-direction comparison and its envelope guardrail, not a
proof of this spherical selection. No compiler, build or formalization
claim is made here. The exact rational calculation in(RS.11)–(RS.15)
was checked independently of the floating-point discovery experiment.

### RS7. The global minimum floor rules out a deterministic-only radial mixture

Status: COMPLETE ORDINARY, UNREVIEWED. This is a genuine application of
the SAME-table minimum floor in(RS.9), unlike the nonglobal test in RS5.
It asserts EXISTENCE of a random minimum among the radial ledgers, not
that EVERY minimum at this table is random, and not a UE conclusion.

The needed native minimum margin is the ordinary prefix-invariant result
recorded as NOETHER RM24: if all owns are0, |r_i(S)|≤M and the true
absorbing minimum is a>0, then EVERY K_abs minimum obeys

    U_i≥a−d_i+a²/(8M)>0,  for every i.              (RS.16)

It follows by the reviewed cap-crossing proof on the absorbing carrier;
its finite prefixes remain absorbing and its strict singleton-column
preemptors follow from the actual small solo-hazard competitor. This is
NOT an application of the tracked FULL-minimum margin with its domain
hypothesis silently removed. Only strict positivity U_i>0 is used here;
no common debt vector, scale, genericity or punishment is assumed.

Suppose, for contradiction, every positive-weight component in(RS.9)
has a deterministic prescribed terminal law δ_H. Singleton H is impossible:
its named participant's native prescribed payoff would be its own0,
contradicting(RS.16). Thus every such H has |H|≥2 and r_i(H)>0 for ALL i.
Group the weights of components with the same H as β_H>0.

First establish the actual all-response rule for such a component.
For its realizing sequence p_k, the original terminal coalition equals
H with probability tending1. Coupling a selected response with the same
original opponent clocks shows, on that event, its coalition can only be

    H, H△{i}, or {i}.                              (RS.17)

When i leaves a nonsingleton first coalition, its other members remain;
when it joins, only i is added; earlier preemption produces its singleton.
This bound is uniform over EVERY finite deadline and Never. The discarded
original event contributes at most2M times its probability to any payoff
comparison. No raw stopping-law tightness is assumed.

Both H and H△{i} are actually obtainable in the limit. Staying with the
old law yields r_i(H). If i∈H, literal Never withdraws it and yields
r_i(H−i). If i∉H, choose a common actual finite date a_k on which the
members of H concentrate and join them there. Such dates are produced,
not assumed: two independent members j,l satisfy
P[T_j=T_l<∞]→1, so max_t p_j(t)→1. A maximizing atom a_k therefore
has p_j(a_k)→1, and the equality event forces p_l(a_k)→1. The original
H event forces every other member of H to concentrate at the SAME a_k
and every outsider to lie strictly after it with probability tending1.
Hence this actual finite test joins H with probability tending1.

Native singleton0 is strictly below r_i(H)>0, so(RS.17) and these lower
witnesses identify its ENTIRE limiting full cap and debt:

    B_i(H)=max(r_i(H),r_i(H△{i})),
    d_i(H)=[r_i(H△{i})−r_i(H)]⁺.                    (RS.18)

This holds for every realizing sequence with that prescribed point mass,
including sequences whose common dates tend arbitrarily late. Consequently
all components grouped at H have the SAME debt here, without invoking
general all-minimum debt rigidity.

Their debt sum is a>0. Choose H and a debtor i, and put J=H△{i}.
Then r_i(J)>r_i(H)>0. By(RS.18) EVERY full-cap-approximating selected
response in an H component converges in outcome to δ_J: its only other
possible payoffs are strictly below r_i(J), uniformly outside a vanishing
exceptional original event. In particular it puts zero limiting mass at H.

No other deterministic minimum component can supply response mass at H.
If its original coalition is K, (RS.17) requires K=H or K=J, since H
is nonsingleton. K=H has just been treated. If J is a singleton there is
NO J minimum by(RS.16). If |J|≥2, its full cap for i is
max(r_i(J),r_i(H))=r_i(J), and EVERY selected cap response must stay at
J rather than yield the strictly smaller r_i(H) or singleton0. Thus it
also supplies no response mass at H.

The i,H coordinate of the actual averaged ledger in(RS.9) is therefore

    a r_i(H)=Σ_aα_a[μ_i^a(H)−μ^a(H)]
            =0−β_H<0,                              (RS.19)

contradicting r_i(H)>0. Therefore EVERY radial representation(RS.9)
contains at least ONE component with a genuinely RANDOM prescribed
terminal coalition law.

This proves a compatible native-source restriction while retaining the
spherical maximum, its all-law floor and its finite response-ledger dual.
It does not replace the canonical stronger full-source random theorem,
nor prove all native minima random. For a random component the reply can
alter singleton-first paths and expose later opponent coalitions; the
pure rule(RS.18) no longer holds. Even with no singleton on a particular
sample, an owner cannot choose a response contingent on an unobserved
coalition. Extending the flow contradiction to those actual random laws,
with ALL birth caps retained, is the open global step.

### RS8. Every own singleton must appear in the ORIGINAL radial ledgers

Status: COMPLETE ORDINARY, UNREVIEWED. This stronger event restriction uses
the actual all-law floor directly. It does not require the native strict
payoff margin for its numerical inequality, nor identify the different
component profiles. Put

    m(S)=Σ_aα_a μ^a(S),  v_i(S)=Σ_aα_a μ_i^a(S).

These are probability bookkeeping distributions, not actual independently
mixed laws. For every j, let ONLY j use an actual geometric finite clock
with hazard θ∈(0,1) and let every other owner Never. It is absorbing.
Owner j has payoff and cap0. Every observer i≠j has prescribed payoff
r_i({j}). Its response at time t has the exact value

    r_i({j})+(1−θ)^t[θr_i({i,j})−r_i({j})].

Never has value r_i({j}), so the ENTIRE finite/Never cap is exactly
max(r_i({j}),θr_i({i,j})). The all-law floor and θ↓0 give

    a≤Σ_(i≠j)[−r_i({j})]⁺.                         (RS.20)

In particular some observer has r_i({j})<0 at EVERY singleton column j.
This is a direct absorbing comparison, not a transported full no-UE screen.
The radial identity supplies ar_i({j})=v_i({j})−m({j}), with v_i({j})≥0.
Hence

    a²≤Σ_(i≠j)[m({j})−v_i({j})]⁺≤3m({j}),
    m({j})≥a²/3>0 for EVERY j.                       (RS.21)

The role is event coverage, not improving a worst-value constant.
For each j there is therefore SOME actual native minimizing component
with positive original probability of first coalition{j}. Such a component
must be genuinely random by the strict native payoff margin: a point mass
at{j} pays its participant own0. This is compatible with the SAME radial
table and its all-law floor. It does not force all four singleton events
at ONE prescribed minimum or preserve an old NP component.

Moreover choose a negative observer r_i({j})<0. Then v_i({j})<m({j}),
so at least one component has strictly smaller selected-response singleton-j
mass than its original mass. Couple its actual original clocks and selected
finite test. A loss of the original coalition{j} can only occur when that
test is no later than j's original first date: it strictly preempts to{i}
or ties to{i,j}. A gain in singleton-j mass may come from removing an
original solo i and exposing j later. The STRICT net loss implies positive
limiting mass of original singleton-j paths destroyed by the chosen FULL
cap test. These are actual moving finite witnesses, not outcome-equivalent
Never aliases. The observer's debt at THIS component may still be zero;
the joining outcome's reward may also be smaller than its old passive
reward. No paid event or favorable own-law relocation is inferred.

This gives a shorter alternative to RS7's deterministic-only contradiction:
if every component were deterministic, (RS.21) would require deterministic
singleton minima, forbidden by native strict U>0. RS7's separate actual
pure-outcome/full-cap argument remains valid and retains its clock seam.

### RS9. Use the existing SAME-table four-finite completion, not a new Never estimate

The ordinary adapter in NOETHER RM40/AT7–AT8 and the independently reviewed
whole-carrier FC completion have the following exact scope: for ANY signed
table with own singletons≥0 and recipient row witnesses
∀i∃j≠i:r_i({j})≤r_i({i}), the carrier closure of all-four-finite actual
laws equals K_abs. At a native table with A>0, the row witnesses are
regenerated at that SAME table via its TV absorbing completion estimate,
a sufficiently large positive terminal-row translation and actual full
normal-core classification. They are not borrowed from an older NP table.
This is distinct from RS8's direct singleton COLUMN witnesses.

It follows that the spherical comparison may choose each NEW-table
near-minimizer with all FOUR Never masses exactly0. Indeed for sufficiently
small ε, (RS.3) gives A(r+εu)>0, so apply that adapter separately there
BEFORE selecting its actual ε²-minimizing laws. Whole-pair closure supplies
all-four-finite laws with that error. Truncate each finite-a.s. law in TV,
moving its finite tail mass to one finite date, to make its support finite
while keeping Never mass EXACTLY0. The prescribed payoffs and ALL observer
finite/Never caps change uniformly by a quantity tending0 under this literal
coupling; the mover's own cap is unchanged. Select the truncation error
smaller than the remaining minimization budget.

Thus the SAME RS4–RS8 proof works with an appropriately defined Z_fin,
whose components have finite-support, all-four-finite realizing laws at
EVERY index. This does not assert raw clock tightness, an attained native
absorbing minimum, a finite limiting response deadline, or an original
FULL minimum. No new whole-carrier theorem or Lean-checked native adapter
is claimed; this is reuse of the reviewed completion and the explicit
ordinary same-table initialization. The live consumer remains a legal
independent change of these laws with EVERY born cap controlled.

### RS10. The radial identity does not force a pure or single-supplier competitor

This EXACT test retires a concrete attempted consumer, not the RS global
source. It has the full radial identity, actual full cap tests and positive
deliveries, but its caps VIOLATE the genuine minimum margin B_i>A. Its
cyclic singleton signs are already in a tracked solved class. No further
bounded search or constant improvement is part of this attempt.

All clocks below are independent and supported on dates0,…,4; every row
of counts is divided by256. Use two base profiles and selected replies:

    P⁰: (64,14,51,127,0),   (95,30,15,115,1),
        (93,15,98,50,0),    (0,63,16,127,50);
    P¹: (125,131,0,0,0),    (15,32,64,18,127),
        (82,144,0,0,30),    (46,67,47,32,64);
    τ⁰=(4,4,0,2),           τ¹=(3,0,2,2).              (RS.22)

Write ρ_j(S) for cyclic addition of j to all owner labels. For a∈{0,1},
let μᵃ be the actual terminal law of Pᵃ and μᵃ_i its law after the literal
replacement by τᵃ_i. Define the full native row vectors

    Vᵃ(S)=¼Σ_i[μᵃ_i(ρ_iS)−μᵃ(ρ_iS)]  if S≠{0},
    Vᵃ({0})=Vᵃ(∅)=0.

For masks0,…,15 the exact integer vectors 4·256⁴Vᵃ are

    A⁰=(0,0,880295284,−746478222,255009908,−110088372,
        282909554,−210336018,−689889420,742770034,
        225480524,−71707410,−243697038,226123502,
        356770030,−358160360),
    A¹=(0,0,60210602,50765698,2787127466,−1928115312,
        639314050,−400740864,−664297558,664919938,
        −461411440,28225024,508862338,−271110656,
        −145842688,−69363664).

Take the exact norm-minimizing coefficient on this chord,

    w=−⟨A¹,A⁰−A¹⟩/‖A⁰−A¹‖₂²
     =2919993234482309189/3206597336624768103 ∈(0,1),
    V=wV⁰+(1−w)V¹,       R_i(S)=V(ρ_{−i}S).           (RS.23)

Thus (RS.22)–(RS.23) specify ALL60 rational reward entries, including
own singletons0 and Never0. Include the four cyclic rotations of each
base profile with weights w/4 and (1−w)/4 respectively, rotating its
selected replies as well. The resulting E-projected response-difference
mixture is EXACTLY R. These eight sources are bookkeeping, not a legal
publicly mixed profile. The norm-minimizing equation makes the selected
regret sum at each base profile, hence each rotation, exactly

    D₀=‖R‖₂²
      =144338660145900502269995879009157185 /
       3696955026009735821942381482006806528,
    39/1000<D₀<40/1000.                               (RS.24)

The selected tests really maximize the FULL caps. Because every opponent
is finite by4, test5 is outcome-equivalent to every later finite deadline
and Never; the six tests0,…,5 are exhaustive. Direct rational enumeration
gives maximizing-test sets

    P⁰: {4,5}, {4,5}, {0}, {2};
    P¹: {3}, {0}, {2,3,4,5}, {2,3,4,5}.

It also gives, at both base profiles and all rotations,

    U_i>1/200000,       B_i<26/1000<D₀.               (RS.25)

This checks (RS.24) as ACTUAL unrestricted debt, rather than the value of
a selected branch. For every pure nonempty coalition S, its actual debt
is Σ_i[R_i(S△{i})−R_i(S)]⁺; all15 such values exceed44/1000>D₀.
The exact calculation uses μᵃ(S)=256⁻⁴Σ_{t:first coalition S}∏_iPᵃ_i(t_i)
and the analogous three-opponent sum for each replacement. All displayed
intervals and maximizer comparisons were checked with rational arithmetic,
not inferred from floating-point discovery.

In fact EVERY absorbing single-supplier stopping law, not merely every
geometric rate, costs more than D₀. For supplier j choose i=j+1 mod4.
Cyclic invariance gives

    R_i({j})=V({3})<−40/1000,
    R_i({i,j})=V({0,3})>0.

With all other prescribed laws Never, observer i's prescribed payoff is
R_i({j}); its date-zero test pays0 if j stops later and the positive pair
reward if j stops now. Its cap is therefore ≥0 and its debt exceeds
40/1000. This covers all finite-a.s. laws of j, all geometric hazards,
and arbitrary offsets. It does not restrict the remaining actual product
laws, which may have several suppliers and many phases.

The failure is conspicuously nonglobal. After reversing the cyclic labels,
the normalized singleton coefficients are

    γ₁=V({3})<0, γ₂=V({2})>0, γ₃=V({1})>0,
    γ₁+γ₂+γ₃>0.

Hence the complete table meets `QuittingCyclicSingletonOpenSignData`, whose
`isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`
produces the actual balanced cyclic tail with unrestricted nonsingleton
rewards. Its `tailData` has survival strictly between0 and1; the underlying
thinned cyclic profiles are absorbing and give A(R)=0. The named structure,
the cyclic matrix definition and consumer were inspected, together with
the hazard construction in `CyclicSingletonTailProducer.lean`. No build,
new producer, or positive-gap example is claimed here.

In particular (RS.25) is incompatible with the genuine native minimum
cap margin. The exact test defeats balance+positive-delivery consumption
by these simple competitor families; it does NOT defeat a comparator
using the true ALL-law floor and that margin. The next construction must
use those hypotheses, rather than infer a favorable pure/solo member
from the radial identity alone.

### RS11. A true occupied-prefix floor forces ORIGINAL collision mass

Status: COMPLETE ORDINARY, UNREVIEWED comparison. This is a SAME-table
native restriction using the actual ALL-law floor, unlike RS10. It does
not produce a lower-debt competitor or identify a paid collision owner.
The already exported full-carrier early-collision theorem is stronger
in its original domain; no new full-carrier theorem is claimed here.

Fix ANY four-player native table r_i({i})=0, Never0, |r_i(S)|≤M with
M>0. Let A=inf_{p∈P_abs}D_r(p)>0, with unrestricted caps throughout.
For an actual ALL-four-finite law profile p define

    η(p)=P_p(|first terminal coalition|≥2).

For ANY γ>0, the following implication holds:

    B_i(p)≥A+γ for every i
      ⇒ D_r(p)≥A+γ²/(16M)−12Mη(p).                   (RS.26)

Only the true absorbing floor and the displayed FULL cap margin are
used. In particular no native true punishment≥0, conditional-cap
nonnegativity, minimizing suffix, Nash row, isolated response or common
debt vector is assumed. Necessarily γ≤M when the premise is satisfied.

First prove (RS.26) for finite-support laws, all with Never mass0.
Let s be the first natural date at which some owner's conditional Quit
rate is1. For t≤s every original marginal survival P(T_i≥t) is positive;
condition each marginal independently on that event and translate its
calendar by t. Denote its actual full semantic pair by (u(t),b(t)) and
its debt by D(t). Its laws are still ALL-four-finite, so D(t)≥A.
Write q_i(t)=P(T_i=t|T_i≥t) and

    c_t=∏_i(1−q_i(t)),  a_t=1−c_t,
    w_t=∏_{v<t}c_v,     χ_t=P_{q(t)}(≥2 Quit).

The first sure row exists and c_s=0. At s+1 a marginal with zero
survival is filled by ANY finite law. The others use their actual
positive-survival conditional laws. This constructs an actual
ALL-four-finite tail, without conditioning on a null event. It supplies
D(s+1)≥A, though that term will be multiplied by0 if the stopping
prefix reaches this seam.

The literal semantic identity at the sure seam needs checking for ALL
responses, not just prescribed play. If h is the sole sure owner, h's
tail cap depends only on the OTHER owners' actual conditionals and is
independent of its filler. For i≠h the Continue tail multiplier α_i
contains 1−q_h=0, so its full root cap is independent of all tail
fillers. If at least two owners are sure, every α_i is0. Prescribed
play also has c_s=0. Thus the same exact root semantic identity holds
at s as at each earlier row, including every finite deadline and Never.

Put Q_i=the literal root Quit payoff and C_i=its Continue payoff against
b(t+1). The full root cap is b_i(t)=max(Q_i,C_i). The arbitrary-root
identity, not an exact-Nash identity, is

    D(t)=c_tD(t+1)+R_t,
    R_t=Σ_i[(1−q_i)(Q_i−C_i)⁺+q_i(C_i−Q_i)⁺].       (RS.27)

This includes EVERY max(Q,C) branch. The literal ordinary prefix has
no free inserted date or omitted late test.

Two elementary estimates provide the comparison. Write
α_i=∏_{j≠i}(1−q_j) and a_i=1−α_i≤a_t. Native own0 gives Q_i=0
when no opponent quits, whence |Q_i|≤Ma_i. Also

    C_i=α_i b_i(t+1)+Π_i,       |Π_i|≤Ma_i.

Although b_i(t+1) may be NEGATIVE, |b_i(t+1)|≤M. Therefore
|C_i−b_i(t+1)|≤2Ma_i. Comparing max(0,Q_i,C_i) with
max(0,0,b_i(t+1)) proves the positive-cap speed estimate

    |b_i(t)⁺−b_i(t+1)⁺|≤2Ma_t.                      (RS.28)

The positive part is indispensable; no false nonnegative conditional
punishment floor enters this step. Empty old rows also obey (RS.28):
they may clip a negative cap to0, but do not move its positive part.

For a literal boundary check, put r_i({i})=0 and every other entry in
row i equal to−1, with all opponents sure at date0. Its tail cap is−1;
prefixing an empty date makes its cap0 by the new solo test. Thus an
absolute-cap speed claim would FAIL at zero root absorption, whereas
(RS.28) correctly compares positive parts0 and0.

For any i, its summand in R_t is at least
q_i(max(Q_i,C_i)−Q_i)=q_i(b_i(t)−Q_i). If every b_i(t)≥L>0,
then independence and the union bound give

    R_t≥LΣ_iq_i−Σ_iq_iQ_i
       ≥La_t−MΣ_{i≠j}q_iq_j
       ≥La_t−12Mχ_t.                                (RS.29)

Indeed Σ_{i≠j}q_iq_j is the expected number K(K−1) of ordered
quitter pairs, and K(K−1)≤12·1_{K≥2}. Signed rewards only make
the upper bound on Σ_iq_iQ_i easier; no branch sign is suppressed.

Stop at the first k∈{1,…,s+1} for which some b_i(k)⁺≤A+γ/2,
or use k=s+1 if no such threshold is reached. For every t<k,
all ORIGINAL conditional head caps are at least L=A+γ/2.
If an actual threshold is reached, (RS.28) and the initial cap premise
give Σ_{t<k}a_t≥γ/(4M). The product bound

    ∏_{t<k}(1−a_t)≤1/(1+Σ_{t<k}a_t)

then gives 1−w_k≥γ/(8M), using γ≤M. If no threshold is reached,
the prefix includes the first sure row and w_k=0, so the same weaker
bound holds. This is PHYSICAL absorption, not a count of root stages.

Now unfold the actual occupied prefix:

    D(0)=w_kD(k)+Σ_{t<k}w_tR_t
        ≥w_kA+(A+γ/2)(1−w_k)−12MΣ_{t<k}w_tχ_t
        ≥A+γ²/(16M)−12Mη(p).

Here Σ_{t<k}w_ta_t=1−w_k, and the weighted collision terms are
actual ORIGINAL first-coalition probabilities. No counterfactual
response collision or publicly mixed ledger substitutes for η(p).
This proves (RS.26) for finite support, including arbitrary sure-rate
and zero-rate rows.

For general ALL-four-finite p, truncate each finite-a.s. clock in total
variation by moving only its finite tail mass to one finite date. Never
mass stays EXACTLY0. Literal coupling makes prescribed outcomes, every
response payoff and therefore all full caps converge uniformly; η also
converges. Apply the finite-support argument with γ'<γ and then let
γ'↑γ. This proves (RS.26) for ALL four-finite laws, without raw-clock
tightness, an attained cap, or a bounded deadline restriction.

Application to RS. At the SAME native spherical table, the ordinary
RM24/BA6 strict minimum margin is

    B_i≥A+γ₀,       γ₀=A²/(8M)>0

at EVERY absorbing minimum semantic pair. RS9 supplies finite-support,
ALL-four-finite realizing sequences for each selected RS ledger.
For any fixed γ∈(0,γ₀), every sufficiently late source profile obeys
the premise of (RS.26). Since D→A,

    liminf η(p^k)≥γ²/(192M²)>0.                      (RS.30)

Thus EVERY selected component in the finite-realizer radial mixture
has a nonsingleton ORIGINAL terminal event; consequently its averaged
prescribed law m does too. This strengthens the sphere-compatible
randomness in RS7–RS8 without changing the table or the chosen radial
identity. It is not a statement that every cap is paid, that one atom
has a prescribed lower bound, or that the full unmodified native game
has a positive unrestricted minimum.

Sources and overlap. The exact autonomous recursion is already tracked
as `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
the root defect is defined in `UniformEquilibrium/Quitting/Root/NashDefect.lean`.
Those declarations and the literal cap prefix were inspected. Neither
states the native absorbing floor comparison (RS.26); they are reused,
not rediscovered. `minimumTerminalSemantic_exactNash_criticalFace` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
concerns an EXACT Nash root against a FULL global minimum, not our
arbitrary occupied roots or restricted native minimum. The independently
reviewed `POSITIVE_MINIMUM_EARLY_ORIGINAL_COLLISION_STAGE.md` proves a
stronger first-stage source theorem for the ORIGINAL unrestricted gap.
Our direct proof uses the different native absorbing floor and remains
compatible with its spherical selection; no new canonical full-source
packet or Lean implementation is claimed.

As an arithmetic diagnostic, (RS.28)–(RS.29) and the individual defect
bound were also checked with exact rational arithmetic on all625 roots
q_i∈{0,1/5,1/2,4/5,1}, signed integer reward rows bounded by3, and
signed half-integer tail caps in[−3,3]. The check included all zero/sure
boundaries and172 strictly positive-head cases. It is a test of the
elementary root estimates, not a finite enumeration proof of the global
floor premise or a Lean build.

The next actual consumer must change these original collision masses
independently and bound all born caps. This proof does not convert a
collision into a charged bridge or collapse its coalition identity to
participant counts; those would require additional arguments.

## Boundary-penalty Nash selection: an entire vanishing-price family fails

COMPLETE ORDINARY, UNREVIEWED architecture falsifier. This changes the
construction after RS11; it does not strengthen the collision lower bound.
The table is already solved by the cyclic singleton producer. No positive
native absorbing gap, spherical radial identity or genuine-minimum margin
is claimed for it.

### BP1. Actual construction and exact all-response seam

For a native table z with own singletons and original Never payoff zero,
fix the finite clock menu {0,…,N,Never}. Change ONLY the payoff when ALL
players choose Never to the vector −c, where every c_i>0. Take an exact
mixed Nash equilibrium in this finite normal-form game. The probabilities
are private and independent. The proposed producer repeats that finite
clock block independently after every block in which everyone continues.
It must be tested against EVERY original finite deadline and Never, not
just against the penalized finite menu.

For any finite block let n_i be its own Never probability, ν=∏n_i,
h_i=∏_{j≠i}n_j, G_i its original prescribed reward numerator, K_i its
original reward when i refuses through the whole block, and F_i its
maximum original pure-deadline value INSIDE the block. If ν<1 the literal
independent repeated profile absorbs and delivers

    U_i*=G_i/(1−ν).

If h_i<1, every response in block k is

    (1−h_i^k)·K_i/(1−h_i)+h_i^k·f_i(t),

where t is its phase and f_i(t) the first-pass value. Literal Never has
value K_i/(1−h_i). Thus the COMPLETE behavioral cap is

    B_i*=max(F_i,K_i/(1−h_i)).                         (BP.1)

This includes arbitrarily late deadlines and all empty phases already
present in the block. No empty phase is inserted or declared free. If
h_i=1, all opponents continue surely throughout every block, so in the
native convention K_i=0, every finite stop pays own singleton zero, and
literal Never also pays zero. Hence B_i*=0 directly; no division by zero
or phantom continuation value occurs.

These repetition facts are existing production, not the new producer.
The exact declarations inspected are
`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow`,
`quittingPeriodicPureTimeTerminalValue_add_period_eq_interpolation`, and
`quittingRootSequenceTerminalValue_eq_windowRestartDelivery_of_periodic`
in `UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean`.
The first two do not require opponent contraction. Also inspected were
`quittingPeriodicWindowBestResponseValue_le_restartDelivery_of_drift`
in that file and `quittingBestReplyValue_periodizedPrefix_le_max` in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`.
They do NOT produce favorable boundary Nash profiles.

### BP2. Complete table and the root facts used below

Use I={0,1,2,3}, indices modulo4. The original Never payoff and own
singleton rewards are zero. The full native table is:

| S | z₀(S) | z₁(S) | z₂(S) | z₃(S) |
| --- | ---: | ---: | ---: | ---: |
| {0} | 0 | −1 | 99 | 99 |
| {1} | 99 | 0 | −1 | 99 |
| {2} | 99 | 99 | 0 | −1 |
| {3} | −1 | 99 | 99 | 0 |
| {0,1} | 98 | 0 | 0 | 0 |
| {0,2} | 98 | 0 | 98 | 0 |
| {0,3} | 0 | 0 | 0 | 98 |
| {1,2} | 0 | 98 | 0 | 0 |
| {1,3} | 0 | 98 | 0 | 98 |
| {2,3} | 0 | 0 | 98 | 0 |
| {0,1,2} | −1 | −1 | −1 | 0 |
| {0,1,3} | −1 | −1 | 0 | −1 |
| {0,2,3} | −1 | 0 | −1 | −1 |
| {1,2,3} | 0 | −1 | −1 | −1 |
| I | −1 | −1 | −1 | −1 |

This is the RZ table in MORSE's notebook, whose original source is
acknowledged rather than claimed as a new fixture. The new claim here is
about ALL negative-boundary Nash selectors and their repetitions.

Write Γ_ij=z_i({j}), diagonal zero. Thus Γ_i,i−1=−1 and its other two
off-diagonal entries are99. In an adjacent pair, the two membership
gaps are +1 and −1; in an opposite pair both are−1. Triple and grand
membership gaps are−1.

No exact Nash ROOT can have a sure owner, at ANY continuation vector.
If z is sure, each nonfavorite i≠z,z+1 has gap−1 whether z is alone or
another opponent also quits, so both are quiet. Favorite z+1 then has
gap+1 and is forced sure. The original sure owner z now has gap−1
against that adjacent sure favorite, contradiction. All later tails are
screened in each asserted comparison.

At continuation v the weighted gap identity is

    Σ_i q_i g_i(q;v)
      =−2[P_q({0,2})+P_q({1,3})]
       −3Σ_{|S|=3}P_q(S)−4P_q(I)
       −Σ_i q_i α_i(q)v_i.                            (BP.2)

At v=0 the ONLY Nash root is q=0. Three or more positive suppliers
give a strictly negative coalition term. Two opposite suppliers give
negative active gaps, and two adjacent suppliers have one negative
active gap. A sole supplier has a quiet favorite with positive gap.
At any strictly positive v the only Nash root is again q=0: sure roots
were excluded, so a nonzero root makes the last sum strictly negative.

### BP3. ALL small negative-boundary roots have positive payoffs

Let q be ANY Nash root at continuation −c with every c_i>0. It is not
zero, and every q_i<1 by BP2. As max_i c_i→0, ALL these roots tend
uniformly to zero. Otherwise compactness and closedness of the finite
Nash inequalities would give a nonzero root at continuation zero,
contrary to BP2. This uses the entire root family, not a preferred
branch or an unproved equilibrium-selection theorem.

Put x_i=q_i/(1−q_i), α_i=∏_{j≠i}(1−q_j). For owner i let
F=x_{i−1} be its favorite opponent's odds and let A,B be the other two
opponent odds. Direct evaluation of all table entries gives

    Q_i(q)=[98(A+B)−H_i]·α_i,
    K_i(q)=[99(A+B)−F]·α_i,
    g_i(q;−c)/α_i=c_i+F−A−B−H_i,
    H_i=F(A+B)+AB+FAB.                                (BP.3)

At a nonsure Nash root every g_i≤0. Therefore A+B>0 for EVERY owner:
otherwise H_i=0 and g_i/α_i=c_i+F>0. If all odds are at mostρ≤1/10,

    H_i≤(ρ+ρ/2+ρ²/2)(A+B)<A+B.

Consequently Q_i>0 for every owner. The equilibrium root payoff v'_i
equals Q_i at a mixed owner and is at least Q_i at a quiet owner.
Thus v' is STRICTLY POSITIVE coordinatewise at EVERY root for all
sufficiently small positive price vectors c. No lower bound on the
relative ratios c_i/c_j is assumed.

### BP4. ALL finite-menu Nash profiles occupy ONLY the last date

For sufficiently small c as above, every exact Nash profile in
{0,…,N,Never} has all n_i>0. If a clock were finite surely, choose the
earliest date at which some cumulative finite mass reaches one. All
owners survive TO that date with positive probability. Conditioning
the actual independent clocks on survival gives a suffix Nash profile:
every surviving prescribed support test remains maximizing after
subtracting the common earlier payoff and dividing by positive opponent
survival. Its root has a sure owner, excluded by BP2. This argument is
valid with the penalized ALL-Never payoff as well.

AllNever itself is not Nash since a finite solo deadline pays0>−c_i.
Hence there is a latest occupied finite date t. At that date the
conditional continuation is exactly −c. BP3 gives a strictly positive
continuation vector immediately BEFORE t. Every earlier root must then
be AllContinue by BP2. Induction shows that t is the ONLY occupied date.

It must in fact be t=N. Otherwise Never, used with positive probability
by every owner, pays K_i−c_i h_i, whereas the allowed finite deadline
t+1 pays K_i in the native own-singleton convention. Since c_i h_i>0,
this contradicts its support optimality. Conversely every Nash root at
−c placed at N is a finite-menu Nash profile: its root/terminal tests
are optimal, and every earlier finite deadline pays0, below the strictly
positive equilibrium payoff. Thus the assertion describes the ENTIRE
finite-menu Nash family for every N, not one bad selector.

Any such root has at least two suppliers: a sole supplier j has a quiet
favorite i=j+1 with gap q_j+c_i(1−q_j)>0. Hence in its repeated profile
EVERY h_i<1 and (BP.1) applies. The original one-block FULL cap is K_i:
all tests after N, including Never, have value K_i, and root Nash plus
c_i>0 gives K_i>Q_i; earlier tests are0. If u_i is its penalized Nash
payoff, its original prescribed payoff is u_i+c_iν. Therefore

    D_original(block)=Σ_i c_i(h_i−ν)≤Σ_i c_i→0.         (BP.4)

This does NOT make it an absorbing near-equilibrium: ν→1. Repetition
must be priced separately.

### BP5. Every repeated selector retains a positive full debt floor

Consider ANY sequence of positive price vectors c→0, ANY calendar
lengths N, and ANY exact Nash selectors. BP4 reduces every chosen block
to one root q at its last date. Let S=Σx_i and pass to a subsequence on
which λ_i=x_i/S converges. Then λ belongs to the probability simplex.
Divide the inequalities g_i≤0 in (BP.3) by S. Because all odds vanish,
H_i/S→0 and c_i/S≥0, so

    2λ_{i−1}+λ_i≤1 for EVERY i.                       (BP.5)

In particular λ_i≤1/2 and every deleted denominator 1−λ_i is positive.
Since

    (Γλ)_i=99(1−λ_i)−100λ_{i−1},

(BP.5) implies (Γλ)_i≥49(1−λ_i)>0 for all owners. The exact signed
block statistics, with ν=∏(1−q_i), now give

    K_i/(1−h_i)→(Γλ)_i/(1−λ_i),
    U_i*=G_i/(1−ν)→(Γλ)_i,
    F_i=max(0,Q_i)→0.                                (BP.6)

If N=0 there is no early empty test, but F_i=Q_i>0 and the same limit
holds. The passive singletons provide the displayed first-order terms;
every participant pair contribution to G_i and every higher coalition
term is of order S². Formula (BP.1), with its literal Never branch,
therefore yields the COMPLETE debt limit

    D_repeated→Σ_i λ_i(Γλ)_i/(1−λ_i)≥49Σ_iλ_i=49.      (BP.7)

Every subsequence has a further simplex limit with this bound. Hence
liminf D_repeated≥49 for the ENTIRE selector family, regardless of how
calendar size, unequal prices and equilibria are chosen. This is not
merely a lower ledger for old maximizing tests: (BP.1) controls ALL new
finite tests and Never and shows Never is eventually the full cap.

An exact common-price check is useful. For x=1/200 take
c_i=ε=x+3x²+x³=40601/8000000 and q_i=x/(1+x)=1/201. Then

    Q=2613133/2706867,
    K=7880000/8120601,
    Q=K−ε(1−q)³,
    D_original=162404/1632240801,
    B_repeated=7880000/120601,
    U_repeated=1583839399/32240801,
    D_repeated=252179586084804/3888272841401>60.

The general proof does not need uniqueness of the common-price root.
All figures above follow from the full displayed table and elementary
rational operations, with no lost experiment artifact. The existing
cyclic construction in RZ4, covered by
`QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`,
gives native absorbing gap zero. BP is consequently NOT an unrestricted
positive-gap table or a contradiction to the actual spherical source.

Unequal prices do not secretly force all four rates positive. For
0<ε<1 take c₀=c₂=ε, c₁=c₃=ε²/2 and odds x₀=x₂=ε,
x₁=x₃=0. The two active root gaps are zero and each quiet scaled
gap is −ε²/2. All root payoffs are positive. This is an exact
two-supplier opposite-pair Nash root at the same last calendar date;
its repeated debt tends99. It is included in BP5, whose argument
never assumed all suppliers active or a uniform price-ratio bound.

### BP6. Mechanism decision and next genuine producer question

RETIRED: choose exact finite-calendar Nash profiles after ANY strictly
negative terminal perturbation tending to zero, then repeat them and
infer absorbing approximate Nash from the perturbation's absolute
size. The ENTIRE family fails on BP's already-solved table. A small
one-block FULL debt and strict positivity of its delivered payoffs do
not fix the failure.

The next test allows a terminal payment which does NOT tend to zero,
and must PRODUCE control of every deleted-player seam, not merely of
joint survival. For a negative payment −c the original FULL cap birth
is bounded by c_i h_i, while original prescribed transport costs c_iν.
Thus c_iν→0 alone is not the relevant bound. An actual finite-Nash
producer with Σ_i c_i h_i→0 and max_i c_i bounded below by a positive
constant would control every original finite/Never test and force
ν→0. A literal small-Never fill could then force absorption. Such
a producer has NOT been proved, and arbitrary favorable Nash selection
or periodization is not supplied as an assumption.

The literature branch checked during this pivot was Ashkenazi-Golan,
Krasikov, Rainer and Solan, “The APS approach for undiscounted quitting
games” (2026), §§2.4 and4.1–4.3, Theorems2.11 and4.10,
<https://doi.org/10.1007/s00182-026-00982-6>. Its Flesch absorption paths
use singleton quitting flows; their payoff set can be empty, and the
essential operator does not produce arbitrary joint-quitting roots.
The integrated essential-APS and finite jump–flow compiler in the
toolkit already cover that conditional architecture. No new producer
or UE hypothesis is borrowed from the paper here.

## NP universal finite-prefix corollary and an actual end-Never graft

### NF9. Every minimum prefix at the SAME separated table has a paid nonsure bridge

This is an ordinary source application, not an extra assumption of NP.
At its ONE final separated, row-generic, common-debt table fix ANY
x∈[0,1]⁴ with Σx_i>0 and ANY w=(u,b) in ORIGINAL K such that
D(T_x(w))=δ. Realize w by finite-law tails and prefix EXACT rates x
at date0. These literal profile pairs converge to T_x(w), hence form
a TRUE original full-minimum sequence.

NP's universal near-minimum joint-Never floor gives
∏_i(1−x_i)≥η>0. In particular every x_i<1. The fixed positive
first-date mixture interval is retained under the marked producer.
No prescribed pre-active head forces it to be the FIRST active stage.
NP's at-least-two-suppliers proof then gives at least two positive
STRICTLY MIXED x_i. Its root/later bridge has a FINITE later moving
tester and positive common debt. All survival factors α_i>0.

The root response is Q_i. Every later response is bounded above
by C_i=A_i+α_i b_i, and conditional finite/Never tail near-cap tests
give full prefix cap at least C_i. A later source maximizer has value
equal to Q_i. These two inequalities give Q_i=C_i. Its nonempty
opponent-root event has positive probability and generic row rewards
distinguish join and wait payoff kernels. No tail Nash, minimum,
cap attainment, old chronology or contact93 is inferred.
This applies afresh after EVERY same-table minimum-preserving graft.

### SG1. Exact global end-graft question and status

COMPLETE ORDINARY DERIVATION, UNREVIEWED. Work at ANY produced true
full minimum q with all n_i=q_i(Never)>0 and positive own s_i.
Write R_i=V_i(Never), h_i=∏_(j≠i)n_j and ν=∏_i n_i>0.
For an arbitrary actual independent tail with pair v=(u,b), replace
each owner's ORIGINAL Never branch by that tail, strictly after
the entire finite original block. Old finite draws stay unchanged.

The exact complete limiting ledger is

    U_i^graft=U_i+ν u_i,
    B_i^graft=max(B_i,R_i+h_i b_i).

This is a genuine independent finite-amplitude competitor, not
a discounted law, a shared lottery, a supplied response selector
or a signed insertion at a nonisolated marked point.

### SG2. Literal finite witnesses and every response cap

For a finite-support original approximant p^k, let L_k be its LAST
finite support date. Keep every old finite atom, and replace only
its Never branch by the shifted arbitrary finite tail law, starting
at L_k+2. No stretch between old dates is used: new empty dates
between old simultaneous stages could change old full caps.
The old calendar already has empty finite dates after L_k, so
date L_k+1 retains their old response value.

Any finite reply through L_k is unchanged exactly. An empty reply
after L_k but before the new tail pays R_i^k+h_i^k s_i, an old
finite response value and thus≤B_i^k. Later finite tail replies
pay R_i^k+h_i^k V_i(t,v_-i): any old finite opponent exit screens
the tail, while the all-opponent-old-Never cylinder has probability
h_i^k and carries the actual tail response. Literal Never has
the same formula with tail Never. Taking ALL finite replies and
Never gives EXACTLY

    B_i^{k,graft}=max(B_i^k,R_i^k+h_i^k b_i).

The old finite supremum is represented before the tail because
positive own s_i makes it dominate old literal Never, and the
old support is finite. Prescribed pay gains exactly ν_k u_i:
only the original joint-Never event reaches the appended tail.

All U_i^k,B_i^k,R_i^k,n_i^k converge under the full marked
compiler, including the separate literal Never kernel. Thus
the graft ledger converges to SG1 and lies in original K. A
second diagonal tail approximation extends the SAME ledger to
EVERY v∈K. Arbitrary finite/Never tail responses remain included.
If v∈K_abs, realize it by absorbing tails; each actual graft
is then absorbing and its limiting debt has the stronger floor
δ_abs. No tail minimality or strategic equilibrium is used.

### SG3. A global tail budget, not a renamed cap price

Define the strictly positive end budgets

    κ_i=(B_i−R_i)/h_i≥s_i.

For EVERY v=(u,b)∈K, actual globality gives

    Σ_i h_i[(b_i−κ_i)⁺−n_i u_i]≥0.

At a separated NP table the SAME expression is≥g>0 for EVERY
v∈K_abs. The old AllNever tail has u=0,b=s and gives equality0,
as it must. This inequality retains ALL original tail laws and
caps; it does not assume compatible punishments or convexify K.

### SG4. Actual positive-simplex tail kills the all-strict budget branch

At the actual Fin4 no-UE table, the checked producer
exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff
in UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean
gives z_j≥0, Σz_j=1 and (Γz)_i>0 for EVERY i. The exact matrix
quittingProjectiveLCPMatrix in
UniformEquilibrium/Quitting/Projective/SingletonLCP.lean is
Γ_ij=r_i({j})−s_i, with recipient ROW i. This tracked source
and its imports were inspected narrowly; it is not a supplied
punishment plan or a homogeneous zero-residual vector.

Take the actual one-date independent tail in which player j
quits with probabilityρ z_j and otherwise uses Never. As ρ↓0,

    u_i(ρ)=ρ v_i+O(ρ²),
    v_i=Σ_j z_j r_i({j})=s_i+(Γz)_i>0.

Uniform marginal coupling with AllNever gives
|b_i(ρ)−s_i|≤2Mρ, including ALL finite responses and Never.
The payoff remainder is bounded by2Mρ², from singleton weight
errors plus nonsingleton probability. Choose ρ>0 small enough
that every u_i(ρ)>0. This is an actual finite tail, not an
asymptotic Nash or a bounded-controller certificate.

If every κ_i>s_i, choose the SAME positive ρ also small enough
that b_i(ρ)<κ_i for every i. SG1 then leaves every original
full cap EXACTLY unchanged and increases EVERY original payoff
by ν u_i(ρ)>0. Its true SUM debt is strictly belowδ.

More explicitly, for all large original finite indices the
strict budget inequalities hold with B_i^k,R_i^k,h_i^k.
Their actual grafted full caps equal B_i^k, and
D(p^{k,graft})=D(p^k)−ν_kΣ_i u_i(ρ)→δ−νΣ_i u_i(ρ)<δ.
Some sufficiently large k supplies an ACTUAL finite-law
competitor belowδ. No cap claim at an unattained marked
deadline is needed.

Therefore every produced positive-Never source has SOME owner
with κ_i=s_i, equivalently

    B_i=R_i+h_i s_i=V_i(c).

The final EMPTY finite compact test c is genuinely maximizing.
It has zero prescribed own/mixture point mass and is distinct
from literal Never, which is strictly suboptimal. This is a
strict actual-source exclusion of the all-strict end-budget
geometry, not a local gain-charge inequality or cap alias count.

### SG5. Remaining source and boundary honesty

PC's upper-support restriction is valid but becomes vacuous at
this produced source: SG4 forces latest active point L=c.
No packet is proposed for PC's already subsumed alternative.
The relevant surviving end wall is now an actual solo-valued
finite test on the positive all-opponent-Never cylinder.

SG4 does NOT say the root/later bridge owner is the c-active
owner, that ALL caps contain c, that the c response is attained
at an original finite deadline, or that its active wall permits
the positive-simplex tail. At this wall the appended tail can
raise caps, and SG3 prices that increase. No UE, rank or full
consumer is asserted.

Without the positive singleton/Q source the strict-budget branch
need not have a useful singleton delivery column; it is not
retired by an unweighted or incorrectly oriented matrix sum.
At a profile which is NOT a true global minimum, SG3 need not
hold even if its profile debt is positive. Its derivation uses
the actual finite witnesses and the original ALL-law floor,
not the absorbing minimum as a substitute.

The next concrete question is whether the nonempty c-active
owner set can be joined to the paid first-root/later-cap bridge
by a whole-law change whose born cap is controlled by SG3,
including every finite/Never tail. Counting those owners or
bounding the first-order leakage alone would not be a consumer.
