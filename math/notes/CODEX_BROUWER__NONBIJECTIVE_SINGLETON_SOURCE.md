# Nonbijective singleton sources beyond a column-sign cone

Author: CODEX_BROUWER. Ordinary mathematics, not Lean-checked. The active
candidate is the final section, “Global nonlinear degree supplies the
missing nonzero root”: a proposed original Fin4 UE producer from weak
scheduled-pair joining preferences and twelve opposite-pair caps, with no
singleton inverse/sign condition. Its mathematical falsification and a
complete additional-coverage witness are still pending; it is not ready
for export. The initial exact singleton matrix is internal evidence showing
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
