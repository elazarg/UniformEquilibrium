# A discounted-index escape for inverse-positive singleton matrices

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematics proof candidate, not independently
reviewed or Lean-checked. No export. The proposed conclusion is an actual
Fin4 UE class, not a source verifier or a temporal interpretation of a
best-response edge. The remaining coverage comparison is explicitly bounded
in Section 7; no claim of being outside every existing sufficient class is made.

## 1. Question and proposed theorem

There are four players, independent behavioral play, a real reward vector
r(S) for each nonempty quitting coalition, and payoff zero at Never.
Rewards are bounded because the table is finite. Write

    s_i = r_i({i}),       Γ_ij = r_i({j}) − s_i.

Rows are recipients and columns are quitters; Γ_ii=0. Assume

    det Γ < 0,           B = Γ⁻¹ has B_ij > 0 for all i,j.       (1)

**Proposed theorem.** Every such Fin4 quitting game has an ordinary uniform-
equilibrium payoff, against all unrestricted behavioral deviations. Own
singletons and nonsingleton rewards may have arbitrary signs. No restrictions
on the 44 nonsingleton payoff coordinates are imposed.

The mechanism is a global fixed-point-index contradiction in the entire
stationary discounted equilibrium set. It is not a local root perturbation.
The essential source claim proved below is uniform localization of EVERY
small-discount equilibrium, under the contrary no-UE assumption.

## 2. Literature motivation and the quantifier trap

I read the published page images of Eilon Solan, *Three-player absorbing
games* (1999), pp. 670, 674–678, 689–693: Theorems 4.5 and 4.7, Lemma 5.3,
the four-player example in Section 9, and the opening support-reweighting
argument in Section 10. Primary reference:
[published paper](https://doi.org/10.1287/moor.24.3.669).

The proof first obtains a suitable discounted limit, then reweights minimal
absorbing neighbors. In a literal quitting game at all Continue these
neighbors are exactly the singleton exits. The three-dimensional geometric
alternative either produces a complementary mixture or a positive cyclic
configuration. Its Section 9 obstruction is itself a quitting table; extra
Continue actions do not explain its four-player failure.

The current full-support reduction does NOT say that every discounted germ
has full singleton support. The declaration
`exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap`
produces SOME full-support packet by a different constrained-stationary
construction. In the same file,
`uniformPayoff_or_fullSupportFullNormalCore_of_finFour_support_card_two`
explicitly gives UE OR a reselected full-support packet, not a consumer of
every support-two germ. That replacement cannot localize the original Nash
set. This invalid initial shortcut is retired.

Instead (1) supplies the necessary universal statement algebraically:

    μ≥0, μ≠0, Γμ≥0  ⇒  μ=B(Γμ)>0.                       (2)

The strict inequality is coordinatewise: Γμ cannot be zero because Γ is
invertible, and B sends every nonzero nonnegative vector to a strictly
positive vector. This applies to EACH original discounted-limit source;
there is no source reselection.

## 3. Exact discounted map and all boundary actions

Assume contrapositively that the original Fin4 game has no UE. The checked
same-table reduction supplies punishment normality

    v_i^pun ≤ s_i   for every i.

Set c_i=min(0,v_i^pun), let r'_i(S)=r_i(S)−c_i, and put a_i=s_i−c_i.
Then a≥0. The singleton difference matrix of r' is still exactly Γ.
If a=0, then every s_i=c_i≤0 and all Never is an exact equilibrium of
the original game. Hence

    a≥0,                    a≠0.                         (3)

The shift is the actual punishment-normalized auxiliary game, not a claim
that terminal translation preserves Never or ordinary strategic equivalence.

For discount complement λ∈(0,1), put d=1−λ. For a stationary hazard vector
q∈[0,1]⁴ define, for each player i,

    α_i(q) = ∏_(j≠i)(1−q_j),       C(q)=∏_j(1−q_j),
    A_i(q) = Σ_[∅≠T⊆I\{i}] Pr_q(T) r'_i(T),
    Q_i(q) = Σ_[T⊆I\{i}] Pr_q(T) r'_i(T∪{i}),
    R_i(q) = q_i Q_i(q)+(1−q_i)A_i(q),
    u_i(λ,q) = d R_i(q)/(1−d C(q)),
    D_i(λ,q) = (1−d α_i(q)) Q_i(q) − A_i(q).           (4)

Here Pr_q(T) is the product law of the opponent Quit set. The denominator
is positive. In particular the final term of D is −A_i, NOT −d A_i.
Its exact meaning is

    Q_i−A_i−α_i u_i = D_i/(1−d C).                     (5)

Therefore q is a stationary discounted Bellman equilibrium exactly when

    q_i=0 ⇒ D_i≤0;   0<q_i<1 ⇒ D_i=0;   q_i=1 ⇒ D_i≥0. (6)

These include every upper face and every intersection of faces. Equivalently
q is a fixed point of the continuous cube map

    F_λ(q)_i = clip_[0,1](q_i+D_i(λ,q)).               (7)

Brouwer gives at least one such point for every λ. Its value is precisely
u in (4), satisfying u=d[R+C u]; no arbitrary continuation annotation is
introduced. The Bellman best-response principle at positive discount gives
the full stationary-discounted equilibrium interpretation of (6).

## 4. No-UE localizes the ENTIRE discounted equilibrium set

First every sequence λ_n↓0 and fixed points q_n of (7) satisfies q_n→0.
Suppose otherwise. By compactness select a limit q_*≠0, together with a
limit of the bounded values u_n. Their graph is semialgebraic: (4) can be
cleared using the strictly positive denominator and (6) is a finite union
of polynomial sign conditions. Semialgebraic analytic curve selection at
this specified endpoint, followed by exact-power normalization of the
positive discount coordinate, gives an analytic discounted Bellman germ
with that SAME endpoint q_*. It is jointly absorbing. The checked theorem
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint` returns an
ordinary UE payoff of the ORIGINAL game, contradiction.

This use of curve selection is endpoint-preserving, not a new call selecting
an unrelated germ. Only existence of an arc in the selected polynomial graph
is used. Its mathematical construction is: select an analytic arc through
the closure point; its positive discount coordinate has a positive leading
coefficient and finite positive order; a local analytic change of parameter
makes that coordinate exactly t^k. This is exactly the prescribed-endpoint
input accepted by the named Bellman germ constructor in Section 8.

Here is a direct sequential proof of the stronger rate localization; it does
not need a uniform Puiseux order. Let q_n→0 be ANY sequence of fixed points,
and set t_n=Σ_i q_(n,i). For small λ no fixed point is all Continue, since
D_i(λ,0)=λ a_i and (3) gives a positive coordinate. Thus t_n>0. Pass to a
subsequence so that

    μ_n=q_n/t_n→μ∈Δ⁴,       ρ_n=λ_n/(λ_n+t_n)→ρ∈[0,1],
    u_n→u_*.

Uniform finite-product expansions give

    R(q_n)=t_n(a+Γμ_n)+O(t_n²),
    1−C(q_n)=t_n+O(t_n²),
    u_*=(1−ρ)(a+Γμ).                                  (8)

The remainder divided by λ_n+t_n tends to zero even when t_n/λ_n is
unbounded. Because all coordinates q_(n,i)<1 for large n, (6) says that
Continue is optimal. Taking its original endpoint inequality to the limit
gives u_*≥a. If μ_i>0, then q_(n,i)>0 for large n and both endpoints tie;
the discounted recursion gives u_(n,i)=d_n Q_i(q_n), so u_*i=a_i.

If ρ=1, (8) and u_*≥a force a=0, impossible. For ρ<1, (8) gives

    Γμ ≥ [ρ/(1−ρ)] a ≥0.                              (9)

Apply (2): μ>0. Thus ALL coordinates pin, u_*=a, and

    (1−ρ)Γμ=ρ a.

The case ρ=0 would give Γμ=0, also impossible. Consequently

    0<ρ<1,       μ(1−ρ)/ρ=B a=:h_*>0.                 (10)

This proves, uniformly over the whole fixed-point set as λ↓0,

    q/λ → h_* .                                       (11)

Indeed a failure of boundedness or convergence has a subsequence of the
compact variables (μ_n,ρ_n,u_n) above, and (10) contradicts that failure.
This rules out both divergent rescaled hazards and zero leading shares.
It does not assert (11) from the mere existence of some full-support packet.

## 5. Uniqueness, orientation, and the contradiction

Since D is polynomial in (λ,q), the function

    H(λ,h)=D(λ,λh)/λ

extends analytically to λ=0. Direct first-order expansion of (4) gives

    H(0,h)=a−Γh,          ∂_h H(0,h_*)=−Γ.             (12)

The implicit function theorem gives a unique zero h(λ) near h_* for small
|λ|, with h(0)=h_*. For positive small λ its corresponding q=λh(λ) is
strictly interior. Equation (11) puts EVERY fixed point there; hence (7)
has exactly this one fixed point and none on the boundary of the cube.

We use only the elementary fixed-point degree fact, not an assumed finite-
game index formula for the rational stationary game. A continuous map F
from a cube to itself with no boundary fixed points has
deg(Id−F,cube°,0)=1: homotope F linearly to the constant center of the cube.
Every positive homotopy time maps the boundary into the strict interior,
so there is no boundary zero throughout the homotopy. At the constant
map the displacement has degree +1.

At our sole fixed point the clipping in (7) is locally inactive. The
displacement is −D, and the chain rule in the rescaling above gives

    ∂_q D(λ,λh(λ))=∂_h H(λ,h(λ))→−Γ.

Thus its local degree is

    sign det(−∂_q D)=sign det Γ=−1.                    (13)

The global degree is the sum of its isolated local degrees, here −1,
contradicting +1. This proves the proposed theorem.

The orientation is explicit: it is Γ, not −Γ or Γᵀ, in the displacement
Jacobian. No temporal order of Nash roots, no equilibrium selection at every
discount, no regularity of the full original game, and no source multiplier
or reward normal are assumed.

For the classical topological input I checked the primary exposition
[Hari Govindan, The Index of Nash Equilibria, 2017](https://eventos.cmm.uchile.cl/dgames2017/wp-content/uploads/sites/40/2017/01/Govindan_Chile.pdf),
slides 9–16, including normalization, local displacement index, and the
degree-one identity. The explicit cube homotopy above avoids importing
finite-normal-form invariance to the nonlinear map (7).

## 6. Exact falsification and nonempty-class tests

The signed matrix

    Γ = [ 0   2   1  −3 ]
        [−3   0   2   3 ]
        [−3   2   0   2 ]
        [ 3  −3  −1   0 ]

has det Γ=−3 and

    B = [6  4/3  7  26/3]
        [5    1  6     7]
        [3    1  3     4]
        [4    1  5     6].                             (14)

Multiplying gives ΓB=I. This is an inhabited raw-table class: choose ANY
real own singleton vector s, put r_i({j})=s_i+Γ_ij, and choose all eleven
nonsingleton reward vectors arbitrarily. The theorem is not inferred from
an equilibrium of one chosen completion.

The determinant sign cannot be discarded. The paired matrix

    Γ⁺ = [ 0  3 −1 −1]
         [ 3  0 −1 −1]
         [−1 −1  0  3]
         [−1 −1  3  0]

has determinant 45, with inverse diagonal 2/15, within-pair off-diagonal
7/15, and cross-pair entries 1/5. Hence inverse positivity alone permits
the single matching equilibrium to carry index +1. This agrees with the
existing all-germ Solan–Vieille boundary obstruction; the argument does not
claim that some better discounted branch must exist there.

The exact arithmetic above can be reproduced without any solver:

```python
import sympy as S
G=S.Matrix([[0,2,1,-3],[-3,0,2,3],[-3,2,0,2],[3,-3,-1,0]])
B=S.Matrix([[6,S.Rational(4,3),7,S.Rational(26,3)],
            [5,1,6,7],[3,1,3,4],[4,1,5,6]])
assert G.det()==-3 and G*B==S.eye(4)
assert all(x>0 for x in B)
P=S.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
assert P.det()==45 and all(x>0 for x in P.inv())
```

## 7. Bounded comparison with existing consumers

The ordinary non-Q and homogeneous consumers do NOT subsume this hypothesis.
For any B>0, B is strictly copositive and hence standard Q by the checked
copositive theorem. Q transfers to Γ=B⁻¹: solve the B-LCP with right-hand
side −Bz, variable w and residual x=B(w−z); then w=z+Γx and x,w≥0,
x_iw_i=0 solve the Γ-LCP. Homogeneous feasibility for Γ is impossible:
w=Γx≥0, x≥0, x⊥w and w≠0 imply x=Bw>0 and therefore w=0, contradiction.

Full standard Q does not imply projective Q on every principal. In (14),
the principal on {0,1,3} is

    T=[0 2 −3; −3 0 3; 3 −3 0].

If Tx≥0 with x≥0, its inequalities imply x_1≥3x_2/2,
x_2≥x_0, and x_0≥x_1, forcing x=0. Thus no homogeneous simplex vector
exists. The stronger Tx≥(1,1,1) is impossible as well, so the standard LCP
at right-hand side (−1,−1,−1) has no solution. By the exact standard-or-
homogeneous dictionary this principal is not projective Q. Thus the full
matrix is not projective Q-bar, despite its full standard-Q property.
Each row also has a distinct negative entry, so all four players survive
the recursive singleton normal-core deletion.

RENY's existing inverse-positive producer assumes a relabeling with every
successor gap negative and every reverse gap positive. Its negative-
determinant subcase is already covered by the signed spectral export.
Matrix (14) has NO such relabeling: player 0's sole negative successor is
3; from 3 the next player is 1 or 2, and either has sole negative successor
0, closing a three-cycle before the fourth player is visited. Thus that
whole signed-four-cycle hypothesis does not contain (14).

This verifies non-subsumption by those named matrix consumers, not by every
possible raw-table criterion or a claimed classification of all completions.
No weakening of the determinant or inverse-positivity premises has been
proved. The positive-determinant inverse-positive chamber remains open to
this mechanism. The general residual need not have a positive inverse.

## 8. Exact checked dependencies and remaining review request

Inspected named declarations, with their actual domains:

- `normalizedSoloMatrix_eq_soloReward_sub`, in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`:
  the literal Γ convention, no transpose or hidden scale.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  used only for same-table all-player punishment normality under no UE.
- `exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap`
  and `uniformPayoff_or_fullSupportFullNormalCore_of_finFour_support_card_two`,
  in `Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`:
  inspected to prevent the SOME-versus-ALL packet error; not used in (11).
- `quittingAuxiliaryLive`, `quittingAuxiliaryReward`,
  `quittingRootFixedPoint_unshift`, and
  `isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`, in
  `Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`:
  the latter is generic in the finite player type and supplies the full
  ordinary-UE consumer, including a noncontracting sole owner's punishment.
- `exists_analyticBellmanGerm_of_positiveCoordinateArc`,
  `exists_analyticBellmanGerm_of_powerCurve`, and
  `analyticBellmanGermOfPowerCurve_endpoint`, in
  `VanishingDiscount/Bellman/Germ.lean`, plus the selected sign-cell
  definitions in `VanishingDiscount/Bellman/CurveGate.lean`:
  prescribed-endpoint constructors, not an unrelated existential germ.
- `nonempty_analyticBellmanGerm_quittingGame`, in
  `Quitting/Boundary/Analytic/Germ.lean`: unconditional germ existence;
  this alone would NOT justify the specified-endpoint step.
- `isStandardQ_of_strictlyCopositive`, in
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`, and
  `isStandardQ_iff_isStandardQMatrix`, in
  `Quitting/Classification/LCP/CopositiveQBridge.lean`:
  the generic/production dictionary used only in the overlap calculation.
- `IsProjectiveQBarMatrix` and the standard-or-homogeneous equivalence, in
  `Quitting/Classification/LCP/MatrixClasses.lean`; the current consumer
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`, in
  `Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.

All paths except the first full path are relative to `UniformEquilibrium/`,
except the explicitly named `MathUE/` path. No theorem in this note is claimed
to be a checked composition already present in those files.

Independent falsification requested: audit (4)–(6), the specified-endpoint
curve-selection bridge, the uniform sequential argument (8)–(11), and the
local/global degree orientation (13). In parallel with that gate, the one
concrete next question is whether inverse positivity can be replaced by a
weaker finite singleton-cone property while still forcing EVERY boundary
component to have the same negative index; no such extension is asserted.
