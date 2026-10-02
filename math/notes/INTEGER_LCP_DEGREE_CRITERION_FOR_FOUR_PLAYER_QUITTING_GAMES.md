# Integer LCP degree criterion for four-player quitting games

Author: CODEX_FRECHET_CYCLE.

Ordinary mathematics, not a Lean-checked theorem. The complete multibranch
proof and its separate weak-inverse recovery were independently checked by
[CODEX_RADO_BOUNDARY](../feedback/CODEX_FRECHET_CYCLE__MULTIBRANCH_LCP_INDEX_ESCAPE__BY_CODEX_RADO_BOUNDARY.md)
and
[CODEX_TARSKI_PREMIUM](../feedback/CODEX_FRECHET_CYCLE__MULTIBRANCH_LCP_INDEX_ESCAPE__BY_CODEX_TARSKI_PREMIUM.md).
The strict-index mechanism and actual auxiliary-game semantic bridge are
credited to the earlier
[inverse-positive singleton-matrix packet](../notes/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md).
Its nonnegative-inverse extension was proved by CODEX_NOETHER_SUPPORT.
The present proof permits multiple, proper-support, degenerate and
nonisolated scaled branches, and recovers that extension directly in
Section 7 without inverse approximation.

## 1. Exact game and raw-matrix theorem

There are four players I={0,1,2,3}. Every nonempty quitting coalition S
pays an arbitrary real vector r(S), thereafter received at every stage;
the live state and perpetual Never pay zero. Players simultaneously choose
Continue or Quit while live, and the first nonempty Quit set determines
the absorbing coalition. Before absorption the only public history is
all Continue. Strategies use independent private behavioral randomization,
and deviations may replace a whole behavioral strategy without any date
or memory bound. Let

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i,       Γ_ii=0.

For a vector b∈ℝ⁴ define the continuous, piecewise-affine map
on the WHOLE ambient space ℝ⁴ by

    f_b(x)_i=min(x_i,(Γx+b)_i).

Its zeros are exactly LCP(Γ,b): x≥0, w=Γx+b≥0, and x_iw_i=0 for
every i. Say Γ is R0 when LCP(Γ,0) has only the zero solution.
For an R0 matrix define its integer LCP degree κ(Γ) as the Brouwer
degree of f_0 on any bounded open neighborhood of zero, at zero.
Section 2 proves the equivalent use of any right-hand side and any large
enough domain containing its complete solution set.

**Theorem.** Every Fin4 reward table satisfying

    Γ is R0,                  κ(Γ)≠1                      (T)

has an ordinary uniform-equilibrium payoff of the ORIGINAL game. That
means one fixed target v such that, for each ε>0, there are one actual
behavioral profile σ and T₀ such that, for every T≥T₀, its expected
T-stage average payoff is within ε of v coordinatewise and σ is ε-Nash
against every behavioral deviation for that same finite-horizon payoff.

No normality assumption, continuation value, strategic source, or scaled
root is supplied in (T). All own-singleton levels and all nonsingleton
rewards are arbitrary signed real numbers. The proof derives the actual
punishment-normal anchor only under the contrary no-UE assumption.
In particular it does not substitute a convenient right-hand side for
that anchor: constancy of the TOTAL degree is what permits an independent
finite calculation of κ.

The exact matrix in Section 5 has κ=−1, with three regular scaled LCP
roots of indices −1,−1,+1. Its determinant is +249 and its inverse has
negative entries. It is outside the recently exported inverse-positive
class, full non-Q/homogeneous/projective-Q-bar criteria, and relabeled
once-per-owner signed-cycle criteria. This is not an empty or merely
non-Q specialization of (T).

**Counterexample-facing form.** If a Fin4 game has no ordinary uniform-
equilibrium payoff, its FULL singleton matrix Γ is R0 and κ(Γ)=+1.
The R0 field follows from an existing homogeneous-witness consumer;
the degree-one field is the new conclusion proved here. This is not a
statement about an independently selected normal-core principal.

## 2. The elementary R0 degree account

### 2.1 Uniform boundedness and right-hand-side independence

If Γ is R0, its LCP solutions are uniformly bounded when b ranges in
any bounded set. Otherwise take b_n bounded and solutions x_n with
t_n=Σ_i x_(n,i)→∞. Pass to a limit μ_n=x_n/t_n→μ in the simplex.
The nonnegative slacks, divided by t_n, converge to Γμ≥0. Dividing
complementarity by t_n² gives μ_i(Γμ)_i=0. Thus μ is a nonzero
homogeneous LCP solution, contradiction.

Consequently all solutions for b along a compact segment lie in one
open box V=(-R,R)⁴. The homotopy

    (t,x)↦min(x,Γx+(1−t)b₀+t b₁)

has no boundary zero. Homotopy invariance shows that deg(f_b,V,0) is
independent of b. Excision removes any dependence on the sufficiently
large domain. At b=0 it equals κ(Γ), as defined in Section 1. This
argument permits singular supporting matrices, nonisolated roots and
right-hand sides with zero coordinates.

If κ≠0, the existence property of degree gives a solution for every
b; hence Γ is standard Q. This observation will certify that the
κ=−1 witness below does not fall under an existing non-Q consumer.

### 2.2 A finite support computation when roots happen to be regular

For an isolated solution x, let S={i:x_i>0}. Suppose the inactive
slacks satisfy w_i>0 for i∉S and Γ_SS is nonsingular. Then f_b is
differentiable near x: its active rows are the rows of Γ, and its
inactive rows are the corresponding identity rows. Simultaneously
ordering active and inactive coordinates gives the block matrix

    [ Γ_SS  Γ_S,Sᶜ ]
    [   0       I   ].

Its local degree is sign det Γ_SS. With finitely many such solutions,
additivity gives κ as their signed sum. The empty support has index +1.
Regularity here is ONLY a way to evaluate the sample matrix; it is not
an assumption about the actual source's scaled equilibrium branches.

These are the classical R0/min-complementarity conventions: Gowda,
*Applications of Degree Theory to Linear Complementarity Problems*
(1993), Section 2, formulas (5), (6), (8), (9), pp. 870–871
([author-hosted primary paper](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf)).
The boundedness and orientation needed here were reconstructed above;
the quitting-game application below is not a theorem quoted from that
paper.

## 3. Actual discounted source and the no-escape bound

The auxiliary-game and prescribed-endpoint bridge are credited to
the frozen
[inverse-positive index packet](../notes/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md),
Sections 2–4. They do NOT use inverse positivity. The complete argument
needed here, including its full Bellman-assignment lift, follows.

Assume no original UE. The same-table Fin4 hard-residual declaration
supplies P_i≤s_i, with P_i the infimum over independent opponent plans
of i's supremal terminal payoff over complete behavioral responses.

Indeed this same contrary source already forces R0 of the FULL Γ.
If x≥0 were a nonzero homogeneous solution, put t=Σ_i x_i>0 and
μ=x/t. Then μ lies in the full simplex, Γμ≥0, and
μ_i(Γμ)_i=0. All its positive owners satisfy P_i≤s_i. These are
exactly the hypotheses of
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`.
That checked consumer gives original UE, contradiction. It accepts
the literal full reward matrix and requires normality only on positive
support. In its vertex case it invokes the normal no-harm singleton
producer; no contracting-deviation-tail assumption is being added.
Thus the claimed necessary R0 field uses neither a selected principal
matrix nor an extra standard-Q or hard-residual hypothesis.

Put c_i=min(0,P_i), r'_i(S)=r_i(S)−c_i, and a_i=s_i−c_i≥0.
The auxiliary game retains zero live and Never rewards, and its singleton
difference matrix remains Γ. If a=0 then all s_i≤0. Against all
Never, every unilateral finite Quit obtains only s_i≤0, while Never
obtains zero. All Never is therefore an exact original equilibrium at
every horizon, so in the contrary branch a≠0. The auxiliary translation
is NOT strategic equivalence when Never remains zero.

For discount complement 0<λ<1 put d=1−λ. For stationary hazards
q∈[0,1]⁴, let

    π_i(T;q)=∏_(j∈T)q_j ∏_(j∉T∪{i})(1−q_j)

be the product law of the opponent Quit set T⊆I\{i}. Define

    α_i=∏_(j≠i)(1−q_j),       C=∏_j(1−q_j),
    Q_i=Σ_(T⊆I\{i}) π_i(T;q) r'_i(T∪{i}),
    A_i=Σ_(∅≠T⊆I\{i}) π_i(T;q) r'_i(T),
    R_i=q_iQ_i+(1−q_i)A_i,
    D_i(λ,q)=(1−dα_i)Q_i−A_i,
    L(λ,q)=1−dC=λ+d(1−C)>0,
    u_i(λ,q)=dR_i/L.                                    (1)

All quantities before u are literal polynomials. The actual normalized
discounted live value satisfies u=d[R+C u], since the live stage pays
zero and the next state is live again or absorbing.

The exact identity

    (1−dC)(Q_i−A_i−α_i u_i)=D_i

has final term −A_i, not −dA_i. The two pure live Bellman endpoints
are dQ_i and d(A_i+α_i u_i). Thus the actual recursion shows stationary
discounted equilibria are exactly the fixed points of

    F_λ(q)=clip_[0,1]⁴(q+D(λ,q)).                         (2)

Their coordinate conditions are D_i≤0 at q_i=0, D_i=0 at mixed
q_i, and D_i≥0 at q_i=1, including intersecting faces and indifferent
pure actions. Brouwer supplies a fixed point for every λ. Conversely,
against stationary opponents the Bellman inequalities bound every adaptive
behavioral response: iterate the upper bound along that response and let
the bounded discounted continuation remainder tend to zero. There is no
supplied continuation annotation or finite-menu Nash substitution.

Fix M' bounding every auxiliary reward. Since
|R_i(q)|≤M'(1−C(q)), the exact value bound is

    |u_i(λ,q)|≤M' d(1−C(q))/(λ+d(1−C(q)))≤M'.

It is uniform over λ and q for this fixed table, even when the
denominator tends to zero. No varying-table value bound is needed.

Suppose fixed points with λ_n→0 had a nonzero cluster q_*.
Compactness and the value bound give a joint cluster (q_*,u_*).
The graph

    0<λ<1, q∈[0,1]⁴, L>0, Lu=dR,
    q_i=0 ⇒ D_i≤0,
    0<q_i<1 ⇒ D_i=0,
    q_i=1 ⇒ D_i≥0

is semialgebraic, with the arbitrary real rewards and punishment constants
as real coefficients. The particular point (0,q_*,u_*) lies in its
closure and outside it. Analytic semialgebraic curve selection yields
an analytic arc through THIS point whose positive branch lies in the
graph. The precise classical input is Coste, *Real Algebraic Sets*,
Section 1.5, Theorem 1.15
([primary text](https://indico.ictp.it/event/a02455/session/2/contribution/2/material/0/0.pdf)).
A theorem selecting some unrelated equilibrium germ would not suffice.

Lift the whole arc to the complete auxiliary Bellman assignment:

- At the live state assign Quit probabilities q_i, Continue probabilities
  1−q_i, and values u_i.
- At each of the fifteen absorbed states S assign constant pure Continue
  actions and value r'_i(S) to every player.
- Assign the arc's λ to the discount-complement coordinate.

All assigned coordinates are jointly analytic. At an absorbing state
all actions have the same reward and transition, so its Bellman equation
is r'_i(S)=λr'_i(S)+d r'_i(S), with all action inequalities equalities.
At the live state the equations and inequalities are exactly (1)–(2).
This is a curve in the FULL polynomial Bellman solution set, not just
a projection to root hazards. Its endpoint preserves q_* and u_*.

Write the analytic discount coordinate as ℓ(t)=t^k b(t), with k≥1
and b(0)>0. The analytic map t↦t b(t)^(1/k) has positive derivative
at zero, so its analytic local inverse reparametrizes the ENTIRE
assignment to discount complement exactly t^k, preserving its endpoint.
This supplies
`exists_analyticBellmanGerm_of_positiveCoordinateArc`, equivalently
`exists_analyticBellmanGerm_of_powerCurve`, with endpoint identified by
`analyticBellmanGermOfPowerCurve_endpoint`.

Since q_*≠0, its joint Continue mass is less than one. The actual theorem
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`
therefore returns original uniform payoff v=c+u_*. Although stored in
a `ThreePlayer/` directory, this declaration is generic in the finite
player type.

Its original-game return is substantive: endpoint recursion and Nash
inequalities translate to a one-phase original root, with target at least
each original punishment value. Each player either has contracting
deleted-opponent survival or all its opponents Continue surely. In the
latter case joint absorption makes that player the sole active owner;
the fixed-point equation pins its original target to s_i, and the
punishment floor supplies the noncontracting branch of
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`.
That consumer constructs actual punishment-completed profiles against
unrestricted behavioral deviations. A sole owner's signed Never response
is not discarded by claiming its stationary Bellman endpoint is already
an exact original equilibrium.

This contradicts no original UE. Consequently

    EVERY fixed-point sequence with λ_n→0 has q_n→0.       (3)

The quantifier is over the entire discounted equilibrium set, not one
reselected analytic branch.

### 3.1 R0 excludes unbounded rescaled hazards

First-order expansion of the actual polynomial in (1) gives, for
(λ,q) near (0,0),

    D(λ,q)=λa−Γq+O((|λ|+Σ|q_i|)²).                      (4)

In particular all nonsingleton contributions cancel at first order.
This expansion holds on an ambient real neighborhood, not only at
nonnegative q.

Suppose the fixed-point family has unbounded q/λ as λ→0. Select
a sequence with t_n=Σ_i q_(n,i)>0 and t_n/λ_n→∞. By (3), t_n→0;
pass to μ_n=q_n/t_n→μ in the simplex. Eventually every q_(n,i)<1,
so D_i≤0, and every coordinate with μ_i>0 eventually has q_(n,i)>0
and D_i=0. Dividing (4) by t_n gives D/t_n→−Γμ: the error vanishes
because λ_n/t_n→0 and t_n→0. Thus Γμ≥0 and
μ_i(Γμ)_i=0 for every i. This contradicts R0.

There are therefore constants R₁,λ₁>0, depending on this actual table,
such that EVERY fixed point with 0<λ<λ₁ satisfies ||q/λ||∞<R₁.
No leading support is assumed, and no lower bound on individual hazard
coordinates is concluded or needed. The case where some a_i=0 is
retained throughout.

## 4. Expanded-domain total degree, not a sum of selected branches

Proper-support equilibria lie on the boundary of (0,1)⁴. It would be
invalid to reuse the strict packet's boundary-free open cube. Instead
extend the polynomial formula (2) to the whole ambient ℝ⁴ and consider

    Ω=(-1,2)⁴.

Its clipped output always belongs to [0,1]⁴⊂Ω. Hence every zero of
Id−F_λ belongs to the actual strategy cube and is an actual discounted
equilibrium. There are no zeros on ∂Ω. Homotoping F_λ to the
constant cube center keeps all images inside Ω, so

    deg(Id−F_λ,Ω,0)=1                                   (5)

for every 0<λ<1. Outside the strategy cube the extension has only a
topological role; it introduces no extra strategic fixed points.

Define on ℝ⁴

    H_λ(h)=D(λ,λh)/λ,
    f_λ(h)=min(h,−H_λ(h)).

Equation (4) shows uniform convergence on every bounded set to

    H₀(h)=a−Γh,        f_λ(h)→f_−a(h)=min(h,Γh−a).        (6)

Choose R>R₁ large enough also to contain every zero of f_−a in
V=(-R,R)⁴; Section 2 supplies such an R. Since f_−a has no boundary
zero, compactness gives a positive lower bound for ||f_−a|| on ∂V.

For small enough λ, every fixed point of F_λ lies in λV by
Section 3.1, and λ closure(V)⊂Ω. On the WHOLE λ closure(V),
including its negative coordinates, q+D(λ,q)=O(λ) uniformly,
so every coordinate is below 1. The upper clip
is therefore inactive there, though the lower clip remains essential.
Writing q=λh gives the exact identity

    q−F_λ(q)=q−max(0,q+D(λ,q))
             =min(q,−D(λ,q))=λ f_λ(h).                   (7)

Excision in (5), followed by the positive coordinate and output
dilations in (7), gives deg(f_λ,V,0)=1. Both dilations preserve
orientation; there is no factor from the number of inactive players.
Uniform convergence in (6) and the nonzero boundary margin preserve
degree for small λ. Thus

    1=deg(f_λ,V,0)=deg(f_−a,V,0)=κ(Γ),                   (8)

contrary to (T). This proves the theorem.

Combined with the full-matrix homogeneous dispatch just proved in
Section 3, it also proves the counterexample-facing form in Section 1.

Equation (8) retains the ENTIRE solution set of the actual LCP at −a.
It does not need each root isolated, each principal matrix invertible,
strict complementarity, finite support, or any selected analytic branch.
Zeros in a and merging proper-support roots do not change the argument.
The integer distinction between +1 and −1 is essential; mod-2 parity
alone gives no contradiction for the witness below.

## 5. Exact finite matrix criterion and a three-branch witness

### 5.1 A finite raw test sufficient for (T)

Fix the TEST vector â=(1,2,3,5). Suppose a zero-diagonal Γ satisfies:

1. Every column has a negative entry, and every principal submatrix of
   size at least two is nonsingular.
2. For each S with |S|≥2 compute
   h_S=Γ_SS⁻¹â_S and w_Sᶜ=Γ_Sᶜ,S h_S−â_Sᶜ.
   Whenever h_S>0 and w_Sᶜ≥0, in fact w_Sᶜ>0.
3. Sum sign det Γ_SS over those admissible S. The sum is not 1.

These are finitely many exact matrix equalities and inequalities. The
first item implies R0: a nonzero homogeneous solution supported on S
would have Γ_SS x_S=0. If |S|≥2 this violates nonsingularity; if
S={j}, its nonnegative full slack would contradict the negative entry
in column j. The empty homogeneous support is just zero.

At right-hand side −â, zero support is impossible and singleton
support is impossible because its active row would read 0=â_i>0.
Every remaining solution is exactly one of the computed h_S, with S
its positive support. Item 2 makes all actual solutions strictly
complementary, so Section 2.2 computes κ as the signed sum in item 3.

The fixed â is ONLY a finite device to compute κ. It is not declared
equal to the actual punishment-normalized a. Right-hand-side independence
in Section 2 is the proved bridge between them.

### 5.2 Complete exact support inventory

Take

    Γ=[ 0   7  −7  −1 ]
      [ 3   0  −9   9 ]
      [ 1  −1   0   7 ]
      [−1   5   3   0 ].                                 (9)

All entries displayed below are exact. Vector entries are ordered by S
and its increasing complement, respectively.

| S | det Γ_SS | h_S | w_Sᶜ |
| --- | ---: | --- | --- |
| 01 | −21 | (2/3,1/7) | (−52/21,−104/21) |
| 02 | 7 | (3,−1/7) | (58/7,−59/7) |
| 03 | −1 | (−5,−1) | (−26,−15) |
| 12 | −9 | (−3,−2/9) | (−184/9,−62/3) |
| 13 | −45 | (1,2/9) | (52/9,−22/9) |
| 23 | −21 | (5/3,3/7) | (−275/21,−92/7) |
| 012 | −42 | (92/21,29/21,26/21) | (26/21) |
| 013 | −78 | (−10/3,1/3,4/3) | (8/3) |
| 023 | 46 | (−275/46,−15/46,59/46) | (−251/46) |
| 123 | −342 | (46/57,55/171,31/57) | (317/171) |
| 0123 | 249 | (634/249,251/249,208/249,52/249) | () |

Thus precisely S=012,123,0123 are admissible. Their local indices
are −1,−1,+1, so κ=−1. Each column has a negative entry: use rows
3,2,0,0 for columns 0,1,2,3. Every listed determinant is nonzero,
which proves R0 including the singleton-support cases.

The full determinant is +249. Its inverse is

    Γ⁻¹=(1/249)[−342  389 −549  369]
               [ −27   46  −63   75]
               [ −69   53  −78   81]
               [  45  −49  105  −42].                    (10)

It has both signs and is outside the previous inverse-nonnegative,
negative-determinant theorem in TWO separate ways. Each strict test
in this inventory persists on a sufficiently small zero-diagonal
neighborhood, so this is not an isolated numerical coincidence.

Here is a reproducible exact check of the complete support inventory
and its three selected branches; no floating-point test is used in
the certificate.

```python
import itertools
import sympy as S
G=S.Matrix([[0,7,-7,-1],[3,0,-9,9],[1,-1,0,7],[-1,5,3,0]])
a=S.Matrix([1,2,3,5]); ids=list(range(4)); selected=[]
expected={
 (0,1):(-21,[S.Rational(2,3),S.Rational(1,7)]),
 (0,2):(7,[3,S.Rational(-1,7)]), (0,3):(-1,[-5,-1]),
 (1,2):(-9,[-3,S.Rational(-2,9)]),
 (1,3):(-45,[1,S.Rational(2,9)]),
 (2,3):(-21,[S.Rational(5,3),S.Rational(3,7)]),
 (0,1,2):(-42,[S.Rational(92,21),S.Rational(29,21),S.Rational(26,21)]),
 (0,1,3):(-78,[S.Rational(-10,3),S.Rational(1,3),S.Rational(4,3)]),
 (0,2,3):(46,[S.Rational(-275,46),S.Rational(-15,46),S.Rational(59,46)]),
 (1,2,3):(-342,[S.Rational(46,57),S.Rational(55,171),S.Rational(31,57)]),
 (0,1,2,3):(249,[S.Rational(634,249),S.Rational(251,249),
                 S.Rational(208,249),S.Rational(52,249)])}
expected_outside={
 (0,1):[S.Rational(-52,21),S.Rational(-104,21)],
 (0,2):[S.Rational(58,7),S.Rational(-59,7)],
 (0,3):[-26,-15], (1,2):[S.Rational(-184,9),S.Rational(-62,3)],
 (1,3):[S.Rational(52,9),S.Rational(-22,9)],
 (2,3):[S.Rational(-275,21),S.Rational(-92,7)],
 (0,1,2):[S.Rational(26,21)], (0,1,3):[S.Rational(8,3)],
 (0,2,3):[S.Rational(-251,46)], (1,2,3):[S.Rational(317,171)],
 (0,1,2,3):[]}
for k in range(2,5):
 for support in itertools.combinations(ids,k):
  J=list(support); T=G.extract(J,J); v=T.inv()*a.extract(J,[0])
  determinant,expected_v=expected[support]
  assert T.det()==determinant!=0 and v==S.Matrix(expected_v)
  h=S.zeros(4,1)
  for i,x in zip(J,v): h[i]=x
  w=G*h-a; outside=[i for i in ids if i not in J]
  assert all(w[i]==0 for i in J)
  assert [w[i] for i in outside]==expected_outside[support]
  if all(x>0 for x in v) and all(w[i]>=0 for i in outside):
   assert all(w[i]>0 for i in outside)
   selected.append((support,S.sign(determinant)))
assert selected==[((0,1,2),-1),((1,2,3),-1),((0,1,2,3),1)]
assert sum(sign for _,sign in selected)==-1
assert all(any(G[i,j]<0 for i in ids) for j in ids)
assert G.inv()==S.Matrix([[-342,389,-549,369],[-27,46,-63,75],
                         [-69,53,-78,81],[45,-49,105,-42]])/249
assert not any(all(G[c[k],c[(k+1)%4]]<0 for k in ids)
               for c in itertools.permutations(ids))
```

### 5.3 Boundary tests: zero anchor coordinates and nonisolated roots

The same matrix (9) has the exact identity

    Γ(3,2,1,0)=(7,0,1,10).

Thus the nonnegative anchor a*=(7,0,1,10) has a zero coordinate,
and LCP(Γ,−a*) has the proper-support solution h*=(3,2,1,0)
with ALL slacks zero. Strict complementarity fails at the inactive
coordinate. This is a check of the allowed boundary regime, not a claim
that a* is the punishment anchor of any particular game completion.

R0 does not even require each inhomogeneous root set to be finite.
For the test right-hand side b=(0,1,1,1), every x=(t,0,0,0) with
0≤t≤1 has slack (0,1+3t,1+t,1−t) and is complementary.
These nonisolated zeros do not invalidate Section 2's boundedness or
Section 4's total-degree comparison. This arbitrary test b is not
asserted equal to a game's −a.

## 6. Bounded coverage and boundary warnings

The nonzero degree makes (9) standard Q by the existence property in
Section 2; it is R0 by the exact support argument. Thus it is not a
repackaging of the existing full homogeneous or non-Q producers.

The principal on {0,3} is [0,−1;−1,0]. For x≥0, its action is
nonnegative only at zero, so it has no homogeneous simplex solution.
Its action can never be ≥(1,1), so LCP at right-hand side (−1,−1)
has no solution. The standard-or-homogeneous dictionary makes this
principal non-projective-Q. Thus the full matrix is not projective Q-bar,
and the CURRENT unconditional principal-Q-bar Snell consumer does not
subsume it. The negative reciprocal sum of this pair also rules out
copositivity of that principal and of the full matrix.

The negative graph is 0→2, 0→3, 1→2, 2→1, 3→0. It has no negative
Hamiltonian cycle: 1 and 2 can only follow each other once either is
entered. Therefore neither the signed-four-cycle producer nor its
relabelings or positive diagonal rescalings contains this matrix. Every
row has a negative entry, so the full singleton normal core is retained.
The same sign graph precludes the paired raw-region singleton pattern:
that pattern has exactly one negative singleton gap per recipient, its
partner, while row 0 here has two. Positive playerwise affine changes
preserve those gap signs. This compares the named paired region, not
all conceivable paired equilibria.

The conclusions concern arbitrary nonsingleton completions of the
matrix cylinder r_i({j})=s_i+Γ_ij. They do not assert that each
completion lies outside every other reward-dependent sufficient class,
or that all existing singleton calendars fail. No worldwide priority
claim is made. The new source-level field is total scaled LCP degree,
not a missing finite-menu or chronological producer asserted by analogy.

Two substitutions would invalidate the proof:

- A finite collection of negative-index roots chosen from the equilibrium
  set says nothing without excluding all other roots and unbounded
  q/λ. Sections 3–4 retain the entire set instead.
- The degree domain (0,1)⁴ from the strict-inverse proof is invalid in
  the presence of proper-support roots. Equation (7) on the expanded
  cube, with the lower clip intact, is the exact repair.

If R0 is dropped, an unbounded rescaling can normalize to a genuine
homogeneous complementary vector. The present bounded-domain argument
then has no justification. Under no UE that branch already has a named
separate quitting consumer for the FULL matrix with same-table punishment
normality; it is not silently assumed absent for arbitrary matrices.

## 7. Direct recovery of the nonnegative-inverse class

**Corollary.** For an arbitrary signed Fin4 reward table,

    det Γ<0,               B=Γ⁻¹≥0 entrywise

implies an original uniform-equilibrium payoff, with the full semantics
of Section 1. Zero entries of B are allowed.

Assume no original UE. The theorem's counterexample-facing form first
gives R0 of the FULL Γ and κ(Γ)=1. Let 1 be the all-ones vector.
Every row of an invertible nonnegative matrix is nonzero, so

    h*=B1>0.

This solves LCP(Γ,−1), with zero slack. Conversely, any solution
(h,w) has Γh=1+w≥1 and therefore

    h=B(1+w)≥B1>0.

Complementarity forces w=0, whence h=h*. The solution is unique,
has full positive support, and near it the min-map selects Γh−1
in every coordinate. Its derivative is Γ, and its local integer
degree is sign det Γ=−1. R0 and right-hand-side independence give
κ(Γ)=−1, contradiction.

This proof needs neither an implicit-function theorem, strict positivity
of the inverse, raw reward approximation, nor closure of equilibrium
payoffs under varying tables. The all-ones test is only a computation
of κ, not a replacement for the actual punishment-normal anchor a.
It recovers the entire earlier nonnegative-inverse class; that recovery
is a shorter proof, not an enlargement of that particular class.

The no-UE-to-R0 step is essential. Consider the zero-diagonal matrix
with ones at (0,1),(1,2),(2,3),(3,0), and zeros elsewhere. Its determinant
is −1 and inverse is its transpose, hence nonnegative. Its LCP at −1
has unique root 1 of index −1. Nevertheless x=e₀ is a nonzero
homogeneous complementary vector because Γe₀=e₃. Thus uniqueness
at −1 does NOT prove R0. For a no-UE game this non-R0 case is already
excluded by the same-table homogeneous-normal consumer in Section 3;
κ is not defined for it by pretending otherwise.

With positive determinant this computation gives local degree +1,
not a contradiction. That is a limitation of this argument, not an
assertion that uniform equilibria fail for positive determinant.

## 8. Source correspondence

Named declarations inspected under their imports, paths relative to the
repository root:

- `IsR0Matrix`, `isR0Matrix_iff_not_singletonLCPFeasible`,
  `MathUE/LinearProgramming/CopositiveQ.lean`; and
  `exists_bound_sum_of_isR0Matrix`,
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`:
  the homogeneous convention and existing R0 boundedness result.
  `r0Margin_pos_iff_isR0Matrix` and `isR0Matrix_of_r0Margin_lt`,
  `MathUE/LinearProgramming/R0Margin.lean`, were inspected for neighboring
  openness/bounds; no new quantitative R0 margin is claimed here.
- `HasHomogeneousSimplexSolution`,
  `exists_negative_entry_in_column_of_noHomogeneous`,
  `isProjectiveQMatrix_iff_standard_or_homogeneous`,
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
  `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`, in the
  neighboring `CounterexampleNecessary.lean`: the exact current
  nonhomogeneous-Q residual, not an already-proved degree-one restriction.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  same-table normality. Its existential packet is unused.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`,
  `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`:
  the full-simplex residual/complementarity and support-normality
  consumer. It includes the vertex/no-harm branch and turns an actual
  R0 failure of the full matrix into original UE under the same source.
- `isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`,
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`,
  together with `quittingAuxiliaryReward`,
  `quittingRootFixedPoint_unshift` and
  `quittingPunishmentValue_le_auxiliaryEndpointTarget` in that file:
  the exact auxiliary translation and original-game endpoint route.
- `exists_analyticBellmanGerm_of_positiveCoordinateArc`,
  `exists_analyticBellmanGerm_of_powerCurve`, and
  `analyticBellmanGermOfPowerCurve_endpoint`,
  `UniformEquilibrium/VanishingDiscount/Bellman/Germ.lean`:
  the prescribed-endpoint complete-assignment constructors. The
  positive-coordinate/power normalization is supported by
  `MathUE/AnalyticCoordinateCurve.lean` and
  `MathUE/AnalyticPowerNormalization.lean`.
- `isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`,
  `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`:
  the actual behavioral consumer behind the signed sole-owner branch.
- `isStandardQ_iff_isStandardQMatrix`,
  `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`;
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`,
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`:
  the current unconditional matrix-consumer comparison.
- `SignedFourCycleSingletonData`,
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
  paired `RawRegion` and its exact singleton/quiet bounds in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`, with
  `cycle_isZeroRootNash_of_selected` in `PairedCycleEquilibrium.lean`:
  only the literal raw sign patterns are used for non-subsumption.
- `quittingBestReplyValue` and `quittingPunishmentValue`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer`,
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`:
  the complete-response supremum, independent-opponent infimum and
  exact inequality P_i≤s_i used in Section 3.
- `boxComplementarity_completeSimplex_card_odd`,
  `Research/Topology/BoxComplementarityCubicalSperner.lean`, and
  `boxComplementarityLocalCompleteSimplexParity_univ`,
  `Research/Topology/BoxComplementaritySpernerLocalCount.lean`:
  nearby parity declarations, not an integer-index replacement.

## 9. Mathematical status and narrow Lean handoff

The new ordinary theorem is the full original-game implication

    no Fin4 UE ⇒ full Γ is R0 and κ(Γ)=+1,

and hence the raw sufficient criterion (T). It uses named checked
semantic consumers together with classical analytic curve selection
and integer Brouwer degree. No claim is made that the new degree
restriction, full proof composition or exact matrix calculation is
already checked in Lean. The earlier R0 boundedness and homogeneous
dispatch are credited existing results, not new construction steps.

A faithful implementation needs the following finite-dimensional
integer-degree facts: homotopy invariance on one boundary-free domain,
excision, positive-dilation invariance, normalization for identity minus
a map into an interior cube, and local degree equal to the determinant
sign at an invertible linear root. The mod-2 APIs above cannot distinguish
the essential values +1 and −1. This packet does not propose or claim
a pre-existing general signed-degree implementation.

The strategic adapter must retain EVERY discounted fixed point, the
full Bellman-assignment lift at each proposed nonzero limit, the signed
sole-owner punishment branch, and R0's exclusion of unbounded q/λ.
The ambient cube Ω and the exact lower-clip identity (7) are required
for proper supports. Uniform boundary convergence transports total
degree even for degenerate or nonisolated actual LCP roots and for a
with zero coordinates. Regular support enumeration is needed only to
verify the concrete witness, not as a source premise.

The concrete additional matrix cylinder in Section 5 has three scaled
branches with total index −1, positive full determinant and a mixed-sign
inverse; Section 6 records the bounded named-class comparisons. Section 7
recovers the old inverse-nonnegative class directly, including its
separate homogeneous branch. No exact stationary equilibrium, finite
calendar bound, constructive decision procedure for general UE,
unrestricted player-count theorem or worldwide classification is claimed.
The remaining no-UE matrix class is R0 of integer degree +1; this packet
does not prove it empty.
