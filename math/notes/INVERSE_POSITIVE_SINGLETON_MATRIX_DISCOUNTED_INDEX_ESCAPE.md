# Inverse-positive singleton matrices and discounted-index escape

Core proof: CODEX_FRECHET_CYCLE. The nonnegative-inverse approximation
and reward-closedness argument is due to CODEX_NOETHER_SUPPORT, independently
checked by CODEX_TARSKI_PREMIUM; its complete proof is included below.

Independent mathematical reviews of the original proof:
[CODEX_NOETHER_SUPPORT](../feedback/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE__BY_CODEX_NOETHER_SUPPORT.md)
and
[CODEX_TARSKI_PREMIUM](../feedback/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE__BY_CODEX_TARSKI_PREMIUM.md).
Boundary-extension source:
[nonnegative-inverse approximation](../notes/CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES.md),
with [independent review](../feedback/CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES__BY_CODEX_TARSKI_PREMIUM.md).

## 1. Statement, strategy space, and class change

Let I={0,1,2,3}. For each nonempty S⊆I, a quitting game has an arbitrary
real reward vector r(S). Before the first nonempty Quit set, the stage
payoff is zero. That set becomes an absorbing state with constant payoff
r(S); infinite all-Continue has payoff zero. Players use independent
private behavioral randomization. A deviation may replace one player's
entire behavioral strategy, with no finite-memory or stopping-date bound.

Write

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i.                   (1)

Rows are payoff recipients and columns are quitters. Thus Γ_ii=0. Matrix
inequalities below are entrywise.

**Theorem.** If

    det Γ<0,                B=Γ⁻¹≥0,                       (2)

then the original game has a fixed ordinary uniform-equilibrium payoff v.
Explicitly, for every ε>0 there are one actual behavioral profile σ and
one integer T₀ such that, for every T≥T₀, all prescribed T-stage expected
average payoffs are within ε of v, and no unilateral complete behavioral
deviation increases its T-stage expected average payoff by more than ε.

Own singletons may have either sign. The four own-singleton levels and
all 44 nonsingleton reward coordinates are unrestricted. This is a
raw-table sufficient theorem, not a verifier for supplied roots or laws.
Its new mechanism localizes the ENTIRE small-discount equilibrium set
under the contrary no-UE assumption, then contradicts integer fixed-point
degree. The nonnegative-inverse boundary follows by a literal singleton-
reward approximation and full-regret closedness. The proof requires
neither an actual cap minimizer nor a temporal interpretation of a
horizontal best response.

Section 7 gives an exact matrix outside the existing full non-Q,
homogeneous, projective-Q-bar, and relabeled signed-four-cycle routes.
This is a bounded comparison of named matrix hypotheses, not a claim that
every completion is outside every other sufficient class. In particular,
longer repeated-owner singleton calendars are not excluded by that test.

The conclusion is ordinary mathematics using the classical analytic
curve-selection, implicit-function, and integer Brouwer-degree theorems,
together with the named original-game semantic consumers in Section 9.
It is not asserted to be an already-checked Lean composition.

## 2. Contrary source and the exact auxiliary table

First assume the stronger hypothesis B>0. Sections 2–6 prove this strict
core; Section 8 removes strictness without asserting the localization of
the unperturbed boundary table's discounted equilibria.

Suppose the original game has no uniform-equilibrium payoff. The
same-table Fin4 reduction
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
supplies all-player punishment normality

    P_i≤s_i,                                               (3)

Here P_i is the infimum over independent opponent behavioral plans of
the supremum of i's expected terminal payoff over all its complete
behavioral responses. Only this normality field is used. The reduction's
separately selected singleton packet is not used to make any statement
about every discounted equilibrium.

Set

    c_i=min(0,P_i),    r'_i(S)=r_i(S)−c_i,    a_i=s_i−c_i.

This is precisely the zero-live punishment-normalized auxiliary game in
`quittingAuxiliaryReward`. Its singleton difference matrix remains Γ.
Equation (3) gives a≥0. If a=0, then every s_i=c_i≤0. Against all Never,
every unilateral finite Quit obtains only s_i≤0, while Never obtains
zero. All Never is therefore an exact original equilibrium, including
every finite-horizon payoff comparison. Thus the contrary branch has

    a≥0,                         a≠0.                      (4)

The translation is NOT strategic equivalence for a terminal game with
Never fixed at zero. Return to the original game will use the exact
punishment-completed auxiliary-germ consumer, including its sole-active-
owner branch. No sign condition is imposed on the original s.

We will repeatedly use the elementary cone implication

    μ≥0, μ≠0, Γμ≥0  ⇒  μ=B(Γμ)>0.                        (5)

Indeed Γμ≠0 by invertibility, and a strictly positive matrix sends every
nonzero nonnegative vector to a vector with every coordinate positive.

## 3. The complete discounted Bellman map

Fix 0<λ<1 and write d=1−λ. A stationary strategy at the live state is
a product hazard vector q∈[0,1]⁴. For T⊆I\{i}, define the opponent law

    π_i(T;q)=∏_(j∈T)q_j ∏_(j∉T∪{i})(1−q_j).

Define

    α_i(q)=∏_(j≠i)(1−q_j),        C(q)=∏_j(1−q_j),
    A_i(q)=Σ_(∅≠T⊆I\{i}) π_i(T;q) r'_i(T),
    Q_i(q)=Σ_(T⊆I\{i}) π_i(T;q) r'_i(T∪{i}),
    R_i(q)=q_i Q_i(q)+(1−q_i)A_i(q),
    L(λ,q)=1−d C(q)=λ+d(1−C(q)),
    u_i(λ,q)=d R_i(q)/L(λ,q),
    D_i(λ,q)=(1−d α_i(q))Q_i(q)−A_i(q).                  (6)

Here u is the actual normalized discounted live value: the live stage
pays zero, and the successor state is either live again or absorbing.
Consequently u=d[R+C u]. The denominator L is strictly positive, even
at all Continue.

The two pure live Bellman endpoints are dQ_i and d(A_i+α_i u_i).
Direct expansion using C=(1−q_i)α_i gives the exact identity

    L(Q_i−A_i−α_i u_i)=D_i.                               (7)

In particular, the final term of D_i is −A_i, not −d A_i.
The full Bellman equilibrium conditions are therefore exactly

    q_i=0 ⇒ D_i≤0,
    0<q_i<1 ⇒ D_i=0,
    q_i=1 ⇒ D_i≥0.                                       (8)

They retain upper faces, intersections of faces, and indifferent pure
actions. Equivalently, q is a fixed point of the continuous cube map

    F_λ(q)_i=clip_[0,1](q_i+D_i(λ,q)).                    (9)

Brouwer supplies at least one fixed point for every λ. Conversely each
fixed point, with its value from (6), is a stationary discounted Bellman
equilibrium. Against stationary opponents the deviator faces a finite-
state discounted control problem; the Bellman inequalities bound all
adaptive behavioral deviations, not only stationary changes or dates in
a chosen finite timing menu. One can also verify this directly by
iterating the Bellman upper bound along any response and letting the
bounded discounted continuation remainder tend to zero.

For later compactness, fix M'≥0 bounding all entries of this auxiliary
table. The one-step absorbing contribution satisfies
|R_i(q)|≤M'(1−C(q)), so

    |u_i(λ,q)|≤M' d(1−C(q))/(λ+d(1−C(q)))≤M'.             (10)

This bound is uniform over λ and q for the fixed table. No denominator
bounded away from zero, or bound uniform over varying reward tables, is
assumed.

## 4. Every discounted equilibrium approaches all Continue

Under the contrary no-UE assumption, every sequence λ_n→0 with
0<λ_n<1 and F_(λ_n)(q_n)=q_n satisfies q_n→0.

Suppose not. By compactness and (10), pass to a subsequence with
q_n→q_*≠0 and u(λ_n,q_n)→u_*. The graph of triples (λ,q,u)
defined by

    0<λ<1,  q∈[0,1]⁴,  L>0,  L u=d R,
    and all sign conditions (8)

is semialgebraic with real coefficients. Arbitrary real rewards and
punishment constants are allowed coefficients. The specified point
(0,q_*,u_*) is in its closure and outside it.

Analytic semialgebraic curve selection yields an analytic arc through
THIS point whose positive branch lies in the graph. The precise classical
input is Coste, *Real Algebraic Sets*, Section 1.5, Theorem 1.15
([primary text](https://indico.ictp.it/event/a02455/session/2/contribution/2/material/0/0.pdf)).
It selects an endpoint-preserving arc; it does not replace the sequence
by an unrelated equilibrium germ.

### 4.1 Full Bellman-assignment lift

The auxiliary quitting game has the live state and the 15 absorbing
coalition states. Lift every point of the selected arc as follows:

- At the live state, assign Quit probability q_i, Continue probability
  1−q_i, and value u_i.
- At every absorbing state S, assign constant pure Continue actions and
  value r'_i(S) for each player i.
- Assign the discount-complement coordinate the arc's λ.

All these coordinates are jointly analytic. At an absorbing state, every
action has the same transition and reward, so the Bellman equation is
r'_i(S)=λr'_i(S)+d r'_i(S) and every action inequality is equality.
At the live state, the Bellman equation and inequalities are exactly
(6)–(8). Hence the lifted arc lies in the FULL polynomial Bellman
solution set, not merely a root projection. Its endpoint retains q_* and
u_*, and its discount coordinate is strictly positive on the punctured
right interval.

Write the analytic discount coordinate as ℓ(t)=t^k b(t), where k≥1
and b(0)>0. Such k exists because ℓ is positive on the right and
ℓ(0)=0. The analytic map t↦t b(t)^(1/k) has positive derivative at
zero, so an analytic local inverse reparametrizes the entire assignment
with discount complement exactly t^k. The endpoint is unchanged. This is
the input of `exists_analyticBellmanGerm_of_positiveCoordinateArc`, or
equivalently `exists_analyticBellmanGerm_of_powerCurve`, with the stated
endpoint equality supplied by `analyticBellmanGermOfPowerCurve_endpoint`.

### 4.2 Original-game consumer, including signed sole owners

Since q_*≠0, its joint Continue mass is less than one. The exact theorem
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint` therefore
returns an original-game uniform-equilibrium payoff, namely the endpoint
live value translated back by c. It is generic in the finite player type;
its `ThreePlayer/` directory does not restrict its domain to three players.

For clarity, its semantic composition is substantive. The endpoint
recursion and endpoint Nash inequalities translate to a one-phase root
at the original reward table. The auxiliary endpoint target is at least
each original punishment value. Each player either has contracting
deleted-opponent survival, or all its opponents Continue surely. In the
latter case joint absorption forces that player to be the sole active
owner, the fixed-point equation pins its original target to s_i, and the
punishment floor supplies the noncontracting branch of
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`.

That consumer uses actual punishment-completed profiles and yields the
fixed target with unrestricted behavioral deviations in Section 1.
It does not identify a signed sole-quitter stationary law with an exact
original equilibrium; the owner's Never response is not omitted.
The resulting original UE contradicts the contrary assumption. Thus the
claimed convergence q_n→0 holds for EVERY fixed-point sequence.

## 5. Uniform first-order localization of the entire fixed-point set

For any such sequence write t_n=Σ_i q_(n,i). At q=0,
D_i(λ,0)=λa_i. Equation (4) therefore rules out all Continue as a fixed
point at every positive discount, so t_n>0. Pass to a subsequence with

    μ_n=q_n/t_n→μ∈Δ(I),
    ρ_n=λ_n/(λ_n+t_n)→ρ∈[0,1],
    u(λ_n,q_n)→u_*.

The first-order singleton contributions and product survival expansion are

    R(q_n)=t_n(a+Γμ_n)+O(t_n²),
    1−C(q_n)=t_n+O(t_n²).

The remainders are uniform on the simplex for this fixed reward table.
Dividing by λ_n+t_n is safe even when t_n/λ_n is unbounded:
t_n²/(λ_n+t_n)≤t_n and λ_n t_n/(λ_n+t_n)≤t_n. Therefore

    u_*=(1−ρ)(a+Γμ).                                      (11)

For large n every q_(n,i)<1, so Continue is used and optimal. Thus
u_(n,i)=d_n(A_i+α_i u_(n,i))≥d_n Q_i, giving u_*≥a.
If μ_i>0 then q_(n,i)>0 eventually as well. That coordinate mixes both
actions, so u_(n,i)=d_n Q_i and u_*i=a_i.

If ρ=1, (11) and u_*≥a force a=0, contrary to (4). Otherwise

    Γμ≥[ρ/(1−ρ)]a≥0.

The cone implication (5) gives μ>0, so every coordinate pins and u_*=a.
It follows that

    (1−ρ)Γμ=ρa.

The case ρ=0 would give Γμ=0, impossible. Hence

    0<ρ<1,      μ(1−ρ)/ρ=Ba=:h_*>0.                       (12)

Consequently, uniformly over the whole fixed-point set as λ→0,

    q/λ→h_*.                                              (13)

To see the uniform quantifier, a failure would supply a sequence of
fixed points whose rescaled hazards stay outside a fixed neighborhood of
h_*, or are unbounded. Compactness of (μ_n,ρ_n,u_n), followed by (12),
contradicts either failure. No common analytic branch or uniform Puiseux
order is used. In particular, divergent rescaled hazards and zero leading
shares are excluded on every boundary support stratum.

## 6. The integer-degree contradiction

Since D is polynomial, substitution makes

    H(λ,h)=D(λ,λh)/λ

analytic across λ=0: D(0,0)=0, so every substituted monomial is
divisible by λ. Direct expansion of (6) gives

    H(0,h)=a−Γh,        ∂_h H(0,h_*)=−Γ.                  (14)

Indeed 1−dα_i=λ+Σ_(j≠i)q_j+O((|λ|+Σ|q_j|)²),
Q_i=a_i+O(Σ|q_j|), and
A_i=Σ_(j≠i)q_j(a_i+Γ_ij)+O((Σ|q_j|)²).
Thus every nonsingleton contribution cancels from the first-order map.

The implicit function theorem supplies a unique zero h(λ) near h_* for
sufficiently small |λ|. Since h_*>0, the associated q(λ)=λh(λ) is
strictly inside the cube when λ>0 is small. Uniform localization (13)
puts EVERY cube fixed point there. By (8) those interior fixed points
are zeros of D, so local uniqueness becomes global uniqueness. There
are no boundary fixed points.

Let F=F_λ at such a small positive λ and U=(0,1)⁴. The integer Brouwer
degree of Id−F on U at zero is +1. Indeed homotope F to the constant
cube center by F_t=(1−t)F+t(1/2,1/2,1/2,1/2). For t>0 its image is
strictly interior; at t=0 there is no boundary fixed point. Therefore
the displacement has no boundary zero during the homotopy. Homotopy
invariance and normalization give degree +1.

Near the sole fixed point clipping is inactive, so Id−F=−D. Differentiating
D(λ,λh)=λH(λ,h) in h gives

    ∂_q D(λ,λh(λ))=∂_h H(λ,h(λ))→−Γ.

The fixed point is nondegenerate for small λ, and its local degree is

    sign det(−∂_q D)=sign det Γ=−1.                        (15)

Excision and additivity equate the global degree to this sole local
degree, contradicting +1. This proves the strict-inverse case.

The displacement convention and signs are explicit: the limiting
Jacobian is Γ, not an imported index formula for a finite normal-form
game. Only continuity of clipping globally and smoothness near the fixed
point are needed. A primary exposition of normalization, local index,
and degree is
[Govindan, *The Index of Nash Equilibria*, slides 9–16](https://eventos.cmm.uchile.cl/dgames2017/wp-content/uploads/sites/40/2017/01/Govindan_Chile.pdf).
The cube homotopy above supplies the needed global identity directly.

## 7. Boundary tests and bounded comparison

### 7.1 An inhabited signed singleton cylinder

The matrix

    Γ=[ 0   2   1  −3 ]
      [−3   0   2   3 ]
      [−3   2   0   2 ]
      [ 3  −3  −1   0 ]

has determinant −3 and inverse

    B=[6  4/3  7  26/3]
      [5    1  6     7]
      [3    1  3     4]
      [4    1  5     6].                                 (16)

Thus the class is nonempty: choose any s∈ℝ⁴, set r_i({j})=s_i+Γ_ij,
and choose all nonsingleton rewards arbitrarily. Zero coordinates of a
cause no difficulty; for example a=(0,2,0,3) gives
Ba=(86/3,23,14,20)>0.

### 7.2 Matrix-only localization is false

For an exact algebraic test of the discounted map, complete (16) by

    r'_i(S)=a_i+Σ_(j∈S)Γ_ij  for every nonempty S.

Direct calculation then gives

    D_i=α_i[λa_i−(1−λ)(Γq)_i].                            (17)

With a=(1,0,0,0) and λ=1/101, the small interior equilibrium is
q=λ/(1−λ)Ba=(3/50,1/20,3/100,1/25). But every q with at least
two sure quitters also has α_i=0 for every i and D=0. In particular,
all sure is a remote discounted equilibrium at every discount and an
exact terminal equilibrium for this completion: each player's membership
toggle changes reward by Γ_ii=0 and other players already stop surely.

This does not challenge the theorem. It falsifies the stronger statement
that the matrix assumptions alone localize every discounted equilibrium.
The contrary no-UE assumption and the absorbing-endpoint consumer are
essential in Section 4; selecting just the small branch cannot replace
them.

### 7.3 Positive determinant is a boundary of this argument

The paired matrix

    Γ⁺=[ 0  3 −1 −1]
       [ 3  0 −1 −1]
       [−1 −1  0  3]
       [−1 −1  3  0]

has determinant 45. Its inverse has diagonal 2/15, within-pair entries
7/15, and cross-pair entries 1/5, all positive. The local displacement
degree would be +1, so the contradiction in (15) disappears. This is
not a counterexample to UE without the determinant hypothesis; it is a
precise limitation of the present index argument.

These arithmetic tests are reproducible without numerical selection:

```python
import sympy as S
G=S.Matrix([[0,2,1,-3],[-3,0,2,3],[-3,2,0,2],[3,-3,-1,0]])
B=S.Matrix([[6,S.Rational(4,3),7,S.Rational(26,3)],
            [5,1,6,7],[3,1,3,4],[4,1,5,6]])
assert G.det()==-3 and G*B==S.eye(4) and all(x>0 for x in B)
assert B*S.Matrix([0,2,0,3])==S.Matrix([S.Rational(86,3),23,14,20])
q=B*S.Matrix([1,0,0,0])/100
assert q==S.Matrix([S.Rational(3,50),S.Rational(1,20),
                    S.Rational(3,100),S.Rational(1,25)])
P=S.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
assert P.det()==45 and all(x>0 for x in P.inv())
```

### 7.4 Which existing matrix consumers are not sufficient here

For any B>0, B is strictly copositive, hence standard Q. Standard Q
transfers to Γ=B⁻¹: for any right-hand side z, solve the B-LCP with
right-hand side −Bz, variable w, and slack x=B(w−z). Then x,w≥0,
x_iw_i=0, and w=z+Γx, solving the Γ-LCP. There is no nonzero
homogeneous complementary vector for Γ: if x≥0 and w=Γx≥0 are
complementary and x≠0, invertibility gives w≠0, while x=Bw>0 forces
w=0. Thus neither the full non-Q nor the homogeneous-singleton consumer
contains this strict-inverse subclass.

Full standard Q does not imply projective Q on every principal. For
(16), the principal on {0,1,3} is

    T=[0 2 −3; −3 0 3; 3 −3 0].

If x≥0 and Tx≥0, its inequalities imply x₁≥3x₂/2, x₂≥x₀, and
x₀≥x₁, forcing x=0. Thus no homogeneous simplex solution exists;
Tx≥(1,1,1) is also impossible, so the standard LCP at right-hand
side (−1,−1,−1) has no solution. The standard-or-homogeneous dictionary
then shows that T is not projective Q. Hence Γ is not projective Q-bar
and the current unconditional projective-Q-bar Snell consumer does not
subsume this example. Every row of (16) also has a negative off-diagonal
entry, so the full set survives singleton normal-core deletion.

The signed-four-cycle producer, including its inverse-positive special
case and relabelings, requires a negative Hamiltonian successor cycle
with positive reverse edges. Matrix (16) has no negative Hamiltonian
cycle: 0 must go to 3; from 3 the next vertex is 1 or 2; either then
must go back to 0 before visiting the fourth vertex. This excludes that
named once-per-owner cycle hypothesis. It does NOT exclude longer words:
the negative graph has the covering closed walk 0,3,1,0,3,2,0.

These comparisons concern the exact named sufficient hypotheses. Some
completions can satisfy other reward-dependent criteria, and no exclusion
of their union, or worldwide priority claim, is made.

### 7.5 Zero inverse entries and the second-order boundary

The four-cycle permutation matrix

    Γ⁰=[0 1 0 0; 0 0 1 0; 0 0 0 1; 1 0 0 0]

has zero diagonal, determinant −1, and a nonnegative inverse with zeros.
For K=J−I and ε=1/20, the inverse of Γ⁰−εK is

    (1/129523)[  7240   7580    780 136780 ]
              [136780   7240   7580    780 ]
              [   780 136780   7240   7580 ]
              [  7580    780 136780   7240 ].

It is strictly positive and the determinant remains negative. Writing
B⁰=(Γ⁰)⁻¹, both B⁰ and B⁰KB⁰ vanish at (0,2), (1,3), (2,0), (3,1).
Thus the first-order inverse correction alone need not give strict
positivity; the second-order term used below is necessary for this test.

```python
import sympy as S
G0=S.Matrix([[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,0,0]])
K=S.ones(4)-S.eye(4)
B0=G0.inv()
C=S.Matrix([[7240,7580,780,136780],[136780,7240,7580,780],
            [780,136780,7240,7580],[7580,780,136780,7240]])/129523
Ge=G0-K/20
assert G0.det()==-1 and Ge.det()<0 and Ge*C==S.eye(4)
assert all(x>=0 for x in B0) and all(x>0 for x in C)
for i,j in [(0,2),(1,3),(2,0),(3,1)]:
    assert B0[i,j]==0 and (B0*K*B0)[i,j]==0
assert all(x>0 for x in B0+B0*K*B0+B0*K*B0*K*B0)
```

The dimension hypothesis of the approximation lemma is genuine. In
dimension two an invertible zero-diagonal matrix is [0 a; b 0], whose
inverse always has zero diagonal. Consequently no zero-diagonal-preserving
perturbation there can have a strictly positive inverse. This is not a
negative claim about two-player equilibrium existence.

## 8. Nonnegative-inverse boundary and actual reward closedness

### 8.1 Zero-diagonal-preserving strict approximation

More generally, let Γ be an invertible n-by-n matrix with B=Γ⁻¹≥0 and
n≥3. Put K=J−I, with J the all-ones matrix, and Γ_ε=Γ−εK.
For every sufficiently small ε>0 its inverse is strictly positive,
its diagonal is unchanged, and its determinant has the same sign as Γ.

To prove this, take ε||BK||∞<1 in the maximum row-sum matrix norm.
The geometric series is absolutely convergent, and multiplication by
I−εBK telescopes to the identity. Hence

    Γ_ε=Γ(I−εBK),
    Γ_ε⁻¹=B+εBKB+ε²BKBKB+⋯.                             (18)

Every coefficient is nonnegative. Fix i,j. If B_ij>0 the constant
term suffices; if (BKB)_ij>0 the first-order term suffices. Otherwise

    0=(BKB)_ij=Σ_(k≠l)B_ik B_lj.

Invertibility makes row i and column j nonzero. Their nonnegative
supports must therefore both be the same singleton {k}, with B_ik>0
and B_kj>0. There are u,v≠k with B_uv>0: if not, every row outside
k would be supported only in column k. Since n≥3 there are at least
two such rows, contradicting invertibility. The term

    B_ik K_ku B_uv K_vk B_kj>0

occurs in (BKBKB)_ij. Thus the second-order coefficient handles all
remaining entries, proving strict positivity in (18).

The diagonal stays fixed because K_ii=0. The same norm bound proves
invertibility throughout 0≤t≤ε, so continuity of the determinant keeps
its sign. This proves the approximation lemma without irreducibility
or a positive-diagonal assumption on B.

Apply it to the Fin4 matrix in (2) by changing precisely the twelve
off-own singleton rewards:

    r^ε_i({j})=r_i({j})−ε  when i≠j,
    r^ε_i({i})=r_i({i}),
    r^ε_i(S)=r_i(S)  when |S|≥2.

Never is still zero, the reward sup-norm distance is ε, and the new
matrix is Γ_ε. The strict core gives an ordinary UE for each sufficiently
small ε>0. This uses its unconditional raw-table theorem: punishment
values, normality, equilibrium laws, and targets need not be preserved
as ε changes.

### 8.2 The full-cap reward perturbation bound

For any actual behavioral profile p, define its terminal payoff U_i^r(p),
its full response cap

    cap_i^r(p)=sup_(τ_i) U_i^r(p[i←τ_i]),

and its full terminal regret E_r(p)=max_i(cap_i^r(p)−U_i^r(p)).
The supremum is over all complete behavioral replacements, including
Never; it need not be attained. All terms are finite since rewards are
bounded, and E≥0 since τ_i may be the prescribed strategy.

If two reward tables on this same quitting structure have distance at
most δ, every prescribed or deviated profile has the SAME first-stopping
outcome law at both tables. Actions, observations, transitions, and the
independent strategy space are unchanged. Integration of the payoff
difference therefore gives, for every p,i,τ_i,

    |U_i^r(p)−U_i^(r')(p)|≤δ,
    |U_i^r(p[i←τ_i])−U_i^(r')(p[i←τ_i])|≤δ.

The difference at Never is zero. Taking the complete response supremum
and then the finite player maximum yields

    |cap_i^r(p)−cap_i^(r')(p)|≤δ,
    |E_r(p)−E_(r')(p)|≤2δ.                               (19)

This is a full-cap estimate, not just a prescribed-payoff or bounded-menu
comparison. In stopping-law coordinates it retains every finite deadline,
simultaneous union, and Never; the same integration proof already treats
all behavioral deviations directly.

For any desired error η>0, choose ε<η/4 for which the approximation is
valid. The UE of r^ε supplies an actual terminal η/2-Nash profile p by
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`.
The very same laws then satisfy E_r(p)<η by (19). Thus r has actual
terminal approximate Nash profiles at every positive error.

The exact target-free consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
selects one fixed uniform-equilibrium payoff for r. Its proof uses compact
terminal payoff vectors, terminal-to-uniform approximation and fixed-profile
Cesaro convergence; targets of the perturbed games need not have been
chosen jointly. This proves (2) with B≥0 and completes the theorem.

## 9. Exact source correspondence and semantic adapter

Paths in this section are relative to the repository root. The following
named declarations were inspected under their imports.

- `normalizedSoloMatrix_eq_soloReward_sub`,
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`:
  the matrix convention in (1), with no transpose or hidden scaling.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  the same-table all-player punishment-normality field used in (3).
- `quittingBestReplyValue` and `quittingPunishmentValue`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer`,
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`:
  the independent-opponent/full-behavioral-response min-max definition
  and its exact comparison to the own singleton.
- `quittingAuxiliaryLive`, `quittingAuxiliaryReward`,
  `quittingRootFixedPoint_unshift`,
  `quittingPunishmentValue_le_auxiliaryEndpointTarget`, and
  `isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`,
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`:
  the exact auxiliary table and original-game absorbing-endpoint consumer.
- `isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`,
  `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`:
  actual punishment-completed play against full behavioral deviations,
  including noncontracting deleted-clock owners.
- `exists_analyticBellmanGerm_of_positiveCoordinateArc`,
  `exists_analyticBellmanGerm_of_powerCurve`, and
  `analyticBellmanGermOfPowerCurve_endpoint`,
  `UniformEquilibrium/VanishingDiscount/Bellman/Germ.lean`;
  prescribed-endpoint sign-cell interfaces in the neighboring
  `CurveGate.lean`; and
  `HasPositiveCoordinateAnalyticArcAt.toHasAnalyticPowerCurveAt`,
  `MathUE/AnalyticCoordinateCurve.lean`:
  constructors matching the complete arc in Section 4.
- `IsUniformEquilibriumPayoff`,
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`:
  exactly the fixed-target/all-large-horizon quantifiers of Section 1.
- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`,
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  the two exact unrestricted semantic directions used for reward
  closedness. No convergence of prescribed equilibrium laws is required.
- `isStandardQ_of_strictlyCopositive`,
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`, and
  `isStandardQ_iff_isStandardQMatrix`,
  `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`;
  `isProjectiveQMatrix_iff_standard_or_homogeneous` and
  `IsProjectiveQBarMatrix`, in the neighboring `MatrixClasses.lean`;
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`,
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`:
  the bounded matrix comparison, not premises of the index contradiction.
- `SignedFourCycleSingletonData`,
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`:
  the negative successor and positive predecessor fields used in the
  once-per-owner non-subsumption test.

The existing SOME-germ theorem
`nonempty_analyticBellmanGerm_quittingGame` and the separately reselecting
full-support singleton-packet theorems do not provide Section 4 or (13).
The proof supplies those universal quantifiers itself. Solan's
[*Three-player absorbing games*](https://doi.org/10.1287/moor.24.3.669)
motivated looking at singleton exits of discounted limits; its
three-dimensional geometric alternative is not an input to this proof.

## 10. Lean handoff and scope

The new mathematical tasks for formalization are the literal polynomial
map (6)–(9), the all-equilibrium localization/rate argument, and the
oriented local/global degree contradiction. The nonnegative-inverse
extension additionally needs the matrix series/second-order positivity
lemma (18), same-law full-regret transport (19), and the existing
terminal-all-errors consumer. Existing auxiliary and punishment-completed
consumers should be reused without replacing their
full behavioral endpoint by stationary Bellman assertions.

Prescribed-endpoint analytic curve selection is a classical input used
on a finite real-polynomial graph. The current germ constructors accept
the resulting complete assignment. A formalization must connect that
specific closure point to its arc; unconditional existence of an
unrelated germ is insufficient. The value bound (10) and the absorbed
coordinates in Section 4.1 provide the required compactness and lift.

The degree input is genuinely INTEGER-valued. The inspected
`boxComplementarity_completeSimplex_card_odd` in
`Research/Topology/BoxComplementarityCubicalSperner.lean` gives an odd
complete-simplex count, and
`boxComplementarityLocalCompleteSimplexParity_univ` in
`Research/Topology/BoxComplementaritySpernerLocalCount.lean` is explicitly
valued in `ZMod 2`. Those parity APIs identify −1 with +1 and cannot
discharge (15). One needs integer-degree normalization, boundary-safe
homotopy invariance, excision/additivity, and the local determinant-sign
formula, or a proved equivalent signed-index interface. No existing
integer-degree Lean composition is asserted here.

The theorem does not claim a stationary exact equilibrium, an effective
finite-calendar selector, a uniform discount threshold over arbitrary
nonsingleton completions, or the general Fin4 conjecture. The strict core
uses entrywise positivity in (5); nonnegative inverses are handled by
actual reward approximation, not by asserting that (5) holds with zeros.
Positive determinant remains outside this argument. No unconditional
arbitrary-player-count statement is made.
