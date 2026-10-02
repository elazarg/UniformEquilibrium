# Universal quitting-game potentials: shape and curvature exclusions

## Status and scope

This note contains ordinary mathematical proofs, not Lean-checked declarations. It does not prove the four-player uniform-equilibrium conjecture and does not construct a counterexample. No repository changes were made.

The result concerns the *entire* floor-free, absorption-relative robust edge relation, not a selected orbit or a face-restricted certificate. Its main conclusion is that a counterexample certificate must be nonquasiconvex and genuinely coupled. The final two results quantify the required coupling and negative curvature.

The repository sources inspected are pinned to `elazarg/UniformEquilibrium` commit `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`:

- `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`: `IsQuittingFloorFreeRobustEdge` and `quittingFloorFreeRobustChargedRelation`.
- `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`: `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`.
- `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`: `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`.
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`: the three-core elimination and resulting four-player full-normal-core restriction; its application is also explicit in `FourPlayerSingletonColumnBlockers.lean`.

The certificate characterization is used only under its stated normality and positive-singleton hypotheses. The matrix argument uses the ambient standard-Q property available for a hypothetical four-player counterexample. No unproved existence theorem from the literature is an input to the proofs below.

## 1. Definitions and orientation

Let the player set be `{1,...,n}`, with `n >= 2`. Write

\[
r^i=r(\{i\}),\qquad s_i=r_i(\{i\}),\qquad R_{ji}=r_j(\{i\})-s_j.
\]

Thus `R_i = r^i-s` is column `i`, and `R_ii=0`. Translating these coordinates is bookkeeping; it does **not** change the game's Never payoff.

Assume `|r_j(S)| <= M`, with `M >= 0`, and put

\[
K=[-M-2,M+2]^n,\qquad
C=\prod_j[s_j,M+1],\qquad W=2M+1.
\]

For a product root `q`, let `a(q)` be its absorption probability and `F(v,q)` its expected one-step payoff when continuation is `v`. A robust edge from `v` to `u` has

\[
|u_j-F_j(v,q)|\le \tau a(q),\qquad
\operatorname{regret}_j(v,q)\le\tau a(q),
\]

with both endpoints in `K`. Regret here is the ordinary one-stage Nash regret computed against continuation `v`, not against the displayed target `u`.

A potential satisfies, for **every** such edge,

\[
P(v)-P(u)\ge a(q). \tag{1}
\]

The direction matters: the source `v` is the continuation; the target `u` is the prefixed payoff. Throughout the quantitative results assume `0 < tau <= 1/4`.

A matrix `R` is standard Q when for every `q in R^n` there exist `z,w >= 0` such that

\[
w=q+Rz,\qquad z_iw_i=0\quad\text{for every }i. \tag{2}
\]

In particular, taking `q=-1` gives a nonzero nonnegative `z` with `Rz>0`. After normalization there is `z in Delta_{n-1}` with `Rz>=0`. The latter, weaker property alone suffices for the separability and mixed-curvature results.

## 2. Exact Nash probes imply a robust differential inequality

### Proposition 1

Let `P` be differentiable on a neighborhood of `C` and satisfy (1) on the full robust relation. For every `x in C` with `x_i=s_i`,

\[
\boxed{\nabla P(x)\cdot(x-r^i)\ge 1+\tau\|\nabla P(x)\|_1.} \tag{3}
\]

In particular the gradient does not vanish anywhere on the lower boundary of `C`.

### Proof

Fix `i,x` and let only player `i` quit, with probability `h>0`. Define

\[
\Delta_j=r_j(\{i,j\})-r_j(\{i\})\quad(j\ne i),
\]

\[
v_i^h=s_i,\qquad
v_j^h=x_j+\frac{h}{1-h}(\Delta_j)_+\quad(j\ne i).
\]

Player `i` is indifferent between Quit and Continue. For `j != i`, Continue minus Quit equals

\[
(1-h)(v_j^h-s_j)-h\Delta_j
=(1-h)(x_j-s_j)+h((\Delta_j)_+-\Delta_j)\ge0.
\]

The root is therefore **exactly Nash** against `v^h`. Its absorption is `h`, and its prescribed payoff is

\[
u^h=(1-h)v^h+hr^i.
\]

For any `e in [-1,1]^n`, `(v^h,q^h,u^h+tau h e)` is a robust edge for sufficiently small `h`. All coordinates remain in `K`: `x` lies strictly inside that outer box and the perturbations tend to zero.

Applying (1), dividing by `h`, and differentiating at `x` gives

\[
\nabla P(x)\cdot(x-r^i-\tau e)\ge1.
\]

Maximizing `nabla P(x) dot e` over the unit cube yields (3). The continuation adjustment appears in both endpoints and cancels at first order. No behavioral realization of `x` is used: the full floor-free relation permits these continuations. QED.

Because `||x-r^i||_infinity <= W`, (3) also gives

\[
\|\nabla P(x)\|_1\ge\frac1{W-\tau},\qquad
\nabla P(x)\cdot(x-r^i)\ge c,
\quad c:=\frac{W}{W-\tau}>0. \tag{4}
\]

## 3. Standard Q excludes every differentiable quasiconvex potential

Recall that `f` is quasiconvex on a convex set if

\[
f((1-t)x+ty)\le\max\{f(x),f(y)\}\quad(0\le t\le1).
\]

The differentiable first-order consequence used below is

\[
f(v)\le f(x)\ \Longrightarrow\ \nabla f(x)\cdot(v-x)\le0. \tag{5}
\]

### Theorem 2: analytic form

Let `R` be a zero-diagonal standard-Q matrix. Let `b_j>0` and `R_ji<b_j` for every `j,i`, and set `D=prod_j[0,b_j]`. There is no differentiable quasiconvex `f` on a neighborhood of `D` satisfying

\[
\nabla f(x)\cdot(x-R_i)>0
\quad\text{whenever }x\in D,\ x_i=0. \tag{6}
\]

### Proof

Let

\[
B=\{x\in D:\min_i x_i=0\},
\]

and choose `x` minimizing `f` on the compact set `B`. Write `J={j:x_j=0}` and `g=nabla f(x)`.

**The minimum is at an intersection of at least two lower faces.** If `J={i}`, then for `j != i`, coordinate variations on `B` give `g_j=0` at interior coordinates and `g_j<=0` at upper coordinates `x_j=b_j`. Since `b_j-R_ji>0` and the own-coordinate term is zero,

\[
g\cdot(x-R_i)\le0,
\]

contradicting (6).

Hence `|J|>=2`. Every permitted one-coordinate variation now stays on `B`, giving

\[
g_j\ge0\ (x_j=0),\qquad
g_j=0\ (0<x_j<b_j),\qquad
g_j\le0\ (x_j=b_j). \tag{7}
\]

Consequently `g dot(v-x)>=0` for every `v in D`; it is strictly positive for every strict interior `v`, since (6) implies `g != 0`.

**Quasiconvexity makes this a minimum on the entire box.** Suppose `f(v)<f(x)` somewhere in `D`. By continuity, move `v` slightly into the strict interior while preserving that inequality. Formula (5) then gives `g dot(v-x)<=0`, contradicting the strict version of (7). Thus `f(x)<=f(v)` throughout `D`.

**Use Q-solvability to force a different boundary point.** Fix `k in J` and, for `t>0`, set

\[
q_t=(1-t)x+tR_k.
\]

Solve (2) at `q_t` and projectivize the solution:

\[
a_{0,t}=\frac1{1+\sum_i z_{t,i}},\qquad
a_{i,t}=\frac{z_{t,i}}{1+\sum_i z_{t,i}},\qquad
y_t=\frac{w_t}{1+\sum_i z_{t,i}}.
\]

Then

\[
y_t=a_{0,t}q_t+\sum_i a_{i,t}R_i,\quad
 a_{0,t}+\sum_i a_{i,t}=1,\quad
 a_{i,t}y_{t,i}=0. \tag{8}
\]

We have `y_t>=0`, and every term in the convex combination is coordinatewise at most `b`; hence `y_t in D`.

Some `i notin J` must satisfy `a_i,t>0`. Otherwise, by (6) at `x`,

\[
g\cdot(y_t-x)
=a_{0,t}t\,g\cdot(R_k-x)
 +\sum_{i\in J}a_{i,t}\,g\cdot(R_i-x)<0,
\]

contradicting (7). Here `a_0,t>0` and `t>0` ensure strictness even when all `a_i,t` vanish.

Take `t` to zero along a subsequence with a fixed such outside index `i`, and with `(y_t,a_t)` convergent. Its limit satisfies

\[
y=a_0x+\sum_i a_iR_i,\qquad a_i y_i=0,\qquad y\in D. \tag{9}
\]

It also satisfies `y_i=0<x_i`, so `y!=x`; therefore `sum_i a_i>0`.

At `y`, each positive `a_i` permits (6). Since `x` is a global minimum on `D`, (5) gives `nabla f(y) dot(y-x)>=0`. Taking the scalar product of (9) with `nabla f(y)` now gives the contradiction

\[
0=a_0\nabla f(y)\cdot(y-x)
 +\sum_i a_i\nabla f(y)\cdot(y-R_i)>0.
\]

QED.

### Corollary 3: application to the quitting certificate

Translate `x` by `s`, take `b_j=M+1-s_j`, and apply Proposition 1. These `b_j` are positive and satisfy `R_ji<=b_j-1`. If the singleton matrix is standard Q, no potential for the full robust relation is quasiconvex on `C`.

In particular there are `x,y in C` and `0<t<1` such that

\[
\boxed{P((1-t)x+ty)>\max\{P(x),P(y)\}.} \tag{10}
\]

This excludes every affine or convex polynomial certificate. It also excludes strictly increasing transforms of quasiconvex functions. It does **not** exclude arbitrary nonquasiconvex polynomials.

### Exact edges and rational witnesses

The quasiconvex exclusion does not require positive tolerance. Using `e=0` in the proof of Proposition 1 shows that unit-charge drift on all **exact** Nash–Bellman edges already forces face drift at least one. Theorem 2 rules this out.

More explicitly, Theorem 2 implies that a differentiable quasiconvex candidate has some lower-face point with `nabla P(x) dot(x-r^i) <= 0`. For rational rewards, a rational polynomial `P`, and rational `M`, continuity and density supply a rational point on the same face with drift less than `1/2`. The exact one-quitter probe has

\[
\frac{P(v^h)-P(u^h)}h\longrightarrow
\nabla P(x)\cdot(x-r^i)<\frac12.
\]

Thus sufficiently small positive rational `h` gives a fully rational exact Nash–Bellman edge with `P(v^h)-P(u^h)<3h/4`, violating the proposed unit-charge inequality by more than `h/4`. No approximate strategic implementation or limiting edge is needed for this witness.

## 4. Separability is impossible, even without Q

### Theorem 4

Assume only that `R` has a nonnegative simplex vector `z` with `Rz>=0`. A function satisfying (6) cannot be additively separable:

\[
f(x)=c_0+\sum_j f_j(x_j).
\]

### Proof

Choose `a_j` minimizing `f_j` on `[0,b_j]`. Its derivative is nonnegative at a lower endpoint, zero at an interior minimum, and nonpositive at an upper endpoint. Put

\[
\lambda_j=\begin{cases}f'_j(a_j),&a_j=0,\\0,&a_j>0.\end{cases}
\]

Then `lambda>=0`. For each `i`, let `x^(i)` equal `a` except that its `i`th coordinate is zero. Separability leaves all the other derivative coordinates unchanged. Lower-endpoint contributions are `-lambda_j R_ji`; interior contributions vanish; upper-endpoint contributions are nonpositive since `b_j-R_ji>0`. The own-coordinate contribution is zero. Thus

\[
0<\nabla f(x^{(i)})\cdot(x^{(i)}-R_i)
\le-\lambda^T R_i
\quad\text{for every }i.
\]

Multiply by `z_i` and sum. This gives `0< -lambda^T Rz<=0`, a contradiction. QED.

### Corollary 5: scalar transforms do not repair separability

A C1 function of the form

\[
f(x)=F\left(c_0+\sum_j f_j(x_j)\right)
\]

also cannot satisfy (6), even without assuming that `F` is globally monotone.

Indeed, the gradient cannot vanish on `B`. Hence `F'` is nonzero on the image of `B`. The lower boundary `B` is connected, so `F'` has a constant sign there. Multiplying the separable inner function by that sign produces a separable function with strictly positive face drift, contradicting Theorem 4.

## 5. An obligatory mixed-curvature budget

Return to the original box `C`, and assume `P` is C2. Let `a` minimize `P` on `C`. Set

\[
\lambda_j=\begin{cases}\partial_jP(a),&a_j=s_j,\\0,&a_j>s_j.\end{cases}
\]

Constrained first-order conditions give `lambda>=0`. For each `i`, let `a^(i,t)` be `a` with coordinate `i` replaced by `t`, and set `x^(i)=a^(i,s_i)`.

For `j != i`, the fundamental theorem of calculus gives

\[
\partial_jP(x^{(i)})=\partial_jP(a)
-\int_{s_i}^{a_i}\partial_{ij}P(a^{(i,t)})\,dt.
\]

As in the separable proof, the terms involving `nabla P(a)` contribute at most `-lambda^T R_i`. Therefore

\[
\nabla P(x^{(i)})\cdot(x^{(i)}-r^i)
\le-\lambda^T R_i
-\sum_{j\ne i}(a_j-r_j^i)
\int_{s_i}^{a_i}\partial_{ij}P(a^{(i,t)})\,dt.
\]

Take any `z in Delta` with `Rz>=0`. Formula (4) yields the signed necessary inequality

\[
\boxed{
-\sum_i z_i\sum_{j\ne i}(a_j-r_j^i)
\int_{s_i}^{a_i}\partial_{ij}P(a^{(i,t)})\,dt
\ge c.} \tag{11}
\]

Since both the integration lengths and the absolute payoff factors are at most `W`,

\[
\boxed{
\max_{x\in C,\ i\ne j}|\partial_{ij}P(x)|
\ge\frac{c}{(n-1)W^2}.} \tag{12}
\]

For four players the denominator is `3W^2`. The unit coefficient of absorption in (1) fixes the scale of this bound.

## 6. Quantitative negative curvature

Assume now that `R` is standard Q. Define

\[
A=\frac14\max_i\sum_{j\ne i}(R_{ji})_+^2.
\]

This is positive: Q-solvability at `q=-1` requires positive matrix entries.

Let

\[
\delta=\max\left\{0,-\min_{x\in C}
\lambda_{\min}(\nabla^2P(x))\right\}.
\]

Then `Q(x)=P(x)+(delta/2)||x-s||_2^2` is convex on `C`. On the face `x_i=s_i`, write `y=x-s`. Its additional drift is

\[
\delta\sum_{j\ne i}y_j(y_j-R_{ji})\ge-\delta A,
\]

because `y_j>=0` and `y_j(y_j-R_ji)>=-(R_ji)_+^2/4`.

If `delta A<c`, then `Q` has strictly positive face drift by (4), contradicting Theorem 2. Consequently

\[
\boxed{
\min_{x\in C}\lambda_{\min}(\nabla^2P(x))
\le-\frac{c}{A}.} \tag{13}
\]

The simpler estimate `A <= (n-1)M^2` gives, when `M>0`,

\[
\min_{x\in C}\lambda_{\min}(\nabla^2P(x))
\le-\frac{c}{(n-1)M^2}.
\]

This is a lower bound on required negative curvature, not an upper bound on certificate degree or coefficients.

## 7. What this establishes for Fin4

Under a hypothetical four-player counterexample, the inspected matrix restrictions give an ambient standard-Q singleton matrix. In the normal positive-singleton setting, the inspected polynomial characterization supplies a robust polynomial certificate. Every such certificate must therefore:

1. violate quasiconvexity already on the inner box `C`;
2. fail every additively separable, or scalar-transform-of-separable, representation;
3. satisfy the signed mixed-curvature budget (11) and the negative-curvature bound (13).

These are universal restrictions on the certificate, derived from exact roots in the full relation. They are not conditions on a conveniently selected orbit.

The remaining issue is not hidden: a genuinely coupled, nonquasiconvex polynomial with sufficiently large mixed and negative curvature is not excluded by these arguments. No such polynomial is constructed here, and no argument shows that all such polynomials fail. Thus this note does not settle Fin4, produce a new unrestricted strategy family, or replace the universal certificate test by its first-order necessary conditions.
