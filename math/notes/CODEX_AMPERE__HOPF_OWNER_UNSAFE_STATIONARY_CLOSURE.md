# The sharp owner-unsafe HOPF completion has a full-support stationary equilibrium

Author: `CODEX_AMPERE`

## Status

This note proves an ordinary-mathematics positive result, not checked in Lean.
It consumes the explicit owner-unsafe completion in
`CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS.md`, Section 7.  Although that
completion has positive spectator singleton reward, strict spectator joining
at `\{2\}`, no pure terminal-coalition equilibrium, a literal forced-pair
source, a globally maximal card-three HOPF ray, and unique all-Continue at the
limiting cap, it nevertheless has a full-support stationary exact terminal
Nash profile against every behavioral deviation.  Hence its global minimum
debt is zero.

The proof is a rational Poincare--Miranda certificate.  It is stable under
small perturbations, so it also gives a genuine open safe subchamber inside
the owner-unsafe completion region.  It does not prove that every
`J_(32)>0` completion has an equilibrium.

## Question

Does the sharp completion that survives the pure-singleton, pure-pair,
maximal-root, and limiting-root screens provide a positive-gap candidate?

The answer is no.  A stationary equilibrium lies in a small explicit rational
box.

## Sources inspected

- `notes/CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md`;
- `notes/CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS.md`;
- `quittingBehavioralBestResponse_eq_sup_pureTime` and the stationary
  best-response results under
  `UniformEquilibrium/Quitting/Stationary/`; and
- `quittingTerminalSemanticDebt_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` for comparison with the
  already-consumed pure chambers.

## 1. The completion and the one remaining real parameter

Use the Section 7 completion with

\[
d=\frac1{100},\qquad L=\frac25-d=\frac{39}{100}.
\]

For active player `i`, its Quit-minus-Continue membership gain at background
`T` is

\[
g_0(T)=\mathbf1_{1\in T}-2\mathbf1_{2\in T}
       +d\mathbf1_{3\in T},
\]

\[
g_1(T)=\mathbf1_{0\in T}-2\mathbf1_{2\in T},
\]

\[
g_2(T)=\frac25(\mathbf1_{0\in T}+\mathbf1_{1\in T})
       -L\mathbf1_{3\in T}.
\]

For player `3`, on nonempty active backgrounds,

\[
g_3(T)=-\mathbf1_{0\in T}-\mathbf1_{1\in T}
       +\mathbf1_{2\in T}.
\]

Its singleton reward is an arbitrary `s_3>0`.  Its passive reward on a
nonempty active coalition is

\[
r_3(T)=s_3+R\mathbf1_{0\in T}-(R+1)\mathbf1_{1\in T},
\tag{1}
\]

where the HOPF orbit defines

\[
R=\sum_{k\ge0}\frac{t_k}{P_{k+1}},
\qquad
P_{k+1}=\prod_{h\le k}(1-t_h)^2(1-z_h).
\tag{2}
\]

Only the bound

\[
\boxed{0<R\le\frac1{37}}
\tag{3}
\]

will be used.  Here is a direct proof from the HOPF estimates.  The orbit
satisfies

\[
t_k\le\frac54 b_k,\qquad b_{k+1}\le\frac12b_k,\qquad b_0=\frac1{100},
\]

and `0<z_k<t_k`.  Therefore

\[
\sum_k t_k\le\frac54\sum_kb_k\le\frac1{40}.
\tag{4}
\]

The absorption of root `(t_k,t_k,z_k)` is at most

\[
2t_k+z_k\le3t_k.
\]

The elementary product bound `prod(1-a_k) >= 1-sum a_k` gives

\[
P_{k+1}\ge1-3\sum_h t_h\ge\frac{37}{40}.
\]

Combining this with (4) proves (3).

## 2. The exact stationary indifference polynomials

Let

\[
x=(x_0,x_1,x_2,x_3)\in(0,1)^4
\]

be a stationary product hazard.  For player `i`, let

\[
s_i=\prod_{j\ne i}(1-x_j),\qquad h_i=1-s_i.
\]

Write `Q_i` for its payoff from Quit now and `N_i` for its payoff from Never
against the stationary opponents.  If `A_i` is the unconditional passive
absorbing contribution from nonempty opponent coalitions and `gbar_i` is the
expected membership gain, then

\[
Q_i=A_i+\bar g_i,qquad N_i=\frac{A_i}{h_i}.
\]

Consequently

\[
F_i(x):=h_i(Q_i-N_i)=h_i\bar g_i-s_iA_i. \tag{5}
\]

The completion data give the following four explicit polynomials:

\[
\begin{aligned}
F_0={}&h_0(x_1-2x_2+dx_3)
 -s_0(1-x_3)(-\tfrac12x_1+x_2),\\
F_1={}&h_1(x_0-2x_2)\\
&-s_1\left((1-x_3)(-\tfrac12x_0+x_2)
 +(d-1)x_0x_3(1-x_2)\right),\\
F_2={}&h_2(\tfrac25(x_0+x_1)-Lx_3)
 -s_2(1-x_3)(-\tfrac15(x_0+x_1)),\\
F_3={}&h_3(-x_0-x_1+x_2)
 -s_3^{\rm surv}\bigl(Rx_0-(R+1)x_1\bigr),
\end{aligned}
\tag{6}
\]

where

\[
s_3^{\rm surv}=(1-x_0)(1-x_1)(1-x_2),
\qquad h_3=1-s_3^{\rm surv}.
\]

The spectator singleton reward cancels from `F_3`.  Indeed, the empty
background contributes `s_3 s_3^{\rm surv}` to the expected membership gain,
while the passive nonempty contribution contains `s_3 h_3`; these produce equal
opposite terms in (5).  Thus (6) is valid for every real singleton level, in
particular every `s_3>0` used by the sharp completion.

## 3. A rational Poincare--Miranda box

Put

\[
\begin{aligned}
c={}&(363/2000,\ 4359/20000,\ 5549/50000,\ 583/1250),\\
q={}&(3/2000,\ 7/4000,\ 3/2000,\ 13/5000),
\end{aligned}
\tag{7}
\]

and let

\[
K=\prod_{j=0}^3[c_j-q_j,c_j+q_j].
\]

Every coordinate of `K` lies strictly between zero and one.  Let `F` be the
column vector in (6), and define `G=AF` with the rational matrix

\[
A=\begin{pmatrix}
-3111/10000&2273/10000&-3/250&-10311/10000\\
1021/1000&-10619/10000&451/10000&-10923/10000\\
-1725/10000&-5358/10000&54/10000&-5571/10000\\
591/1000&-6953/10000&-30444/10000&-17754/10000
\end{pmatrix}.
\tag{8}
\]

This matrix is invertible, since

\[
\det A=\frac{443076546006639}{156250000000000}>0. \tag{9}
\]

For completeness, the following is a rational interval certificate for the
four face signs.  Set `R_0=1/74`.  Direct substitution gives

\[
10^6G(c,R_0)\in
[-6,-5]\times[30,31]\times[5,6]\times[25,26].
\tag{10}
\]

On `K times [0,1/37]`, outward rational differentiation gives

\[
A D_xF\in
\begin{pmatrix}
[.976,1.024]&[-.028,.028]&[-.020,.020]&[-.004,.004]\\
[-.035,.035]&[.965,1.035]&[-.040,.040]&[-.014,.014]\\
[-.018,.018]&[-.015,.015]&[.984,1.017]&[-.005,.005]\\
[-.054,.054]&[-.058,.058]&[-.038,.038]&[.980,1.020]
\end{pmatrix}
\tag{11}
\]

and

\[
A\partial_RF\in
[-.024,-.019]\times[-.025,-.020]
\times[-.013,-.010]\times[-.041,-.033].
\tag{12}
\]

All decimal endpoints in (11)--(12) are terminating rationals, rounded
outward.  Equations (10)--(12) are obtained only by addition and
multiplication of the rational endpoints in (3), (6)--(8).  A coarser
mean-value calculation already gives, for every `R in [0,1/37]`,

\[
\begin{array}{c|cc}
j&G_j\text{ on }x_j=c_j-q_j&G_j\text{ on }x_j=c_j+q_j\\ \hline
0&\le-1/1000&\ge1/1000\\
1&\le-1/1000&\ge1/1000\\
2&\le-1/1000&\ge1/1000\\
3&\le-1/1000&\ge1/1000.
\end{array}
\tag{13}
\]

For example, using (10)--(12), the upper bounds on the four lower faces are
respectively at most

\[
-0.001055,\quad-0.001171,\quad-0.001228,\quad-0.001728,
\]

while the lower bounds on the upper faces are at least

\[
0.001044,\quad0.001232,\quad0.001239,\quad0.001779.
\]

These displayed decimals are again weaker terminating-rational bounds; the
strict `1/1000` signs in (13) are the only facts used.

Poincare--Miranda applied to `G` on `K` gives a point `x^star in K` with

\[
G(x^\star)=0.
\]

By (9),

\[
\boxed{F_i(x^\star)=0\quad(i=0,1,2,3).} \tag{14}
\]

For orientation only, at the actual orbit value
`R approximately 0.02503849`, numerical Newton iteration locates

\[
x^\star\approx
(0.18175143,\ 0.21818005,\ 0.11110740,\ 0.46679806),
\]

well inside the certified box.  The numerical value is not used in the
proof.

## 4. Full behavioral exactness

At `x^star`, every hazard is strictly positive.  Against stationary
opponents, opponent absorption therefore occurs almost surely.  Before
absorption, the public history is only a finite string of all-Continue
outcomes and the opponents' next actions are fresh independent stationary
draws.

For an arbitrary randomized, calendar-dependent, or history-dependent
behavioral strategy of player `i`, terminal payoff is consequently a convex
combination of exactly two values:

- `Q_i`, on histories where `i` chooses Quit at the absorbing date; and
- `N_i`, on histories where `i` Continues and a nonempty opponent coalition
  absorbs.

Both endpoints are attainable by Quit-now and Never.  Equation (14), together
with `h_i>0`, says `Q_i=N_i` for every player.  Thus every unilateral
behavioral deviation has the same payoff as the prescribed stationary
mixture.  The stationary profile `x^star` is an exact terminal Nash profile
against the unrestricted behavioral strategy class.

It follows that the sharp completion has a uniform-equilibrium payoff and

\[
\boxed{D_*=0}. \tag{15}
\]

## 5. Consequences and scope

The Section 7 construction is not a positive-gap candidate.  Its failure is
not visible to any of the pure-coalition screens: it has no pure equilibrium.
Nor is it visible in the limiting cap game, whose unique exact root is
all-Continue.  The missing equilibrium is a genuinely full-support stationary
one at a finite, nonzero scale.

The face margins in (13) are strict.  Therefore the same Poincare--Miranda
argument survives all sufficiently small perturbations of the finite reward
table.  This gives an open owner-unsafe safe chamber containing the sharp
completion.

A positive-gap HOPF completion must now evade three distinct mechanisms:

1. `J_(32)<=0`, which gives pure `\{2\}`;
2. the pure-pair and induced singleton-base safe chambers; and
3. the full-support stationary indifference zero certified here, including
   its open neighborhood.

The proof does not show that every arbitrary spectator completion lies in one
of these chambers.  A remaining candidate must force the stationary
Quit-versus-Never map away from zero while preserving the maximal-ray and
source constraints.  That is a stricter target than the sign split alone.
