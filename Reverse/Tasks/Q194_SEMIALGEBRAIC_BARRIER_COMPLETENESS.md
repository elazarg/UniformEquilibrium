# Question 194: Semialgebraic completeness of positive-debt barriers

## Quitting-game semantic dynamics

Let \(I\) be a finite nonempty player set. A rational quitting table assigns
a vector \(r(S)\in\mathbb Q^I\) to every nonempty quitting coalition
\(S\subseteq I\). Perpetual continuation pays \(0\).

A semantic state is a pair \(z=(u,b)\in\mathbb R^I\times\mathbb R^I\), where
\(u\) is a prescribed terminal payoff and \(b\) is the vector of unilateral
best-response payoffs. Put

\[
d_i(z)=b_i-u_i,
\qquad
D(z)=\sum_{i\in I}d_i(z).
\]

For a product mixed action \(x\), write \(q_i\) for player \(i\)'s Quit
probability, \(c_i=1-q_i\), and

\[
p^x_{-i}(A)=
\prod_{j\in A}q_j
\prod_{j\in I\setminus(A\cup\{i\})}c_j
\qquad(A\subseteq I\setminus\{i\}).
\]

For a continuation scalar \(v_i\), define

\[
\begin{aligned}
Q_i(x_{-i})
  &=\sum_{A\subseteq I\setminus\{i\}}
      p^x_{-i}(A)r_i(A\cup\{i\}),\\
C_i(x_{-i};v_i)
  &=p^x_{-i}(\varnothing)v_i+
    \sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
      p^x_{-i}(A)r_i(A),\\
F_i(x;v_i)&=q_iQ_i(x_{-i})+c_iC_i(x_{-i};v_i).
\end{aligned}
\]

The one-stage prefix map \(T_x(u,b)=(u',b')\) is

\[
u'_i=F_i(x;u_i),
\qquad
b'_i=\max\{Q_i(x_{-i}),C_i(x_{-i};b_i)\}.
\]

Let \(e_\infty\) be the semantic state of perpetual continuation and let

\[
\mathcal K=
\overline{\{T_we_\infty:
  w\text{ is a finite word, including the empty word}\}}.
\]

The global debt floor is

\[
D_*:=\min_{z\in\mathcal K}D(z).
\]

## Positive barriers

For \(\delta>0\), a positive-debt barrier is a set
\(\mathcal B\subseteq\mathbb R^I\times\mathbb R^I\) such that

\[
e_\infty\in\mathcal B,
\qquad
T_x(\mathcal B)\subseteq\mathcal B\quad\text{for every }x,
\qquad
D(z)\ge\delta\quad\text{for every }z\in\mathcal B.
\tag{1}
\]

An unrestricted barrier exists exactly when \(D_*>0\): in the nontrivial
direction one may take \(\mathcal B=\mathcal K\) and any
\(0<\delta\le D_*\). This does not give a finite description of the barrier.

A **rational semialgebraic barrier** is a barrier described by a finite
Boolean combination of polynomial weak and strict inequalities in the
coordinates of \((u,b)\), with rational coefficients.

## Question

For every rational quitting table satisfying \(D_*>0\), does there exist a
rational semialgebraic positive-debt barrier?

Equivalently, is the rational semialgebraic barrier language complete for
certifying positive global semantic debt floors?

## Why this is separate from the equilibrium question

An affirmative answer would turn barrier synthesis into a complete
semidecision procedure for positive-gap rational tables: enumerate rational
semialgebraic candidates and verify (1). Without such a theorem, finding a
barrier is still a valid certificate, but failure of any fixed template
search has no game-theoretic consequence.

The question does not obstruct a proof of universal equilibrium existence,
which may instead rule out the positive-gap configuration. Nor does it
obstruct an ad hoc counterexample construction with an explicitly chosen
barrier.

## Known restrictions

Two coarse languages are not complete:

1. coordinatewise order-rectangular sets, which independently recombine
   attained prescribed-payoff and best-response coordinates, necessarily
   contain a zero-debt diagonal point;
2. debt-saturated sets, whose membership depends only on \(b-u\), admit
   calibrated prefix contractions below every proposed positive floor.

Hence any successful language must couple absolute prescribed-payoff and
best-response levels. These restrictions do not decide whether general
rational semialgebraic barriers are complete.

## Acceptance criteria

An affirmative answer must construct, from an arbitrary rational table with
\(D_*>0\), a finite rational semialgebraic description of a set
\(\mathcal B\) and a rational \(\delta>0\) satisfying (1). A non-effective
existence argument with \(\mathcal B=\mathcal K\) does not suffice.

A negative answer must give a rational quitting table with \(D_*>0\) and
prove that no rational semialgebraic set satisfies (1). Refuting one bounded
degree, one number of inequalities, or one template family is useful pruning
but is not a negative answer.

Either answer must distinguish finite certificate complexity from the
unrestricted barrier characterization.

# Answer

## Verdict

The completeness question remains unresolved. We have neither a construction
of a rational semialgebraic barrier from the sole hypothesis \(D_*>0\), nor a
rational positive-gap table for which every rational semialgebraic barrier is
impossible.

There is now an exact structural reduction. It supplies a normalized barrier
language and a conditional finite-horizon certificate, but it does not prove
that the finite condition ever occurs.

## 1. A positive invariant tube

Every prefix map is nonexpansive in the coordinatewise sup metric on semantic
pairs. Consequently, if a state is within \(\varepsilon\) of the forward-
invariant carrier \(\mathcal K\), then every one-stage prefix remains within
\(\varepsilon\) of \(\mathcal K\).

Moreover, total debt is \(2|I|\)-Lipschitz in that metric. Thus the
\(\varepsilon\)-tube around \(\mathcal K\) has debt at least

\[
D_*-2|I|\varepsilon.
\]

In particular, \(2|I|\varepsilon<D_*\) gives a positive-radius invariant
neighborhood with a positive debt floor. This is a metric statement, not a
finite semialgebraic description of the neighborhood.

## 2. The debt-safe hull

For \(A\subseteq\mathbb R^I\times\mathbb R^I\), put
\((u,b)\in\mathsf H(A)\) when there are points
\(z^k=(u^k,b^k)\in A\) and weights \(\lambda_k\ge0\), with
\(\sum_k\lambda_k=1\), such that

\[
u_i\le\sum_k\lambda_k u_i^k,
\qquad
b_i^k\le b_i
\quad\text{for every }i,k.
\tag{2}
\]

This hull lowers prescribed payoffs, raises best-response payoffs, and
convexifies only the prescribed-payoff coordinates. It has the following
exact properties:

1. \(A\subseteq\mathsf H(A)\), it is monotone in \(A\), and
   \(\mathsf H(\mathsf H(A))=\mathsf H(A)\);
2. every debt floor on \(A\) is preserved on \(\mathsf H(A)\);
3. every witness can be compressed to at most \(|I|+1\) points;
4. for every product mixed action \(x\),
   \[
   T_x(\mathsf H(A))\subseteq\mathsf H(T_x(A)).
   \tag{3}
   \]

The third item is Carathéodory compression in the prescribed-payoff
coordinates. The fourth uses the common nonnegative affine coefficient in all
prescribed-payoff coordinates and the coordinatewise monotonicity of the
max-affine best-response update.

## 3. Conditional finite stabilization

For \(N\ge0\), let

\[
R_N=\{T_we_\infty: |w|\le N\}.
\]

Suppose \(D_*>0\) and, for some \(N\),

\[
R_{N+1}\subseteq\mathsf H(R_N).
\tag{4}
\]

Then \(\mathsf H(R_N)\) is a positive-debt barrier. Indeed,

\[
\begin{aligned}
T_x(\mathsf H(R_N))
&\subseteq\mathsf H(T_x(R_N))\\
&\subseteq\mathsf H(R_{N+1})\\
&\subseteq\mathsf H(\mathsf H(R_N))
=\mathsf H(R_N),
\end{aligned}
\]

and the carrier floor on \(R_N\) is preserved by the hull.

This is a genuine finite-stabilization consumer. It is not an eventual-
stabilization theorem.

## 4. The remaining bridge

The unresolved implication is

\[
D_*>0
\quad\Longrightarrow\quad
\text{some finitely described rational semialgebraic post-fixpoint exists}.
\tag{5}
\]

Condition (4) is one concrete candidate. Two further steps would be needed to
turn it into the requested completeness result:

1. establish the rational semialgebraic and effective representation of the
   finite reachable sets and the debt-safe hull certificate;
2. prove that positive debt forces (4), or replace (4) by a more expressive
   finite construction that is forced by \(D_*>0\).

The first is a representation/effectivity problem. The second is the genuine
completeness problem. Nonexpansiveness alone does not prove it: an
all-Continue prefix can preserve coordinates exactly, so approximate finite
stabilization need not become exact stabilization.

Failure of (4) for every \(N\) would not be a negative answer; a different
semialgebraic barrier could still exist.

## Follow-up: weighted contraction and the remaining finite bridge

The follow-up yields one genuine structural improvement, but it does not establish barrier completeness.

Let
\[
\alpha(x)=\prod_j c_j,\qquad
\beta_i(x)=\prod_{j\ne i}c_j,\qquad
\ell(x)=\max_i\beta_i(x).
\]
The coordinate formulas give the sharper one-step estimate
\[
 \lVert T_xz-T_x\widetilde z\rVert_\infty
 \le \ell(x)\lVert z-\widetilde z\rVert_\infty.
\tag{2}
\]
Thus a word \(w=(x_1,\ldots,x_m)\) contracts by
\(\Lambda(w)=\prod_{t=1}^m\ell(x_t)\). This weighted estimate is now
formalized independently of the discussion below.

### A normalized Lipschitz safety margin

Fix a rational \(0<\delta<D_*\), and let
\[
 \vartheta(t)=\min\{1,\max\{0,t\}\}.
\]
Use the convention
\[
 T_{v\cdot x}=T_v\circ T_x,
 \qquad
 \Lambda(v\cdot x)=\Lambda(v)\ell(x).
\]
For \(\Lambda(w)>0\), set
\[
 h_w(z)=\vartheta\!\left(\frac{D(T_wz)-\delta}{\Lambda(w)}\right).
\tag{3}
\]
When \(\Lambda(w)=0\), the map \(T_w\) is constant; define \(h_w\) to be
the corresponding constant indicator of \(D(T_wz)>\delta\). Include the
empty word, with \(T_\varnothing=\operatorname{id}\) and
\(\Lambda(\varnothing)=1\), and set
\[
 H(z)=\inf_{w\text{ finite}}h_w(z).
\tag{4}
\]

Because \(D\) is \(2|I|\)-Lipschitz and \(T_w\) is
\(\Lambda(w)\)-Lipschitz, every \(h_w\), and hence \(H\), is
\(2|I|\)-Lipschitz. Forward invariance of \(\mathcal K\) gives
\[
 H(z)\ge \min\{1,D_*-\delta\}>0\qquad(z\in\mathcal K),
\tag{5}
\]
whereas the empty word gives
\[
 D(z)\le\delta\quad\Longrightarrow\quad H(z)=0.
\tag{6}
\]

The clipping inequality
\[
 \vartheta(at)\ge a\,\vartheta(t)
 \qquad(0\le a\le1)
\tag{7}
\]
implies
\[
 H(T_xz)\ge\ell(x)H(z).
\tag{8}
\]
There are two boundary cases in this calculation. If
\(\Lambda(v)>0\), apply (7) to the word \(v\cdot x\). If
\(\Lambda(v)=0\), then \(v\) and \(v\cdot x\) define the same constant
word map, so
\[
 h_v(T_xz)=h_{v\cdot x}(z)
 \ge \ell(x)h_{v\cdot x}(z).
\]
If \(\ell(x)=0\), the map \(T_x\) itself is constant and its value lies
in \(\mathcal K\), so (5) applies directly.

Consequently \(\{H>0\}\) is an open forward-invariant positive-debt
barrier. This is a useful multiplicative Lyapunov description, but it
does not strengthen the bare barrier-existence conclusion: a
sufficiently small open tube around \(\mathcal K\) already supplies an
open Lipschitz positive-debt barrier. The new information is the
weighted law (8).

### Two sufficient bridges that remain open

Write
\[
 \rho(z)=\operatorname{dist}_\infty(z,\mathcal K).
\]
Equation (2) and forward invariance give
\[
 \rho(T_xz)\le\ell(x)\rho(z).
\tag{9}
\]
Choose a rational invariant box \(P=[-M,M]^{2|I|}\) containing
\(\mathcal K\); such an \(M\) follows from a common bound on the reward
coordinates.

One sufficient bridge would be the following relative approximation
statement: for every rational \(\eta>0\), find a rational semialgebraic
\(V_\eta:P\to\mathbb R\) such that
\[
 |V_\eta(z)-\rho(z)|\le\eta
\tag{10}
\]
and
\[
 V_\eta(T_xz)
 \le \ell(x)V_\eta(z)+(1-\ell(x))\eta.
\tag{11}
\]
Then a suitable rational sublevel set of \(V_\eta\) is forward
invariant and retains a positive debt floor. Ordinary uniform
approximation yields the weaker error
\((1+\ell(x))\eta\), which does not vanish on the near-neutral faces
\(\ell(x)=1\). Thus (11), not ordinary semialgebraic approximation, is
the missing assertion.

A second sufficient bridge would be a bounded-bad-word theorem. If
there were \(N\) such that every word carrying a point of \(P\) into
\(\{D\le\delta\}\) had a witness of length at most \(N\), then
\[
 \mathcal B_N=
 \left\{z\in P:
   D(T_wz)>\delta\ \text{for every word }w,\ |w|\le N
 \right\},
\tag{12}
\]
where the empty word is included, would be a rational semialgebraic
forward-invariant positive-debt barrier. The bounded-witness premise is
itself a global structural statement, not yet a finite certificate, and
does not currently follow from \(D_*>0\).

Therefore the weighted contraction and normalized safety margin are
real progress in the representation of the problem. They do not prove
that a finite rational semialgebraic barrier language is complete.
That completeness question remains open.

## Followup 2

The (\Lambda(v)=0) correction is necessary. With the convention that (xv) satisfies (T_{xv}=T_vT_x), the dynamic argument is:

* If (\ell(x)>0) and (\Lambda(v)>0), then
  [
  \begin{aligned}
  h_v(T_xz)
  &=
  \vartheta!\left(
  \ell(x)\frac{D(T_{xv}z)-\delta}
  {\ell(x)\Lambda(v)}
  \right)\
  &\ge \ell(x)h_{xv}(z)
  \ge \ell(x)H(z).
  \end{aligned}
  ]
* If (\Lambda(v)=0), then (T_v) is constant. Its constant value equals (T_vk) for any (k\in\mathcal K), hence belongs to (\mathcal K). Since (\delta<D_*), (h_v\equiv1), and therefore
  [
  h_v(T_xz)=1\ge \ell(x)H(z).
  ]
* If (\ell(x)=0), the desired inequality is immediate because (H\ge0).

Taking the infimum over (v) gives the corrected proof of

[
H(T_xz)\ge \ell(x)H(z).
\tag{2}
]

The next useful step is not another approximation of (H), but a different thickening of (\mathcal K) whose available slack is proportional to (1-\alpha(x)), not (1-\ell(x)).

## 1. Exact reduction to (n+1) state coordinates

Put

[
U=\sum_i u_i,\qquad
\alpha(x)=\prod_jc_j,\qquad
\beta_i(x)=\prod_{j\ne i}c_j.
]

Write

[
h_i(x)=
\sum_{\varnothing\ne A\subseteq I\setminus{i}}
p^x_{-i}(A)r_i(A),
]

so that

[
C_i(x_{-i};v_i)=\beta_i(x)v_i+h_i(x).
]

Define

[
g_i(x)=q_iQ_i(x_{-i})+c_i h_i(x),
\qquad
G(x)=\sum_i g_i(x).
]

Then the projection

[
\pi(u,b)=\left(\sum_i u_i,b\right)
]

semiconjugates the original system to

[
\overline T_x(U,b)
==================

\left(
\alpha(x)U+G(x),
\left(f_i^x(b_i)\right)_i
\right),
\tag{3}
]

where

[
f_i^x(t)
========

\max{Q_i(x_{-i}),\beta_i(x)t+h_i(x)}.
\tag{4}
]

Debt becomes

[
\overline D(U,b)=\sum_i b_i-U.
]

Thus

[
D_*=\min_{\overline{\mathcal K}}\overline D,
\qquad
\overline{\mathcal K}=\pi(\mathcal K).
]

Any rational semialgebraic barrier for the reduced system lifts under (\pi) to one for the original system. So the individual (u_i)'s are irrelevant to the certificate-completeness issue.

The scalar maps in (4) satisfy the one-sided estimate

[
\bigl(f_i^x(a)-f_i^x(b)\bigr)*+
\le
\beta_i(x)(a-b)*+.
\tag{5}
]

## 2. An invariant wedge with strict (1-\alpha) slack

Let (A\subseteq\mathbb R^{1+n}). Fix parameters

[
\gamma\ge1,\qquad r>0,\qquad c>\gamma r.
]

Define

[
\mathcal W_{\gamma,r,c}(A)
==========================

\left{
(U,b):
\begin{array}{l}
\exists,(V,a)\in A,[1mm]
p_i=(a_i-b_i)_+\le r\quad\forall i,[1mm]
U\le V+c-\gamma\sum_i p_i
\end{array}
\right}.
\tag{6}
]

The variables (p_i) measure only unfavorable (b)-errors: an increase of (b_i) is free.

### Wedge invariance

Assume (A) is forward invariant. Let ((V,a)\in A) witness ((U,b)\in\mathcal W_{\gamma,r,c}(A)), and put

[
(V',a')=\overline T_x(V,a).
]

By (5),

[
p_i':=(a_i'-f_i^x(b_i))_+
\le\beta_i p_i
\le r.
\tag{7}
]

Let the input wedge slack be

[
s=V+c-\gamma\sum_i p_i-U\ge0.
]

Since (U'=\alpha U+G) and (V'=\alpha V+G),

[
\begin{aligned}
V'+c-\gamma\sum_i p_i'-U'
&\ge
\alpha s
+(1-\alpha)c
-\gamma\sum_i(\beta_i-\alpha)p_i.
\end{aligned}
\tag{8}
]

The special identity is

[
\beta_i-\alpha=q_i\beta_i,
]

and hence

[
\sum_i(\beta_i-\alpha)
======================

\Pr_x(\text{exactly one player Quits})
\le1-\alpha.
\tag{9}
]

Using (p_i\le r) in (8) gives

[
V'+c-\gamma\sum_i p_i'-U'
\ge
\alpha s+(1-\alpha)(c-\gamma r).
\tag{10}
]

Therefore

[
\overline T_x
\bigl(\mathcal W_{\gamma,r,c}(A)\bigr)
\subseteq
\mathcal W_{\gamma,r,c}(A).
\tag{11}
]

The point of (10) is that the strict part is governed by (1-\alpha). Since

[
\alpha(x)=1
\iff
x\text{ is the all-Continue action},
]

every nonzero action creates positive wedge slack, including singleton actions for which (\ell(x)=1).

### Debt preservation

For the same witness,

[
\begin{aligned}
\overline D(U,b)-\overline D(V,a)
&=
\sum_i(b_i-a_i)-(U-V)\
&\ge
-c
+\sum_i(b_i-a_i)*+
+(\gamma-1)\sum_i(a_i-b_i)*+\
&\ge -c.
\end{aligned}
\tag{12}
]

Thus

[
\overline D\ge d_A\text{ on }A
\quad\Longrightarrow\quad
\overline D\ge d_A-c
\text{ on }\mathcal W_{\gamma,r,c}(A).
\tag{13}
]

Taking (A=\overline{\mathcal K}), rational parameters satisfying

[
0<c<D_*,
\qquad
0<r<\frac c\gamma,
\tag{14}
]

and rational (0<\delta<D_*-c), gives another unrestricted positive-debt barrier. Unlike the ordinary metric tube, however, it has the quantitative strictness (10).

If (A) is rational semialgebraic, then so is (\mathcal W_{\gamma,r,c}(A)), by existential quantification. So it remains to replace (\overline{\mathcal K}) by a rational semialgebraic approximate anchor set with errors paid out of (10).

## 3. The exact relative-anchor criterion

Suppose (A) is not invariant. Given (a=(V,a^b)\in A), (x), and a proposed successor anchor

[
a'=(V',a'^b)\in A,
]

define only the unfavorable discrepancies

[
\eta_0=
\bigl(\alpha V+G-V'\bigr)_+,
\tag{15}
]

and

[
\eta_i=
\bigl(a_i'^b-f_i^x(a_i^b)\bigr)_+.
\tag{16}
]

Thus lowering the proposed (U)-anchor or raising the proposed (b_i)-anchor costs error; errors in the debt-safe directions cost nothing.

Assume that for every (a\in A) and every (x), some (a'\in A) satisfies

[
\eta_i\le r(1-\beta_i)
\qquad\forall i,
\tag{17}
]

and

[
\eta_0+\gamma\sum_i\eta_i
\le
(c-\gamma r)(1-\alpha).
\tag{18}
]

Then (\mathcal W_{\gamma,r,c}(A)) is exactly invariant.

Indeed, if (p_i=(a_i-b_i)_+), then

[
p_i'
====

(a_i'^b-f_i^x(b_i))_+
\le
\beta_i p_i+\eta_i
\le r.
\tag{19}
]

Moreover,

[
U'
\le
V'+\eta_0+\alpha
\left(c-\gamma\sum_i p_i\right).
]

Consequently,

[
\begin{aligned}
V'+c-\gamma\sum_i p_i'-U'
&\ge
(1-\alpha)(c-\gamma r)
-\eta_0-\gamma\sum_i\eta_i\
&\ge0.
\end{aligned}
\tag{20}
]

This gives a genuine finite certificate scheme:

> If a rational semialgebraic (A) contains the initial anchor, has a rational debt lower bound (d_A>c), and satisfies (17)–(18), then
> [
> \mathcal B=\pi^{-1}\mathcal W_{\gamma,r,c}(A)
> ]
> is a rational semialgebraic positive-debt barrier, with any rational
> [
> 0<\delta<d_A-c.
> ]

All parts of the criterion are first-order over the reals.

This is stronger than asking for a Hausdorff approximation of (\mathcal K). The approximation error is required to scale with the exact coordinatewise contraction deficits.

## 4. The zero-tolerance locus is much smaller than it first appears

The tolerances in (17)–(18) vanish only in specific cases:

[
1-\alpha=0
\iff q_i=0\quad\forall i,
\tag{21}
]

and

[
1-\beta_i=0
\iff q_j=0\quad\forall j\ne i.
\tag{22}
]

Let

[
s_i=r_i({i}).
]

At the all-Continue action,

[
\overline T_0(U,b)
==================

P(U,b)
:=
\left(U,\left(\max{s_i,b_i}\right)_i\right).
\tag{23}
]

This is a rational semialgebraic idempotent.

On a singleton face where only player (i) may Quit, the coordinate with zero tolerance is precisely

[
b_i\longmapsto \max{s_i,b_i},
\tag{24}
]

independently of the value of (q_i). Thus zero error is not required for an arbitrary neutral evolution; it is required only for a fixed rational clamp.

For any rational semialgebraic (A_0), define

[
A_{\mathrm{clamp}}
==================

\bigcup_{J\subseteq I}P_J(A_0),
\tag{25}
]

where (P_J) clamps exactly the coordinates in (J). Then (A_{\mathrm{clamp}}) is rational semialgebraic, is closed under every individual clamp, and has no smaller debt floor than (A_0).

So the literal zero-tolerance part of (17) is finitely enforceable. The remaining issue is the first-order movement of (U) and of the contracting (b)-coordinates.

## 5. The controlling first-order system

On the fixed face of (P),

[
b_i\ge s_i\qquad\forall i,
]

write

[
q_i=t\lambda_i,\qquad
\lambda\in\Delta(I),\qquad
t\downarrow0.
]

Let

[
R^k=\sum_m r_m({k}).
]

Then

[
\alpha=1-t+O(t^2)
]

and

[
U'
==

U+t\sum_k\lambda_k(R^k-U)+O(t^2).
\tag{26}
]

For (b_i>s_i), the Continue branch is locally active and

[
b_i'
====

b_i+
t\sum_{j\ne i}
\lambda_j\bigl(r_i({j})-b_i\bigr)
+O(t^2).
\tag{27}
]

At (b_i=s_i), the two branches meet, giving

[
\begin{aligned}
b_i'
====

s_i+t\max\Bigg{
&
\sum_{j\ne i}
\lambda_j\bigl(r_i({i,j})-s_i\bigr),\
&
\sum_{j\ne i}
\lambda_j\bigl(r_i({j})-s_i\bigr)
\Bigg}
+O(t^2).
\end{aligned}
\tag{28}
]

The graph of this tangent system is rational semialgebraic and piecewise affine. Points with (b_i<s_i) first undergo the finite clamp (23); the vanishing-step analysis then takes place on the fixed face.

Thus the missing relative approximation is no longer a generic approximation problem for the infinite-word closure. Its infinitesimal part is a rational diagonal piecewise-affine differential inclusion.

## 6. A word-level near-spine dichotomy

There is also a useful improvement over the stagewise factor (\prod_t\ell(x^t)).

For a word (w=(x^1,\ldots,x^m)), put

[
C_j(w)=\prod_{t=1}^m c_j^t.
]

The composite map has the form

[
\overline T_w(U,b)
==================

\left(
A_wU+G_w,,
\left(
\max{M_{i,w},B_{i,w}b_i+H_{i,w}}
\right)_i
\right),
\tag{29}
]

where

[
A_w=\prod_j C_j(w),
\qquad
B_{i,w}=\prod_{j\ne i}C_j(w).
\tag{30}
]

Hence its exact Lipschitz factor is at most

[
L(w)=\max_iB_{i,w}.
\tag{31}
]

This detects contraction hidden by alternating singleton movers.

Fix a rational compact invariant box (X). There is a table-dependent rational constant (C_X) such that, if (\widetilde x^{,k}) is obtained from (x) by retaining (q_k) and setting every (q_j), (j\ne k), to zero, then

[
|\overline T_xz-\overline T_{\widetilde x^{,k}}z|*\infty
\le
C_X\sum*{j\ne k}q_j
\qquad(z\in X).
\tag{32}
]

Now suppose (L(w)\ge\frac12), and choose (k) with

[
B_{k,w}=L(w).
]

Since

[
B_{k,w}=\prod_{j\ne k}C_j(w),
]

each (C_j(w)), (j\ne k), is at least (L(w)). Moreover,

[
\sum_t q_j^t
\le
-\log C_j(w).
]

Therefore

[
\sum_t\sum_{j\ne k}q_j^t
\le
(n-1)(-\log L(w))
\le
2(n-1)(1-L(w)).
\tag{33}
]

Let (w^{[k]}) be the word obtained by deleting all hazards except those of player (k). Telescoping (32), using nonexpansiveness of every intervening prefix and suffix, gives

[
\boxed{
|\overline T_wz-\overline T_{w^{[k]}}z|_\infty
\le
2C_X(n-1)(1-L(w)).
}
\tag{34}
]

So every almost-noncontractive word is quantitatively close to a fixed-owner chronology. An indefinitely alternating chronology cannot remain almost noncontractive unless all but one player's total hazard tends to zero.

The coefficient in (34) is fixed by the reward scale. It cannot simply be paid from the wedge slack (c-\gamma r), because (D_*), and hence the available (c-\gamma r), may be arbitrarily small. Zeroth-order deletion of foreign hazards is therefore still insufficient. What is needed is a first-order fixed-owner spine model whose residual is

[
o(1-L(w)),
]

or, more usefully, at most

[
\varepsilon(1-L(w))
]

for an arbitrarily prescribed (\varepsilon>0).

## 7. The remaining bridge, now localized

The semialgebraic-completeness bridge would follow from the following relative approximation statement.

> **Palm–spine approximation lemma.**
> Given prescribed rational (\rho,\sigma>0), construct a rational semialgebraic, clamp-closed anchor set (A), with debt floor arbitrarily close to (D_*), such that for every (a\in A) and every product action (x), there is (a'\in A) satisfying
> [
> \eta_i\le \rho(1-\beta_i)
> \quad\forall i,
> ]
> and
> [
> \eta_0+\gamma\sum_i\eta_i
> \le\sigma(1-\alpha).
> ]

Taking

[
\rho=r,
\qquad
\sigma=c-\gamma r
]

then closes the proof by (17)–(20).

Away from the neutral faces, ordinary sufficiently fine semialgebraic approximation has fixed positive tolerance. At the neutral faces, exact clamp saturation handles the literally zero coordinates. The remaining limiting problem is the rational piecewise-affine Palm system (26)–(28), together with the fixed-owner word spines isolated by (34).

So the new reduction is:

[
\boxed{
\text{semialgebraic completeness}
\quad\Longleftarrow\quad
\text{relative semialgebraic trapping for the Palm/spine PWA system}.
}
]

I have not yet proved that final Palm–spine approximation lemma. The wedge construction does, however, remove the earlier false obstruction from all singleton actions: the available scalar slack is ( (1-\alpha)(c-\gamma r)), while the only exactly neutral coordinate is governed by a finite rational clamp.

## Last followup

All six qualifications are correct. In particular, the corrected Palm–spine statement must produce a bounded rational semialgebraic set

[
A\subseteq X,\qquad \pi(e_\infty)\in A,
]

not merely a relatively invariant approximation somewhere near (\overline{\mathcal K}).

I have not established that lemma or a negative table. The following does close two load-bearing gaps and gives a sharper finite reduction, but it also exposes why the remaining step is not a routine approximation argument.

## 1. The uniform rational constant in (32)

Choose a rational (R\ge1) such that

[
|r_i(S)|\le R
]

for every (i,S), and enlarge (R), if necessary, so that (e_\infty\in[-R,R]^{2n}).

The full box

[
\widehat X=[-R,R]^{2n}
]

is invariant. Indeed, every (u_i') is a convex combination of (u_i) and quitting rewards, while (Q_i) and (C_i) lie in ([-R,R]), and hence so does their maximum.

In reduced coordinates, use

[
X=[-nR,nR]\times[-R,R]^n.
\tag{1}
]

Fix (k\in I). Given (x), let (\widetilde x^{,k}) retain (q_k) and set (q_j=0) for (j\ne k). Put

[
\varepsilon_k(x)=\sum_{j\ne k}q_j.
]

Couple the product coalitions generated by (x) and (\widetilde x^{,k}) using the same independent uniform random variables. The two coalitions differ only if at least one (j\ne k) Quits, so

[
\Pr(S_x\ne S_{\widetilde x^{,k}})
\le\varepsilon_k(x).
\tag{2}
]

For the reduced (U)-coordinate, define the random payoff

[
\Phi_U(S;U)=
\begin{cases}
U,&S=\varnothing,\
\displaystyle\sum_i r_i(S),&S\ne\varnothing.
\end{cases}
]

On (X), (|\Phi_U|\le nR). Hence the coupling inequality gives

[
\left|
\overline T_x(U,b)*U-
\overline T*{\widetilde x^{,k}}(U,b)_U
\right|
\le 2nR,\varepsilon_k(x).
\tag{3}
]

For a fixed (i), both (Q_i) and (C_i(,\cdot,;b_i)) are expectations of variables in ([-R,R]). The opponent coalitions in the two coupled experiments can differ only if some (j\ne k) Quits; changing (q_i) itself is immaterial because player (i) is omitted from (x_{-i}). Therefore

[
|Q_i(x_{-i})-Q_i(\widetilde x^{,k}_{-i})|
\le2R,\varepsilon_k(x),
\tag{4}
]

and

[
|C_i(x_{-i};b_i)-
C_i(\widetilde x^{,k}_{-i};b_i)|
\le2R,\varepsilon_k(x).
\tag{5}
]

Since

[
|\max{a,b}-\max{c,d}|
\le\max{|a-c|,|b-d|},
]

we obtain

[
\boxed{
|\overline T_xz-\overline T_{\widetilde x^{,k}}z|*\infty
\le C_X\sum*{j\ne k}q_j,
\qquad C_X=2nR.
}
\tag{6}
]

Thus (32) holds with an explicit uniform rational constant.

## 2. The corrected near-spine word estimate

For a word (w=(x^1,\ldots,x^m)), define

[
C_j(w)=\prod_{t=1}^m c_j^t,
]

and

[
A_w=\prod_j C_j(w),\qquad
B_{i,w}=\prod_{j\ne i}C_j(w).
]

The composite map has coordinate sensitivities at most (A_w) in (U) and (B_{i,w}) in (b_i). Consequently its Lipschitz factor is at most

[
L(w)=\max_iB_{i,w}.
\tag{7}
]

Choose (k) attaining the maximum, and let (w^{[k]}) be obtained by deleting all hazards except player (k)'s at every stage. Telescoping (6), using nonexpansiveness of all preceding and succeeding factors, gives

[
|\overline T_wz-\overline T_{w^{[k]}}z|*\infty
\le
C_X\sum_t\sum*{j\ne k}q_j^t.
\tag{8}
]

Because

[
B_{k,w}=\prod_{j\ne k}C_j(w)=L(w),
]

every (C_j(w)), (j\ne k), is at least (L(w)). Furthermore,

[
\sum_tq_j^t
\le
\sum_t-\log(1-q_j^t)
====================

-\log C_j(w).
]

Hence

[
\sum_t\sum_{j\ne k}q_j^t
\le(n-1)(-\log L(w)).
\tag{9}
]

For (L(w)\ge\frac12),

[
-\log L(w)\le2(1-L(w)).
]

Combining this with (8),

[
\boxed{
|\overline T_wz-\overline T_{w^{[k]}}z|_\infty
\le
2C_X(n-1)(1-L(w))
}
\tag{10}
]

for every (z\in X). This proves the asserted near-spine estimate, with the corrected wording concerning the Lipschitz factor.

The coefficient in (10), however, is fixed by the reward box. It cannot be made arbitrarily small merely by refining an approximation.

## 3. An exact finite reset lift

There is a useful finite algebraic representation of all branch maps.

For a pure coalition (S\subseteq I) and a branch vector

[
\sigma\in{Q,C}^I,
]

define a rational coordinate-reset map (P_{S,\sigma}) on the full semantic state by

[
(P_{S,\sigma}z)_{u_i}
=====================

\begin{cases}
u_i,&S=\varnothing,\
r_i(S),&S\ne\varnothing,
\end{cases}
\tag{11}
]

and

[
(P_{S,\sigma}z)_{b_i}
=====================

\begin{cases}
r_i((S\setminus{i})\cup{i}),
&\sigma_i=Q,[1mm]
b_i,
&\sigma_i=C,\ S\setminus{i}=\varnothing,[1mm]
r_i(S\setminus{i}),
&\sigma_i=C,\ S\setminus{i}\ne\varnothing.
\end{cases}
\tag{12}
]

Let

[
p_x(S)=\prod_{j\in S}q_j\prod_{j\notin S}c_j.
]

For a fixed branch vector (\sigma), the corresponding affine branch of (T_x) is exactly

[
A_{x,\sigma}
============

\sum_{S\subseteq I}p_x(S)P_{S,\sigma}.
\tag{13}
]

For example, averaging the (Q)-line of (12) over the full coalition (S) eliminates player (i)'s own Quit probability and gives (Q_i(x_{-i})). The (C)-line similarly gives (C_i(x_{-i};b_i)).

Compositions of the (P_{S,\sigma}) form a finite monoid (M): every coordinate is either left unchanged or reset to one of finitely many rational constants. There are therefore only finitely many possible composite reset maps.

For (m\in M), define the rational affine form

[
L_m(z)=D(mz).
\tag{14}
]

If (\tau(m,S,\sigma)=m\circ P_{S,\sigma}), then

[
\boxed{
L_m(T_xz)
=========

\max_{\sigma\in\Sigma_m}
\sum_{S\subseteq I}
p_x(S)L_{\tau(m,S,\sigma)}(z).
}
\tag{15}
]

Here (\Sigma_m) need only contain choices for those (b_i)-coordinates that (m) does not subsequently reset. Formula (15) follows because a sum of coordinatewise independent maxima is a maximum over the corresponding finite branch vectors.

Thus the quitting semantic dynamics has a finite-dimensional max-stochastic lift.

## 4. A finite rational polyhedral certificate theorem

Formula (15) gives a stronger conditional certificate scheme than the wedge construction.

Suppose there are rational numbers (h_m), (m\in M), and a rational (\varepsilon>0), such that

[
L_m(e_\infty)\ge h_m+\varepsilon
\qquad(m\in M),
\tag{16}
]

and

[
h_m
\le
\max_{\sigma\in\Sigma_m}
\sum_{S\subseteq I}
p_x(S)h_{\tau(m,S,\sigma)}
\qquad
(m\in M,\ x\in[0,1]^I).
\tag{17}
]

Assume also

[
h_{\mathrm{id}}+\varepsilon>0.
\tag{18}
]

Then

[
\mathcal B_h
============

{z:L_m(z)\ge h_m+\varepsilon
\text{ for every }m\in M}
\tag{19}
]

is a rational polyhedral positive-debt barrier.

Containment of (e_\infty) follows from (16). If (z\in\mathcal B_h), then by (15),

[
\begin{aligned}
L_m(T_xz)
&=
\max_\sigma
\sum_Sp_x(S)L_{\tau(m,S,\sigma)}(z)\
&\ge
\max_\sigma
\sum_Sp_x(S)
\bigl(h_{\tau(m,S,\sigma)}+\varepsilon\bigr)\
&=
\max_\sigma
\sum_Sp_x(S)h_{\tau(m,S,\sigma)}
+\varepsilon\
&\ge h_m+\varepsilon.
\end{aligned}
]

Hence (T_xz\in\mathcal B_h). Finally,

[
D(z)=L_{\mathrm{id}}(z)
\ge h_{\mathrm{id}}+\varepsilon>0.
]

All conditions in (16)–(18) are first-order real-algebraic conditions. Consequently a supplied (h) is a finite, exactly checkable certificate.

This theorem does **not** prove existence of (h) from (D_*>0).

## 5. Why (D_*>0) does not immediately produce the finite potential

Let

[
v(z)=(L_m(z))_{m\in M}.
]

Equation (15) defines finite max-stochastic maps (\Phi_x) satisfying

[
v(T_xz)=\Phi_x(v(z)).
\tag{20}
]

The hypothesis (D_*>0) controls only the identity component along the correlated orbit:

[
(\Phi_wv(e_\infty))*{\mathrm{id}}\ge D**.
\tag{21}
]

By contrast, (17) asks for a coordinatewise lower subsolution. Constructing such a subsolution effectively permits different virtual reset coordinates to be protected by different worst-case continuations. That independently recombines future histories which, in the actual semantic dynamics, must be generated by one common chronology.

More concretely, the tempting definition

[
h_m=\inf_wL_m(T_we_\infty)
\tag{22}
]

does not give (17). Max and coordinatewise infimum have the wrong order:

[
\Phi_x!\left(\inf_w v(T_we_\infty)\right)
\le
\inf_w\Phi_x(v(T_we_\infty))
]

can be strict. This is the same correlation loss underlying the failure of order-rectangular barriers.

Thus the finite reset lift localizes the missing theorem, but does not remove it.

## 6. A fixed-owner shortcut also fails

For an action in which only player (k) can Quit, let (c=1-q_k). For (i\ne k), the scalar (b_i)-map is

[
f_c(t)
======

\max{cs+(1-c)a,;ct+(1-c)d},
\tag{23}
]

where

[
s=r_i({i}),\qquad
a=r_i({i,k}),\qquad
d=r_i({k}).
]

One might hope that a spine could be collapsed to a single action with the same cumulative survival, via

[
f_{c_2}(f_{c_1}(t))
\ge f_{c_1c_2}(t).
\tag{24}
]

That inequality is false. Take the entirely rational data

[
s=0,\qquad a=1,\qquad d=-1,\qquad
t=-1,\qquad c_1=c_2=\frac12.
]

Then

[
f_{1/2}(-1)=\frac12,
\qquad
f_{1/2}!\left(\frac12\right)=\frac12,
]

whereas

[
f_{1/4}(-1)=\frac34.
]

Thus

[
f_{1/2}\circ f_{1/2}(-1)
<
f_{1/4}(-1).
\tag{25}
]

Chronological subdivision along a singleton face can affect the best-response envelope at first order; it is not determined only by cumulative survival. Clamp closure controls (b_k), but not these (b_i), (i\ne k), envelopes.

## 7. Correct status of the Palm–spine route

The needed lemma must have at least the following form.

For arbitrarily prescribed rational (\rho,\sigma>0), it must construct a rational semialgebraic set

[
A\subseteq X,\qquad
\pi(e_\infty)\in A,
\tag{26}
]

with a suitable positive debt lower bound, such that for every (a=(V,a^b)\in A) and every (x), there is (a'=(V',a'^b)\in A) for which

[
\eta_i=
\bigl(a_i'^b-f_i^x(a_i^b)\bigr)_+
\le \rho(1-\beta_i)
\tag{27}
]

and

[
\eta_0+\gamma\sum_i\eta_i
\le\sigma(1-\alpha),
\qquad
\eta_0=(\alpha V+G-V')_+.
\tag{28}
]

Clamp closure supplies the exact zero-error condition in the literally neutral coordinates. It does not establish (27)–(28) on singleton faces. Estimate (10) supplies only a fixed relative constant, not arbitrarily prescribed (\rho,\sigma).

The closest general robust-safety result I found proves semialgebraic invariant existence for a **single algebraic linear update** under robust perturbation of the initial state. Its proof uses the spectral decomposition of one matrix and does not extend to the continuum of max-affine prefix maps here. ([DROPS][1])

Accordingly, the requested definitive bridge is still not proved. What is now rigorous is

[
D_*>0
\Longrightarrow
\text{an open Lipschitz barrier},
]

the explicit estimate (6)–(10), and the finite reset/potential certificate theorem (16)–(19).

There is also an exact correction at the representation level. A probability
law on joint reset modes, updated using one pure-outcome sample shared by all
coordinates, semiconjugates exactly to the terminal semantic prefix map. This
avoids the coordinatewise false recombination in (22). The full construction,
including its left-regular-band structure and exact tail coefficients, is in
[the exact joint-reset lift](../../docs/JOINT_RESET_LIFT.md).

The [one-Palm spine compression](../Runs/Q194_ONE_PALM_SPINE_COMPRESSION.md)
gives a quadratic endpoint error and a finite affine branch normal form. The
generic collision estimate and joint-reset semiconjugacy are checked in Lean;
the bounded affine compression is rigorous mathematics recorded as run
evidence. It does not preserve selector validity at the compressed
intermediate states.

For a rational initial state, the convex hull of all joint reset images is a
rational invariant polytope. It is not a positive barrier: individual reset
modes can have negative debt, and the full hull can contain negative-debt
points. Nor does the finite lift prove that its selector-consistent reachable
closure is semialgebraic. One sufficient unresolved implication is therefore
a semialgebraic trapping theorem on the correlation-preserving law space:

[
\boxed{
D_*>0
\ \Longrightarrow
\begin{array}{c}
\text{a rational semialgebraic set of joint reset laws containing the}\\
\text{identity law, closed under maximizing-selector transitions, and}\\
\text{having a uniformly positive projected debt floor}
\end{array}.
}
]

Neither the near-spine estimate nor clamp saturation establishes that
implication. The joint law lift removes false correlation from the
representation, but it does not prove the displayed trapping implication.

[1]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.163/LIPIcs.ICALP.2025.163.html "https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.163/LIPIcs.ICALP.2025.163.html"
