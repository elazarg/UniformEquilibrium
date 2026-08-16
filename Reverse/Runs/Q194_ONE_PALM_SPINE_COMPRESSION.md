# Q194 one-Palm spine compression with quadratic residual

## Status

This run proves a near-spine representation theorem for the synchronous
reset-law lift. The common-coupling semiconjugacy is proved in Lean in
[`TerminalSemanticJointResetLift`](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticJointResetLift.lean),
and its quadratic collision estimate is proved in Lean by
`Math.PMFProduct.collisionMass_le_sq_sum_div_two`. The affine branch-compression
theorems below are rigorous mathematics but are not checked in Lean here.

The lift does **not** give a finite description of the selector-consistent
reachable closure, and the full reset polytope is not a positive-debt barrier.
Its valid contribution is an exact law-level semiconjugacy preserving the
common coupling used across the counterfactual endpoint calculations.

The representation theorem gives a quadratic residual:

\[
\operatorname{dist}_\infty
 \bigl(\overline T_w z,\mathsf{OnePalm}_k(z)\bigr)
 =O\bigl((1-L(w))^2\bigr).
\]

Thus the required \(o(1-L(w))\) error is available at the **representation
level**. Barrier completeness requires a positive, selector-valid
semialgebraic trapping set for the resulting one-Palm relation.

Throughout, the reward table is rational.  A fixed reset vertex
\(m(z_0)\) is rational only when the chosen initial state \(z_0\) is rational.
For the quitting application,
\(z_0=\pi(e_\infty)\) is rational because its coordinates are obtained from
rational rewards using \(0\), addition, and finite maxima.

---

## 1. Selected affine branches and exact sensitivity

Work in the reduced state

\[
z=(U,b)\in\mathbb R^{1+n},
\qquad
U=\sum_i u_i.
\]

For a product root \(x\), write

\[
\alpha(x)=\prod_j c_j,
\qquad
\beta_i(x)=\prod_{j\ne i}c_j.
\]

Choose one maximizing branch vector

\[
\varepsilon\in\{\mathrm Q,\mathrm C\}^I
\]

at the current state.  Let \(G_{x,\varepsilon}\) be the corresponding affine
branch of \(\overline T_x\).  Its linear part is diagonal:

\[
DG_{x,\varepsilon}
=
\operatorname{diag}\left(
 \alpha(x),
 \mathbf 1_{\varepsilon_i=\mathrm C}\beta_i(x)
 \right)_{i\in I}.
\tag{1}
\]

The forced-Quit branch is independent of \(b_i\), while the Continue branch
has coefficient \(\beta_i(x)\).

For a branch word
\((x^1,\varepsilon^1),\ldots,(x^m,\varepsilon^m)\), the exact coordinate
sensitivities are therefore

\[
J_U(w)=\prod_{t=1}^m\alpha(x^t),
\tag{2}
\]

and

\[
\boxed{
J_i(w)=
\prod_{t=1}^m
\mathbf 1_{\varepsilon_i^t=\mathrm C}\,
\beta_i(x^t).
}
\tag{3}
\]

In particular, one forced-Quit selector kills all earlier \(b_i\)-dependence.

If an error vector \(e^t\) is inserted after stage \(t\), the exact affine
Duhamel expansion gives the coordinatewise bounds

\[
|e_U^{\rm out}|
\le
\sum_t
\left(\prod_{s>t}\alpha(x^s)\right)|e_U^t|,
\tag{4}
\]

and

\[
\boxed{
|e_i^{\rm out}|
\le
\sum_t
\left(
 \prod_{s>t}
 \mathbf 1_{\varepsilon_i^s=\mathrm C}\beta_i(x^s)
\right)
|e_i^t|.
}
\tag{5}
\]

The branchwise sensitivity (3), rather than merely
\(\prod_t\beta_i(x^t)\), is the correct law-level factor.

---

## 2. A sharper foreign-hazard bound

For a word \(w=(x^1,\ldots,x^m)\), put

\[
C_j(w)=\prod_t c_j^t,
\qquad
B_{i,w}=\prod_{j\ne i}C_j(w),
\qquad
L(w)=\max_i B_{i,w}.
\]

Choose \(k\) with \(B_{k,w}=L(w)\), and define the total foreign hazard

\[
E_k(w)=\sum_t\sum_{j\ne k}q_j^t.
\tag{6}
\]

Assume \(L(w)>0\). Since
\(q\le-\log(1-q)\),

\[
\begin{aligned}
E_k(w)
&\le
\sum_{j\ne k}\sum_t-\log c_j^t\\
&=
-\log\prod_{j\ne k}C_j(w)\\
&=
-\log B_{k,w}\\
&=
\boxed{-\log L(w)}.
\end{aligned}
\tag{7}
\]

There is no factor \(n-1\).  If \(L(w)\ge\tfrac12\), then

\[
E_k(w)\le-\log L(w)\le2(1-L(w)).
\tag{8}
\]

Consequently the zeroth-order deletion estimate has coefficient
\(2C_X\), rather than \(2C_X(n-1)\), in front of \(1-L\). Its coefficient is
fixed, so this alone does not solve the relative approximation problem.

---

## 3. The common base-outcome coupling

Fix the maximizing selector vector \(\varepsilon^t\) used by the exact
semantic orbit at every date.  For each date \(t\), expand the selected affine
branch using one pure base outcome

\[
\omega^t\in\{\mathrm C,\mathrm Q\}^I.
\]

The variables \(\omega^t\) are an algebraic coupling device for the affine
branch expansion.  They couple the payoff and all counterfactual endpoint
calculations to the same base outcome.

They are **not** one jointly realized behavioral or deviation history.
In particular, pure outcomes at algebraically inner stages may be overwritten
by an earlier terminal reset.

Because all elementary reset maps are affine,

\[
G_{x^m,\varepsilon^m}\circ\cdots\circ
G_{x^1,\varepsilon^1}(z)
=
\mathbb E\left[
 E_{\varepsilon^m,\omega^m}\circ\cdots\circ
 E_{\varepsilon^1,\omega^1}(z)
\right].
\tag{9}
\]

This is the law-level semiconjugacy used below.

---

## 4. Global one-Palm truncation

Fix the dominant owner \(k\).  Consider all foreign Bernoulli variables

\[
Y_{t,j}=\mathbf 1_{\omega_j^t=\mathrm Q},
\qquad j\ne k.
\]

Let

\[
N_F=\sum_t\sum_{j\ne k}Y_{t,j}.
\]

Construct a coupling as follows:

1. keep every configuration with \(N_F=0\);
2. keep every configuration with \(N_F=1\);
3. when \(N_F\ge2\), replace all foreign bits by Continue while leaving the
   entire sequence of player \(k\)'s base outcomes unchanged.

Call the resulting branch endpoint
\(\widehat T^{(1),k}_w z\).  This operation keeps all first-order foreign
events, including collisions between \(k\) and one foreign player.  It
discards only configurations containing two or more foreign Quit events
across the whole word.

Let \(X\) be a compact box containing every elementary reset image, and put

\[
\Delta_X=\operatorname{diam}_\infty(X).
\]

### Theorem 1: quadratic one-Palm error

\[
\boxed{
\left\|
 \overline T_wz-\widehat T^{(1),k}_wz
\right\|_\infty
\le
\frac{\Delta_X}{2}E_k(w)^2.
}
\tag{10}
\]

Hence, for \(L(w)\ge\tfrac12\),

\[
\boxed{
\left\|
 \overline T_wz-\widehat T^{(1),k}_wz
\right\|_\infty
\le
2\Delta_X(1-L(w))^2.
}
\tag{11}
\]

#### Proof

The event \(N_F\ge2\) is contained in the union over unordered pairs of
foreign stage-player variables that both equal one.  Therefore

\[
\Pr(N_F\ge2)
\le
\sum_{a<b}\Pr(Y_a=Y_b=1)
\le
\frac12
\left(\sum_a\Pr(Y_a=1)\right)^2
=
\frac12E_k(w)^2.
\tag{12}
\]

The original and truncated couplings agree off this event.  On this event,
their final reset outputs are two points of \(X\), so their sup-distance is
at most \(\Delta_X\).  Averaging proves (10).  Equations (7)--(8) give
(11). \(\square\)

For the reduced rational box

\[
X=[-nR,nR]\times[-R,R]^n,
\]

one may take \(\Delta_X=2nR\), giving the explicit bound

\[
\left\|
 \overline T_wz-\widehat T^{(1),k}_wz
\right\|_\infty
\le
4nR(1-L(w))^2.
\tag{13}
\]

Thus, for every prescribed \(\eta>0\), the residual is at most

\[
\eta(1-L(w))
\]

whenever

\[
1-L(w)\le\frac{\eta}{2\Delta_X}.
\tag{14}
\]

This is the requested \(o(1-L)\) scale, but only for the finite branch
representation constructed below.

---

## 5. Convex one-event form

Let \(z^0\) be the selected branch endpoint obtained by setting every foreign
base-outcome bit to Continue while retaining player \(k\)'s original mixed
roots.

For every stage-player pair \((t,j)\), \(j\ne k\), let \(z^{t,j}\) be the
selected branch endpoint obtained by forcing exactly that foreign bit to Quit
and every other foreign bit to Continue, again retaining player \(k\)'s mixed
roots.

Let

\[
\lambda_{t,j}
=
q_j^t
\prod_{\substack{(s,\ell)\ne(t,j)\\\ell\ne k}}
c_\ell^s
\tag{15}
\]

be the probability that \((t,j)\) is the unique foreign Quit event.  After
moving the multi-event mass to the zero-event configuration,

\[
\widehat T^{(1),k}_wz
=
\lambda_0z^0+
\sum_{t,j\ne k}\lambda_{t,j}z^{t,j},
\tag{16}
\]

where

\[
\lambda_0=1-\sum_{t,j\ne k}\lambda_{t,j}.
\]

Thus the one-Palm truncation is a convex combination of:

* one fixed-owner branch endpoint; and
* branch endpoints with exactly one foreign Palm insertion.

In reduced dimension \(d=n+1\), Carathéodory compresses (16) to at most

\[
d+1=n+2
\tag{17}
\]

such endpoints.  If the total one-event mass is to be preserved as an
additional coordinate, at most \(d+2=n+3\) endpoints suffice.

This compression uses one common convex combination for the whole state; it
does not independently recombine payoff or cap coordinates.

---

## 6. Exact bounded compression of a fixed-owner branch

The remaining apparent infinitude is the length of the fixed-owner branch
word.  At the selected-branch level, that length can also be bounded exactly.

Suppose only player \(k\) may Quit at a root, and let \(c\) be \(k\)'s Continue
probability.  Put

\[
R^k=\sum_i r_i(\{k\}),
\qquad
s_i=r_i(\{i\}),
\qquad
a_{ik}=r_i(\{i,k\}),
\qquad
d_{ik}=r_i(\{k\}).
\]

The selected branch formulas are

\[
U'=cU+(1-c)R^k,
\tag{18}
\]

\[
b_k'=
\begin{cases}
s_k,&\varepsilon_k=\mathrm Q,\\
b_k,&\varepsilon_k=\mathrm C,
\end{cases}
\tag{19}
\]

and, for \(i\ne k\),

\[
b_i'=
\begin{cases}
cs_i+(1-c)a_{ik},&\varepsilon_i=\mathrm Q,\\
cb_i+(1-c)d_{ik},&\varepsilon_i=\mathrm C.
\end{cases}
\tag{20}
\]

Consider an arbitrary fixed-owner selected branch word
\((c_t,\varepsilon^t)_{t=1}^m\), and let

\[
C=\prod_t c_t.
\]

For \(i\ne k\):

* if \(\varepsilon_i^t=\mathrm C\) at every date, then
  \[
  b_i^{\rm out}=Cb_i+(1-C)d_{ik};
  \tag{21}
  \]
* otherwise let \(\tau_i\) be the last date with
  \(\varepsilon_i^{\tau_i}=\mathrm Q\), and let
  \[
  P_i=\prod_{t>\tau_i}c_t.
  \]
  Then
  \[
  b_i^{\rm out}
  =
  P_i\bigl(c_{\tau_i}s_i+
      (1-c_{\tau_i})a_{ik}\bigr)
  +(1-P_i)d_{ik}.
  \tag{22}
  \]

For \(i=k\), the output is \(b_k\) if no forced-Quit selector occurs and
\(s_k\) otherwise.

Only the last forced-Quit date of each cap coordinate matters.

### Theorem 2: bounded selected-branch spine

Every fixed-owner selected affine branch word is exactly equal, as an affine
map on \((U,b)\), to one of length at most

\[
\boxed{2n+1.}
\tag{23}
\]

#### Proof

Mark the distinct dates which are the last forced-Quit date of at least one
cap coordinate.  There are at most \(n\) such dates.

Keep every marked date with its original \(c_t\).  At a marked date, select
Quit exactly for the coordinates whose last forced-Quit date is that date,
and select Continue for every other coordinate.

Replace each gap of unmarked dates by one all-Continue-selected fixed-owner
branch whose Continue probability is the product of the \(c_t\)'s in that
gap.

There are at most \(n\) marked dates and \(n+1\) gaps.  Formulas
(18)--(22) show that the resulting branch map is identical to the original
one. \(\square\)

The compressed selector word need not remain selector-consistent at its new
intermediate states.  The theorem is an affine branch normal form, not an
executable semantic chronology.

---

## 7. Bounded one-Palm branch family

A branch endpoint \(z^{t,j}\) with one foreign event consists of:

1. a fixed-owner prefix;
2. one root where \(j\) is forced to Quit and \(k\) retains its mixed action;
3. a fixed-owner suffix.

Compressing the prefix and suffix with Theorem 2 gives a branch word of
length at most

\[
(2n+1)+1+(2n+1)
=
\boxed{4n+3.}
\tag{24}
\]

Let \(\mathsf S_k\subseteq X\times X\) be the relation consisting of outputs
of selected branch words of length at most \(4n+3\) in which:

* every root has support contained in \(\{k\}\), except possibly one root;
* at the exceptional root, one player \(j\ne k\) is forced to Quit;
* all branch selectors are recorded as finite discrete data.

For rational rewards, \(\mathsf S_k\) is a rational semialgebraic relation:
there are finitely many discrete patterns, the root probabilities range over
boxes, and every bounded branch output is polynomial in those probabilities
and affine in the input state.

Let

\[
\mathsf{OnePalm}_k(z)
=
\operatorname{conv}
\{z':(z,z')\in\mathsf S_k\}.
\tag{25}
\]

By the \(n+2\)-point Carathéodory representation, its graph is also rational
semialgebraic.

### Corollary 3: finite semialgebraic near-spine representation

For every exact semantic word \(w\), every \(z\in X\), and every
\(k\) attaining \(B_{k,w}=L(w)\),

\[
\boxed{
\operatorname{dist}_\infty
\bigl(
 \overline T_wz,
 \mathsf{OnePalm}_k(z)
\bigr)
\le
\frac{\Delta_X}{2}(-\log L(w))^2.
}
\tag{26}
\]

For \(L(w)\ge\tfrac12\),

\[
\boxed{
\operatorname{dist}_\infty
\bigl(
 \overline T_wz,
 \mathsf{OnePalm}_k(z)
\bigr)
\le
2\Delta_X(1-L(w))^2.
}
\tag{27}
\]

This avoids coordinatewise false recombination and gives a finite rational
semialgebraic \(o(1-L)\) representation of every almost-neutral word endpoint.

---

## 8. What this does and does not settle

The Palm--spine reduction gives:

\[
\boxed{
\text{almost-neutral exact word}
\Longrightarrow
\text{finite one-Palm semialgebraic branch representation}
+
o(1-L).
}
\tag{28}
\]

It removes the fixed-coefficient obstruction of zeroth-order foreign-hazard
deletion.

It does **not** prove:

1. that every point of \(\mathsf{OnePalm}_k\) is selector-consistent;
2. that \(\mathsf{OnePalm}_k\) has positive debt;
3. that its selector-consistent reachable closure is semialgebraic;
4. that a positive semialgebraic subset is closed under all required
   successors;
5. Q194's barrier-completeness statement.

Invalid selected branches can have negative debt, even though the particular
one-Palm point produced from an exact word is
\(O((1-L)^2)\)-close to the positive carrier.

The remaining theorem has a sharper form:

> **Selector-valid one-Palm trapping problem.**
> Construct a bounded rational semialgebraic positive-debt anchor set which is
> relatively closed under the selector-valid part of
> \(\mathsf{OnePalm}_k\) for every owner \(k\), or prove that every such
> one-Palm system admits a debt-descent chronology.

Theorem 2 bounds the affine endpoint representation of a selector-valid
fixed-owner chronology. The **validity trace** certifying that the selected
branches were optimal at their original intermediate states can remain
unbounded. Merging Continue-selected
gaps need not preserve that validity.  This is precisely the singleton-envelope
problem left open by Q194.

The correlation problem separates into two statements:

\[
\begin{array}{ll}
\text{endpoint correlation:}&
\text{handled by the law coupling and one-Palm compression};\\[1mm]
\text{selector-valid chronology:}&
\text{the remaining obstruction.}
\end{array}
\]


---

## 9. Block wedge lemma and quantitative absorption

The one-stage wedge calculation extends verbatim to a finite word.

Write the composite word map as

\[
\overline T_w(U,b)
=
\left(
 A_wU+G_w,\,
 \left(f_{i,w}(b_i)\right)_i
\right),
\tag{29}
\]

where

\[
A_w=\prod_i C_i(w),
\qquad
B_{i,w}=\prod_{j\ne i}C_j(w),
\tag{30}
\]

and

\[
(f_{i,w}(a)-f_{i,w}(b))_+
\le B_{i,w}(a-b)_+.
\tag{31}
\]

The cumulative coefficients satisfy

\[
\sum_i(B_{i,w}-A_w)
=
\sum_i(1-C_i(w))
 \prod_{j\ne i}C_j(w)
\le
1-A_w.
\tag{32}
\]

The left side is the probability that exactly one of independent Bernoulli
variables with Continue probabilities \(C_i(w)\) fails.

Let \(A\subseteq X\), and suppose that for an anchor
\(a=(V,a^b)\in A\) and a word \(w\), there is
\(a'=(V',a'^b)\in A\) with unfavorable errors

\[
\eta_0=(A_wV+G_w-V')_+,
\tag{33}
\]

\[
\eta_i=(a_i'^b-f_{i,w}(a_i^b))_+.
\tag{34}
\]

If

\[
\eta_i\le r(1-B_{i,w})
\qquad\forall i,
\tag{35}
\]

and

\[
\eta_0+\gamma\sum_i\eta_i
\le
(c-\gamma r)(1-A_w),
\tag{36}
\]

then the wedge \(\mathcal W_{\gamma,r,c}(A)\) is preserved by this word
transition.

Indeed, if \(p_i=(a_i^b-b_i)_+\le r\), then

\[
p_i'\le B_{i,w}p_i+\eta_i\le r.
\]

The output wedge slack is at least

\[
(1-A_w)c
-\gamma\sum_i(B_{i,w}-A_w)p_i
-\eta_0-\gamma\sum_i\eta_i,
\]

which is nonnegative by (32) and (36).

Now let \(L(w)=\max_iB_{i,w}\), and let \(y\) be the one-Palm endpoint from
Corollary 3.  Put

\[
\delta_w=\|\overline T_w a-y\|_\infty.
\]

Since

\[
A_w\le B_{i,w}\le L(w),
\]

we have

\[
1-A_w\ge1-L(w),
\qquad
1-B_{i,w}\ge1-L(w).
\tag{37}
\]

For \(L(w)\ge\tfrac12\),

\[
\delta_w\le2\Delta_X(1-L(w))^2.
\tag{38}
\]

Therefore (35)--(36) hold whenever

\[
1-L(w)
\le
\frac{1}{2\Delta_X}
\min\left\{
r,\,
\frac{c-\gamma r}{1+\gamma n}
\right\}.
\tag{39}
\]

Thus the one-Palm approximation error can be paid from the exact block wedge
slack for every sufficiently neutral word. The fixed-linear coefficient does
not obstruct this estimate.

This argument assumes that the one-Palm approximant \(y\) belongs to the chosen
anchor set \(A\).  The remaining problem is therefore not quantitative
approximation.  It is the existence of a positive-debt semialgebraic anchor
set closed under the selector-valid one-Palm endpoint relation.
