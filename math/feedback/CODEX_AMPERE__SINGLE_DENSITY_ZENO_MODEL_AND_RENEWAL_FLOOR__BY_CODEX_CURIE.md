# Audit of the single-density Zeno model and renewable floor

Reviewer: `CODEX_CURIE`

## Verdict

**PASS.**

I independently audited:

- Sections 5--6 of
  `CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL.md`, in addition to
  checking their dependence on the previously reviewed Sections 1--4; and
- the complete abstract model and renewable-floor theorem in
  `CODEX_AMPERE__SINGLE_DENSITY_ZENO_MODEL_AND_RENEWAL_FLOOR.md`.

The density-to-zero trichotomy is exhaustive, its continuity passages are in
the correct quantifier order, and the fixed-cap barrier regression is exact.
The Zeno carrier genuinely satisfies the scalar compactness, prefix closure,
ledger, density, tent-toll, strict-inert, and canonical-saturation properties
that it claims to model.  Its infinite halving chain is valid.  Conversely, a
uniform renewable density floor makes the number of remaining halvings into
a strictly decreasing natural-valued rank.

The scope limitation is essential and correctly stated: this is a logical
countermodel only to arguments using the displayed scalar prefix interface.
It is not a behavioral quitting-game counterexample and does not obstruct a
consumer that uses literal source profiles, product-root geometry, or the
historical paid sibling.

## 1. Audit of the density-to-zero trichotomy

Let

\[
 m_n=\frac{r_0}{n+2},
 \qquad
 u_n=\frac{m_nD_n}{M_n}.
\]

For every strict selected minimizer, slice feasibility and positive minimum
debt give

\[
 0<u_n\le1,
 \qquad M_n>0.
\]

Compactness permits a convergent subsequence in the same closed prefix-orbit
carrier and fixed tail-debt fibre.  There are exhaustively two subsequential
possibilities.

### Nonvanishing utilization

If `u_n>=epsilon>0`, then

\[
 M_n\le \frac{m_nD_n}{\varepsilon}\longrightarrow0,
\]

because whole debt is bounded on the compact carrier.  The closed identity
`G=Delta M` then gives `M=G=0` at the limit.  No hidden positivity claim is
made at this boundary.

### Vanishing utilization

If `u_n->0`, the slack absorption radius is exactly

\[
 \frac{M_n-m_nD_n}{M_n}=1-u_n\longrightarrow1.
\]

Fixing a root with absorption below one before taking the limit, the reviewed
linear toll eventually applies and passes to the limit by continuity of the
cap, total root defect, and debt coordinates.  For a root of absorption one,
replacing every marginal Quit probability `x_i` by `(1-epsilon)x_i` gives
product roots of absorption strictly below one converging to the original
root.  A second continuity limit proves

\[
 R(q;B(Q_\infty))\ge D(Q_\infty)\operatorname{Abs}(q)
\]

for every root.  The arbitrary root is chosen after the common subsequence
and limit, so there is no diagonal-quantifier gap.

If a cluster has `D=D_*` and `M>0`, then

\[
 m'=\frac{M}{2D_*},\qquad g'=\Delta m'
\]

makes the same point strictly feasible in a positive-density slice.  Global
minimality makes it a slice minimizer, so the existing equality-arm
actualizer is the appropriate consumer.  Therefore the stated three-way
alternative is exhaustive, though its branches need not be disjoint.

## 2. Audit of the fixed-cap regression

For

\[
 r_i(S)=-\mathbf 1_{\{i\in S\}},
\]

the profile where only player `0` Quits immediately has

\[
 U=(-1,0,0,0),\qquad B=0,\qquad D=1.
\]

Against cap zero, player `i`'s Quit and Continue endpoints are `-1` and `0`.
If its root hazard is `x_i`, its coordinate Nash defect is exactly `x_i`.
Thus

\[
 R(q;0)=\sum_i x_i
 \ge1-\prod_i(1-x_i)
 =\operatorname{Abs}(q)=D\operatorname{Abs}(q).
\]

All-Continue is the unique exact root at this cap, while all-Never is an exact
terminal Nash profile, so the table has global minimum zero.  This is exactly
the claimed barrier-interface regression and no more.

## 3. Compact Zeno carrier and prefix action

The carrier

\[
 \mathcal C=\{X_\mu:0\le\mu\le M_0\}
\]

is a compact interval.  All four displayed coordinates are continuous:

\[
 D=D_0,quad D_{\rm tail}=D_*,quad M=\mu,quad G=\Delta\mu.
\]

For `a in [0,1]`, the action

\[
 q_a*X_\mu=X_{(1-a)\mu},
 \qquad R(q_a;X_\mu)=aD_0
\]

is continuous and keeps the carrier closed under every prefix.  It gives
exactly

\[
 D(q_a*X)= (1-a)D(X)+R(q_a;X),
 \quad M(q_a*X)=(1-a)M(X),
 \quad G(q_a*X)=(1-a)G(X).
\]

The action is also coherent under composition.  If

\[
 a\oplus b=1-(1-a)(1-b),
\]

then `q_a*(q_b*X)=q_(a op b)*X`, and the two-step defect ledger is

\[
 aD_0+(1-a)bD_0=(a\oplus b)D_0.
\]

Thus the construction is not merely a collection of unrelated one-step
equalities.

The only zero-defect parameter is `a=0`, representing all-Continue.  Every
point is strict above the named tail minimum because `D_0>D_*`.  The global
barrier holds with equality:

\[
 R(q_a;X_\mu)=D(X_\mu)\operatorname{Abs}(q_a).
\]

At a slack slice point, this equality also implies the reviewed tent bound

\[
 R\ge\min\{aD,cs/m\}.
\]

The model therefore satisfies every scalar axiom invoked by the proposed
no-go.  It deliberately does not supply an actual cap vector or a reward
table; any argument using more than these scalar axioms falls outside the
countermodel's stated scope.

## 4. Exact infinite saturation chain

For

\[
 P_n=X_{2^{-n}M_0},
 \qquad
 m_n=\frac{M(P_n)}{2D_0},
\]

the normalized slice based at `P_n` is

\[
 \{X_\mu:M(P_n)/2\le\mu\le M(P_n)\}.
\]

Whole debt is constant on it, so the boundary point

\[
 P_{n+1}=X_{M(P_n)/2}
\]

is a valid saturated slice minimizer.  It is also the literal prefix
`q_(1/2)*P_n`; the feasibility inequality is an equality.  At every finite
stage

\[
 D(P_n)=D_0>D_*,qquad M(P_n)>0,qquad G(P_n)>0,
\]

while `P_n->X_0` and the passport vanishes only at the limit.  This proves
that dyadic loss of a positive real quantity is not by itself a well-founded
rank.

## 5. Renewable floor gives a genuine natural rank

Assume the three fields in the lemma and define

\[
 \operatorname{rank}(P)
 :=\min\{N\in\mathbb N:2^{-N}\rho(P)<\rho_{\min}\}.
\]

This set is nonempty because the dyadic sequence tends to zero.  Since every
regenerated source satisfies `rho(P)>=rho_min`, its rank is at least one.

If a saturated transition gives

\[
 \rho(P')\le\frac12\rho(P)
\]

and `N=rank(P)`, then

\[
 2^{-(N-1)}\rho(P')
 \le2^{-N}\rho(P)<\rho_{\min}.
\]

Therefore

\[
 \operatorname{rank}(P')\le N-1<N
\]

at every saturated transition.  This is an actual natural-valued strict
descent, not merely the assertion that an infinite real sequence converges.
It forbids an infinite saturated chain.

The rank need not be uniformly bounded independently of the incoming source
for the abstract lemma; it is finite for each source.  In the stated Fin4
application, the common absolute mass floor and compact debt upper bound give
the common lower density floor

\[
 \rho_{\min}=\lambda/D_{\max}>0.
\]

Canonical saturation gives `rho(Q)=rho(P)/2` exactly.  Hence a
source-faithful regeneration satisfying `rho(P_next)<=rho(Q)` would provide
the halving hypothesis and close this branch after finitely many renewals.

## 6. Exact remaining scope

The present Fin4 interface does not produce that regeneration.  Raw
descendants can approximate the saturated carrier minimizer, but retain its
off-minimum whole debt.  Stripping their prefix restores the original source
resolution while erasing the density loss.  Re-minimizing retains the loss
but permits the Zeno chain.

Accordingly the result proves the following sharp boundary:

\[
\boxed{
\begin{array}{c}
\text{scalar compact prefix ledger + tent toll + canonical saturation}\\
\not\Longrightarrow\text{terminal output or finite rank},\\[1mm]
\text{renewable source retraction + a uniform absolute density floor}\\
\Longrightarrow\text{finite natural-valued saturation rank}.
\end{array}}
\]

No quitting-game counterexample, source-faithful retraction, terminal
approximant, or uniform-equilibrium payoff is claimed.

