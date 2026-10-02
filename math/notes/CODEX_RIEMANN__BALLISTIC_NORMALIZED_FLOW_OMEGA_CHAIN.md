# The uniformly ballistic strict ray has an exact source-compatible omega-chain

Author: CODEX_RIEMANN

## Status

This note proves an ordinary-mathematics compact omega-chain theorem for the
uniformly ballistic full-binding branch of the strict Fin4 normalized cap
flow.  It is not checked in Lean.

The theorem produces a bi-infinite path in one explicit compact
finite-dimensional semialgebraic relation.  This is the honest invariant
object carried by the normalized flow.  It does not by itself produce a
stationary terminal equilibrium or a finite periodic Nash--Bellman orbit:
normalized current hazards are infinitesimal directions, not literal product
roots at a fixed payoff.

A rational matrix-level regression shows one limitation is real.  The
relation admits a uniformly full-support aperiodic irrational-rotation orbit
with renewal ratio \(1/2\), while its normalized solo matrix is the checked
paired-singleton residual-hard matrix.  Thus a selected source-compatible
omega-chain satisfying the exact normalized identities, the full algebraic
hard class, uniform ballisticity, and full current support need not itself be
stationary or periodic.  The same relation also has an explicit stationary
fixed point, so the example does **not** refute existence of a periodic state
elsewhere in the relation.  The regression is not an actual quitting ray or
positive-gap table.

## Question

Assume an actual source-attached strict Fin4 ray has:

1. full limiting binding;
2. a normalized renewal ratio bounded below by one fixed
   \(\eta>0\); and
3. the exact checked tail-normalized cap-flow and endpoint identities.

Does compact recurrence force the actual source-derived omega-chain to close
into a stationary full-support terminal Nash profile or a finite periodic
Nash--Bellman block?

Not from these data alone.  What is forced is the source-compatible
omega-chain below.  The weaker question whether the abstract normalized
relation must contain *some* stationary or periodic state remains open here;
the regression in Section 5 has such a fixed point.

## Sources inspected

- QuittingForwardExactCapTail and QuittingTailNormalizedCapFlow in
  Research/Quitting/ForwardExactCapTailFlow.lean;
- tailNormalizedCapFlow in
  Research/Quitting/ForwardExactCapTailFirstOrder.lean;
- FinFourStrictRayForwardExactCapTail and Analysis in
  Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean;
- CompactHazardState and CompactHazardCluster in
  Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean;
- pairedSingletonMatrix and its checked full normal core, standard-Q,
  no-homogeneous, and non-projective-Q-bar facts in
  UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean
  and
  UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean.

## 1. The finite-dimensional ballistic relation

Let

\[
\Delta=\left\{z\in\mathbb R_{\ge0}^4:\sum_i z_i=1\right\}.
\]

Write \(M\) for the normalized solo matrix and \(J\) for the collision
matrix.  Fix \(\eta>0\).  The state space is

\[
X_\eta=\Delta\times\Delta\times[\eta,1].
\]

A state is \(x=(\lambda,\Lambda,\rho)\), where:

- \(\lambda\) is the normalized current marginal-hazard direction;
- \(\Lambda\) is the normalized remaining-tail hazard barycenter; and
- \(\rho\) is the current-hazard to remaining-hazard ratio.

For

\[
W_i(x):=(M\Lambda)_i+\rho(J\lambda)_i,
\tag{1}
\]

define the closed relation \(\mathcal R_{M,J,\eta}\subseteq X_\eta^2\) by

\[
x\,\mathcal R_{M,J,\eta}\,x^+
\]

exactly when

\[
\boxed{\Lambda=\rho\lambda+(1-\rho)\Lambda^+}
\tag{2}
\]

and

\[
\boxed{W_i(x)\le0,\qquad \lambda_iW_i(x)=0
\quad(i=0,1,2,3).}
\tag{3}
\]

The relation is compact and semialgebraic.  Equation (2) is the exact renewal
identity.  Equation (3) is the full-binding ballistic collision LCP obtained
from the checked limiting collision inequality and complementarity.

The successor's \(\lambda^+\) and \(\rho^+\) enter through the requirement
that \(x^+\in X_\eta\) and through the next edge.  This is a relation rather
than a claimed single-valued dynamic map.

## 2. Omega-chain theorem

Let an actual source-attached flow satisfy full binding and

\[
\exists\eta>0\;\exists K\;\forall k\ge K,\qquad
\rho_k\ge\eta.
\tag{4}
\]

Then there is a bi-infinite sequence

\[
x_m=(\lambda_m,\Lambda_m,\rho_m)\in X_\eta,
\qquad m\in\mathbb Z,
\tag{5}
\]

such that

\[
\boxed{x_m\,\mathcal R_{M,J,\eta}\,x_{m+1}
\quad\text{for every }m\in\mathbb Z.}
\tag{6}
\]

It has the stronger source provenance:

> For every finite window \([-L,L]\), there are actual ray dates
> \(n_j\to\infty\) such that the complete normalized windows
> \((x_{n_j-L},\ldots,x_{n_j+L})\) converge coordinatewise to
> \((x_{-L},\ldots,x_L)\).

### Proof

Delete the finite prefix before (4).  The actual normalized state sequence

\[
\widehat x_k=(\lambda_k,\Lambda_k,\rho_k)
\]

lies in compact \(X_\eta\).  Choose centers \(n_j\to\infty\).  For each
integer offset \(m\), the sequence \(\widehat x_{n_j+m}\) is defined for all
sufficiently large \(j\).  Repeated finite-dimensional compactness followed
by the standard diagonal extraction gives one subsequence along which every
fixed offset converges.  Call the limits \(x_m\).  The same extraction gives
the finite-window provenance above.

The renewal equation

\[
\Lambda_k=\rho_k\lambda_k+(1-\rho_k)\Lambda_{k+1}
\]

is exact at every actual date, so continuity gives (2) at every limiting
edge.

Fix an integer \(m\).  The dates \(n_j+m\) form an eventually strict
subsequence of actual ray dates.  Full binding makes every coordinate
eligible for the checked collision-limit theorems.  Applying
subseq_collision_nonpos and subseq_collision_complementarity to this
subsequence gives (3) for \(x_m\).  This proves (6).

No stationary payoff or product root has been introduced.

## 3. Balanced occupation measure

The omega-chain also supplies the exact occupation-measure form of the
obstruction.  Let

\[
\pi_N=\frac1N\sum_{m=0}^{N-1}\delta_{(x_m,x_{m+1})}.
\]

Compactness of \(X_\eta^2\) gives a weakly convergent subsequence with limit
\(\pi\).  Since \(\mathcal R_{M,J,\eta}\) is closed,

\[
\operatorname{supp}\pi\subseteq\mathcal R_{M,J,\eta}.
\tag{7}
\]

The two marginals of \(\pi\) are equal.  Indeed, for every continuous \(f\),

\[
\frac1N\sum_{m<N}\bigl(f(x_{m+1})-f(x_m)\bigr)
=\frac{f(x_N)-f(x_0)}N\longrightarrow0.
\tag{8}
\]

Thus the ballistic branch yields a balanced probability flow on the explicit
finite-dimensional relation.  Integrating (2) gives

\[
\int\!\left[\Lambda-\rho\lambda-(1-\rho)\Lambda^+\right]\,d\pi=0.
\tag{9}
\]

Equal marginals do not simplify (9) to
\(\int\Lambda\,d\pi=\int\lambda\,d\pi\), because \(\rho\) is correlated with
the successor.  Likewise, averaging the complementary products in (3) does
not preserve pointwise complementarity for the averaged vectors.

## 4. Why a source omega-chain is not yet a stationary or periodic compiler

A stationary quitting equilibrium requires an actual product root \(q\) and
an actual payoff vector \(v\) satisfying

\[
v=F_q(v)
\tag{10}
\]

together with exact endpoint Nash at that same \(v\).  The state
\((\lambda,\Lambda,\rho)\) contains neither an absolute root hazard nor an
absolute payoff.  It records only ratios after the actual hazards and cap
gaps have vanished.  In particular, the literal roots of the strict ray
converge to all Continue, while the vectors \(\lambda_m\) need not.

A finite periodic Nash--Bellman block similarly requires literal roots and
payoffs with an exact closing seam.  A periodic orbit of (2)--(3), even if
one exists, supplies only first-order normalized closure.  It does not imply
the absolute Bellman identity (10).

Accordingly, neither the checked stationary endpoint compiler nor a periodic
Nash--Bellman compiler applies directly to the selected chain (6) without a
new selection and lifting theorem.  The existence of a different periodic
state somewhere in the normalized relation would still not supply the
absolute Bellman data or the original source provenance.

## 5. Rational aperiodic selected-chain regression inside the full hard matrix class

Nonperiodicity of the selected normalized chain is not just a logical
warning.

Use the checked paired-singleton normalized solo matrix

\[
M=
\begin{pmatrix}
0&3&-1&-1\\
3&0&-1&-1\\
-1&-1&0&3\\
-1&-1&3&0
\end{pmatrix}.
\tag{11}
\]

The project proves that this matrix has full normal core, is standard Q on
that core, has no homogeneous simplex solution, and is not projective Q-bar.
Thus it realizes the complete algebraic ResidualHardClass, not merely the
no-homogeneous field.

Put

\[
u=\tfrac14(1,1,1,1),\qquad
v=(1,-1,0,0),\qquad
w=(0,0,1,-1),\qquad a=\tfrac18.
\]

Let the circle advance by the rational rotation

\[
R=
\begin{pmatrix}
3/5&-4/5\\
4/5&3/5
\end{pmatrix}.
\tag{12}
\]

For a phase vector \(c=(\cos\theta,\sin\theta)\), define

\[
\lambda(\theta)=u+a[v\;w]c.
\tag{13}
\]

Every coordinate lies in \([1/8,3/8]\), so the current support is uniformly
full.  Set \(\rho=1/2\), and define the exact geometric tail barycenter

\[
\Lambda(\theta)
=\sum_{n\ge0}2^{-(n+1)}\lambda(\theta+n\alpha),
\tag{14}
\]

where \(R\) is rotation by \(\alpha\).  Then

\[
\Lambda(\theta)
=\tfrac12\lambda(\theta)+\tfrac12\Lambda(\theta+\alpha).
\tag{15}
\]

On the oscillatory two-plane, the tail operator is

\[
H=\tfrac12(I-\tfrac12R)^{-1}
=
\begin{pmatrix}
7/13&-4/13\\
4/13&7/13
\end{pmatrix}.
\tag{16}
\]

Choose the zero-diagonal rational collision matrix

\[
J=
\begin{pmatrix}
0&-42/13&-4/13&20/13\\
-42/13&0&20/13&-4/13\\
20/13&-4/13&0&-42/13\\
-4/13&20/13&-42/13&0
\end{pmatrix}.
\tag{17}
\]

This matrix is obtained row by row from the exact prescriptions

\[
J_i u=-2M_i u,
\]

\[
J_i v=-2M_i\!\left(\tfrac7{13}v+\tfrac4{13}w\right),
\qquad
J_i w=-2M_i\!\left(-\tfrac4{13}v+\tfrac7{13}w\right),
\tag{18}
\]

and \(J_{ii}=0\).  Direct substitution gives, for every phase,

\[
\boxed{M\Lambda(\theta)+\tfrac12J\lambda(\theta)=0.}
\tag{19}
\]

Thus the circle orbit

\[
x_m=
\left(\lambda(\theta+m\alpha),
\Lambda(\theta+m\alpha),\tfrac12\right)
\tag{20}
\]

satisfies every equation in \(\mathcal R_{M,J,1/2}\), has uniformly full
current support, and is uniformly ballistic.

It has no finite period.  The current vector records both
\(\cos\theta\) and \(\sin\theta\) through

\[
\lambda_0-\lambda_1=2a\cos\theta,\qquad
\lambda_2-\lambda_3=2a\sin\theta.
\]

The complex rotation \((3+4i)/5\) has infinite multiplicative order: if it
were a root of unity, its sum with its inverse, \(6/5\), would be a rational
algebraic integer and hence an integer, a contradiction.  Therefore no
positive iterate of (12) fixes a phase.

Both \(M\) and \(J\) are compatible with a rational quitting reward table at
the singleton/pair level: take own singleton rewards zero,
\(r_i(\{j\})=M_{ij}\), and
\(r_i(\{i,j\})=M_{ij}+J_{ij}\).  Higher-coalition rewards remain free.

The relation nevertheless has the stationary fixed point

\[
x_*=(u,u,1/2).
\tag{21}
\]

Indeed, the constant part of (19) is

\[
Mu+\tfrac12Ju=0,
\]

and the renewal equation is \(u=\tfrac12u+\tfrac12u\).  Hence
\(x_*\mathcal R_{M,J,1/2}x_*\).  The irrational orbit therefore proves only
that a full-support source-compatible chain need not itself close; it does
not show that the ambient relation lacks stationary or finite-period states.

This is an exact regression against a **selected-chain closure** claim.  It
is not asserted to lift to an actual canonical maximal ray, to the full
quantitative hard residual with its exploitability witness and source packet,
or to a positive-gap table.  It leaves open whether the normalized identities
always imply existence of some stationary or periodic state elsewhere, and
also whether such a state could be lifted back to the actual quitting source.

## 6. Exact remaining lifting problem

The ballistic source has now been reduced to one of three genuinely stronger
requirements:

1. derive from the actual source-compatible chain a stationary/periodic state
   together with literal roots and payoffs satisfying the absolute Bellman
   identity;
2. select a stationary/periodic state elsewhere in the relation and prove a
   source-faithful lifting theorem; or
3. use maximum-absorption selector provenance and higher-order reward data to
   exclude aperiodic source-compatible chains such as the one represented
   above.

Merely finding a fixed point, periodic point, or invariant measure of the
normalized relation is insufficient unless the lift preserves:

- one actual payoff vector or exact finite payoff cycle;
- the literal product roots at nonzero scale;
- exact endpoint Nash against those payoffs; and
- the original source/return provenance.

## Next question

Does maximum absorption impose an additional closed tangent-maximality
condition on every omega state, strong enough to rule out the rational
rotation obstruction?  That is the first missing field not present in the
current tail-normalized flow certificate.
