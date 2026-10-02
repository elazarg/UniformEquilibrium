# Quasiconvex exclusion for the full exact root relation

Owner: CODEX_ALEXANDROV.

Mathematical scope: the theorem below is an ordinary mathematical proof, not
checked in Lean. It combines the global-minimum
argument already in
[CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
with the boundary-minimum argument in
[QUITTING_POTENTIAL_EXCLUSION.md](../gpt/QUITTING_POTENTIAL_EXCLUSION.md).
This is a consequence of those arguments, not a claim of an independently new
global-minimum method. The separate packet review is
[QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md](../feedback/QUITTING_POTENTIAL_EXCLUSION__BY_CODEX_ALEXANDROV.md).

The complete parallel note
[CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md](CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md)
has an independent mathematical check, including its weaker hypothesis of
exact-edge drift only on \(K'\). Its upper-coordinate probe adjustment is
valid. The feedback above records that independent review in detail.

## Exact question and conclusion

Let there be \(n\ge2\) players with independent Boolean root actions. Give
each nonempty quitting coalition \(S\) a reward vector \(r(S)\in\mathbb R^n\),
with \(|r_j(S)|\le M\), where \(M\ge0\). Write \(r^i=r(\{i\})\) and

\[
s_i=r_i^i,\qquad
K=[-M-2,M+2]^n,\qquad K'=[-M-1,M+1]^n,\qquad
C=\prod_j[s_j,M+1].
\]

For a product root \(q\in[0,1]^n\), \(a(q)\) is the probability of at least
one Quit and \(F(v,q)\) is the expected reward at that root, with payoff
vector \(v\) if all players Continue. A root is exact Nash against \(v\)
when each player's prescribed independent mixture maximizes that player's
one-stage expected payoff against the other root marginals. This does not
assert behavioral realizability of the supplied \(v\).

Suppose \(P:K\to\mathbb R\) is continuous on \(K'\), agrees near \(C\) with
a differentiable function defined on an open neighborhood of \(C\), and
satisfies

\[
P(v)-P(F(v,q))\ge a(q)
\tag{A}
\]

for every \(v\in K\) and every exact Nash root \(q\) against \(v\).
Every displayed target belongs to \(K\), since it is a convex combination
of \(v\) and the coalition reward vectors.

**Theorem.** \(P\) cannot be quasiconvex on \(C\). No matrix-Q condition,
punishment normality, positive singleton, or positive tolerance is assumed.
In particular, every polynomial potential for the packet's full robust
relation violates quasiconvexity on \(C\), regardless of its singleton matrix.

## Proof

The packet's exact repaired singleton probe gives, at each \(x\in C\) with
\(x_i=s_i\),

\[
\nabla P(x)\cdot(x-r^i)\ge1. \tag{B}
\]

For completeness, put \(d_i=0\) and
\(d_j=(r_j(\{i,j\})-r_j^i)_+\) for \(j\ne i\). Let only \(i\) quit with
probability \(h\in(0,1)\), and use continuation
\(v_h=x+h d/(1-h)\). Player \(i\) is indifferent; each other player's
Continue-minus-Quit payoff is
\((1-h)(x_j-s_j)+h(d_j-r_j(\{i,j\})+r_j^i)\ge0\).
Thus the root is exact Nash, with absorption \(h\) and target
\(u_h=(1-h)v_h+hr^i\). Both endpoints lie in \(K\) for small \(h\).
Differentiability at \(x\) gives
\((P(v_h)-P(u_h))/h\to\nabla P(x)\cdot(x-r^i)\), proving (B).

Continuity supplies a global minimizer \(z\in K'\). Finite mixed Nash
existence supplies an exact root against \(z\). Its successor lies in \(K'\),
so (A) and minimality imply

\[
0\le a(q)\le P(z)-P(F(z,q))\le0.
\]

Hence \(q\) is All-Continue. Exact Nash then implies \(z_i\ge s_i\) for
every \(i\), and \(z\in C\). In fact \(z_i>s_i\) for every \(i\): if
\(z_i=s_i\), (B) gives a strictly negative directional derivative along
\(r^i-z\), whereas the entire segment from \(z\) to \(r^i\) lies in \(K'\)
and minimality makes that derivative nonnegative. The same reasoning applies
to every global minimizer on \(K'\).

Let \(B=\{x\in C:\exists i,\ x_i=s_i\}\). Compactness therefore gives

\[
\min_C P=\min_{K'}P<\min_B P. \tag{C}
\]

Choose a minimizer \(x\) of \(P\) on \(B\), set
\(J=\{i:x_i=s_i\}\), and let \(g=\nabla P(x)\). If \(J=\{i\}\),
one-coordinate variations for every \(j\ne i\) show that \(g_j=0\) at
interior coordinates and \(g_j\le0\) at upper coordinates. Since
\(M+1-r_j^i\ge1\) and \(x_i-r_i^i=0\), this makes
\(g\cdot(x-r^i)\le0\), contrary to (B).

Thus \(|J|\ge2\). Every feasible one-coordinate variation now preserves
membership in \(B\), yielding

\[
g_j\ge0\ (x_j=s_j),\qquad
g_j=0\ (s_j<x_j<M+1),\qquad
g_j\le0\ (x_j=M+1).
\]

By (B), \(g\ne0\). Consequently \(g\cdot(v-x)>0\) for every
\(v\in\operatorname{int}C\). If \(P\) were quasiconvex on \(C\), then
\(P(v)\le P(x)\) would imply \(g\cdot(v-x)\le0\), by differentiating
the segment inequality at \(x\). But (C) and continuity supply a point
\(v\in\operatorname{int}C\) with \(P(v)<P(x)\). This is a contradiction.

## Scope and dependencies

This proof excludes a class of supplied full-relation potentials. It does
not produce an equilibrium, exclude all polynomials, or convert first-order
face inequalities into the full potential inequality. The latter distinction
is essential: for \(R_{12}=R_{21}=-1\), \(R_{11}=R_{22}=0\), and
\(f(x)=x_1+x_2\) on \([0,1]^2\), each lower-face drift
\(\nabla f(x)\cdot(x-R_i)\) is at least one. Thus the purely analytic
face theorem cannot simply drop Q. Likewise a quadratic convexification of
\(P\) need not preserve (A), so this proof does not by itself remove Q from
the packet's quantitative negative-curvature bound.

The source check read `exists_isZeroQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/NashExistence.lean`), whose statement has
no payoff, normality, or matrix restriction, and the full relation's
`IsQuittingFloorFreeRobustEdge`
(`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`). The
review linked above records the remaining bounded dependency inventory.
No Lean build was run. The full-relation strengthening retains its explicit
continuity hypothesis and is distinct from the matrix-only analytic theorem
and its quantitative curvature application.
