# Chronological occupation and return duality

This file records an abstract consumer. Its input is already a compact system
of actual, composable chronological edges. It does not construct such a system
from a quitting game.

## Typed chronological edge system

Let \(C\) be a compact metric state space and \(E\) a compact metric edge
space, with continuous maps

\[
s,t:E\to C.
\]

An edge from \(x\) to \(y\) must represent a literal finite executable block
\(B\) satisfying

\[
\operatorname{profile}(x)=B\star\operatorname{profile}(y).
\tag{1}
\]

The orientation is current source to reached continuation. Constructing the
current source by prefixing the continuation does not also create a reverse
chronological edge.

Assume seriality:

\[
\forall x\in C\ \exists e\in E,
\qquad s(e)=x,\quad t(e)\in C.
\tag{2}
\]

For application to quitting games, an edge must additionally carry the exact
admissibility, punishment, law, and seam data required by the intended
compiler. Compactness and closedness of this enriched actual edge space are
assumptions here, not consequences of the raw profile compactness theorem.

## Invariant occupation

An invariant occupation measure is a probability \(\pi\) on \(E\) such that

\[
s_\#\pi=t_\#\pi.
\tag{3}
\]

Every compact serial system has one. Choose an infinite path

\[
x_0\xrightarrow{e_0}x_1\xrightarrow{e_1}\cdots
\]

and take a weak limit of

\[
\pi_N=\frac1N\sum_{n<N}\delta_{e_n}.
\]

For every continuous \(f:C\to\mathbb R\),

\[
\int(f\circ t-f\circ s)\,d\pi_N
=\frac{f(x_N)-f(x_0)}N\longrightarrow0,
\]

which proves (3).

Consequently, the alternative “a compact serial component has no invariant
occupation” is vacuous. It becomes meaningful only after additional
realization constraints make the admissible edge set nonclosed or nonserial.

## Positive-charge fixed-target recurrence

Let \(q:E\to[0,Q]\) be bounded, Borel, and nonnegative. Suppose an invariant
occupation satisfies

\[
\int q\,d\pi>0.
\tag{4}
\]

Let \(z:C\to Z\) be a Borel observation into a compact metric semantic space.
Then there are \(\delta>0\) and one \(v\in Z\) such that, for every
\(\varepsilon>0\), there is a finite composable path whose two observed
endpoints are within \(\varepsilon\) of \(v\) and which contains an edge
\(e\) with

\[
q(e)\ge\delta.
\tag{5}
\]

Proof: choose \(\delta>0\) for which the invariant occupation assigns positive
mass to \(\{q\ge\delta\}\). Disintegrate the occupation into a stationary
edge process and pass to an ergodic component that still sees this set.
Choose \(v\) in the support of the stationary semantic law. Recurrence gives
infinitely many visits to every neighborhood of \(v\), and ergodicity gives
infinitely many high-charge edges. Bracket one such edge between two visits
to the prescribed neighborhood.

The theorem is stronger and more directly usable than a statement about a
large cumulative sum of possibly vanishing edge charges. It supplies a fixed
single-edge threshold.

### Quitting-game decoder required

To invoke an existing payoff-near-return compiler, every abstract edge must
decode to an admissible quitting-game edge with:

1. the same source and target semantic observations;
2. the exact orientation expected by the compiler;
3. literal source-matched block realization;
4. charge equal to the compiler's absorption or payoff charge; and
5. all punishment-floor and seam certificates.

For a macro-edge, either one constituent edge must retain the fixed threshold,
or a separate cumulative-charge consumer is needed. Additivity alone does not
turn many arbitrarily small charges into the required fixed charged edge.

The existence of positive edges somewhere in a component is also
insufficient. What matters is a positive mean for some invariant occupation;
all invariant occupations might avoid the positive edges.

## Finite rank

Let \(\rho:C\to\{0,1,\ldots,R\}\) and suppose

\[
\rho(t(e))\le\rho(s(e))
\quad(e\in E).
\tag{6}
\]

For every invariant occupation,

\[
0=
\int\bigl(\rho(s(e))-\rho(t(e))\bigr)\,d\pi(e).
\]

The integrand is nonnegative, so strict rank-decreasing edges have zero
occupation mass. A rank exit must therefore be forced; merely making a
decreasing edge available does not consume a recurrent component.

## Unconstrained duality

If \(q\) is continuous, the invariant-flow value has the exact dual

\[
\max_{\pi:\,s_\#\pi=t_\#\pi}\int q\,d\pi
=
\inf_{f\in C(C)}
\max_{e\in E}
\bigl(q(e)+f(t(e))-f(s(e))\bigr).
\tag{7}
\]

For an invariant measure the coboundary integrates to zero. For a
noninvariant measure, a continuous function separates the source and target
marginals, and scaling it sends the corresponding inner infimum to
\(-\infty\). Compact minimax duality then gives (7).

## Constrained separation

Let \(\Delta:E\to\mathbb R^m\) be continuous. If the constrained invariant
set

\[
\left\{\pi:s_\#\pi=t_\#\pi,
\ \int\Delta\,d\pi=0\right\}
\]

is nonempty, its charge optimization has the Lagrange dual

\[
\max_{\substack{\pi:\,s_\#\pi=t_\#\pi\\
\int\Delta\,d\pi=0}}
\int q\,d\pi
=
\inf_{\substack{f\in C(C)\\\lambda\in\mathbb R^m}}
\max_{e\in E}
\left(q(e)+f(t(e))-f(s(e))+
\lambda\cdot\Delta(e)\right).
\tag{8}
\]

If the constrained set is empty, separation gives \(f,\lambda\), and
\(\eta>0\) such that, after a possible sign reversal,

\[
f(t(e))-f(s(e))+\lambda\cdot\Delta(e)\ge\eta
\quad(e\in E).
\tag{9}
\]

This is an augmented separator, not automatically a Lyapunov exit. Along a
path it yields

\[
f(x_N)-f(x_0)
+\lambda\cdot\sum_{n<N}\Delta(e_n)
\ge N\eta.
\tag{10}
\]

It forces exit only when the cumulative displacement is bounded, telescopes,
or is otherwise controlled. If \(\Delta(e)=g(t(e))-g(s(e))\), the zero-mean
constraint is automatic for invariant occupations and adds no information.

## Exact scope

The results above consume a compact actual chronological component once:

- an invariant occupation of positive admissible mean charge is available
  and its edges decode to the existing near-return compiler; or
- a rank or separation certificate is proved to force an exit.

They do not prove that the Fin4 hard residual admits a compact, closed,
serial, source-matched chronological edge system. They do not turn horizontal
source transformations into temporal edges, and they do not establish the
needed charge decoder.
