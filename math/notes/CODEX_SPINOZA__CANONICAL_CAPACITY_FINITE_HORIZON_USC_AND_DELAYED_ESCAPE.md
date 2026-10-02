# Finite-horizon capacity is USC; a unique-Continue discontinuity escapes to infinity

Author: `CODEX_SPINOZA`

## Status

**Exact ordinary mathematics with checked compact-relation inputs; not
Lean-checked as a packet and not a terminal consumer.**  The capacity-to-go
of the canonical exact Nash--Bellman relation is the increasing supremum of
finite-horizon upper-semicontinuous values.  Bounded total capacity does not
make this convergence uniform and therefore does not by itself make the full
capacity value upper semicontinuous, let alone continuous or lower
semicontinuous.

At a payoff whose only exact root is all Continue, however, every finite and
infinite exact capacity value is zero.  Hence a fixed-capacity sequence
converging to such a payoff has an exact far-end escape: for every growing
horizon there is a finite exact path with vanishing charge in its entire
initial horizon but fixed charge later.  Applied to the small-semantic-seam
arm of the two-sure renewal dichotomy, the common limit therefore yields
either a non-all-Continue exact limiting root or a moving far-end exact
capacity packet.  This sharpens the discontinuity arm but does not yet
consume it.

## Question

Does bounded exact Nash--Bellman capacity make its canonical value
semicontinuous at the common limit of a vanishing horizontal cap-child seam?

Finite horizons are upper semicontinuous.  The full value is upper
semicontinuous only under an additional uniform-exhaustion hypothesis.
Lower semicontinuity still requires persistence of exact root branches and
is not supplied by the closed root graph.

## 1. Payoff-indexed capacity values

Fix a finite quitting game and its canonical bounded payoff box.  The state
used by the checked full boxed charged relation is a pair consisting of a
payoff vector and a simplex root.  The tail state's stored root is irrelevant
in `IsQuittingNashBellmanEdge`: outgoing predecessors depend only on the tail
payoff.  Thus the charged-relation value has a well-defined payoff-indexed
version

\[
 \phi(U)=\Phi((U,q_0)),
\tag{1}
\]

independent of the harmless choice of stored root \(q_0\).

For \(N\in\mathbb N\), let \(\phi_N(U)\) be the maximum total absorption
charge of an exact predecessor path starting at payoff \(U\) and having
length at most \(N\).  The empty path is allowed, so \(\phi_N\ge0\), and

\[
 \phi_N(U)\le\phi_{N+1}(U),
 \qquad
 \phi(U)=\sup_N\phi_N(U).
\tag{2}
\]

The maximum in \(\phi_N\) exists.  A length-at-most-\(N\) path can be padded
by zero-charge all-Continue identity edges whenever that root is exact; more
generally one may take the finite disjoint union of the compact path spaces
of exact lengths \(0,\ldots,N\).  Each path space is a closed subset of a
finite product of the compact boxed state and edge spaces, and charge sum is
continuous.

## 2. Finite-horizon upper semicontinuity

### Theorem 2.1

For every fixed \(N\), the function \(\phi_N\) is upper semicontinuous on the
canonical payoff box.

#### Proof

It is enough to use the sequential criterion, since the box is compact
metrizable.  Let \(U_n\to U\), pass to a subsequence realizing
\(\limsup_n\phi_N(U_n)\), and choose a maximizing path of length at most
\(N\) from each \(U_n\).  Pass again so that the finitely many lengths agree.
Compactness of the finite product gives a convergent subsequence of all path
states and roots.  The exact Nash--Bellman edge graph is closed, so the limit
tuple is an exact path from \(U\).  Continuity of the finite charge sum gives

\[
 \limsup_n\phi_N(U_n)
 \le\phi_N(U).
\tag{3}
\]

This is upper semicontinuity.  QED

The same argument does not prove lower semicontinuity.  That direction would
have to approximate every exact path from \(U\) by paths from nearby
\(U_n\), which is precisely lower hemicontinuity of the exact-root/path
correspondence.  The checked edge graph is closed, hence upper
hemicontinuous, but exact root branches can be born at a limiting tail.

## 3. Uniform exhaustion is the missing infinite-horizon input

Define the nonnegative remainder

\[
 R_N=\sup_U\bigl(\phi(U)-\phi_N(U)\bigr).
\tag{4}
\]

### Proposition 3.1

If \(R_N\to0\), then \(\phi\) is upper semicontinuous.

#### Proof

Equation (4) says exactly that \(\phi_N\to\phi\) uniformly.  A uniform limit
of upper-semicontinuous real functions is upper semicontinuous.  QED

Bounded exact capacity supplies only

\[
 0\le\phi_N(U)\le\phi(U)\le H
\tag{5}
\]

uniformly in \(N,U\).  It does not imply \(R_N\to0\).  The obstruction is a
family of longer and longer exact paths whose fixed amount of capacity moves
beyond every fixed row horizon.

One sufficient condition illustrates the distinction.  Suppose there is
\(a>0\) such that every exact root in the whole box is either all Continue
or has absorption at least \(a\).  A zero-absorption product root is literally
all Continue and gives an identity edge.  Under the capacity bound \(H\), a
path has at most \(\lfloor H/a\rfloor\) nonidentity edges.  Deleting identity
edges shows

\[
 \phi=\phi_{\lfloor H/a\rfloor},
\tag{6}
\]

so Theorem 2.1 makes \(\phi\) upper semicontinuous.  The actual quitting
relation has no such global absorption gap in general; exact roots may
approach all Continue with arbitrarily small positive absorption.

Even (6) supplies only upper semicontinuity.  It does not supply lower
semicontinuity, because a positive exact root present at the limit need not
persist to nearby tails.

## 4. Unique all-Continue limit and delayed capacity escape

### Theorem 4.1

Let \(U_*\) be a payoff vector for which all Continue is the unique exact
product root.  Then

\[
 \boxed{\phi_N(U_*)=\phi(U_*)=0\quad\text{for every }N.}
\tag{7}
\]

If \(U_n\to U_*\), then for every fixed \(N\),

\[
 \phi_N(U_n)\longrightarrow0.
\tag{8}
\]

Suppose additionally that \(\phi(U_n)\ge c>0\).  Then there are indices
\(n(N)\to\infty\) and finite exact predecessor paths \(P_N\) from
\(U_{n(N)}\) such that

\[
 \operatorname{charge}(P_N)\ge c/2,
 \qquad
 \operatorname{charge}(P_N\upharpoonright N)\longrightarrow0.
\tag{9}
\]

Consequently, for all large \(N\), the suffix strictly after the first
\(N\) rows carries charge at least \(c/3\).

#### Proof

At \(U_*\), every first exact root is all Continue.  Its predecessor payoff
is again \(U_*\) and its charge is zero.  Induction makes every finite exact
path constant and zero-charge, proving (7).

Theorem 2.1 gives

\[
 0\le\limsup_n\phi_N(U_n)\le\phi_N(U_*)=0,
\]

which proves (8).  For each \(N\), choose \(n(N)\) sufficiently large that
\(\phi_N(U_{n(N)})\le1/N\), and then choose a finite exact path from that
source whose charge is at least \(c/2\).  Its first \(N\) rows have charge at
most \(\phi_N(U_{n(N)})\le1/N\), proving (9).  The remaining suffix has
charge at least \(c/2-1/N\ge c/3\) for large \(N\).  QED

This theorem uses uniqueness only at the limit.  It does not assume an open
unique-all-Continue neighborhood.  If such an open neighborhood exists, the
stronger conclusion is immediate: \(\phi\) is identically zero throughout
that neighborhood, so no positive-capacity source sequence can converge to
it at all.

## 5. Application to the two-sure small-seam arm

In the small-semantic-seam alternative of the reviewed renewal reduction,
there are actual horizontal pairs with payoff coordinates
\(U_n,V_n\to U_*\) and

\[
 \phi(V_n)-\phi(U_n)\ge a_0/2.
\tag{10}
\]

Since \(\phi\ge0\), the high-capacity side satisfies
\(\liminf_n\phi(V_n)\ge a_0/2\).

There are now two exact cases.

1. If the exact root set at \(U_*\) is not the singleton consisting of all
   Continue, then \(U_*\) admits a non-all-Continue exact root.  Every such
   product root has strictly positive absorption.  This is a literal limiting
   charged root, although it is not automatically a root at either finite
   actual source.
2. If all Continue is the unique exact root at \(U_*\), apply Theorem 4.1 to
   \(V_n\) with, for example, \(c=a_0/3\) after discarding finitely many
   terms.  The high-capacity children produce exact paths of total charge at
   least \(a_0/6\), with vanishing charge in every growing initial horizon
   and at least \(a_0/9\) pushed beyond that horizon.

Thus the discontinuity branch cannot remain an unspecified topological
failure.  It is either a limit-born positive exact root or an exact moving
far-end capacity packet.  The latter is the precise all-summable/escaping
clock boundary: every fixed prefix converges to the zero-charge identity,
while a fixed charge survives farther out.

## Sources inspected

- `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`,
  especially `isClosed_quittingNashBellmanEdgeGraph` and the definition of
  `IsQuittingNashBellmanEdge`;
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`;
- `MathUE/ChargedPathBudget.lean`;
- `formalized/OPEN_ALLCONTINUE_BASIN_EXACT_PATH_RIGIDITY.md`;
- `formalized/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`;
- `formalized/VANISHING_RESPONSE_MAXIMAL_ROOT_RESET_REDUCTION.md`; and
- `notes/CODEX_SPINOZA__TWO_SURE_RENEWAL_CAPACITY_BARRIER_MODULUS_FAILURE.md`,
  frozen at SHA-256
  `bf5db04c65cbaa9fc82346773a74537bab2f09a0f1c4ffd7620dad3d25c4a73b`.

## Boundary and nonclaims

- Finite-horizon values are upper semicontinuous, not asserted continuous.
- Uniform boundedness of \(\phi_N\) is not uniform convergence to \(\phi\).
- Theorem 4.1 produces exact finite paths with charge escaping past every
  fixed horizon.  It does not concatenate paths selected from different
  sources, and it does not retain one finite root label at a fixed date.
- These paths are selected from the full canonical boxed capacity relation.
  They are not automatically punishment-floor admissible and therefore do
  not, without a separate floor-repair theorem, instantiate the maintained
  approximate-forward-packet compiler.
- The non-all-Continue limiting root in Section 5 need not be realized at a
  finite actual source; lower hemicontinuity is exactly what is unavailable.
- The delayed packet has fixed total charge, not unbounded charge.  It is not
  by itself a terminal approximate Nash profile or uniform-equilibrium
  payoff.
- If the common limit lies in the checked open strict all-Continue basin, the
  delayed branch is impossible; the current renewed sources are not known to
  converge into that basin.

## Next exact question

Can the delayed exact-capacity paths in (9), whose first growing horizon has
vanishing charge but whose far suffix retains fixed charge, be attached to
the two prescribed sure clocks to produce one persistent-clock chronological
packet?  The missing point is source-compatible reversal: the finite exact
paths grow as predecessors from varying tail sources, while the two actual
sure clocks live in those terminal tails.
