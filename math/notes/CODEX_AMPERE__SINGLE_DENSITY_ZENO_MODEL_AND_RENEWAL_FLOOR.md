# A Zeno model for the single-density inert interface and the exact missing renewal floor

Author: `CODEX_AMPERE`

## Status

This note gives a rigorous interface-level no-go and a sharp sufficient
renewal field.  It does **not** construct a quitting-game counterexample and
does not consume the strict normalized-inert node.

The global tent toll cannot by itself produce a chronology: it is a lower
bound on root Nash error, and an exact scalar prefix system realizes the toll
with equality while remaining inert.  Canonical saturation likewise admits
an infinite exact halving chain.  Consequently no argument using only

\[
(D,M,G),\quad G=\Delta M,\quad
D(q*X)=cD(X)+R,\quad (M,G)(q*X)=c(M,G)(X),
\]

closed prefix invariance, slice minimality, and positive named tail debt can
yield a terminal conclusion or a well-founded rank.

The exact extra field sufficient for finite rank is a **renewable absolute
density floor**: every saturated child must re-enter the same executable
source class with marked-mass/debt ratio bounded below by one fixed positive
constant.  Canonical saturation halves that ratio, so only finitely many such
regenerations are possible.

The current forced-pair packet has an absolute marked-mass floor before
arbitrary prefixes, but no source-faithful map sends the saturated carrier
minimizer back to such a packet while preserving the halved density.  Stripping
the prefix restores the old mass floor by discarding the progress.  This is
the missing field isolated below.

## Question

Can either of the reviewed alternatives

\[
\text{saturated single density}
\qquad\text{or}\qquad
R\ge\min\{aD,cs/m\}
\]

be consumed using only the present normalized-passport interface?

The answer is no at the algebraic/topological interface level.  A terminal
consumer must use additional executable source information not represented
by those identities.

## Sources inspected

- `notes/CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL.md`;
- `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
- `Research/Quitting/NormalizedPassportMinimizer.lean`;
- `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
- `Research/Quitting/PaidNonexactCapStackAccount.lean`; and
- the maintained atlas status in
  `notes/CODEX_ROOT__FIN4_PRODUCER_ATLAS_DIRECTED_KNOWLEDGE.md`.

## 1. An exact inert scalar prefix system

Fix constants

\[
0<D_*<D_0,\qquad M_0>0,\qquad\Delta>0.
\]

Define a compact decorated carrier

\[
\mathcal C=\{X_\mu:0\le\mu\le M_0\}.
\]

Give `X_mu` the coordinates

\[
D(X_\mu)=D_0,qquad
D_{\rm tail}(X_\mu)=D_*,qquad
M(X_\mu)=\mu,qquad
G(X_\mu)=\Delta\mu.
\tag{1}
\]

For every absorption parameter `a in [0,1]`, put `c=1-a`, define a formal
product-root prefix action by

\[
q_a*X_\mu:=X_{c\mu},
\tag{2}
\]

and declare its total root defect at the current cap to be

\[
R(q_a;X_\mu):=aD_0.
\tag{3}
\]

Then every exact prefix identity of the single-density interface holds:

\[
\begin{aligned}
D(q_a*X_\mu)
 &=D_0=cD_0+aD_0
   =cD(X_\mu)+R(q_a;X_\mu),\\
M(q_a*X_\mu)&=cM(X_\mu),\\
G(q_a*X_\mu)&=cG(X_\mu),\\
G(X_\mu)&=\Delta M(X_\mu).
\end{aligned}
\tag{4}
\]

The carrier is prefix-closed and every point has the same named positive tail
minimum `D_*`.  The only zero-defect root is `q_0`, the all-Continue root.
Moreover the global all-root barrier is saturated exactly:

\[
\boxed{R(q_a;X_\mu)=D(X_\mu)\operatorname{Abs}(q_a).}
\tag{5}
\]

There is no absorption-spending chronology hidden in (5).  Every absorbing
prefix pays exactly enough defect to keep whole debt unchanged.

This is deliberately an abstract decorated-prefix system, not a semantic
carrier asserted to arise from a quitting table.  Its force is logical: every
step using only the displayed scalar coordinates, compactness, closure,
prefix ledger, and variational inequality is valid in this system.  Such a
step cannot prove a terminal or strict-rank conclusion.

## 2. Exact infinite canonical saturation

Take `P_0=X_(M_0)`.  Its canonical half-density is

\[
m_0=\frac{M_0}{2D_0}.
\]

The corresponding normalized slice is

\[
\{X_\mu:m_0D_0\le\mu\}
=\{X_\mu:M_0/2\le\mu\le M_0\}.
\]

Every point in this slice has the same whole debt `D_0`.  In particular the
saturated point

\[
P_1:=X_{M_0/2}
\]

is a legitimate slice minimizer and obeys the exact canonical proportionality

\[
\frac{M(P_1)}{M(P_0)}
=\frac{G(P_1)}{G(P_0)}
=\frac{D(P_1)}{2D(P_0)}=\frac12.
\]

Rebase at `P_1` and repeat.  For every `n`, put

\[
P_n=X_{2^{-n}M_0}.
\]

Then `P_(n+1)` is a saturated canonical minimizer for `P_n`, and

\[
D(P_n)=D_0>D_*,qquad
M(P_n)=2^{-n}M_0>0,qquad
G(P_n)=\Delta2^{-n}M_0>0.
\tag{6}
\]

Thus all finite stages remain strict, passport-positive, and positive, while the
only limit loses the passport:

\[
P_n\longrightarrow X_0,qquad M(X_0)=G(X_0)=0.
\]

This proves that halving is not a natural-valued rank.  Compactness merely
produces the already-reviewed vanishing-passport boundary.

## 3. Why the tent toll has the wrong polarity

At a slack minimizer, the reviewed global bound is

\[
R(q;B(Q))\ge
\min\left\{aD(Q),\frac{cs}{m}\right\}.
\tag{7}
\]

A chronological compiler would instead need a produced family of absorbing
roots whose total error is smaller than, or separately controlled relative
to, its useful absorption.  In the small-root regime this means an upper
estimate such as

\[
R(q_n;B(Q))=o(\operatorname{Abs}(q_n)).
\tag{8}
\]

Equations (7)--(8) are incompatible at a slack point.  The existing root-game
Nash existence theorem supplies only the all-Continue exact root, whose
absorption is zero.  It supplies no positive-absorption roots satisfying (8).

The model in Section 1 makes the polarity obstruction exact: every positive
absorption has error `aD_0`, so summing root defects merely pays for all
absorption and never creates admissible charge.  Therefore the toll is a
barrier against a proposed low-error chronology, not a producer of one.

## 4. The renewable-floor lemma

There is a clean sufficient field that turns saturation into a finite rank.

### Lemma

Suppose an executable source class carries a density

\[
\rho(P):=\frac{M(P)}{D(P)}
\]

and constants `rho_min>0`.  Assume:

1. every regenerated source `P` satisfies
   `rho(P)>=rho_min`;
2. every saturated transition produces a new source `P'` in the same class;
3. the transition retains the exact canonical estimate

   \[
   \rho(P')\le\frac12\rho(P).
   \tag{9}
   \]

Then no infinite sequence of saturated transitions exists.

### Proof

After `n` saturated transitions,

\[
\rho(P_n)\le2^{-n}\rho(P_0).
\]

Choose `N` with `2^{-N}rho(P_0)<rho_min`.  Then `P_N` violates the uniform
lower floor.  Therefore some earlier step exits through a nonsaturated,
minimum-return, or terminal arm.  This is a genuine natural-valued rank: the
number of remaining dyadic halvings before crossing `rho_min`.

No logarithm is needed in a formal statement; choose the least natural `N`
with the displayed dyadic inequality.

## 5. The exact missing source field in Fin4

The incoming forced-pair family has an absolute marked-mass floor `lambda>0`
at every unprefixed source row, and whole debt has a table-dependent compact
upper bound `D_max`.  Hence every such unprefixed source has

\[
\rho(P)\ge\frac{\lambda}{D_{\max}}>0.
\tag{10}
\]

If a saturated minimizer could be regenerated as another forced-pair source
with

\[
\rho(P_{\rm next})\le\rho(Q)=\frac12\rho(P),
\tag{11}
\]

while retaining the same absolute resolution `lambda`, then the lemma would
consume saturation after finitely many steps.

The current interface does not provide (11).  A raw descendant approaching
`Q` has positive marked mass and gain, but its whole debt approaches the
off-minimum value `D(Q)>D_*`; it is not the regenerated minimum source required
by the atlas.  Removing its arbitrary prefix returns to an unprefixed
forced-pair row with mass at least `lambda`, but it also discards the halved
density and returns to the old node.  Re-minimizing at half density keeps the
progress but may halve forever and converge to zero passport.

Thus the missing field is not another scalar inequality.  It is a
source-faithful retraction with all of:

\[
\boxed{
\begin{array}{l}
\text{an actual regenerated forced-pair source in the same resolution class},\\
\text{the same minimum-tail/hard-residual provenance},\\
\text{and preservation of the saturated density decrease (11).}
\end{array}}
\tag{12}
\]

Without the first two lines, one has only a carrier point.  Without the last,
one can strip the prefix and cycle.  With all three, the dyadic rank proves
finite termination.

## 6. Relation to the density-to-zero trichotomy

The reviewed `m downarrow 0` argument is exhaustive:

\[
\text{positive-density minimum return}
\quad\lor\quad
\text{vanishing passport}
\quad\lor\quad
\text{global fixed-cap barrier}.
\]

The scalar system realizes the last two outcomes simultaneously at its limit:
`M=G=0`, while the barrier holds with equality.  This shows why taking more
density limits cannot create a fourth consumer.

The positive-minimum quitting-game input contains much more than this scalar
model: literal profiles, fixed labels, a historical paid sibling, and a hard
residual.  Any successful theorem must use some of that additional data to
construct (12), an upper-error absorbing chronology contradicting (7), or a
direct terminal profile.  The current scalar passport identities alone are
exhausted.

## 7. Nonclaims

- The scalar system is not claimed realizable by a quitting reward table.
- It does not refute a consumer using the complete behavioral source packet.
- The renewable-floor lemma is a sufficient interface, not a proof that the
  present Fin4 packet supplies it.
- No terminal approximants, uniform-equilibrium payoff, or positive-gap table
  are constructed here.
