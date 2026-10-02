# CODEX_MINER — Fin5 scalar seam/box certificate classification

Author: `CODEX_MINER`

Status: **INDEPENDENTLY REVIEWED/PASS as ordinary mathematics; internal,
no export.**

Independent review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION__BY_CODEX_RAMSEY.md).

The canonical reward-box rows are redundant after exact nonseam Bellman
propagation, but a closing-seam row can be indispensable in a minimal affine
infeasibility certificate.  Section 5 gives an exact rational `Fin 5`
quitting-table/root example with a positive nonempty atom on every quiet face.
It is a source-interface separation, not a counterexample to uniform-equilibrium
existence and not an unconditional producer.

This note branches from
[`CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md`](CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md).

## 1. Exact scalar normal form

Fix a reward table bounded coordinatewise by `M >= 0`, five product roots
`x^t`, and one payoff coordinate `i`.  Write

\[
 F_t(z)=a_t+\beta_tz,
 \qquad
 \beta_t=\Pr_{x^t}(\hbox{all Continue}).                 \tag{1.1}
\]

The affine form is exactly
`quittingRootExpectedPayoff_eq_absorbingContribution_add`.  Since the
nonempty root outcomes have total mass `1-beta_t`,

\[
 0\le\beta_t\le1,
 \qquad
 |a_t|\le M(1-\beta_t).                                \tag{1.2}
\]

Choose the cut scalar `x=v_0(i)`.  Impose exact Bellman recursion at the four
nonseam phases by setting

\[
 v_4=F_4(x),\quad v_3=F_3(v_4),\quad
 v_2=F_2(v_3),\quad v_1=F_1(v_2).                      \tag{1.3}
\]

Every `v_t` is affine in `x`.  The phase-zero closing map is

\[
 \Phi(x):=F_0(v_1(x))=A+Bx,
 \qquad B=\prod_{t=0}^4\beta_t\in[0,1].               \tag{1.4}
\]

An approximate closing seam of size `delta >= 0` is the pair of affine rows

\[
 x-\Phi(x)-\delta\le0,
 \qquad
 \Phi(x)-x-\delta\le0.                                \tag{1.5}
\]

For a phase root, the endpoint difference of player `i` has the form

\[
 G_{i,t}(z)=c_{i,t}-m_{i,t}z,
 \qquad
 m_{i,t}=\Pr(\hbox{every opponent of }i\hbox{ Continues}). \tag{1.6}
\]

Thus the two exact approximate-Nash support rows are

\[
 p^C_{i,t}G_{i,t}(v_{t+1})-\varepsilon\le0,
 \qquad
 -p^Q_{i,t}G_{i,t}(v_{t+1})-\varepsilon\le0,          \tag{1.7}
\]

where `p^C` and `p^Q` are the root marginal masses.  Substitution from (1.3)
makes every phase row affine in the one cut scalar.  This proves the claimed
coordinate separation: successor payoffs and endpoint differences read no
other continuation coordinate.  Recombining the five independently chosen
scalar coordinates is legitimate for these fixed common roots.

This one-variable reduction is specific to **exact propagation at the four
nonseam phases**.  If independent Bellman errors at all five phases remain
free variables, they cannot be silently eliminated by the one-dimensional
interval theorem.

## 2. Canonical payoff-box rows are redundant

### Proposition 2.1

If `x in [-M,M]`, every value in (1.3) also lies in `[-M,M]`.  Consequently
the canonical `quittingNashBellmanBox` rows for all five propagated values
may be deleted before constructing the affine interval system.

### Proof

From (1.2), for every `|z|<=M`,

\[
 |F_t(z)|\le |a_t|+\beta_t|z|
 \le M(1-\beta_t)+\beta_tM=M.                        \tag{2.1}
\]

Apply (2.1) successively in (1.3).  This is the scalar content of
`abs_quittingRootExpectedPayoff_le_bound` in
`Quitting/Bellman/Finite/NashBellmanSpine.lean`.  Hence every intermediate
box inequality is true throughout the cut interval, rather than merely
compatible with the other rows.  QED.

This conclusion concerns the canonical symmetric reward cube.  An extra
punishment floor, target interval, or externally imposed lower bound is not a
canonical box row and need not be harmless.  Likewise, if approximate errors
are inserted into (1.3), exact cube preservation no longer proves the same
statement without enlarging or separately controlling the errors.

## 3. The seam family is feasible but not harmless against phase rows

By Proposition 2.1, the composite `Phi` maps `[-M,M]` into itself.  It has a
fixed point in that interval.  Explicitly, if `B<1`, then

\[
 x_*={A\over1-B}\in[-M,M];                            \tag{3.1}
\]

if `B=1`, (1.2) forces every phase with `beta_t=1` to have zero absorbing
contribution and the composite is the identity.  Thus (1.5) is always
feasible by itself for every `delta>=0`.

It follows that neither a singleton seam row nor a seam--seam pair can be a
minimal infeasible certificate.  This does **not** imply that seam rows are
harmless after phase-Nash rows are added: a face row can require a cut value
strictly to one side of the seam interval.

For exact closure in the absorbing case `B<1`, the shortest formulation is to
evaluate every phase-Nash row at the unique `x_*`.  There is then no free
interval variable and no box test.  The interval formulation is useful only
when one deliberately allows a nonzero closing mismatch.

## 4. Exact use of `finiteAffineIntervalFeasible_iff`

Normalize the cut interval by

\[
 x(w)=(1-w)(-M)+wM,
 \qquad 0\le w\le1.                                  \tag{4.1}
\]

This remains valid at `M=0`: both endpoints and every `x(w)` are zero.  If
`g(x)` is affine, then

\[
 g(x(w))=(1-w)g(-M)+wg(M).                           \tag{4.2}
\]

Therefore `Math.finiteAffineIntervalFeasible_iff` applies with `lower` and
`upper` equal to the endpoint evaluations of every phase row and both seam
rows.  Negating its criterion gives an infeasibility certificate of size at
most two:

1. one row is positive at both endpoints; or
2. a decreasing/lower-bound row `(L>0>=U)` and an
   increasing/upper-bound row `(L'<=0<U')` violate

   \[
   L U'\le U L'.                                     \tag{4.3}
   \]

For the exact-propagation/canonical-box system, inclusion-minimal
certificates have precisely these possible type patterns:

- one phase-Nash row;
- two phase-Nash rows; or
- one phase-Nash row and one seam row.

No canonical box row occurs by Proposition 2.1.  No seam singleton or
seam--seam pair occurs because the seam family contains `x_*`.  Phase--phase
crossings are structurally possible: the affine rows
`3/4-w<=0` and `w-1/4<=0` are the two endpoint-Nash orientations in (1.7)
and form a minimal crossed pair.  The next section shows that the remaining
phase--seam pattern occurs in literal `Fin 5` quitting data, even with all
five desired nonempty face atoms.

If one instead places `x` in a larger ambient interval and encodes
`[-M,M]` as two extra rows, box--phase crossed pairs can of course appear;
for example `x<=1` and `3/2-x<=0`.  Such a certificate is a normalization
artifact: on the canonical domain `[-1,1]`, the phase row alone is infeasible.

## 5. Exact Fin5 phase--seam crossed certificate

Let the players be `0,1,2,3,4`.  Define the reward coordinate of player `0`
by

\[
 r_{\{0,1\}}(0)=1,
 \qquad
 r_{\{0,q\}}(0)=-1\quad(q=2,3,4),                   \tag{5.1}
\]

and set every other terminal reward coordinate, including all singleton
rewards, to zero.  The reward bound is `M=1`.

At phase `t`, exactly the player `q_t` mixes Quit with probability `1/2`,
where

\[
 (q_0,q_1,q_2,q_3,q_4)=(2,3,4,2,1),                \tag{5.2}
\]

and every other player Continues surely.  Since `q_t != t`, phase owner `t`
Continues surely.  Each phase has the nonempty opponent-only atom `{q_t}` of
mass `1/2`, so the quiet-face atom hypotheses hold with `rho_t=1/2`.

Player `0` Continues surely at every phase.  Its payoff on every singleton
`{q_t}` is zero, hence every scalar Bellman map is

\[
 F_t(z)=\tfrac12z.                                   \tag{5.3}
\]

With `x=v_0(0)`, exact propagation through phases `4,3,2,1` gives

\[
 v_4=\tfrac12x,\quad v_3=\tfrac14x,\quad
 v_2=\tfrac18x,\quad v_1=\tfrac1{16}x.             \tag{5.4}
\]

The phase-zero closing map is `Phi(x)=x/32`, so its upper seam row is

\[
 \frac{31}{32}x-\delta\le0.                         \tag{5.5}
\]

For player `0`, forcing Quit against the phase-`t` opponents gives
`r_{\{0,q_t\}}(0)/2`, while forcing Continue gives `v_{t+1}(0)/2`.  Thus its
only supported endpoint row is

\[
 \frac12\bigl(r_{\{0,q_t\}}(0)-v_{t+1}(0)\bigr)\le0. \tag{5.6}
\]

At phases `0,1,2,3`, (5.1) makes this row automatic throughout the canonical
box because it asks that the successor value be at least `-1`.  At phase `4`,
the successor is `x` and (5.6) asks

\[
 x\ge1.                                              \tag{5.7}
\]

Every other player's reward coordinate is identically zero, so all of their
Bellman and root-Nash rows are exact at the zero annotation.

At `delta=0`, the seam requires `x=0`, while the only nontrivial phase row
requires `x=1`.  Each condition is separately feasible, but together they are
not.  In the normalized variable `w=(x+1)/2`, the phase row and the upper
seam row have endpoint pairs

\[
 (L_F,U_F)=(1,0),
 \qquad
 (L_S,U_S)=\left(-\frac{31}{32},\frac{31}{32}\right). \tag{5.8}
\]

They violate the checked cross-product criterion exactly:

\[
 1\cdot\frac{31}{32}
 >0\cdot\left(-\frac{31}{32}\right).                \tag{5.9}
\]

The same minimal phase--seam obstruction persists for every
`0<=delta<31/32`.  This is a literal rational product-root example; it is not
an arbitrary affine array.  It also satisfies all five nonempty atom floors,
so atom contraction cannot remove the scalar closing seam.

The provenance claim stops there for this printed table.  Every reward
coordinate except player `0` is identically zero, and player `0` has no
positive outward omitted-player gap on face `0`.  Thus this example does
**not** co-realize the full omitted-player gap provenance on all five faces;
it rules out elimination using the scalar algebra, canonical reward bounds,
and positive atom floors alone.

Ramsey's independently reviewed stronger completion,
[`FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION`](CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION.md),
adds an actual exact deleted-game suffix and a strictly positive
omitted-player outward gap on every face while preserving the phase--seam
obstruction.  Euler's audit is
[`PASS`](../feedback/CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION__BY_CODEX_EULER.md).
That completion is still a local/source-compatible separation: its five
sources are unrelated and its ambient game has an exact all-Quit equilibrium,
so it does not supply a cardinal-minimal positive-gap source or a consumer.

There is no contradiction with the conditional cyclic seed theorem.  The
example proves that the roots do not admit simultaneously small local defect
and small closing seam; it does not satisfy the seed theorem with both errors
zero.

## 6. Source and duplicate audit

Inspected declarations/files:

- `Math.finiteAffineIntervalFeasible_iff` in
  `MathUE/FiniteAffineIntervalFeasibility.lean`;
- `quittingRootExpectedPayoff_eq_absorbingContribution_add` in
  `Quitting/Stationary/Payoff.lean`;
- `IsεQuittingRootEndpointNash` in
  `Quitting/Root/SuccessorCertificate.lean`;
- `abs_quittingRootExpectedPayoff_le_bound` and `quittingNashBellmanBox` in
  `Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- `quittingRootSequenceBackwardPayoff_sub` and
  `quittingRootSequence_fixedContinuation_unique` in
  `Quitting/Cycles/CyclicPeriodicExtension.lean`; and
- the cyclic selection/contraction theorems in
  `Quitting/Cycles/PeriodicCompiler.lean` and
  `Quitting/Cycles/CycleMismatchContraction.lean`.

The only checked use of `finiteAffineIntervalFeasible_iff` found is the
collision-rate elimination in
`Quitting/Boundary/Repair/CollisionRateFiniteDispatch.lean`; it has no cyclic
seam or propagated payoff-box rows.  The existing periodic compiler selects
the actual cyclic terminal value and gives exact/quantitative attachment once
the fixed roots and root-Nash data are supplied.  It does not prove that face
constraints are compatible with the closing fixed point.  The companion-map
contraction in `CycleMismatchContraction.lean` likewise starts after exact
endpoint Nash and therefore does not eliminate the phase--seam crossing in
Section 5.

The current codimension-one quiet-face source supplies unrelated reached
suffix/root families, and its chosen atom may be empty.  Section 5 shows that
making all five atoms nonempty does not remove the scalar seam.  Ramsey's
reviewed stronger completion shows that even adding exact deleted-game
suffixes and positive omitted-player outward gaps on all five faces does not
remove it at the local-source level.  Neither table realizes the global
positive-minimum/cardinal-minimal provenance that a conjecture-facing
consumer could still exploit.

## 7. Consequence for the Fin5 seed interface

The honest one-scalar producer output is not “two literal face rows.”  After
canonical normalization it is the finite alternative

1. one phase row is infeasible on the entire reward interval;
2. two phase rows cross; or
3. one phase row crosses one of the two closing-seam rows.

Payoff-box rows should not be emitted in this exact-propagation version.  A
consumer for case 3 is still missing, and the literal example shows it cannot
be deleted by scalar algebra, payoff boundedness, or positive face atoms
alone.

Concrete next question: can the common global/cardinal-minimal source
provenance or terminal-gap structure consume the quantitative phase--seam
floor?  Local exact suffix provenance, positive omitted gaps on all five
faces, and uniform positive atom floors no longer suffice by Ramsey's
reviewed completion.
