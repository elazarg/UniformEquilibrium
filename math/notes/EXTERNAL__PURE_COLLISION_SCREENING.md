# Pure-collision screening removes the Fin4 tail condition

Author: external contribution supplied in conference

## Status

Ordinary-mathematics proof passed two independent adversarial reviews.  It
strictly strengthens the reviewed nonsingleton self-tail contraction: every
positive-mass nonsingleton marked row enters the concentrated-singleton node
without any tail-debt hypothesis or self-tail replacement.  The new Lean
adapter described below is not yet checked.

## Statement

Let `r` be a quitting-game reward table on `Fin 4`.  Assume its terminal-
semantic carrier has positive minimum total debt

\[
D_*:=\min D>0.
\]

Let `p` be an actual behavioral profile, let `t` be a marked date, and suppose
a nonsingleton coalition `S` has unconditional stage mass at least
`lambda>0` at `t`.

Then replace the marked root literally by the pure root of `S`, and thereafter
use literal same-stage best-endpoint updates.  This preserves every live root
outside date `t` and produces an actual singleton endpoint at `t`.  If `L_t`
is the original live mass at `t`, the final singleton has stage mass exactly
`L_t`, hence at least `lambda`.  Every strict best-endpoint edge after the
pure nonsingleton root is installed has actual payoff gain at least

\[
\lambda D_*/4.
\]

and in fact at least `L_t D_*/4`.  The initial pure-root installation and the
final possibly nonprofitable pair-to-singleton route are not asserted to have
this gain floor.

Consequently every nonsingleton minimum-law source in the checked Fin4 atlas
enters the source-attached strong concentrated-singleton node.  Neither the
high-tail/low-tail split nor a self-tail closure is needed.

## Proof

### Pure nonsingleton zero transport

Fix any actual post-date tail `tau` and a pure nonsingleton root `q_C`, where
`|C|>=2`.  Let

\[
x_C=\operatorname{Sem}(q_C\triangleright\tau),
\qquad y=\operatorname{Sem}(\tau).
\]

For every player `i`, choose `j in C\{i}`.  After forcing `i` to Continue,
`j` still Quits surely.  Hence the opponents-only Continue mass is zero:

\[
\operatorname{OppCont}_i(q_C)=0.
\tag{1}
\]

The checked arbitrary-root debt bounds are

\[
\Delta_i(y^u,q_C)
\le d_i(x_C)
\le \Delta_i(y^u,q_C)
 +\operatorname{OppCont}_i(q_C)d_i(y).
\tag{2}
\]

The tail is actual, so its debt is nonnegative.  Combining (1) and (2) gives

\[
d_i(x_C)=\Delta_i(y^u,q_C)
\quad\text{for every }i.
\tag{3}
\]

Thus a pure nonsingleton row screens off every coordinate of continuation
debt exactly.

### Uniform endpoint gain

The current pair `x_C` is actual, so global minimality gives

\[
D_*\le D(x_C)=\sum_{i\in\operatorname{Fin}4}\Delta_i(y^u,q_C).
\]

Some player therefore has

\[
\Delta_i(y^u,q_C)\ge D_*/4.
\tag{4}
\]

Change only that player at the marked row to its better pure endpoint.  If
`L_t` is the live mass at `t`, the checked literal one-date identity gives

\[
U_i(p')-U_i(p)=L_t\Delta_i(y^u,q_C).
\tag{5}
\]

Since the displayed coalition has stage mass at least `lambda`, `L_t` is at
least `lambda`.  Hence

\[
U_i(p')-U_i(p)\ge\lambda D_*/4.
\tag{6}
\]

The same update subtracts this gain exactly from the mover's unrestricted
behavioral debt, preserves the complete post-date tail, and routes the marked
mass without loss.

### Finite same-stage orbit

Replace the marked product root simultaneously by the pure root of its
displayed nonsingleton coalition.  This is an actual profile operation, not a
unilateral profitable edge.  It leaves all off-date roots literal and raises
the marked stage mass to exactly the original live mass `L_t`.

From a pure nonsingleton coalition, use (4)--(6).  If the routed coalition is
a singleton, stop.  Otherwise continue.  The relation is serial on the finite
set of nonsingleton coalitions.  It therefore reaches a singleton or contains
a simple closed segment.

Every strict pure-orbit edge has gain at least `lambda*D_*/4`, which is
stronger than the
`lambda*D_*/8` floor required by `QuittingSameStageEndpointEdge`.  The checked
generic theorem

```text
sameStageEndpointTrace_false_of_effectiveSupport_card_le_four
```

excludes the closed segment.  Therefore a singleton is reached.  On `Fin 4`,
at most three profitable toggles are needed before the final, possibly
nonprofitable, pair-to-singleton route.  All updates occur at the same marked
date, so the past, post-date tail, original source, and exact stage mass `L_t`
remain literal.

## Atlas consequence

For a nonsingleton minimum-law atom, the selected-row theorem eventually
provides stage mass greater than

\[
\lambda=\mu^2/8.
\]

Apply the theorem above directly to any such actual selected row.  The output
is the weak source-attached singleton endpoint, which the checked positive-
stage adapter sends to the strong concentrated packet.  Monodromy and
quantitative tail escape disappear before the consumer boundary.

## Probability and strategy audit

- Stage mass is unconditional and includes the probability of reaching `t`.
- Roots are independent product actions at the unique live history.
- The tail is one literal complete behavioral profile.
- Equation (2) uses unrestricted behavioral terminal debt, including Never
  and arbitrarily late deviations.
- The zero opponents-only Continue factor is valid separately for every
  unilateral deviator because another member of `C` Quits surely.
- No target root is asserted cap--Nash, and no terminal-law mass is identified
  with a fresh prefix root's absorption.

## Boundary tests

- Nonsingleton cardinality is essential: at a pure singleton root, its unique
  owner can Continue and expose the entire tail debt.
- Positive `D_*` is essential for the uniform edge floor.
- The support-cardinality-at-most-four theorem is essential for excluding the
  finite closed segment.  The zero-transport lemma itself holds for any finite
  player type.
- The result produces a singleton endpoint, not a terminal equilibrium or a
  total-debt decrease.

## Lean handoff

Likely new declarations:

```text
quittingPureNonsingleton_prefixDebt_eq_coordinateNashDefect
quittingLiteralSameStage_exists_singleton_or_endpointEdge_noTail
quittingPureNonsingleton_sameStage_dispatch_noTail
quittingPureNonsingleton_finFourSameStage_dispatch_noTail
FinFourMinimumAtomProducer.nonempty_strongConcentratedPacket_noTail
```

The existing combined dispatch declarations still assume `lowTail`; they
cannot be invoked unchanged.  The implementation should add the short
pure-row no-tail dispatch adapter, use the raw finite-orbit and generic
support-at-most-four impossibility theorems, and retain the full minimum-law
source as dependent provenance.  It must not manufacture a `FinFourLowTailRow`
or keep a redundant tail-escape constructor.

## Nonclaims

This theorem does not consume the strong concentrated-singleton node.  It
does not control cross-coordinate cap leakage after the eventual singleton
packet, prove terminal approximants, build a cumulative return, or regenerate
a lower-rank minimum source.
