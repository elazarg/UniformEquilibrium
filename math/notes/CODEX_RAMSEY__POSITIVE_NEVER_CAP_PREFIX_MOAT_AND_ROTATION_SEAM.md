# Positive-Never cap-prefix moat and the exact rotation seam

Author: `CODEX_RAMSEY`

Status: **PROVED ORDINARY MATHEMATICS IN THE STATED CONDITIONAL SCOPE;
INTERNAL; INDEPENDENT REVIEW REQUESTED**

## 1. Question and correction

Let `(x,mu)` be a positive-Never global-minimum joint semantic/law point,
with

\[
 D(x)=D_*>0,\qquad \mu(\mathrm{Never})>0,
\]

whose positive-debt support `K` has maximum cardinality among all
positive-Never minimum joint points.  The reviewed rectangle theorem
[`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md`](CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md)
produces an actual off-minimum corner limit `(z,nu)` when a decoded corner
has a newcomer outside `K`.

A tempting claim is that no exact cap prefix of `(z,nu)` can return to the
minimum fiber, because the newcomer survives exact cap scaling.  This claim
is false under the stated maximum-*cardinality* selection alone.  The corner
may have lost an old member of `K`; a minimum endpoint with a rotated support
of the same cardinality does not contradict maximality.

The exact result is the following dichotomy.

1. If the corner support strictly contains `K` (or merely has cardinality
   larger than `K`), then every finite exact cap-prefix endpoint stays in a
   compact, uniformly separated off-minimum moat.
2. With only a newcomer, any exact cap-prefix endpoint which does reach the
   minimum fiber is a positive-charge transition to a genuinely rotated
   support: it retains the newcomer and must omit at least one old member of
   `K`.

The second alternative is not yet a well-founded regeneration theorem.  It
identifies exactly why the reviewed rectangle excursion cannot presently be
declared trapped off the minimum fiber.

## 2. Exact prefix scaling

Let `(z,nu)` be any joint terminal-semantic/law carrier point with

\[
 D(z)>0,\qquad \nu(\mathrm{Never})>0.
\]

Let `q_0,...,q_{N-1}` be a finite word in which `q_t` is an exact Nash root
against the cap coordinate of the semantic tail at stage `t`.  Let

\[
 c_t=\operatorname{ContinueMass}(q_t),\qquad
 C_N=\prod_{t<N}c_t.
\]

Write `(z_N,nu_N)` for the joint point obtained by applying these prefix
roots in their Bellman order.  Repeated use of
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and the
definition of `quittingTerminalOutcomeLawPrefix` gives, for every player
`i`,

\[
 d_i(z_N)=C_Nd_i(z),\qquad
 D(z_N)=C_ND(z),\qquad
 \nu_N(\mathrm{Never})=C_N\nu(\mathrm{Never}).       \tag{2.1}
\]

All three are equalities.  The law statement is not merely a lower bound:
fresh first-stage absorption never contributes to the `Never` coordinate.
The joint endpoint remains in the joint carrier by repeated application of
`quittingTerminalSemanticLawPrefix_mem_carrier`.

Now suppose `D_*` is a positive lower bound for total debt on the semantic
carrier.  Then

\[
 C_ND(z)=D(z_N)\ge D_*,
 \qquad C_N\ge c_0:=\frac{D_*}{D(z)}>0.              \tag{2.2}
\]

In particular a zero-survival prefix is impossible: it would give
`D(z_N)=0<D_*`.  Equations (2.1)--(2.2) also give the uniform persistence

\[
 d_i(z_N)\ge c_0d_i(z),\qquad
 \nu_N(\mathrm{Never})\ge c_0\nu(\mathrm{Never}).   \tag{2.3}
\]

Thus every positive-debt label of `z`, and positive Never mass, survive not
only each finite prefix but every cluster of such endpoints.

## 3. Compact strict-containment moat

Return to the maximum-cardinality minimum point `(x,mu)` and put

\[
 K=\operatorname{supp}_+d(x).
\]

Assume the off-minimum joint point `(z,nu)` satisfies

\[
 \nu(\mathrm{Never})>0,
 \qquad |\operatorname{supp}_+d(z)|>|K|.             \tag{3.1}
\]

The stronger condition `K` strictly contained in `supp_+ d(z)` implies
(3.1), so it is sufficient.

Let `E(z,nu)` be the set of endpoints of all finite exact cap-prefix words
over `(z,nu)`, including the empty word, and let `C` be its closure inside
the compact joint semantic/law carrier.  The set `C` is compact.  By (2.3),
every point `(y,lambda)` in `C` satisfies

\[
 \lambda(\mathrm{Never})
 \ge c_0\nu(\mathrm{Never})>0,
\]

and every label in `supp_+ d(z)` has positive debt at `y`.  Hence every
point of `C` has debt-support cardinality strictly larger than `|K|`.

No point of `C` can lie on the minimum fiber: it would be a positive-Never
minimum joint point with support cardinality larger than the selected
maximum.  The continuous function `D-D_*` is therefore strictly positive on
the compact set `C`, so it has a positive minimum.  Thus

\[
 \exists\eta>0\quad\forall (y,lambda)\in C,
 \qquad D(y)\ge D_*+\eta.                            \tag{3.2}
\]

This is the genuine compact cap-prefix moat.  It applies to arbitrary finite
word length and arbitrary exact cap-root selections.  It is not a statement
only about the maximal selector.

## 4. The newcomer-only case: return means rotation

Assume only that there is a newcomer

\[
 j\notin K,\qquad d_j(z)>0,                           \tag{4.1}
\]

with `nu(Never)>0`.  Let a finite exact cap word have endpoint `(z_N,nu_N)`
on the minimum fiber.  Equations (2.2)--(2.3) give

\[
 C_N>0,qquad \nu_N(\mathrm{Never})>0,qquad
 \operatorname{supp}_+d(z_N)=\operatorname{supp}_+d(z).       \tag{4.2}
\]

Maximum cardinality of `K` then gives

\[
 |\operatorname{supp}_+d(z)|\le |K|.                \tag{4.3}
\]

Since (4.1) puts a label outside `K` in that support, (4.3) forces at least
one old label to be absent:

\[
 \exists k\in K,\qquad d_k(z)=d_k(z_N)=0.            \tag{4.4}
\]

Thus a minimum-fiber endpoint is a genuine support rotation, not a strict
support extension.

Moreover, when `D(z)>D_*`, such a return has positive charge.  Indeed

\[
 C_N=\frac{D_*}{D(z)}<1,                             \tag{4.5}
\]

so at least one root in the word has positive absorption.  This is a literal
exact cap-prefix descent from the off-minimum tail to a positive-Never
minimum endpoint, but it does not by itself connect the new minimum endpoint
back to the original minimum source.

## 5. Why newcomer alone does not prove a moat

The support logic already shows the failed implication.  For example, the
abstract supports

\[
 K=\{0,1\},\qquad L=\{1,2\}
\]

have the same cardinality, while `2` is a newcomer relative to `K` and `0`
has been lost.  Exact cap scaling by any positive scalar preserves `L`.
Nothing in maximum cardinality excludes a positive-Never minimum point with
support `L`.

This is not asserted to be a quitting-game counterexample.  It is a complete
counterexample to the *support-theoretic inference* used by the unqualified
moat argument.  Miner's bilinear rectangle theorem avoids this problem only
when all four rectangle corners are minimum: its executable proper interior
has the union of the four supports and therefore contains all of `K` as well
as the newcomer.  A cap prefix of one off-minimum corner is not that rectangle
interior, and no checked declaration identifies their supports or laws.

## 6. Conjecture-facing disposition

The strict-containment branch (3.2) proves that exact cap dynamics cannot
return the literal excursion to the minimum fiber.  It therefore rules out
the simplest reverse-leg construction rather than completing it.

The newcomer-only branch has one potentially useful output: if cap dynamics
does return to the minimum, (4.2)--(4.5) give a source-native positive-charge
exact descent to a rotated positive-Never minimum support.  To become the
well-founded regeneration required by `FIN4_BT_QUESTION.md`, one still needs
either:

- a natural-valued orientation preventing cycles among equal-cardinality
  supports; or
- re-extraction of the full rectangle at the returned source together with a
  proof that a repeated support cannot recur without a prescribed-payoff
  charged return.

Neither is claimed here.  In particular, the finite set of supports alone
only forces a cycle; the literal rectangle legs between successive minimum
sources are not exact Nash--Bellman edges.

## 7. Exact source audit

The proof uses:

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalOutcomeLawPrefix`, its exact `Never` branch, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- compactness of `quittingTerminalSemanticLawCarrier`; and
- the reviewed maximum-support rectangle theorem cited in Section 1.

The theorem is ordinary mathematics, not a checked Lean declaration.  A
formal version should define the finite iterated joint-prefix action and
prove (2.1) by list induction before taking the compact closure.

## Review request

Please check the list-order prefix scaling, exclusion of zero survival, the
uniform lower bounds through closure, the strict-containment compact
separation, and especially the correction that a newcomer without retained
base support permits equal-cardinality rotation.  The intended scope is
internal: the theorem identifies a valid moat branch and an exact charged
rotation seam, not a completed regeneration or uniform-payoff consumer.
