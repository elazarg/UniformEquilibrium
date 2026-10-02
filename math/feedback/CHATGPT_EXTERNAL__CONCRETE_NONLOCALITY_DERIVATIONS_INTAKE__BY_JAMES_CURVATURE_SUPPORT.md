# Independent review of concrete nonlocality derivations, Items 3--4

**Reviewer:** `JAMES_CURVATURE_SUPPORT`  
**Date:** 2026-08-26  
**Source:** `../idea_derivations.zip`, items
`03_PREFIX_CURVATURE_COCYCLE.md` and
`04_MINIMUM_FIBER_SUPPORT_LATTICE.md`  

## Verdicts

- **Item 3 — REVISE, then PASS as a conditional algebraic cocycle.**  The
  payoff, cap, debt, matrix-product, and Duhamel identities are exact.  The
  prescribed-hazard term has the stated positive sign.  The mandatory repair
  is semantic: a signed square `W_t` and even the positive quantity
  `H_t * |W_t|` are not themselves a positive executable wall flux.  They are
  reached absolute wall-curvature budgets.  One must select and orient an
  actual corner and retain the prescribed-action/provenance data before
  invoking a strategic consumer.
- **Item 4 — PASS with the exact checked typing retained.**  The support-union
  theorem and every quantitative inequality follow from the named checked
  affinity/chord-gap declarations.  The source and target must differ only in
  one mover's complete stopping law, the mixed strategy must be the canonical
  `quittingStoppingLawMixtureBehaviorStrategy`, and the formal minimum
  hypothesis is over the full terminal-semantic carrier.  These are short
  diagnostic corollaries, not a producer of a minimum-fiber endpoint.

Neither item is export-ready.  Both are reasonable Research-lane
formalization targets, but they do not close a maintained residual or supply
a chronology/rank decrease by themselves.

# Item 3: prefix curvature cocycle

## 1. One-step cap and payoff formulas

Fix observer `i` and one common product prefix root.  Let

\[
p=\Pr(i\text{ Quits}),\qquad
c=\Pr(\text{all opponents of }i\text{ Continue}).
\]

Let `q` be the payoff after forcing `i` to Quit now and let `a` be the
unnormalized absorbing payoff contribution after forcing `i` to Continue.
For a suffix prescribed payoff `u` and suffix unrestricted cap `B`, the exact
prefix identities are

\[
P(u)=p q+(1-p)(a+cu),                                \tag{3.1}
\]

\[
C(B)=\max\{q,a+cB\}=a+cB+w(B),
\quad w(B)=(q-a-cB)_+.                              \tag{3.2}
\]

The cap identity is the scalar content of
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.  It uses an
opponents-only survival coefficient because the deviating observer forces
Continue before entering its suffix response.  The prescribed payoff instead
uses joint survival `(1-p)c`.  No best-response attainment is required.

For four literal suffixes under the same root, constants cancel under the
signed square

\[
\square z=z^{11}-z^{10}-z^{01}+z^{00}.
\]

Therefore

\[
\square u'=(1-p)c\,\square u,                       \tag{3.3}
\]

\[
\square B'=c\,\square B+\square w(B),               \tag{3.4}
\]

and, because `d=B-u`,

\[
\boxed{
\square d'=c\,\square d+pc\,\square u+\square w(B).} \tag{3.5}
\]

The `+pc square u` term is correct.  It is precisely

\[
c\square B-(1-p)c\square u
=c\square d+pc\square u.
\]

It disappears only when the observer is prescribed to Continue surely.

## 2. Matrix product and Duhamel indexing

Write

\[
A_t=
\begin{pmatrix}(1-p_t)c_t&0\\p_tc_t&c_t\end{pmatrix},
\quad
H_t=\prod_{s<t}c_s,
\quad
J_t=\prod_{s<t}(1-p_s)c_s.
\]

The triangular product is

\[
A_0\cdots A_{T-1}
=\begin{pmatrix}J_T&0\\H_T-J_T&H_T\end{pmatrix}.   \tag{3.6}
\]

The ordering in the archive is correct.  If
`W_t = square (w_t(B_{t+1}))`, then a wall inserted at time `t` is multiplied
by `A_0 ... A_(t-1)`.  Since every earlier matrix sends `(0,W)` to
`(0,c_s W)`, its weight is exactly

\[
H_t=\prod_{s<t}c_s,
\]

not `H_(t+1)` and not a joint-survival product.  Thus the block identities

\[
\square u_0=J_T\square u_T,                         \tag{3.7}
\]

\[
\square B_0=H_T\square B_T+
  \sum_{t<T}H_tW_t,                                 \tag{3.8}
\]

\[
\boxed{
\square d_0=H_T\square d_T+(H_T-J_T)\square u_T
 +\sum_{t<T}H_tW_t}                                 \tag{3.9}
\]

all pass.  Formula (3.9) can also be checked directly by subtracting (3.7)
from (3.8), so there is no omitted intermediate prescribed-hazard term.

When every `p_t=0`, one has `J_T=H_T`, and the archive's clean debt cocycle
follows.

## 3. Quantitative inequalities and sign

For one observer-Continue prefix,

\[
K_0=cK_1+W_0.
\]

If `c>=alpha>0` and `|K_1|>=kappa`, then

\[
\alpha\kappa\le c|K_1|
=|K_0-W_0|\le |K_0|+|W_0|,
\]

which proves the factor-two alternative in (4.2).  If instead
`K_1>=kappa`, then `K_0-W_0>=alpha*kappa`; hence either
`K_0>=alpha*kappa/2` or `-W_0>=alpha*kappa/2`.  The signed orientation in
(4.3) is correct.

Likewise, for a Continue block,

\[
H_T|K_T|
\le |K_0|+\sum_{t<T}H_t|W_t|,                       \tag{3.10}
\]

so (4.5) and (4.6) are valid (state `T>0` in the pointwise version, or note
that its hypotheses exclude the zero-length case).  The infinite identities
also pass under the archive's boundedness, absolute summability, and terminal
vanishing hypotheses.

The interpretation needs repair.  Each corner wall value `w_t(B^{ab})` is
nonnegative, but

\[
W_t=w^{11}_t-w^{10}_t-w^{01}_t+w^{00}_t
\]

has either sign.  For example, wall values
`(w11,w10,w01,w00)=(0,1,1,0)` give `W=-2`.  Accordingly:

- `sum H_t |W_t|` is an **absolute wall-curvature budget**, not the signed
  Duhamel flux and not a positive linear flow;
- a large `|W_t|` implies only that some corner has
  `w_t(B^{ab}) >= |W_t|/4`;
- the sign selects a diagonal-versus-off-diagonal aggregate, but does not by
  itself provide the corner, action support, floor safety, or chronological
  orientation expected by an admissible-payoff consumer.

Thus replace the sentence “curvature lost ... becomes a positive,
reached-history wall flux” by “curvature loss forces a positive reached
absolute wall-curvature budget.”  Keep the archive's own final nonclaim that
the wall square is not yet an admissible-payoff edge.

## 4. Novelty relative to existing curvature-prefix work

`CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL.md` already proves the common-root
cap maximum identity and its three-corner affine-curvature transport, and its
independent review identifies the same opponent-versus-joint survival split.
The checked tree already contains the one-prefix cap maximum and pure-time
difference transport.

What is new here is narrow but real:

1. the simultaneous four-corner payoff/cap/debt triangular system;
2. the explicit prescribed-hazard coupling `pc square u`; and
3. the finite-block Duhamel formula with opponent-reach weights.

These are algebraic packaging rather than a new strategic consumer.  The
all-Continue case again copies the same square without progress, while a
general wall square remains signed and unconsumed.  Recommended disposition:
formalize near the prefix-cap identities if the richer reset-square carrier
is maintained, but keep internal and do not describe it as a renewable rank.

# Item 4: minimum-fiber support lattice

## 5. Exact checked hypotheses

The controlling declaration is
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`.
Its exact data are:

- one ambient behavioral profile;
- one mover and two complete behavioral strategies `source,target` for that
  mover, with every other player's strategy fixed;
- the canonical mixture
  `quittingStoppingLawMixtureBehaviorStrategy` with `0<=lambda<=1`;
- a source pair which minimizes total debt over the full
  `quittingTerminalSemanticCarrier`; and
- equality of target and source total debt.

Under those hypotheses, every observer coordinate is exactly affine:

\[
d_i^\lambda=(1-\lambda)d_i^0+\lambda d_i^1.          \tag{4.1}
\]

The archive's phrase “whole-stopping-law mixture” is correct, but it must not
be weakened to an arbitrary convex combination of semantic pairs, a public
lottery over profiles, or simultaneous replacement of several players.

## 6. Exact support conclusions

Actual terminal-semantic debts are nonnegative.  Therefore, for
`0<lambda<1`, both coefficients in (4.1) are strictly positive and

\[
d_i^\lambda>0
\iff d_i^0>0\ \text{or}\ d_i^1>0.                   \tag{4.2}
\]

This proves exactly

\[
\operatorname{supp}_+(d^\lambda)
=\operatorname{supp}_+(d^0)\cup
  \operatorname{supp}_+(d^1),                       \tag{4.3}
\]

and the dual zero-set intersection.  The endpoint-only persistence,
no-new-debtor equivalence, and impossibility of an interior support decrease
all follow exactly as written.

The strict endpoint support criterion is also a correct set-theoretic
equivalence: strict containment requires no acquisition outside the source
support and disappearance of at least one source-active coordinate.  Calling
those two obligations “independent of same total debt” is valid only in this
logical sense.  The checked affinity theorem does not produce either
obligation.

The existing
`positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`
already obtains an actual strict support drop in the more structured
full-replacement setting by separately supplying exact diagonal vanishing,
flatness, no entry, and minimum-fiber membership.  Item 4 is the general
geometric diagnostic explaining why those extra fields are necessary; it
does not subsume that producer theorem.

## 7. Quantitative chord inequalities

The checked quantitative declaration is
`quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum` in
the same affinity file.  Its formal near-minimum hypothesis is

\[
D^0\le D(\text{candidate})+\varepsilon
\quad\text{for every carrier candidate}.
\]

Put `R=D^1-D^0`.  It proves coordinatewise

\[
0\le(1-\lambda)d_i^0+\lambda d_i^1-d_i^\lambda
\le\varepsilon+\lambda R.                           \tag{4.4}
\]

For `d_i^0=0`, rearrangement gives

\[
\lambda d_i^1-(\varepsilon+\lambda R)
\le d_i^\lambda\le\lambda d_i^1.                    \tag{4.5}
\]

For `lambda>0`, division yields exactly the archive's (4.3).  Consequently:

- `d_i^1 > R + epsilon/lambda` implies `d_i^lambda>0`; and
- `d_i^lambda=0` implies `d_i^1 <= R + epsilon/lambda`.

The signs, the coefficient of `R`, and the absence of a player-count factor
are all correct.  No absolute value should be inserted around `R`: the
one-sided theorem controls the convexity gap by the actual total-debt rise.
Its hypotheses already force the displayed upper bound to be nonnegative
whenever the gap exists.

## 8. Formalization and scope recommendation

The support-union theorem and its no-new-debtor corollary are concise Research
formalization candidates immediately downstream of the checked affinity
theorem.  The quantitative zero-detection corollary is also legitimate if its
statement exposes the exact near-minimum and canonical-mixture hypotheses.

Their novelty is limited: the coordinatewise affinity and chord-gap estimate
are already checked, and the support facts are elementary finite-set
consequences.  More importantly, nothing in Item 4 produces an endpoint on
the same minimum fiber, prevents inactive debt acquisition, or clears an
active coordinate.  Therefore Item 4 is an internal diagnostic/support API,
not a strict-rank producer and not a standalone export candidate.
