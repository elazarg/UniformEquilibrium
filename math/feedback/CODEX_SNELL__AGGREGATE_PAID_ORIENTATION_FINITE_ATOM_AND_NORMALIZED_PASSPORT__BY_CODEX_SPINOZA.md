# Review of Section 7.16: large selected effect to same-tail paid port

Reviewer: CODEX_SPINOZA

Date: 2026-09-03

Verdict: **PASS for Section 7.16, within its stated local paid-port scope.**

## Claim checked

I adversarially checked only Section 7.16 of
`CODEX_SNELL__AGGREGATE_PAID_ORIENTATION_FINITE_ATOM_AND_NORMALIZED_PASSPORT.md`:
the conversion of the large selected adjacent-deadline operational effect into
a literal same-tail unilateral paid port.  I checked both branches, all signs
and constants, cap/debt invariance, the product telescope, and the provenance
needed to dispose of a full-large but selected-small output.

## Never-coordinate branch

Here `P_j(\infty)` and `R_j(\infty)` are the `none` masses of the finite timing
law: they mean pass through the finite prefix to the common tail, not terminal
Never forever.  With every opponent assigned the deterministic `none` prefix,
every finite action of mover `k` produces exactly singleton `{k}`, and mover
`none` reaches the literal tail.  Thus

\[
 U_k(P_k)=(1-p_k)r_k(\{k\})+p_k u_k,
 \qquad
 U_k(R_k)=(1-c_k)r_k(\{k\})+c_k u_k,
\]

so the oriented payoff difference is exactly

\[
 |c_k-p_k|\bigl(u_k-r_k(\{k\})\bigr)
 \ge {\gamma\over16M}{\delta\over2}
 ={\delta\gamma\over32M}.
\]

The orientation toward the larger pass coefficient is correct because the
tail-minus-singleton factor is positive.  The two complete profiles differ
only in mover `k`'s finite-prefix law and use the same tail.  Hence mover `k`'s
opponents, and therefore its unrestricted continuation best-response cap, are
identical.  The semantic debt decreases by precisely the payoff gain.

## Selected boundary-gain branch

Put `epsilon = gamma/(16M)`.  If all four `none` discrepancies are strictly
smaller than `epsilon`, the large selected gauge

\[
 {\gamma\over8M}\le
 \max\{\max_j|p_j-c_j|, |g_P^0-g_R^0|/(4M)\}
\]

forces `|g_P^0-g_R^0| >= gamma/2`; the factor `4M` has the correct orientation
because `M>0`.

The exact retained-tail identity is
`quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul`
in `AdjacentDeadlineRetainedTailReprojection.lean` (defined in
`RetainedTailGraftDecomposition.lean`).  A pure finite boundary response has
zero joint `none` mass.  Consequently its grafted gain against base law `P` is

\[
 g_P^\tau=g_P^0-m(P)u_o,
\]

and likewise for `R`; the minus signs in (7.89) are therefore correct.  For
coordinates in `[0,1]`, the standard four-factor telescope gives

\[
 |m(P)-m(R)|\le\sum_j|p_j-c_j|<4\epsilon={\gamma\over4M}.
\]

Together with `|u_o| <= M`, this yields

\[
 |g_P^\tau-g_R^\tau|>\gamma/4.
\]

The triangle inequality then forces one absolute grafted gain above
`gamma/8`.  A positive gain orients base-to-boundary; a negative gain orients
boundary-to-base.  In either orientation only observer `o` changes strategy,
the opponents and cap are exactly fixed, and debt falls by the oriented gain.
Thus the uniform local floor

\[
 \min\{\delta\gamma/(32M),\gamma/8\}
\]

is correct.

## Dispatch provenance and scope

The checked declaration
`quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant`
in `AdjacentDeadlineSelectedBoundaryEffectDispatch.lean` really returns
selected-large or an already paid reverse participant, under its displayed
scale, reward, pass, and tail-separation hypotheses.  The full operational
distance theorem is proved by rerunning that selected dispatch and only then
weakening selected-large to full-large.  Therefore a consumer may legitimately
rerun the selected dispatch when the reported full-large coordinate is
unselected: selected-large is consumed by Section 7.16, while selected-small
returns the already-paid arm.  It would be invalid to infer selected-large
from full-large alone, and the note explicitly avoids that inference.

The wording “Never prefix” should continue to be read as deterministic finite
timing `none` followed by `tau`; it is not terminal all-Never.  This is a
terminological caution, not a mathematical defect.  I found no sign, constant,
cap, padding, or full-distance gap in the reviewed conversion.  The result is
only a local paid-port producer: it does not locate its source on the global
minimum fibre or supply a chronological consumer, exactly as the note states.
