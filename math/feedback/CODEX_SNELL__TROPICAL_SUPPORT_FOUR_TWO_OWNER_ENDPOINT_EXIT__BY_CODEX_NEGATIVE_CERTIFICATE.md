# Review of support-four two-owner endpoint exit

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`../notes/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md`](../notes/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md)

Reviewed SHA-256:
`45a88c93fb9e21b09b75940c27951ca0aef2e9ee9222a12fd886686ce1fe78a9`

## Verdict

**PASS.**  I found no mathematical, cap-orientation, or chronology defect.
The two active-entry sign cases are exhaustive; the zero-cross case uses
homogeneous infeasibility in the correct row/column orientation; every strict
limiting endpoint comparison becomes an exact finite-(n) unrestricted cap;
and the positive-minimum collar applies to both active-owner and removed-
outsider Quit exits.  Starting from full support, the construction uses no
more than four literal chronological updates before reaching the already
identified off-minimum paid-port/source-reentry waist.

The theorem does not consume that paid port or produce a uniform equilibrium,
and the note states this limitation explicitly.

## Stationary all-behavior cap envelope

After the first two literal Never updates, only (p) and (k) retain their
positive source hazards.  Their opponents remain stationary, including the
two literal-Never coordinates.  For any player (a), every deterministic
pure Quit time is therefore an exact convex interpolation between Quit at
date zero and literal Never.  Both endpoints are attained.  The checked
theorem `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
therefore yields

\[
B_a(\tau_n)=\max\{Q_{n,a},N_{n,a}\}
\]

over arbitrary behavioral deviations.  No bounded-clock or stationary-
deviator assumption remains.

Because (x_{n,p}/h_n\to\lambda_p) and
(x_{n,k}/h_n\to\lambda_k), the repeated two-owner terminal law converges to
the normalized singleton mixture with weights
(\lambda_p/\Lambda,\lambda_k/\Lambda).  Same-row collisions have conditional
mass (O(h_n)), so bounded nonsingleton rewards vanish in every limit used
below.

## Active-owner formulas and orientation

For active owner (p), deleting its prescribed hazard leaves only owner
(k), so in fact

\[
N_{n,p}=r_p(\{k\})=s_p+A_{pk}
\]

exactly at every finite (n).  Quit-now tends to (s_p), while the prescribed
payoff tends to

\[
s_p+{\lambda_k\over\Lambda}A_{pk}.
\]

Thus:

- if (A_{pk}>0), Never is eventually the exact cap and its gain tends to
  ((\lambda_p/\Lambda)A_{pk}>0);
- if (A_{pk}<0), Quit-now is eventually the exact cap and its gain tends to
  (-(\lambda_k/\Lambda)A_{pk}>0).

The coefficients and signs in (2.3)--(2.4) are correct.  The same argument
applies with (p,k) interchanged.  In the positive case, setting that owner
to literal Never leaves exactly one positive source hazard, which tends to
zero; hence the child is a genuine diffuse one-owner stationary descendant,
not a separately chosen law.

## Zero-cross outsider

Assume (A_{pk}=A_{kp}=0), and let (\mu) be supported on (p,k) with the
normalized source weights.  Zero diagonal and the two cross equalities give

\[
(A\mu)_p=(A\mu)_k=0.
\]

If both removed outsiders had nonnegative residual, then (A\mu\ge0) and
(\mu_a(A\mu)_a=0) for every coordinate.  This would be a homogeneous
simplex solution, contradicting (1.1).  Therefore one fixed removed outsider
(b) has

\[
R_b={\lambda_pA_{bp}+\lambda_kA_{bk}\over\Lambda}<0.
\]

That outsider is still literal Never at the actual child, so its current
payoff is exactly its Never endpoint.  The terminal-law limit gives
(N_{n,b}\to s_b+R_b), while Quit-now tends to (s_b); simultaneous Quit and
stationary collision terms are (o(1)).  The strict sign makes Quit-now the
exact finite-(n) behavioral cap for all large (n), with gain tending to
(-R_b).  This is one literal update from the actual two-owner child.

The hard adapter from nonexistence of a Fin4 uniform payoff to (1.1) is valid:
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` supplies
no-homogeneous on the normal principal matrix,
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` makes
the core full, and `singletonLCPFeasible_reindexMatrix_iff` transports the
statement across the canonical full-core subtype equivalence.

## Collar handoff

For every selected Quit-now branch, the exact cap coordinates converge to the
corresponding solo value: (B_b(y)=s_b) at any descendant semantic cluster
point, where (b) may be the negatively oriented active owner or the
zero-cross outsider.  At every minimum-fibre point (z), the checked theorem
`minimumTerminalSemantic_singletonMargin` gives

\[
D_*\le B_b(z)-s_b=B_b(z)-B_b(y).
\]

This excludes every cluster point from the minimum fibre.  Compactness of the
cluster set and continuity of total semantic debt then give a fixed
sequence-dependent (\delta>0) with
(D(\tau_n)\ge D_*+\delta) eventually.  The orientation and quantified scope
match the independently reviewed singleton-collar theorem.

If instead a positive cross entry first produces a one-owner child, the
singleton-collar theorem applies to that literal child and supplies one
further exact-cap Quit response.  Thus the update counts from full support
are:

```text
two Never updates + one immediate Quit exit       = 3 updates, or
two Never updates + one Never + one blocker Quit  = 4 updates.
```

## Exhaustiveness and boundary checks

- A negative cross entry gives case 1 regardless of the sign of the reverse
  entry.
- With no negative entry, either both entries are zero (case 2) or at least
  one is positive (case 3).  These cases exhaust the real sign plane.
- Equality is used only in the homogeneous-infeasibility branch; no strict
  finite-(n) cap is inferred from a zero active entry alone.
- The two removed outsiders have no hidden positive hazard.  This is specific
  to the full-support source after two literal Never updates and is stated in
  Section 1.
- Nonsingleton rewards affect finite endpoint values but not the strict
  limiting signs, since all current hazards vanish.
- A sure-Quit target is not reclassified as a diffuse source; the theorem
  stops at the paid-port/source-reentry waist.

No revision is required.

## Exact-hash delta review

I rechecked the repaired note at SHA-256
`0ca3860f9359cc3ca7039ee7aeff8d73bdb1bb276f4bc44e0e3f547cb2b8fb3f`.
The verdict remains **PASS**.

The Section 1--3 algebra and sign dispatch are unchanged.  The positive-cross
branch now cites the reviewed origin-independent singleton-collar theorem at
its exact SHA
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`;
that theorem's hypotheses, rather than any claimed provenance, are exactly
what the one-owner child supplies.

The added literal paid-row audit is also correct.  At every final Quit-now
edge the source is stationary, the responding player's prescribed
date-zero action is Continue with probability tending to one (or exactly one
for a removed outsider), and the opponents' joint date-zero Continue
probability tends to one.  Hence all three displayed continuation/reach
fields are eventually at least one half, the row is reached with probability
one, the strict limiting gain admits the asserted fixed half-limit lower
bound, and the joint-Continue successor is literally the same stationary
source.  This strengthens the source-attached chronology but does not purport
to consume the paid port or prove a near-return.  Delimiter normalization is
presentation-only.  I found no new mathematical or scope objection.
