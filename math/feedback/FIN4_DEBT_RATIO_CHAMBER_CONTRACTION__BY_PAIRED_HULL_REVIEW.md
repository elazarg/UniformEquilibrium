# Final gate review of Fin4 debt-ratio chamber contraction

Reviewer: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE — mathematics passes; one source/consumer typing repair is required**

## Claim checked

The packet proves, for unrestricted behavioral terminal debts,

\[
D_* - \eta\ge \sqrt{4M^2+\eta^2}-2M>0,
\]

and proves that the entire chamber

\[
\eta<D_*<2\eta
\]

admits literal approximate-best-response targets whose total debt is at least

\[
D_*+\frac{D_*(2\eta-D_*)}{D_*-\eta}
\]

in the limit.  I rechecked the full proof, constants, carrier passage,
behavioral scope, named declarations, boundary tests, and proposed downstream
port.

## 1. Theorems A--C: PASS

The quadratic argument is correct.  With (h=D_*-eta\), a near-minimizer
and a maximal debtor (p\) give nonmover debts at most (h+\delta\).  Mixing
the complete stopping law of (p\) by weight (\theta\) toward a
(\zeta\)-best reply bounds the mover by

\[
(1-\theta)(\eta+h+\delta)+\theta\zeta
\]

and every nonmover by (h+\delta+4M\theta\).  The admissible interval

\[
\frac h{\eta+h}<\theta<\frac{\eta-h}{4M}
\]

is nonempty exactly under the negation of the stated quadratic bound.  No
attainment or compactness of the behavioral strategy space is used.

The ratio-chamber crossing is also correct.  Along a one-player stopping-law
chord the mover debt is affine and total debt is convex.  At the point where
the mover reaches debt (\eta\), the global maximum-debt floor forces a
second coordinate of debt at least (\eta\).  Solving the resulting chord
inequality gives

\[
D(\rho)-S\ge \frac{a(2\eta-S)}{a-\eta}.
\]

The monotonicity step has the right direction because
(z/(z-\eta)\) decreases on ((\eta,\infty)\).

The carrier version handles nonattainment honestly.  The approximate-response
debt (e_n\) tends to zero; the crossing parameters converge to
((a-\eta)/a\); and rearranging the convexity inequality gives

\[
\liminf_n(D(\rho_n)-D_*)
\ge \frac{a(2\eta-D_*)}{a-\eta}
\ge \frac{D_*(2\eta-D_*)}{D_*-\eta}.
\]

Compactness is used only after the literal source and target profiles have
been constructed.  No response strategy is selected at the carrier limit.

The proof covers arbitrary behavioral stopping laws, including Never and
unbounded stopping times.  The (2M\theta\) cap estimate is valid uniformly
over the complete response class because, for every fixed response, changing
the opponent's stopping law by the displayed mixture changes its payoff by at
most (2M\theta\); taking suprema preserves the bound.

## 2. Boundary and novelty audit: PASS

The lower boundary (D_*=\eta\) is genuinely excluded.  The upper boundary
(D_*=2\eta\) correctly gives zero port excess, and the debt-vector example
is appropriately labelled algebraic rather than a quitting-game realization.
The blow-up near the lower boundary is consistent with Theorem A.

The named stopping-law convexity and carrier declarations provide the stated
inputs but do not contain the quadratic separation or the ratio-chamber
crossing.  The packet is a genuine chamber contraction, not a duplicate of
the fixed-certificate thin-slice result.

## 3. Required source/consumer repair

The packet currently conflates two different paid objects.

Theorem C constructs the literal full response

\[
\sigma_n\longrightarrow\rho_n
\]

by one fixed maximal-debt payer (p\), with gain tending to at least (\eta\)
and with the target (\rho_n\) uniformly off minimum.

By contrast, the existing
`QuittingActualProfileTerminalGapPaidCapPort` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
is built **at one supplied profile** from a terminal-gap first-disagreement
row.  Its stored observer/paid row is newly selected by the terminal-gap
theorem, and its `source.gain` is the chosen gap (\gamma\).  It does not
store the incoming profile (\sigma_n\), the maximal debtor (p\), the full
response (\tau_{p,n}\), or its asymptotic gain (\eta\).

The honest adapter is still sufficient, but must be stated in two steps:

1. Theorem C produces the source-matched off-minimum targets (\rho_n\),
   retaining the literal (p\)-response edge externally.
2. For each (\rho_n\), choose (0<\gamma<\eta\) and invoke
   `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` with
   **source profile (\rho_n\)**.  This supplies a paid cap port whose
   observer and row may be unrelated to (p\), while its initial debt retains
   the fixed off-minimum excess.  Its `exactTrichotomy` can then be invoked.

If the author wants one packaged object retaining both pieces, the packet must
define a composite wrapper containing the literal response edge and the
separately selected port.  It must not identify the port observer or
`source.gain` with (p\) or the (\eta\)-scale response gain.

Accordingly, revise these statements:

- In Theorem C, replace “packaged as a source-attached paid cap port with ...
  fixed payer (p\), asymptotic paid gain at least (\eta\)” by the explicit
  two-step conclusion above.
- In “Adapter and consumer”, say that the port is instantiated at (\rho_n\),
  not that the same response becomes the port's paid row.
- State (0<\gamma<\eta\), not merely (\gamma<\eta\).
- Correct the source path to
  `Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`.

This is a bounded typing repair.  It does not affect Theorems A--C or the
strict contraction of the ratio chamber.

## 3.1 Delta recheck of the repaired adapter

The two-stage adapter repair is mathematically correct.  It now distinguishes
the fixed maximal debtor (p\) and its full-response edge from the separately
selected paid-port observer and row at source profile (\rho_n\).  The port's
stored gain is correctly identified as (\gamma\), not the incoming
(\eta\)-scale gain.

Two final bounded precision repairs remain before export:

1. Equation (C3) is a liminf bound.  Thus the phrase that each port source
   “has the fixed off-minimum excess from (C3)” should say either that the
   excess has liminf at least (\Delta_{\mathrm{port}}\), or, after discarding
   finitely many indices, use the literal uniform floor
   (\Delta_{\mathrm{port}}/2\).  The current wording can be read as the
   pointwise bound (D(\rho_n)-D_*\ge\Delta_{\mathrm{port}}\), which was not
   proved.
2. Two source paths still contain an extra `Diagnostics/` component.  The
   actual files are
   `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
   and
   `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`.

Accordingly the final delta verdict remains **REVISE**, but only for these
mechanical/quantifier corrections.  The adapter objection itself is closed.

## 3.2 Final delta

Both remaining items are repaired.  The packet preserves (C3) as a liminf
statement and explicitly discards finitely many indices before using the
uniform pointwise floor (\Delta_{\mathrm{port}}/2\).  The source paths now
name the actual `Quitting/Root` and `Quitting/Terminal` files.  The two-stage
adapter remains correctly typed.

**Final verdict: PASS.**  No mathematical or packet-format objection remains.

## 4. Export-format gate

The packet otherwise satisfies the required format: exact statements,
complete proof, unrestricted-strategy audit, positive and negative boundary
tests, source and novelty audit, two independent reviews, Lean handoff, and
explicit nonclaims.  After the source/consumer repair above, my verdict would
be **PASS**.  Until then, it should not be copied into `exports/` because its
current interface overstates what the existing paid-port structure retains.
