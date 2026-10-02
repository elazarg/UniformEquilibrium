# Review of singleton-descent reactivation off-minimum collar

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`../notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`](../notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md)

Reviewed SHA-256:
`eaea3e3f603c06f32b7dc7fd6ef3ad8ccffafeab0944884a6060f7e310cc1dc0`

## Verdict

**PASS.**  I found no mathematical objection.  The hard Fin4 adapter really
does put a negative entry in every full singleton column.  At a stationary
one-leading-owner descendant, the selected blocker has an eventual exact
unrestricted Quit-now cap with the stated limiting gain.  The checked
minimum-singleton-margin theorem has exactly the orientation needed for the
cap-coordinate collar, and compactness upgrades exclusion of every cluster
point from the minimum fibre to a uniform positive total-debt excess.  The
sure-Quit update does not regenerate a diffuse singleton source after the
blocker is deleted, so the note's nonrenewal qualification is essential and
correct.

This is ordinary mathematics using checked ingredients.  It creates a
literal paid edge and a state-space collar, not an additive returned-block
charge or a uniform-payoff consumer.

## Full-core and no-homogeneous adapter

Write (A=\operatorname{normalizedSoloMatrix}(r)), so
(A_{ik}=r_i(\{k\})-r_i(\{i\})) and (A_{ii}=0).  From nonexistence of a
uniform-equilibrium payoff,
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` supplies
nonexistence of a homogeneous simplex solution for the principal matrix on
the normal core.  In Fin4,
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
makes that core the full player set.

There is a small type transport hidden in the prose but no mathematical gap.
Use the equivalence

\[
i\longmapsto \langle i,\ i\in\operatorname{normalCore}A\rangle
\]

from `Fin 4` to the normal-core subtype.  Under it, `normalPlayerMatrix A` is
the reindexing of (A).  Homogeneous feasibility is invariant under this
reindexing by `singletonLCPFeasible_reindexMatrix_iff` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
Therefore (A) itself has no homogeneous simplex solution.

The declaration
`exists_negative_entry_in_column_of_noHomogeneous` in the same file then
gives, for each column (k), a row (b(k)) with
(A_{b(k),k}<0).  The diagonal identity forces (b(k)\ne k).  Finite choice
over four columns and finiteness make

\[
g_0=\min_k(-A_{b(k),k})>0.
\]

Thus the selector, its orientation, and its uniform quantitative constant are
correct.

## One-owner law and exact finite-n cap

Let (q_n>0) be the leading hazard of owner (k), with all other retained
hazards totaling (o(q_n)), and (q_n\to0).  One-row absorption is
(q_n+o(q_n)); singleton (k) has mass (q_n+o(q_n)), while every other
singleton and collision has mass (o(q_n)).  Normalizing the infinitely
repeated stationary row gives

\[
\operatorname{Law}(\tau_n)\to\delta_{\{k\}},\qquad
U_i(\tau_n)\to r_i(\{k\}).
\]

For (b=b(k)\ne k), deleting (b)'s own strategy leaves stationary
opponents with the positive hazard (q_n), so they absorb almost surely.  As
in the reviewed chronological descent, every deterministic pure Quit time is
exactly a convex combination of the two stationary endpoints:

- literal Never, which tends to (r_b(\{k\})); and
- Quit at date zero, which tends to (s_b=r_b(\{b\})), because simultaneous
  opponent Quit probability tends to zero.

Since

\[
s_b-r_b(\{k\})=-A_{bk}\ge g_0>0,
\]

the endpoints are strictly separated for all sufficiently large (n).
Quit-now attains the exact pure-time maximum, and
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` makes it the exact cap
over every behavioral deviation.  Hence

\[
B_b(\tau_n)-U_b(\tau_n)\to -A_{bk},
\]

and the literal sure-Quit update gains at least (g_0/2) on a common tail.
This remains valid whether (b) was already literal Never or retained a
lower-order positive hazard.

## Positive-minimum collar

The terminal semantic carrier is compact by
`quittingTerminalSemanticCarrier_isCompact` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and total
semantic debt is continuous.  The checked equivalence
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in
`UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`
justifies an attained minimum (D_*>0).

Let (y) be any semantic cluster point of the descendants.  Exact cap
attainment and the endpoint limits above give

\[
U_b(y)=r_b(\{k\}),\qquad B_b(y)=s_b.
\]

For every minimum point (z\in\mathcal F), the hypotheses of
`minimumTerminalSemantic_singletonMargin` are satisfied and its conclusion
is exactly

\[
D_*\le B_b(z)-s_b.
\]

The orientation is therefore

\[
B_b(z)-B_b(y)\ge D_*.
\]

In particular no descendant cluster belongs to the minimum fibre.  If no uniform
δ in (3.6) existed, a subsequence would have
(D(\tau_n)\downarrow D_*); compactness would yield a cluster point (y)
with (D(y)=D_*), contradicting the preceding collar.  Thus some
sequence-dependent (\delta>0) satisfies

\[
D(\tau_n)\ge D_*+\delta
\]

eventually.  The proof neither asserts nor needs an explicit universal value
of (\delta).

## Deleted-law nonrenewal

After replacing (b) by a sure date-zero quitter, the full terminal law does
converge to (\delta_{\{b\}}), since all other date-zero hazards vanish.
However, deleting (b) from this new profile restores precisely the old
opponents, among whom (k) still has the leading hazard.  The deleted law
therefore converges to (\delta_{\{k\}}), not to an inert lower-order
background.

Accordingly the new target is not a renewable one-owner-(b) diffuse source.
Turning (k) to Never and softening (b)'s sure Quit are two additional
changes, neither supplied as a unilateral cap response by Theorem 2.1.  The
off-minimum inequality is a state separation rather than a telescoping
potential charge, so it cannot be summed repeatedly without a returned
chronological seam.  All of these limitations are stated explicitly.

## Boundary checks

- The blocker cannot equal the leading owner because (A_{kk}=0) while its
  selected entry is strictly negative.
- Lower-order positive outsiders are not deleted.  They affect finite values
  but vanish in the normalized one-owner law and the strict endpoint limits.
- The cap conclusion depends on stationarity of the child and is applied only
  to the stationary descendants produced by the period-one Never descent.
- The collar applies to the cap coordinate, not directly to prescribed
  payoff or terminal-law distance.
- The first removed predecessor need not be the blocker; the note keeps these
  labels distinct.

The displayed `(4.1)` has a minor rendering typo (`)longrightarrow`), but its
mathematical statement and all subsequent uses are unambiguous.  No
mathematical revision is required.

## Origin-independent refactor delta

I checked the refactored note at exact SHA-256
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`.
The theorem now expressly accepts any literal stationary sequence satisfying
the Section 1 hypotheses, regardless of how it was produced, and expressly
does not assert that a support-two or support-four construction reaches such
a singleton.  The earlier display (4.1) is also repaired.

This change is mathematically valid.  The proof uses only: one fixed leading
owner with hazard (q_n>0\to0); total retained outsider hazard (o(q_n));
stationarity (including literal Never coordinates); the Fin4 hard
no-homogeneous singleton matrix; and positive minimum terminal-semantic debt.
It nowhere uses the number, labels, or profitability of earlier Never
updates.  Consequently the conclusion applies unchanged to a singleton
produced by the support-four two-owner exit theorem.  **Delta PASS** for the
exact refactored hash.
