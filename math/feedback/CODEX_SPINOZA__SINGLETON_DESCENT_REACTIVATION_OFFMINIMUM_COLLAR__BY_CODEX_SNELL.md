# Review of singleton descent reactivation off-minimum collar

Reviewer: `CODEX_SNELL`

Reviewed note:
[`../notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`](../notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md)

Reviewed SHA-256:
`eaea3e3f603c06f32b7dc7fd6ef3ad8ccffafeab0944884a6060f7e310cc1dc0`

## Verdict

**PASS, with one presentation-only repair requested.**  I found no
mathematical, chronological, probability-mode, or strategy-class defect.  In
equation (4.1), `longrightarrow` is missing its leading backslash; this should
be repaired when the result is assembled for export.

The theorem genuinely strengthens the reviewed tropical two-Never descent:
whenever that descent reaches a one-leading-owner descendant, the Fin4 hard
matrix supplies a fixed different player whose literal Quit-at-zero response
eventually attains the complete all-behavior cap.  Positive minimum terminal
debt then places every semantic cluster point of the descendant strictly off
the minimum fibre by one cap-coordinate collar of width at least `D_*`.

## Full-core negative-column check

For a putative Fin4 counterexample,
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` makes
the normal core the full player set.  The field `no_homogeneous` of
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` is stated on the
normal principal matrix.  Under the full-core identification that matrix is a
reindexing of the full normalized singleton matrix.  Transport by
`singletonLCPFeasible_reindexMatrix_iff` therefore gives

\[
 \neg\operatorname{HasHomogeneousSimplexSolution}(A).
\]

Since `normalizedSoloMatrix_diagonal` gives `A_{kk}=0`,
`exists_negative_entry_in_column_of_noHomogeneous` gives, for every column
`k`, a label `b(k)` with `A_{b(k),k}<0`.  The diagonal equality forces
`b(k)\ne k`.  Finiteness of `Fin 4` makes

\[
 g_0=\min_k(-A_{b(k),k})>0.
\]

Thus neither standard-Q row positivity nor punishment normality is being
silently substituted for the required negative-column statement.

## Exact finite-profile cap check

At a descendant `tau_n` with leading owner `k`, write the owner's hazard as
`q_n>0`; all other positive hazards have total `o(q_n)`, and `q_n\to0`.
Then the opponent first-quit law against `b=b(k)` converges to the singleton
`{k}`.  Consequently literal Never gives

\[
 N_{n,b}\longrightarrow r_b(\{k\}),
\]

whereas Quit at date zero gives

\[
 Q_{n,b}\longrightarrow s_b.
\]

The latter limit remains correct with arbitrary nonsingleton rewards: the
probability of any simultaneous opponent Quit in row zero is `o(1)`.
Every opponent strategy is stationary (literal Never is stationary hazard
zero), so a pure quit time `t` has exactly

\[
 (1-a_n^t)N_{n,b}+a_n^tQ_{n,b},
\]

with `a_n` the opponents' joint one-row Continue probability.  Both endpoints
are attained by literal Never and Quit at zero.  The checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` therefore upgrades
their maximum to the supremum over every complete behavioral deviation.
Because

\[
 s_b-r_b(\{k\})=-A_{bk}\ge g_0>0,
\]

Quit at zero is the exact unrestricted cap at every sufficiently large
finite `n`, not only an asymptotic best response, and its actual gain tends to
`-A_{bk}`.

This update is literal and source-attached: it changes only player `b` in the
actual descendant produced by the earlier Never updates.  The proof does not
identify a counterfactual sibling with a chronological child.

## Positive-minimum collar check

Let `y` be any cluster point of the literal terminal semantic pairs of
`tau_n`.  The preceding endpoint limits give exactly

\[
 U_b(y)=r_b(\{k\}),\qquad B_b(y)=s_b.
\]

For every minimum-fibre point `z`, the checked theorem
`minimumTerminalSemantic_singletonMargin` gives

\[
 D_*\le B_b(z)-s_b.
\]

Subtracting `B_b(y)=s_b` yields

\[
 B_b(z)-B_b(y)\ge D_*.
\]

Taking `z=y` would contradict `D_*>0`, so no cluster point lies in the
minimum fibre.  The semantic carrier is compact by
`quittingTerminalSemanticCarrier_isCompact`, and total semantic debt is
continuous by `continuous_quittingTerminalSemanticDebtSum`.  Hence the compact
cluster set has a strictly positive debt-value separation from `D_*`, proving
the eventual `D(tau_n)\ge D_*+delta` conclusion for some sequence-dependent
`delta>0`.

The positivity of `D_*` is available under the counterexample hypothesis from
`exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff` plus
coordinatewise nonnegativity of carrier debt.  It is not an extra property of
the tropical source.

## Boundary and remaining waist

- The result applies to the support-one outputs: one Never deletion from
  support two, or two chronological Never deletions from support three.  The
  reviewed support-four descent stops at support two and is not silently
  covered by this collar theorem.
- Lower-order positive hazards are retained.  They are negligible for the
  singleton and cap limits but can become leading after deletion, so they may
  not be discarded from the provenance.
- The hard blocker need not equal the predecessor removed by the first Never
  update.
- The sure-Quit target has terminal law tending to `{b}`, but deleting `b`
  exposes the old owner `k`.  It is therefore not a regenerated diffuse
  one-owner source.  The note correctly refuses to infer renewable descent,
  an additive debt budget, or a terminal equilibrium.

Accordingly, the combined result reduces the support-one tropical residual to
the existing source-attached off-minimum paid-port/source-reentry waist.  It
does not consume that waist.

## Delta review of the origin-independent refreeze

Refrozen SHA-256:
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`.

**PASS.**  The revised statement now takes the literal stationary
one-leading-owner conditions of Section 1 as its hypotheses, independently of
which chronological descent produced them.  The proof and every quantitative
conclusion are unchanged.  The revised nonclaim correctly says that the note
does not itself produce a singleton from arbitrary support two or four.  This
scope repair legitimately covers a singleton child later produced from the
support-four two-owner exit, without claiming that the earlier collar theorem
performed that production.
