# Review of every Fin4 tangent frontier has a quantitative paid port

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict: **PASS**

## Claim audited

For an arbitrary Fin4 positive-minimum tangent family, any active mover
\(p\), and any compact full-replacement cluster \(y\) for that mover, the
literal target profiles

\[
Y_n=\texttt{frontier.fullReplacementProfile}\ p\
       (\texttt{endpoint.subseq}\ n)
\]

eventually carry a paid first-disagreement row for one fixed nonmover
\(j\), with declared gain \(D_*/16\), an actual-support source witness, and
the three stated reach floors.  The claim is only a producer reduction to
the paid-port waist; it does not temporalize the full replacement or consume
the paid port.

## Declaration-level verification

The proof is sound.

1. `FullReplacementCluster.cluster_mem` places \(y\) in the terminal
   semantic carrier.  The frontier's `base_minimum` therefore gives
   \(D(y)\ge D_*\).

2. `FullReplacementCluster.mover_debt_eq_zero` is unconditional: it uses
   the exact diagonal identity and the stored vanishing-regret replacement
   bound, not flatness, total slope, support entry, or the minimum-fibre
   case.  Hence \(d_p(y)=0\).

3. Carrier debts are coordinatewise nonnegative.  On `Fin 4`, the three
   nonmovers therefore carry total debt at least \(D_*\), so one fixed
   \(j\ne p\) satisfies \(d_j(y)\ge D_*/3\).  The observer is selected once
   from the limiting cluster; it is not allowed to vary with \(n\).

4. `FullReplacementCluster.fullReplacement_tendsto` is literally
   convergence of the semantic pairs of the displayed \(Y_n\).  Continuity
   of `quittingTerminalSemanticDebt` gives
   \(d_j(Y_n)\ge D_*/4\) eventually.

5. Applying
   `positiveDebt_exists_actualJointReach_paidRow_mem_support` to \(Y_n\),
   observer \(j\), and \(\Delta=D_*/4\) returns exactly:

   \[
   \text{declared gain}=\Delta/4=D_*/16,
   \]

   \[
   \Delta\le4M\,\operatorname{OwnSurvival},\qquad
   \Delta\le8M\,\operatorname{OppReach},
   \]

   and

   \[
   \Delta^2\le32M^2\,\operatorname{JointReach}.
   \]

   Its source witness belongs to the support of \(j\)'s actual complete
   stopping law.  These are unrestricted behavioral-cap debts; no
   finite-clock or stationary restriction enters.

6. By the definitions of `fullReplacementProfile` and
   `fullReplacementPair`, \(Y_n\) is the literal complete \(p\)-strategy
   replacement of
   `frontier.source (endpoint.subseq n)`.  Earlier absorption and arbitrary
   mixed tails are already part of those actual profiles and do not alter
   this typing.

## Falsification checks

- If the endpoint stays on the minimum fibre, the nonmover total is exactly
  \(D_*\), so the argument still has its floor.
- If it is off minimum, the lower bound only improves; no return to the base
  is inferred.
- If support entry occurs, the selected observer may be the entering
  coordinate but need not be.  Nothing uses a no-entry condition.
- The selected mover cannot also be the observer because its limiting debt
  is exactly zero while \(D_*>0\).
- At \(D_*=0\) the conclusion loses every positive floor, as the note
  correctly records.
- A positive reward bound need not be separately postulated: positive debt
  and \(|r|\le M\) already exclude \(M=0\).  The invoked theorem itself only
  requires the displayed reward bound and \(\Delta>0\).

## Scope and novelty

The result really collapses the positive-slope, flat-entry, and off-minimum
*row-production* tags: the same quantitative row exists before those tags
are inspected.  It does not collapse the downstream paid-cap trichotomy.
In particular, neither the full replacement nor the paid row is a
Nash--Bellman edge, quantitative debt descent is not made well founded, and
the all-Continue inert branch remains.

This is a useful uniform adapter rather than a terminal theorem.  I found no
mathematical or source-provenance blocker to export at that stated scope.

## Frozen export-candidate audit

I separately checked
`/tmp/FIN4_TANGENT_FRONTIER_QUANTITATIVE_PAID_PORT.md` at SHA-256
`582bf7f52539774f8a2f853445fee6f1a5afff448f820aeef4173d55427e8cc4`.
It preserves the theorem and all scope limitations audited above.  Its
statement quantifies over arbitrary behavioral profiles and its source audit,
boundary tests, checked adapter, downstream paid-port trichotomy, and Lean
handoff are complete.  All cited source files exist.  The packet has balanced
mathematical delimiters and contains no control bytes or tab characters.

Two packaging deltas are needed before placement: add this review beside the
already linked `PAIRED_HULL_REVIEW` review, and replace the retired mutable
question link by plain text naming the maintained quantitative paid-port
question.  Neither edit changes the mathematics.  Subject to those changes,
the frozen candidate **PASSES** the export gate.
