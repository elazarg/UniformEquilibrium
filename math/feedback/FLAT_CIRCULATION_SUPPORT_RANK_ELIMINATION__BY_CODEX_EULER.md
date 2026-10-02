# Whole-packet gate for `FLAT_CIRCULATION_SUPPORT_RANK_ELIMINATION`

Reviewer: `CODEX_EULER`

Verdict: **PASS after two applied literal statement repairs.**  The
mathematics, finite-rank induction, actual-data adapter, three-consumer
reduction, behavioral semantics, source audit, boundary analysis, and Lean
handoff all pass.  The earlier theorem-level falsification remains valid.

## Exact repairs

1. In the opening reward-table type, replace the undeclared codomain symbol
   `R` by `\mathbb R` (or explicitly declare `R=\mathbb R`).
2. Theorem C must state the two chronological producer hypotheses literally,
   rather than saying only that a frontier “produces chronological
   debt-shadowing certificates.”  Use the checked quantifiers

   ```text
   hpositiveSlope :
     forall frontier,
       (exists mover, 0 < sum observer, frontier.tangent mover observer) ->
       forall eta : Real, 0 < eta ->
         Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)

   hsupportEntry :
     forall frontier,
       HasQuittingStoppingLawFlatSupportEntry
         frontier.base frontier.positiveDebtSupport frontier.tangent ->
       forall eta : Real, 0 < eta ->
         Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)

   hpaid : PaidFirstDisagreementUniformPayoffConsumer reward.
   ```

   In particular, replace “`PaidFirstDisagreementUniformPayoffConsumer r`
   holds for `(R)`” by the literal `hpaid` hypothesis.  The proof already uses
   precisely these fields, so this is only the mandatory self-contained
   statement repair.

## Gate audit

- **Statement and proof.**  The arbitrary-mover equality/strict split is
  exhaustive.  Equality invokes the checked minimum-fiber re-extraction and
  strictly lowers `positiveDebtSupport.card`; strict separation invokes the
  checked eventual fixed-gain paid-row theorem with observer distinct from
  the mover.  Strong induction is well founded, and every recursive call uses
  the checked strict cardinal inequality.
- **Actual-data adapter and consumer.**  Positive minimum supplies a tangent
  family; nonempty positive-debt support supplies an active mover; compactness
  supplies a literal full-replacement cluster.  The `(P)` and `(E)` outputs
  enter the checked all-error chronological compiler, while `(R)` has exactly
  the arguments of `PaidFirstDisagreementUniformPayoffConsumer`.  No
  conditioned packet or source reprojection is inserted.
- **Behavioral semantics.**  Semantic caps are unrestricted behavioral
  best-response suprema.  Full replacements are ordinary stopping laws, and
  the paid witnesses are actual deterministic quit-time deviations.  The
  packet does not upgrade them to Nash--Bellman roots.
- **Boundaries.**  The equality, strict-separation, support-entry, nonflat,
  and conditioned-packet boundaries are correctly separated.  In particular,
  inactive support entry is exactly the hypothesis whose presence invalidates
  the support-drop argument, and positive slope is deliberately retained.
- **Source and novelty.**  The named declarations contain the two endpoint
  arms and the old four-exit induction separately.  The arbitrary-mover
  composition, reduced three-exit induction, and deletion of `hcirculation`
  are not existing declarations.  No external literature claim is used.
- **Lean handoff and scope.**  The proposed reduced predicate, arbitrary-mover
  lemma, `Nat.strong_induction_on`, and copied three-consumer capstone are the
  narrow implementation.  The nonclaims correctly retain positive slope,
  support entry, and the paid producer as open obligations.

Both displayed statement edits were applied exactly.  No mathematical or
export-gate objection remains.
