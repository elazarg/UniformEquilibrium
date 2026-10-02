# Mathematical audit of open pull requests — 2026-08-29

## Status

I inspected the mathematical content of every open pull request, comparing each
branch with its declared base.  This is not an engineering, style, build, or
integration review.  I found no new proof of Fin4 and no counterexample.  Four
PR layers contain genuinely useful mathematics; two are primarily exact-search
infrastructure; two add no material mathematics at the current frontier.

The stacked PRs must not be double-counted:

```text
main -> #82 -> #84 -> #85
```

## PR-by-PR verdict

### PR #77 — retain arbitrary resolution through source-faithful causalization

This is genuine and potentially important quantitative infrastructure.

The key observation is that, sufficiently near a positive global minimum, the
exact cap-root correspondence freezes to all Continue.  Inducting through a
finite cap-Nash prefix word then makes every root literally all Continue, so the
word survival is exactly one.  A retained terminal atom therefore loses no mass
through the causalization prefix.  The PR propagates an arbitrary requested
positive resolution through the source-faithful singleton and forced-pair
constructions, including equality-arm cycle regeneration.

This removes a real potential failure mode: repeated source reconstruction no
longer has to consume a new constant factor from the atom floor.  It does not
orient the recursive transition, prove a renewable rank decrease, or consume
the resulting concentrated packet.

Mathematical verdict: **new, sound-looking, and important as renewal
infrastructure; not a terminal consumer.**

Files inspected include
`SourceFaithfulRetainedResolution.lean`,
`SourceFaithfulRenewedSingleton.lean`,
`ExplicitResolutionForcedPair.lean`, and `PaidCycleRenewal.lean`.

### PR #78 — eliminate singleton binding on a strict Fin4 ray

The argument is mathematically valid: a small positive singleton hazard at a
singleton binding face gives a non-all-Continue exact root, contradicting cap
uniqueness.

It is no longer new.  Current `main` contains the stronger generic result in
`BindingCollisionGainPositivity.lean`, including
`bindingFinset_card_ne_one_of_uniqueAllContinue` and a pair-face strengthening.

Mathematical verdict: **correct but superseded; no new frontier content.**

### PR #80 — consume the strong concentrated Fin4 atlas packet

This PR contains research notes rather than a completed consumer.

The decreasing-resolution schedule is elementary and useful, but PR #77 gives
a stronger literal retained-resolution construction.  The uniform-escape note
records a correct-looking telescope and the familiar deletion-versus-join
orientation at a paid pair, but it explicitly stops before chronological
composition or a regenerated rank.

Mathematical verdict: **diagnostic only at the current frontier; the title's
consumer is not supplied, and the useful scale point is superseded by #77.**

### PR #81 — exact fixed-table counterexample certificates

There is useful mathematical/computational content here:

* a finite rational lower-certificate verifier whose soundness implies a lower
  bound on terminal exploitability; and
* a fixed-table semidecision that is complete if the table has a positive
  exploitability infimum.

This is a legitimate negative-route certification theorem.  It does not find a
table or produce a certificate in this PR.

The strict-inert wrapper is not itself evidence that strict inertness forces a
counterexample: its positivity input is the already supplied terminal
exploitability witness in the hard residual.  Thus the search conclusion is
being recovered from an assumption that already says the table has a positive
gap, rather than from the inert geometry.

Mathematical verdict: **new and useful exact-search infrastructure, but not a
structural advance on the strict-inert branch.**

Files inspected include `FinFourIndependentCertificateSoundness.lean`,
`FinFourFixedTableCounterexampleSearch.lean`, and
`StrictInertExactCounterexampleSearch.lean`.

### PR #82 — regenerate a paid reset source after cap descent

This is genuine source-provenance progress.  A quantitative debt descent along
the selected paid cap lift is made visible at one finite actual prefix.  Exact
prefix transport preserves the zero reset debt and positive incidence needed
to rerun the fixed-law reset dispatcher, while the shifted paid row remains
attached to the literal descendant profile.

The resulting alternative is an actual finite paid/reset regeneration or a
literal inert stall.  This closes the source-side realization gap that a mere
limiting debt inequality did not close.

It still supplies only a strict real-valued descent, not a well-founded or
renewable descent, and it leaves the inert arm.

Mathematical verdict: **new, sound-looking, and important provenance closure.**

File inspected: `FinFourPaidResetDescentRegeneration.lean`.

### PR #83 — source-attached exact search

This filters a global rational-table semidecision by exact equality with the
source reward table and carries an arbitrary proposition beside the output.
Completeness again assumes the source's existing positive-gap witness.

It adds no mathematical implication from source attachment or strict inertness,
and PR #81 contains the stronger fixed-table/certificate formulation.

Mathematical verdict: **a thin wrapper, not new important mathematics.**

File inspected: `FinFourSourceAttachedExactSearch.lean`.

### PR #84 — regenerate both descent arms and use a maximal exact root

Relative to #82 this contains two substantial advances.

First, it reconstructs the positive incidence needed on the repaired-owner
side, so quantitative descent of the repaired cap port also yields an actual
finite paid/reset regeneration.

Second, it replaces an arbitrary cap-root selector by a maximal-absorption exact
root.  If maximal absorption is positive, one exact prefix strictly lowers debt
and transports the paid/reset data to an actual descendant.  If it is zero,
maximality implies every exact root has zero absorption, hence every exact root
is literally all Continue.  The residual is therefore genuine cap uniqueness,
not selector-induced inertness.

This is a sharp and useful dichotomy.  It does not consume the unique-cap arm,
and its strict descent is still not well founded.

Mathematical verdict: **new and important; probably the strongest structural
advance among the open PRs.**

Files inspected: `FinFourPaidResetDoubleDescentRegeneration.lean` and
`PaidCapMaximalOneStepRegeneration.lean`.

### PR #85 — reduce the double port to double unique caps

This composes #84 on the original and repaired actual profiles.  Unique
all-Continue at a source cap makes every selected cap-prefix semantic pair
literally equal to its source and every selected root all Continue, so every
summable selected port is a genuine zero-charge inert stall.  Applying the
maximal-root alternative on both sides yields:

```text
source-side finite paid/reset regeneration
or repaired-side finite paid/reset regeneration
or unique all-Continue at both actual caps.
```

This is a clean selector-independent normal form and is potentially important
because it identifies the exact residual configuration.  It does not prove
that the double-unique configuration is impossible and does not make either
strict descent renewable.

Mathematical verdict: **new and useful classification, conditional on the #82
and #84 stack; not a consumer of the final inert obstruction.**

Post-audit implementation correction: the proof of
`repairedOwner_debt_eq_zero` in the PR incorrectly treats the stationary
unilateral cap as definitionally equal to the unrestricted terminal-semantic
envelope.  The mathematical claim nevertheless survives.  The checked theorem
`quittingTerminalSemanticPair_stationary_envelope_eq_cap` gives exactly that
equality for every stationary root, using the full behavioral best-reply value,
and `repaired_owner_cap_eq_payoff` then makes the debt zero.  The imported PR
#84 layer already uses this bridge for the same repaired profile in
`exists_repairedPaidResetRegeneration`.  Thus this is a real proof-script gap,
not a false stationary-to-behavioral inference or a failure of the #85
dichotomy.

File inspected: `FinFourPaidCapMaximalDoubleRegeneration.lean`.

## Net assessment

The mathematically valuable chain is:

```text
#77: retained quantitative resolution

#82: source-side finite paid/reset regeneration
  -> #84: repaired-side regeneration plus maximal-root dichotomy
  -> #85: double-port reduction to two genuine unique-all-Continue caps
```

PR #81 is independently useful for exact counterexample certification.  PRs
#78, #80, and #83 should not be counted as new frontier progress.

The open PRs therefore sharpen and source-attach the remaining obstruction;
they do not remove it.  After the stacked regeneration chain, the unresolved
mathematical object is a double actual-cap configuration in which all Continue
is the unique exact root on both the source and repaired sides, while the paid
reset geometry remains present.  No open PR supplies a terminal compiler, a
renewable finite rank, or a contradiction for that configuration.

## Exact scope of this audit

I inspected the open branches and their declared-base diffs, with narrow source
checks against current `main`.  In particular, I compared PR #78 with the
stronger declarations already on `main`.  There were no mathematical review
comments attached to the eight PRs at inspection time.  This note makes no
claim about build status or integration quality.
