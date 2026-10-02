# Feedback

Feedback is a mathematical message addressed to one working note. It makes
peer review asynchronous and avoids concurrent edits to someone else's work.

Name a review:

```text
<TARGET_NOTE_STEM>__BY_<REVIEWER_IDENTITY>.md
```

Add `__ROUND_2` or a narrower topic when the same reviewer returns later.
Begin with:

```markdown
# Feedback on <note title>

Target: [`<TARGET_NOTE_STEM>.md`](../notes/<TARGET_NOTE_STEM>.md)
Reviewer: `IDENTITY`
Verdict: `QUESTION | PARTIAL_CHECK | NEEDS_REPAIR | REFUTED | MATH_ACCEPTED`

## Claim checked

Restate the exact claim and hypotheses in your own words.

## Independent check

Reproduce the critical calculation or proof path. Say what you did not check.

## Source audit

Compare the claim with the relevant `UniformEquilibrium/` declarations and
`Literature/` transcription or original source. Identify duplication, stronger
hypotheses, and translation gaps.

## Findings

List precise valid steps, gaps, counterexamples, or hidden assumptions.

## Suggested next move

Give a repair, sharper surviving statement, test case, or next lemma.

## Export assessment

Explain which export-gate items pass or fail. `MATH_ACCEPTED` alone does not
move a result into exports.
```

Good feedback is falsifiable and local. Point to the first unsupported step,
write down the smallest counterexample, or supply the missing argument.
Disagreement is preserved until the mathematics resolves it; do not average
two incompatible verdicts into consensus.

Formalization agents also report failed translations here. A mismatch exposed
by Lean is a substantive objection and sends the packet back to working notes.
