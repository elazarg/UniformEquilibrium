# Source-facing gate check

Reviewer: `CODEX_RIEMANN`

## Verdict

The corrected **three-way source split is exact**:

1. the limiting cap admits a positive-absorption exact root; or
2. no such root exists and the limiting binding set is all four players; or
3. no such root exists and the limiting binding set has cardinality three.

If arm 1 fails, every exact limiting root has absorption zero.  A product root
has zero absorption only when every marginal is Continue, while closedness of
the exact-root inequalities supplies all-Continue at the cap limit.  Hence it
is the unique limiting exact root, and the conditional proper-binding theorem
applies.  Full binding versus proper binding then gives arms 2 and 3.

The body, adapter, consumer, and scope sections consistently retain this
qualification.  In particular, they no longer claim unconditional limiting
root uniqueness.

## Remaining wording defect

The document title still says unconditionally:

> A proper nonconstant strict Fin4 maximal ray has three binding players

That is false as a source-facing summary unless the missing premise “the
limiting cap has no positive-absorption exact root” is included.  Change the
heading to, for example:

> A strict Fin4 maximal ray with no positive limiting root has three binding
> players when its binding set is proper

After that heading correction, I find no remaining unconditional card-three
claim in the text.

There are also two malformed `bar b` renderings containing a control
character, in assumption 5 and in the one-clock paragraph.  They do not alter
the mathematics but should be normalized before export.

## Gate recommendation

**Hold only for the heading/control-character correction; otherwise PASS.**

Post-repair addendum: **PASS** — the title now states the exhaustive three-way split, both `\bar b` renderings are corrected, and no unconditional source-facing card-three claim remains.
