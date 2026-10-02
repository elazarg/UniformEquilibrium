# Packet gate: two-date timing-Nash terminal-debt half bound

Reviewer: CODEX_MINER

Packet:
[`exports/TWO_DATE_TIMING_NASH_TERMINAL_DEBT_HALF_BOUND.md`](../exports/TWO_DATE_TIMING_NASH_TERMINAL_DEBT_HALF_BOUND.md)

## Delta verdict after source repair

**PASS.**  The packet now states that the `K=2` theorem by itself reaches
level `48`, while the subsequently reviewed general-`K` theorem subsumes the
universal half inequality and reaches level `59`.  It retains the present
packet for its genuinely sharp self-contained `K=2` equality theorem and
unique rational regression, which the general theorem's fixed-prefix result
uses.  The Scope section repeats the same distinction and no longer presents
level `49` as the current global frontier.  This exactly resolves the only
gate objection below; no mathematical or packaging objection remains.

A direct Markdown link to
[`FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md`](../exports/FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md)
would improve navigation, but the current explicit source comparison is
unambiguous and this is not a blocking repair.

## Original verdict

**REVISE for one current-source disposition; mathematical packet PASS.**  The
two mandatory theorem repairs are incorporated correctly, the new normalized
Fin4 hierarchy cutoff `M<=48` is exact, and the packet otherwise satisfies
the proof, behavioral-strategy, boundary, adapter, and Lean-handoff gates.

The required update is that the packet's novelty/source audit predates the
now twice-reviewed stronger note
[`CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`](../notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md).
That result contains the universal `K=2` half bound as a special case and
improves the hierarchy cutoff at `K=3` to `59`.  The packet should either:

1. add this comparison and remain explicitly the self-contained **sharp
   `K=2` base/equality regression** used by the general theorem; or
2. be folded into a forthcoming general-`K` export packet if the queue is to
   retain only the strongest statement.

The general note's Section 8 invokes this reviewed two-date source and does
not make the self-contained sharp base valueless, so option 1 is defensible.
What is not acceptable under the current source-audit gate is leaving the
stronger reviewed result unmentioned and describing level `49` as the current
frontier without qualification.

## Mathematical and semantic gate

The exact statement quantifies over every nonempty finite player set, every
reward table bounded by `R>=0`, and every mixed Nash equilibrium of the
`{0,1,Never}` timing game.  The behavioral hazard realization retains Never
and handles zero denominators only on zero-reach histories.

The four pure-time values are exhausted correctly: the permitted values
`V_0,V_1,V_N` and one common after-support value `L`.  Mixed Nash gives
`U=max(V_0,V_1,V_N)`, and checked pure-time extremality gives the cap against
all randomized history-dependent behavioral deviations.

The repaired comparisons are now safe:

\[
d\le\max(0,L-V_1)\le2Rh_1,
\]

\[
d\le\max(0,L-V_0)\le2Rh_0+(R-s)h_1,
\qquad d\le as.
\]

The right sides are nonnegative in the positive-singleton arm.  The scalar
elimination yields

\[
 d/R\le {4x\over x^2+3x+4}\le1/2
\]

with no division in the `R=0` or zero-debt cases.

The sharpness proof now uses the required equilibrium-specific dummy
argument.  It does not claim global strict dominance of date one: it excludes
dummy date zero, rules out either active player being sure at date zero, then
uses positive date-one reach to force both dummies to Never.  The active
zero-sum matrix has the unique law `(1/4,1/4,1/2)`, and player 1's exact late
debt is `1/2`.

## Hierarchy delta

The two-date pair belongs literally to every relevant finite-clock center.
Its diagonal midpoint is at distance at most half the maximum debt, hence at
most `R/4`.  For normalized Fin4,

\[
 1/4\le12/M\quad\Longleftrightarrow\quad M\le48.
\]

Thus `L_M(r)=0` through level `48`.  The packet correctly retains the
`HasEscapeAwareQuantileClockCompression reward` qualification in its Lean
handoff for the currently checked lower-value API.  The ordinary hierarchy
statement itself is unconditional in the already reviewed export.

As a statement about this producer, level `49` is the first level it does not
cover.  It is no longer the best current universal producer after the
general-`K` theorem, which is exactly why the source comparison above is
mandatory.

## Remaining README items

The packet has complete finite data and proof, an unrestricted-deviation
audit, exact positive and negative boundary tests, two independent reviews,
an arbitrary-table finite-Nash adapter, the actual-center hierarchy consumer,
and a narrow Lean handoff that does not assume the desired result as a field.
No new mathematical claim entered during assembly.

After the source/disposition update, I would record **PASS** if this packet is
kept as the sharp self-contained `K=2` base.  Its scope must continue to say
that it is neither a vanishing-error theorem nor a uniform-payoff result.
