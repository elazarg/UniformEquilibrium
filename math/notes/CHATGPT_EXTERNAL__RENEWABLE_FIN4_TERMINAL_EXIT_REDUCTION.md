# Correct mathematical reduction of the three renewable Fin4 terminal exits

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; independently reviewed core with statement repairs still
required, and no terminal consumer claimed.

Source: supplied as `ephemeral/TERMINAL_EXIT_REDUCTION_CORRECTED.md` and moved
here without rewriting the mathematical body.

## Status

This note gives the strongest consequence of the three terminal exits that
follows from the retained packets without adding a chronology-seam hypothesis.
It is a rigorous reduction, not a complete consumption theorem.

The previously proposed proof by "exactifying" static response rectangles into
closed punishment-floor Nash--Bellman blocks was invalid: neither the tangent
atom packet nor source-faithful causalization supplies compatible successor
seams for those horizontal strategy replacements. Repeating such a purported
block is therefore unavailable.

## Setup

Let `b` be the base terminal-semantic pair of a positive-minimum tangent
family. Write

\[
 d_i(z)=B_i(z)-U_i(z),\qquad D(z)=\sum_i d_i(z),\qquad D(b)=D_*>0.
\]

Fix an active mover `m`. Let `t_{mi}` be its tangent row, and let `c` be any
cluster of the literal full-replacement profiles along a strict subsequence.
The checked endpoint inequalities are

\[
 d_i(c)-d_i(b)\ge t_{mi}\quad\text{for every }i,
 \tag{1}
\]

with equality in the mover coordinate,

\[
 d_m(c)-d_m(b)=t_{mm}=-d_m(b),
 \qquad d_m(c)=0.
 \tag{2}
\]

Consequently

\[
 D(c)-D_*\ge s_m:=\sum_i t_{mi}.
 \tag{3}
\]

These facts use the literal full-replacement subsequence; no independently
selected endpoint is introduced.

## 1. Positive total slope

Assume `s_m>0`. Equation (3) gives

\[
 D(c)>D_*.
\]

Thus every full-replacement cluster for this mover is strictly off the minimum
fibre. Moreover, by (2),

\[
 \sum_{i\ne m} t_{mi}=s_m+d_m(b)>0.
\]

For four players some `i\ne m` satisfies

\[
 t_{mi}\ge \frac{s_m+d_m(b)}{3}>0. \tag{4}
\]

The normalized tangent convergence and the common-response rectangle decoder
therefore produce one fixed positive charge

\[
 q=\frac{7}{16}t_{mi}>0
\]

and, eventually on the literal tangent source sequence, a strong
vanishing-debt atom alternative with decoder error tending to zero. Exact
Nash-prefix stack access preserves this atom after arbitrarily long prefixes.

This is the strongest unconditional positive-slope output. It is still a
static deviation/atom output at the suffix. The increasingly long exact
prefixes have vanishing total absorption charge when two active debtors are
retained, so the stack itself is not a positive admissible return.

## 2. Flat support entry

Assume

\[
 s_m=0,
 \qquad d_i(b)=0,
 \qquad t_{mi}>0
\]

for an entrant `i` outside the positive-debt support of `b`.

For a full-replacement cluster `c`, there are two cases.

### 2.1 Off-minimum endpoint

If `D(c)>D_*`, the checked flat-endpoint theorem yields an eventually fixed
positive-gain paid first-disagreement row on the literal full-replacement
profiles. This is exactly the third terminal output.

### 2.2 Minimum-fibre endpoint

Suppose `D(c)=D_*`. In (1), all coordinate defects

\[
 e_j=(d_j(c)-d_j(b))-t_{mj}
\]

are nonnegative, while

\[
 \sum_j e_j=(D(c)-D_*)-s_m=0.
\]

Hence every defect vanishes:

\[
 d_j(c)-d_j(b)=t_{mj}\quad\text{for all }j. \tag{5}
\]

In particular

\[
 d_m(c)=0,
 \qquad d_i(c)=t_{mi}>0. \tag{6}
\]

There is a stronger exact chord statement. For `0<theta<1`, form the literal
stopping-law mixtures between each retained source profile and its full
replacement, and compactify them along the same endpoint subsequence. Let
`x_theta` be any resulting semantic limit. Coordinate debt is convex along a
one-player stopping-law mixture, so

\[
 d_j(x_\theta)\le (1-\theta)d_j(b)+\theta d_j(c). \tag{7}
\]

The point `x_theta` lies in the semantic carrier, hence `D(x_theta)>=D_*`.
Summing (7), and using `D(b)=D(c)=D_*`, gives the reverse upper bound
`D(x_theta)<=D_*`. Therefore equality holds. The nonnegative coordinate chord
defects in (7) have zero sum and hence vanish individually:

\[
 d_j(x_\theta)=(1-\theta)d_j(b)+\theta d_j(c)
 \quad\text{for every }j. \tag{8}
\]

For every old active coordinate `j`, the right side is positive because
`theta<1` and `d_j(b)>0`. By (6), the entrant coordinate is also positive
because `theta>0`. Thus

\[
 \operatorname{supp}_+(b)\subsetneq\operatorname{supp}_+(x_\theta).
 \tag{9}
\]

So a minimum-fibre support entry gives a complete exact-minimum
**support-expansion** source on the same literal mixture sequence, not a
near-return and not a contradiction.

## 3. Off-minimum paid first disagreement

The third exit already consists of

\[
 D(c)>D_*

a fixed observer distinct from the mover, a fixed gain `g>0`, and eventually a
paid first-disagreement row on the literal full-replacement profiles.

Applying the paid cap-lift construction to each such actual receiving profile
gives the exact trichotomy:

1. positive total cap-lift absorption and zero cap displacement, which is a
   positive cumulative admissible-payoff near-return and hence a uniform
   equilibrium payoff;
2. positive cap displacement, which pays a strict quantitative drop in total
   semantic debt; or
3. zero total absorption, in which every selected exact root is all Continue
   and the paid row shifts through every prefix without loss.

The second branch is a strict real-valued descent, but its size is proportional
to the cap displacement and may tend to zero. The third branch is the genuine
unique/all-Continue inert obstruction. Current maximal-root regeneration
sharpens branches 2 and 3 to an immediate paid/reset regeneration on one of two
actual sources, or a double unique-all-Continue cap. It does not eliminate the
last case and does not make repeated real descent well founded.

## 4. Combined exact reduction

Every renewable terminal exit therefore yields one of the following:

- a fixed strong vanishing-debt atom with arbitrary exact-prefix access;
- a source-faithful exact-minimum point with strictly larger positive-debt
  support;
- a positive cumulative admissible-payoff near-return;
- a regenerated paid/reset source after strict semantic-debt descent; or
- a unique/all-Continue inert cap (in the sharpened two-source form, a double
  unique cap).

The original support-descending renewal trace can be extended by the
support-expansion edge in the second bullet, but support expansion and support
drop can alternate. Support cardinality alone is no longer well founded, and
a repeated support label is not yet an admissible chronological cycle.

## 5. Exact missing theorem

A complete consumer now reduces to either of two genuinely equivalent forms.

### A. Atom chronology

Convert the fixed strong suffix atom, after arbitrary exact-prefix access, into
one source-faithful root sequence carrying infinitely many compatible marked
rows whose cumulative refusal/acceptance charge is positive. The recently
proved finite-refusal ledger would then bound that charge by one player's
unrestricted debt and yield a contradiction or a terminal approximation.
The missing datum is nested compatibility of the marked suffixes; arbitrary
long one-mark stacks do not provide it.

### B. Support-recurrence exactification

When support expansion and support drop revisit a finite support label, compile
the resulting loop of literal minimum-fibre full replacements into an exact
punishment-floor admissible path. The common-response cap compiler controls
cap displacement on each horizontal seam, but the retained packets still do
not turn those seams into successor-compatible Bellman edges.

Without A or B, the implication

\[
 \text{`FinFourRenewableTerminalExit node`}
 \Longrightarrow
 \text{positive admissible near-return}
\]

has not been proved. In particular, the earlier geometric-amplification note
was invalid because it began by assuming the exact closed block whose
construction is the open problem.
