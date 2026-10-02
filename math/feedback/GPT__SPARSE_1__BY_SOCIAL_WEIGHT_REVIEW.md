# Review of `gpt/SPARSE_1.md`

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE (mathematics mostly correct; no Fin4 consumer and little
novel content).**

## Claim checked

The note claims that the sparse social-boundary certificates at a positive
global minimum follow already from the minimum singleton inequality, that
source-supported conic sparsification is still not behavioral, and that a
uniform all-Continue cap moat blocks naive small-hazard execution.

## Valid algebra

Let

\[
 a=U-s,\qquad d_i=B_i-U_i,\qquad \sum_i d_i=D_*>0.
\]

The checked minimum singleton margin gives

\[
 a_i\ge D_*-d_i=\sum_{j\ne i}d_j.
\]

Everything below is correct.

1. All coordinates of `a` are nonnegative and at most one is zero.
2. For every nonnegative weight `theta` with at least two positive
   coordinates,

   \[
   \theta\cdot a\ge
   D_*\bigl(\sum_i\theta_i-\max_i\theta_i\bigr)>0.
   \]

   Hence a closing costate satisfying `theta · s >= 0` is impossible: the
   positive averaging outcome cannot be Never and so some finite coalition
   violates the required nonpositive surplus inequality.
3. The sixteen-outcome mass--surplus pigeonhole estimate is correct.
4. For every `J` of cardinality at least two, conic Caratheodory applied
   inside the positive support of the literal source law produces a
   reweighted law on at most `|J|` source atoms whose `J`-reward moment is
   coordinatewise at least `s|J` and strict in one coordinate.

The four-player example is also correct.  Its displayed source law is

\[
 \tfrac14\delta_{\{0\}}+
 \tfrac14\delta_{\{1\}}+
 \tfrac14\delta_{\{0,1\}}+
 \tfrac14\delta_{\{2,3\}},
\]

its prescribed payoff is `(1/2,1/2,1/2,1/2)`, and its debt vector is
`(0,0,1/4,1/4)`.  The reweighting supported on the two disjoint pairs is not
an ordinary behavioral terminal law.  At a first positive-absorption date,
zero singleton mass forces at least two sure quitters; absorption is then
certain and every terminal coalition must contain one common sure pair.

The product-density rectangle identity is the standard exact likelihood
ratio characterization on an interior Boolean product law.  With boundary
zeros, product support must be a Boolean interval (subcube).  This is a
necessary product-realization test, not a chronology or rank by itself.

## The small-root calculation

The local calculation is correct after making its domain explicit.  Let `z`
be the positive global-minimum semantic pair, let `q=t h` with `h_i >= 0`
and `t` small enough that every coordinate lies in `[0,1]`, and prefix `z`
by this one product root.  If rewards are bounded by `M`, then

\[
 C_i^B(q_{-i})-Q_i(q_{-i})
 \ge c_i(q)D_*-2M(1-c_i(q)).
\]

Thus the displayed threshold gives a strict Continue endpoint gap of at
least `D_*/2`.  On this fixed cap branch, direct expansion gives

\[
 D(T_{th}z)=D_*+t\sum_i h_i
 \bigl[(U_i-s_i)-(D_*-d_i)\bigr]+O(t^2).
\]

The cancellation of the opponent-singleton rewards in the total first-order
coefficient is exact.  This is a clean local lemma.

## Required correction

The sentence that the moat by itself “rules out” rare-hazard serialization is
too strong.  A fixed endpoint gap does rule out a nontrivial **exact** root,
but a root using Quit with probability `q_i` has ordinary mixed-action regret
only of order `q_i D_*`.  Therefore arbitrarily small hazards can still be
rowwise approximate roots.  To exclude an absorbing chronology made from
such roots one needs the global refusal accumulation argument (or an
equivalent cumulative-deviation theorem): with a fixed Continue-over-Quit
gap, divergent reached Quit mass for one of finitely many players yields one
profitable behavioral deviation which refuses all those dates.

The note may safely say:

> Small hazards do not produce exact cap--Nash roots, and any absorbing
> approximate serialization would additionally have to overcome the global
> refusal account.

It should not attribute the full chronological obstruction to (6)--(7)
alone.

## Novelty audit

Most of the claimed reduction is already recorded.

- `formalized/NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER_AND_SPARSE_REWARD_BOUNDARY.md`
  contains the weighted chamber, the mass--surplus certificate, the conic
  sparse alternative, the product/behavioral realization barrier, and the
  Nash barrier.
- `notes/CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE.md`,
  Section 8, already states that at a positive minimum the sparse law for
  every fixed `J` can be selected by reweighting positive atoms of the same
  source law, and explicitly says that the changed weights are not an
  executable source law.
- `notes/CODEX_SOCIAL_PAIR__SOURCE_SUPPORTED_TWO_OUTCOME_CERTIFICATES.md`
  proves the pair specialization and gives disjoint-pair behavioral and
  product-but-non-Nash regressions.

The potentially new item is only the explicit quantitative small-root moat
and its first-order total-debt expansion.  It is a useful local negative
lemma, but it is weaker at the chronological level than the existing global
refusal machinery and does not remove a live Fin4 branch.

## Fin4 verdict

This note does **not** give a terminal approximate equilibrium, a charged
admissible return, a renewable rank transition, or a contradiction in either
the full-debt or reset-rigid chamber.  It is a correct consolidation plus a
local exact-root moat.  After the rare-hazard wording is repaired, it is
suitable as an internal note; it is not presently an export candidate and
should not be counted as an actual Fin4 consumer.
