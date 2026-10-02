# Review of the postmark immediate-atom / reached-two-cut producer

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS**, with two interface clarifications

## Claim reviewed

The note starts from one literal sequence of postmark restart profiles
(s_n) whose joint semantic/law points converge to a positive global minimum
((z_*,\nu)).  A fixed positive finite atom (A) of the limiting law is used
to select either:

1. a uniform date-zero (A)-atom in the same restart family; or
2. a block from date (1) to a moving finite date (e_n), with uniform
   entry reach and uniform total marginal hazard.

It then feeds the second arm into the checked positive-minimum two-cut
coercivity and paid-splice theorem.  I checked the atom selection, every
constant, the survival/hazard implications, the paid-splice outputs, and the
claimed source boundary.

The mathematics is correct.  It is a clean producer for the weak postmark
two-cut input.  It does not consume either output and it does not put the
block after an independently selected later paid row.

## 1. Compactification and the fixed atom are sound

Joint semantic/law convergence gives coordinatewise convergence of the
finite terminal-law coordinate (A).  The hard-residual minimum-law theorem
supplies (A\ne\varnothing) and

\[
\mu=\nu(A)>0.
\]

Therefore, eventually,

\[
\nu_n(A)=\sum_{t\ge0}w_{n,t}(A)>3\mu/4.
\]

No profile, law, or source rank is reselected after fixing the common strict
subsequence.  The use of countable additivity is legitimate because the
events “first terminal coalition is (A) at date (t)” are disjoint and
their union is the terminal outcome (A).

## 2. The dichotomy and constants are exact

If (w_{n,0}(A)\ge\mu/8) cofinally, strict subsequence extraction gives the
immediate arm with exactly that floor.

Otherwise the strict reverse inequality holds eventually, and

\[
\sum_{t\ge1}w_{n,t}(A)
 >3\mu/4-\mu/8=5\mu/8.
\]

For every such rank, monotone convergence of the finite partial sums gives
an (e_n>1) with

\[
\sum_{1\le t<e_n}w_{n,t}(A)>\mu/2.
\]

Every event counted at (t\ge1) requires joint Continue at date zero.
Consequently survival from the start of (s_n) to date one is greater than
(5\mu/8), and hence greater than the advertised common floor (mu/2).

At each date,

\[
w_{n,t}(A)
 =L_{n,t}\,\Pr_{q_{n,t}}(A)
 \le \Pr_{q_{n,t}}(\text{absorb})
 \le\sum_{i<4}q_{n,t,i}(Q).
\]

Summation over (1\le t<e_n) therefore gives total marginal hazard greater
than (mu/2).  Thus the choices

\[
\operatorname{entryCut}=1,
\quad \operatorname{exitCut}=e_n,
\quad \operatorname{reachFloor}=\operatorname{hazardFloor}=\mu/2
\]

are all valid.  For the checked structure one may set `markedRow = 0`; this
should be made explicit in a Lean-facing adapter.

## 3. The two-cut coercivity output and constants are correct

The checked structure does not require the entry semantic pair itself to be
near minimum.  It requires only a supplied positive global minimum, a
positive hazard floor, and positive absolute entry reach.  Therefore it may
be instantiated by the literal root sequence of (s_n) with the cuts above.

With

\[
\chi=\mu/2,
\qquad K=(1-e^{-\chi})D_*,
\qquad \delta={(e^\chi-1)D_*\over2},
\]

`offMinimum_or_exists_entryDebt_gt` gives exactly

\[
D(\operatorname{suffix}_{e_n}s_n)\ge D_*+\delta
\]

or some payer with entry debt greater than (K/8).  In Fin4, choosing
tolerance (K/16) gives conditional entry-suffix gain greater than (K/16)
and target payer debt at most (K/16).  The checked splice identity multiplies
the conditional gain by entry reach.  Since entry reach is greater than
(mu/2), the parent-level gain is strictly greater than

\[
{\mu\over2}{K\over16}={\mu K\over32}.
\]

The splice leaves every live root at times strictly before entryCut unchanged,
so date zero is retained.

The phrase “reached payer debt” is important: the (K/16) debt bound is for
the updated entry profile.  The whole parent target need not have payer debt
at most (K/16), although its payer-debt decrease equals the whole-profile
gain.

## 4. Literal-profile and ancestry precision

The block roots, dates, atom masses, and cuts are all read from the same
actual (s_n).  The checked two-cut API packages the canonical
history-independent profile reconstructed from `quittingProfileLiveRoot
s_n`.  Terminal payoffs, caps, laws, and live-root chronology agree with the
original quitting profile.  If a later declaration claims definitional
equality with the original complete behavioral strategy object (s_n), it
will need the standard live-root/canonical-profile adapter; the current
mathematical claims need only the on-live-path identity.

Cross-tail reattachment does preserve the earlier forced-pair row literally.
It cannot preserve a positive gain there: that pure pair has zero joint
Continue probability.  The note states this limitation correctly.

## 5. Comparison with the uniform-entrance postmark problem

This producer does not use the uniformly reached paid row selected in
`CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION.md`.
Its block begins after date zero of the restart tail (s_n), not necessarily
after that separately selected paid row (t_n).  Thus it **bypasses** that
row and solves the weaker input required by
`QuittingUniformlyReachedPostMarkTwoCutBlock`; it does not prove a later
reached cut downstream of every supplied paid first-disagreement row.

In the atlas application this is nevertheless genuinely postmark relative to
the original retained forced-pair date: (s_n) already starts strictly after
that date, and entryCut (=1) is one further live-tail row.

## 6. What remains open

The note correctly does not infer:

- return of the exit suffix to the minimum fibre;
- exact Nash--Bellman roots in the block;
- positive outer reach through the preceding pure pair;
- control of nonpayer cap leakage;
- a renewable child source/rank; or
- a terminal or charged-return consumer.

The immediate arm is a valid same-family positive-atom entrance for
source-faithful causalization after reindexing.  The later arm is exactly the
known off-minimum/paid waist.  No branch of that waist is eliminated here.

## Novelty and recommendation

The underlying estimate is elementary, but it improves the earlier
entryCut-(0) finite-window producer into an exhaustive source-coherent
alternative with a strict downstream cut and a fixed absolute entry-reach
floor.  This is useful adapter mathematics.

It is suitable for formalization as a producer.  It should not be advertised
as a terminal consumer or as a solution of the stronger “later than the
selected paid row” problem.  Those scope clarifications are sufficient; I
found no mathematical blocker.
