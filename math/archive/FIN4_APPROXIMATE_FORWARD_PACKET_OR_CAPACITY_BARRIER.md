# Consume bounded exact capacity or build an approximate forward packet

## Mathematical data

Let a four-player quitting game be in the positive-minimum hard residual, and
let \(P\) be its behavioral punishment vector. Fix one compact payoff box
\(K\) containing the canonical admissible payoff region.

For a product root with Quit probabilities \(q_i\), put

\[
p_q(S)=\prod_{i\in S}q_i\prod_{i\notin S}(1-q_i),
\qquad
c(q)=p_q(\varnothing),
\]

and define its prefix evaluation by

\[
F(q,v)=\sum_{\varnothing\ne S\subseteq I}p_q(S)r(S)+c(q)v.
\]

Thus \(v\) is the continuation payoff after all players Continue, and
\(F(q,v)\) is the payoff before that root is played.

A finite forward packet of tolerance \(\delta>0\) consists of payoff vectors
\(v_0,\ldots,v_H\in K\) and product roots
\(q_0,\ldots,q_{H-1}\) such that:

1. Each construction step prefixes one root to the preceding continuation:
   
   \[
   v_{t+1}=F(q_t,v_t);
   \]

2. every action used with positive probability in \(q_t\) is within
   \(\delta\) of a best root action against \(v_t\);
3. \(v_{t,i}\ge P_i-\delta\) for every player and every date; and
4. its charge is

   \[
   C=\sum_{t<H}\Pr_{q_t}(\text{some player Quits}).
   \]

The construction index runs outward through successive prefixes. In play
order the roots are \(q_{H-1},\ldots,q_0\), with continuation values
\(v_{H-1},\ldots,v_0\), respectively. In particular, the Nash comparison for
\(q_t\) uses \(v_t\).

## Question

Prove that, for every \(\delta>0\) and every \(Q\ge0\), the hard residual
produces such a packet with \(C\ge Q\).

This conclusion implies a uniform-equilibrium payoff: compact charged
recurrence selects two packet values which are close after a fixed positive
amount of absorption, and reversing the intervening exact Bellman block gives
an approximate periodic quitting profile.

The following exact-capacity alternative may be used.  If the table has no
uniform-equilibrium payoff, then there is \(H<\infty\) such that every finite
exact Nash--Bellman block in the canonical payoff box satisfies

\[
 \sum_{t}\sum_i \Pr_{q_t}(i\text{ Quits})\le H.
\tag{B}
\]

Thus an equally useful answer is to carry \((B)\), or a source-derived bound on
one fixed positive tolerance \(\delta_0\), to a terminal consumer, a
renewable finite rank, or a complete positive-gap table.  Merely reproving
\((B)\) is not an answer.

## Macroscopic-seam alternative

At one fixed tail, all normalized small-absorption product-root motions form
the convex hull of the binding singleton-reward columns.  If that convex hull
contains zero, one synthetic small root already supplies the available
one-row compiler.  At a positive global-minimum cap every singleton inequality
has a uniform strict margin, so no such vanishing-error positive-absorption
motion exists there.

Thus an equally useful answer may instead construct a source-faithful move to
a different tail and prove one of:

1. the macroscopic semantic seam is paid by an accepted chronological charge;
2. the seam creates a renewable finite-rank transition; or
3. the robustly inert minimum-cap chamber is incompatible with the hard
   residual.

A fixed-tail normalized-motion separator without a source transition or a
consumer is only a reformulation of the bounded-capacity branch.

## Why this target is weaker than exact chronology

The roots need not be exact Nash roots. Exact Bellman successor matching is
required, but support-Nash errors may be uniformly small. Therefore a local
row with absorption of order \(h\) and support error of order \(h^2\) is
potentially usable if it can be reconstructed at each moving successor.  The
main issue is renewable moving-source construction, not exactification of one
fixed paid row.

## Required provenance for forward packets

- One fixed compact payoff carrier is chosen before \(Q\).
- Successive rows use the literal preceding Bellman value; separately selected
  local rows do not form a packet.
- The same tolerance \(\delta\) controls every row, regardless of packet length.
- The punishment-floor bound holds along the whole packet.
- The construction works for arbitrarily large \(Q\), not merely one positive
  block.

## Nonanswers

- a finite exact block with bounded total charge;
- a quadratic-error row at one frozen payoff with no renewal theorem;
- a static toggle or face cycle with no Bellman successor matching;
- cyclic, permuted, or stationary randomized rematching of actual carrier
  seams;
- support errors whose bound grows with the packet length; or
- an approximate-capacity barrier with no source consequence.
