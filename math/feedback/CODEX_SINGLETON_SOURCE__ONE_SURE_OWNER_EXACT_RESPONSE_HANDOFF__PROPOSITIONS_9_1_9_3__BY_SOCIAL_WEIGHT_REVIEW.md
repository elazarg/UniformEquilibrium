# Review of Propositions 9.1--9.3

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS, with two scope/bookkeeping clarifications.**

## Claims checked

The reviewed section asserts that every finite-clock positive-global-minimum
profile on `Fin 4` admits the following exact reduction.

1. A canonical exact-response rule keeps all finite clocks in one fixed
   horizon and hence gives either an off-minimum response or a literal finite
   horizontal response cycle.
2. If every strategy on the cycle is a pure deadline or Never, the cycle has
   one common earliest date and projects to a strict Boolean toggle cycle.
3. Mixed finite-clock backgrounds can be purified in at most four
   minimum-fibre steps, unless one first reaches an off-minimum actual profile
   from which a complete response of gain greater than `D_*/4` is available.

All caps here are against unrestricted behavioral replacements.

## Proposition 9.1: PASS

Let `H_{-i}` be the largest finite date in the support of any opponent.  For
fixed opponents, every finite pure time strictly after `H_{-i}` has the same
payoff: on opponent absorption the outcome is already fixed, and on opponent
survival the player eventually Quits alone.  Never is the one additional
endpoint.  Pure-time extremality therefore reduces the complete cap to

\[
 0,1,\ldots,H_{-i}+1,\infty.
\]

The proposed tie rule is exactly what prevents horizon growth.  If some
opponent uses the date `H_0+1`, that opponent cannot be on its original law
and hence Quits there surely.  Every later finite time and Never then induce
the same terminal law for the current mover, so the tie rule selects Never.
If no opponent uses `H_0+1`, the finite response bound is already at most
`H_0+1`.  Thus the invariant is valid.

At a minimum state, a maximum-debt player has debt at least `D_*/4`.  Replacing
that player by an exact pure-time maximizer gains exactly the old debt and
kills the mover debt.  Carrier minimality gives the exact minimum/off-minimum
split.  In the equality lane the visited profile set is finite, and positive
gain excludes a self-loop, so literal recurrence produces a nontrivial
horizontal response cycle.

No compactness, cap attainment at an unbounded time, or stationary
restriction is hidden here.

## Proposition 9.2: PASS

At every positive global minimum the singleton moat gives

\[
 B_i-r_i(\{i\})\ge D_*>0.
\]

If a pure response stopped strictly before every opponent, it would attain
exactly the singleton payoff.  It therefore cannot be an exact best response.
The earliest finite stopping date is consequently nondecreasing along every
edge.  Literal recurrence forces it to be constant around the cycle.

Once that date is fixed, a profitable pure-time change has only two possible
effects:

- an outsider moves to the common date and joins the current quitter set; or
- a current quitter moves later/never while another quitter remains and
  leaves the set.

Changing between two dates strictly after the common absorbing date changes
no payoff, and leaving a singleton would raise the earliest date, which the
cycle excludes.  Hence every edge is exactly a strict nonempty Boolean toggle

\[
 S\longrightarrow S\triangle\{i\}.
\]

The all-Never profile is not a missing boundary case: its total debt is zero
when every singleton payoff is nonpositive, while any positive singleton
payoff violates the positive singleton moat.

This proposition correctly claims only a same-stage static toggle cycle, not
a Nash--Bellman chronology.

## Proposition 9.3: PASS

For a non-pure finite stopping law `pi` of a zero-debt player `h`, payoff
affinity gives

\[
 B_h=U_h=\sum_q\pi(q)V_h(q),\qquad V_h(q)\le B_h.
\]

Therefore every positive-support pure time is itself cap-attaining.  Replacing
`h` by any such atom is a literal exact best response of gain zero and keeps
its own debt zero.  Selecting a support completion of least total debt gives
the honest dichotomy: an equality completion if any exists, and a strict
off-minimum completion otherwise.  No Jensen average is being mistaken for
one favorable atom.

For a positive-debt non-pure player, an exact pure cap response gives the same
purification directly.  Every equality step permanently removes one
non-pure coordinate, because subsequent steps alter only their own
coordinate and every selected replacement is pure.  Hence at most four
minimum-fibre purifications occur.

From a strict completion `tau`, choose a maximum-debt player `p`.  Then

\[
 d_p(\tau)\ge D(\tau)/4>D_*/4,
\]

and finite-clock cap attainment supplies the asserted paid complete response.
Its first-disagreement row is literal and includes Never if that is the
selected endpoint.

## Clarifications required in any export or formal interface

1. **Step count.**  The edge with gain greater than `D_*/4` is generally a
   second response launched *from* the strict off-minimum completion.  The
   purification edge which first leaves the minimum fibre may have gain zero
   (or an arbitrarily small positive gain).  Thus the exact bound is:

   > at most four purifications, followed, in the strict arm, by one paid
   > response edge.

   The current proof has this construction, but shorthand such as “after at
   most four responses” would be false if it counted the paid edge too.

2. **Source attachment.**  The result retains a literal finite horizontal
   ancestry from the supplied minimum profile to the off-minimum profile and
   its paid response.  It does not by itself preserve a marked atom, a
   `FinFourMinimumAtomProducer` chronology, or a cap--Nash prefix stack.  If
   “source-attached” is used in a stronger atlas-type sense, those fields need
   a separate wrapper.  For the generic actual-profile paid-cap port, the
   literal ancestry and same reward table are sufficient.

## Conjecture-facing value

The propositions genuinely eliminate unbounded calendar growth and mixed
finite-clock backgrounds as independent subbranches.  They reduce every
finite-clock positive minimum to

\[
 \text{off-minimum actual paid response}
 \quad\lor\quad
 \text{pure same-stage strict-toggle cycle at minimum points}.
\]

They do not consume either output.  The first enters the already-known
paid-cap descent/inert trichotomy.  The second is horizontal static geometry;
its conversion to a product/root consumer is handled only in further special
topologies.  No terminal approximate equilibrium or unconditional Fin4
closure follows from Propositions 9.1--9.3 alone.
