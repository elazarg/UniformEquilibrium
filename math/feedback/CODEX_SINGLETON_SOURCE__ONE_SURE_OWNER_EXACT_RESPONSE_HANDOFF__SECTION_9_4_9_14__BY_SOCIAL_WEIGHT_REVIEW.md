# Review of the common-base cycle reduction

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS, with two statement-scope repairs.**

## Claim checked

I checked Proposition 9.4 and the subsequent support-local form
(9.13)--(9.14).  The claim is that cap Jensen convexity rules out a
two-free-player common-base strict cycle at positive global minimum, rules
out the Hamiltonian eight-cycle for a singleton host and three free players,
and reduces a surviving singleton-host six-cycle to either an off-minimum
pure face profile or an attained minimum product profile whose only debtor is
the host.

## Valid core

The common-tail construction is legitimate.  A nonempty sure base screens
every free player's complete behavioral replacement at the root.  If the
base is a singleton, only the specialization in which every free player
Continues exposes the continuation when the host deviates; choosing that
specialization's literal tail therefore suffices for all face vertices.
Revealing the free root actions to a deviator only enlarges its response
class, so

\[
B_i(\sigma_x)\leq\sum_R p_x(R)B_i(z_R)
\]

is a valid upper bound for the unrestricted behavioral cap.  Prescribed
payoff is exactly affine.  If every pure specialization in the product
support is a global minimum, carrier minimality forces equality in the total
Jensen bound and hence equality in every coordinatewise cap bound.

At an induced-game Nash point every free coordinate has zero complete debt:
the sure base makes all behavior after the root irrelevant for a free
deviator.  Coordinatewise Jensen equality then forces every free debt to
vanish at every positive-weight pure specialization.  If one such
specialization is a cycle vertex, its strict outgoing free-player toggle is
a legal unilateral response with positive gain, a contradiction.  This
proves (9.13).

The stated consequences are correct:

* with two free players, a simple cycle is the full square, so every induced
  Nash support meets it;
* with three free players, a Hamiltonian eight-cycle contains every cube
  vertex, so every nonempty product support meets it;
* a six-cycle omits exactly two vertices.  If neither omitted specialization
  is off minimum, every induced Nash support consists only of omitted
  vertices.  Two omitted vertices in a three-cube are adjacent or antipodal;
  a Cartesian product support contained in them has dimension at most one.
  The resulting actual product profile is a global minimum, all three free
  debts are zero, and in Fin4 the singleton host is therefore the sole
  debtor, with debt exactly \(D_*\).

None of these arguments serializes the horizontal cycle as play.

## Required statement-scope repairs

1. Proposition 9.4 says that the induced two-by-two game has no pure Nash
   equilibrium and therefore "its Nash equilibrium" is completely mixed.
   The conclusion needed is only that **every** Nash equilibrium is
   completely mixed (equivalently, select any Nash equilibrium).  In a
   strict best-response square this is true, but uniqueness of the mixed
   equilibrium is not needed and should not be suggested unless separately
   stated.

2. The reference after (9.14) to the owner-response handoff should explicitly
   note that the original Section 1 entrance assumes full debt, whereas the
   new product minimum has three zero free debts.  The cap formula and exact
   owner response use only the sure host, the host's positive debt, the
   singleton moat, and the product/Never realization, so the response proof
   does extend.  The statement should cite this weaker hypothesis list rather
   than invoking the full-debt entrance wholesale.

These are exposition/interface repairs, not mathematical blockers.

## Boundary

The reduction does not consume the six-cycle.  In its second arm the host's
exact response kills the only old debt, but a minimum-fibre target may create
the full amount \(D_*\) on the three free coordinates.  No old-zero
preservation, chronological Nash--Bellman edge, or decreasing renewable rank
follows.  The empty-base/complementary topology also remains outside the
common-tail screening argument.

## Novelty assessment

The general persistent-base induced-Nash compiler and its negative chamber
already existed.  The new useful delta is the support-local Jensen criterion
(9.13), especially its application eliminating the Hamiltonian singleton-host
eight-cycle and reducing the six-cycle to the one-debtor owner handoff.  This
is a genuine finite geometric contraction, but not a terminal Fin4 consumer.

## Stronger bypass found during review

There is a shorter route which appears to make the pure-cycle classification
unnecessary for the stated contraction.  It is written separately in
[`SOCIAL_WEIGHT_REVIEW__ANCHORED_ERASURE_OF_PURE_MINIMUM_TO_SINGLETON_OR_PAID_PORT.md`](../notes/SOCIAL_WEIGHT_REVIEW__ANCHORED_ERASURE_OF_PURE_MINIMUM_TO_SINGLETON_OR_PAID_PORT.md).

Starting from any pure finite-clock global minimum with earliest coalition
`S`, fix `b in S` and erase the other date-`t` quitters one at a time while
retaining `b`.  At every preceding minimum sibling, the singleton moat makes
the removed player's complete cap exactly the maximum of the two adjacent
terminal endpoint payoffs.  The first off-minimum sibling is therefore
attached to a minimum by an exactly oriented complete best-endpoint
comparison and carries its own `>D*/4` maximum-debt response.  If no sibling
leaves the minimum fibre, the last one is the singleton `{b}` and `b` is its
unique debtor of size `D*`.

If this strengthening passes independent review, Propositions 9.4--9.6 remain
valid finite geometry but are no longer needed to send the purified branch to
the off-minimum/reset-rigid waist.
