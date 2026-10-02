# Review of `CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE`

Reviewer: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Verdict: **PASS**, with one worthwhile strengthening and one trivial copy edit.

## Claim checked

The note claims that a coordinatewise limit of ordinary behavioral terminal
laws with zero Never mass and zero singleton mass is a one-root product law
with at least two sure quitters.  It further claims that, when the limiting
caps dominate the singleton rewards, one passive all-Continue row followed by
that product root and then Never realizes the limiting prescribed payoff,
unrestricted behavioral cap vector, and law.

I checked the first-efficient-root selection, the total-variation coupling,
the limiting argument, and the cap transport against arbitrary behavioral
replacements.  I found no mathematical gap.

## First-efficient-root selection

Let `sigma_n` and `zeta_n` be total singleton and Never mass and choose
`delta_n -> 0` with `sigma_n / delta_n -> 0`.  If there were no positive-
absorption root satisfying

\[
 b(q_{n,t})\leq\delta_n a(q_{n,t}),
\]

then every positive-absorption date would satisfy the reverse strict
inequality.  Summing with the live weights gives

\[
 1-\zeta_n=\sum_tL_{n,t}a(q_{n,t})
 \leq \sigma_n/\delta_n,
\]

contradicting `zeta_n -> 0`.  Before the first efficient date the identical
summation gives

\[
 E_n=1-L_{n,t_n}\leq\sigma_n/\delta_n\to0.
\]

Zero-absorption dates cause no problem.  The suggested convention when
`sigma_n = 0` is also harmless.

The local concentration lemma is correct.  The inequalities

\[
 a(q)-b(q)\leq\sum_{i<j}q_iq_j
 \leq {N\choose2}a(q)^2
\]

exclude `a(q^n) -> 0`; compactness and `b(q)=0<a(q)` then force at least two
coordinates of the limit root to equal one.

## Law coupling

The fact that the original profile reaches `t_n` with probability only
`1-E_n`, rather than one, does not invalidate the coupling.  Sample the
date-`t_n` product draw for the one-root profile in all cases.  On the event
that the original profile survives to `t_n`, use that same draw for its root.
Count every earlier absorption as disagreement.  If the original survives
and both selected pair members Quit, both terminal coalitions are the same,
independently of the later tail.  Therefore

\[
 d_{TV}(\mu_n,\nu_n)
 \leq E_n+1-q^n_iq^n_j\to0.
\]

This argument uses the ordinary behavioral semantics correctly: conditional
on the live history, the displayed root is the fresh product distribution.
It does not select a date after observing private actions.

Because the terminal outcome space is finite, coordinatewise convergence to
a law with zero Never and singleton coordinates indeed implies
`zeta_n -> 0` and `sigma_n -> 0`.  Polynomial continuity of the product law
then proves Theorem 5.1 exactly.  The Fin4 support-size conclusion
`1`, `2`, or `4` follows because the fractional set has cardinality at most
two after fixing a sure core of cardinality at least two.

## Full cap transport

The strengthened semantic theorem is also sound.

For a fixed player `i`, compare the original opponents with opponents who
Continue before `t_n`, play the selected root there, and Never thereafter.
Under one common arbitrary behavioral replacement of `i`, disagreement can
occur only if an original opponent stops before `t_n`, or all opponents
Continue at `t_n`.  The first event has probability at most
`1-H_{n,i} <= E_n`.  If `i` is itself one member of the almost-sure pair, the
other member remains among its opponents, so the second probability still
tends to zero.  This proves the uniform payoff bound

\[
 2R(1-H_{n,i}+h_{n,i})\to0
\]

over the complete behavioral replacement class, and taking suprema is valid.

A deviator who Quits in a pre-root padding row is not omitted: it receives
the singleton payoff `s_i`.  If `t_n>0`, this is exactly the extra option in
the padded cap.  If `t_n=0`, the source limit first identifies the unpadded
cap; the hypothesis `B_i >= s_i` shows that adding the padding option does not
raise it.  Thus the argument works even when the deviator is one of the two
sure quitters and covers Never, late stopping, calendar dependence, and
private randomization.

The prescribed payoff and law are unchanged by the passive padding row and
converge by the preceding law coupling.  Hence Theorem 6.1 really realizes
the full limiting semantic pair and law, not only a stationary cap.

## Strengthening boundary: long-calendar laws versus compressed caps

The same coupling gives more than cap convergence, but only before calendar
compression.  Let `P` be the stabilized almost-sure pair.  Keep the reference
root at the original selected date `t_n`.  For any fixed intervention set
`A` not containing all of `P`, install the same arbitrary behavioral
replacements for the players in `A` on the source and this **long-calendar**
reference.  If `k in P \ A`, the resulting terminal laws admit a coupling
with

\[
 d_{TV}\leq E_n+(1-q^n_k)\to0,
\]

uniformly over the replacements.  Replaced players who stop before the
selected date do so identically on both sides; an unchanged player stopping
early is covered by `E_n`; and at the selected root player `k` screens the
entire later tail with probability tending to one.

It would be false to assert the same pointwise law coupling after compressing
the `t_n` passive rows to one padding row.  A calendar-dependent replacement
can, for example, Quit exactly at `t_n`; using that literally unchanged
strategy against a root moved to date one can change the terminal coalition
with probability one.  Cap values survive because the replacement can be
rebased and only its supremal value is retained, not because every labeled
strategy has the same law after compression.

Player-deleted laws are a valid special strengthening: Never is invariant
under calendar rebasing, so every player-deleted terminal law converges to
that of the padded product profile.  More generally, one obtains uniform
counterfactual-law transport to the long-calendar reference, or a convergence
statement for the *sets* of laws after explicitly rebasing interventions—not
pointwise transport of the same labeled strategies.  This is useful
provenance, but it still does not make the attained minimum root Nash or turn
a static endpoint change into a chronology.

## Novelty and boundary

The exact behavioral nonrealizability statement in the social-dual export
only forces a common pair in each realized zero-singleton law.  The present
argument additionally proves closure, one-root product form, literal finite
semantic realization, and uniform order-one counterfactual transport.  I did
not find an existing declaration or conference theorem with this complete
combination.

The note is appropriately cautious about consumption.  A persistent-base
product minimum can still have profitable member-leaving endpoints, and the
argument supplies no source-preserving return, support descent, or UE by
itself.

## Addendum: renewable sure-core softening split

I checked the revised Section 10 strengthening.  The continuous softening
argument is correct and repairs the nonrenewability of pure deletion.

If `K={i:q_i=1}` has cardinality at least two, every player has a sure
quitter among its opponents.  Hence opponent-all-Continue mass is zero and

\[
 U_i=q_iQ_i+(1-q_i)C_i.
\]

At a positive minimum, `B_i-s_i >= D_* > 0`, so the padding singleton option
is strictly nonbinding and `B_i=max(Q_i,C_i)`.  Under full positive debt, a
sure quitter `p in K` has `U_p=Q_p<B_p`, whence

\[
 B_p=C_p,\qquad C_p-Q_p=d_p>0.
\]

For `0<theta<1`, replace `q_p=1` by `q_p=1-theta`.  The exact gain is
`theta*d_p`, the unrestricted `p`-cap is unchanged, and

\[
 d_p(\theta)=(1-\theta)d_p(0)>0.
\]

All other debts are continuous, so a sufficiently small positive `theta`
keeps every coordinate debt positive.  Along this one-coordinate segment,
each prescribed payoff and each root endpoint is affine in `theta`; each cap
is the maximum of two affine endpoints and the constant singleton option.
Thus total debt `D(theta)` is convex.  Global minimality gives
`D(theta)>=D(0)` throughout, and a convex function with its minimum at the
left endpoint is nondecreasing.

If one small selected `theta` has strict inequality, monotonicity gives
`D(1)>D_*`, so the pure deletion endpoint is genuinely off minimum and carries
the full paid gain.  If equality holds, the selected child is an attained
**full-debt** minimum, while its maximal sure core is exactly `K\{p}`.  The
same construction therefore iterates while that core has cardinality at
least two.

At core cardinality two, softening `p` gives the other sure quitter `k`
singleton mass

\[
 \theta\prod_{j\notin K}(1-q_j)>0.
\]

The strict/equality split consequently yields either an off-minimum pure paid
endpoint or, after at most three minimum-child steps in Fin4, an attained
positive-singleton minimum.  No source is reselected along the equality
lane.

My earlier pure-deletion regression does not refute this repair.  In fact it
illustrates why softening is the right operation: for the table where the
pure triple has debt `(1/4,1/4,1/4,1/4)` and its pure-deletion target has debt
`(0,0,0,1)`, the softened segment has constant total debt one and all four
debts remain positive for every `theta<1`.  It therefore follows the claimed
full-debt core descent before reaching the problematic endpoint.

This is a genuine finite-rank transition for the zero-Never/zero-singleton
full-debt product arm.  It still ends in the independently open off-minimum
paid-port or positive-singleton consumers, so it does not alone prove UE.

## Minor edit

Section 5 currently contains the duplicated fragment `Put Choose ... Put`.
This is purely typographical and does not affect the proof.

## Delta addendum: padding is unnecessary once two quitters are sure

The strengthened no-padding statement is correct.

Let the product root `q` have a sure-quitter core `K` of cardinality at
least two.  Compare either the profile that plays `q` once and then Never,
or the stationary repetition of `q`.  For any deviator `i`, choose
`k in K` with `k != i`.  Player `k` Quits at the first row with probability
one even after replacing all of `i`'s behavior.  Thus absorption occurs at
that first row under every unilateral behavioral replacement.  The
deviator's later behavior, including Never and arbitrary calendar-dependent
actions, is never reached.  Its unrestricted cap in both profiles is
therefore exactly

\[
 \max\{Q_i(q_{-i}),C_i(q_{-i})\}.
\]

The prescribed payoff and terminal law in both profiles are also the
one-root product payoff and law.  Hence root-then-Never and stationary
repetition realize the same complete semantic pair and time-forgetting law,
with no all-Continue padding row.  This argument remains valid when the
deviator itself belongs to `K`, because the other sure quitter screens it.

The strict minimum singleton margin is not needed for this screening
identity itself.  It is useful only for identifying the same cap formula in
nearby roots after the sure-core hypothesis is weakened, or for other
minimum-fibre conclusions.  This delta is a genuine simplification of the
realization, not a new consumer of the off-minimum toll branch.
