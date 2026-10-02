# Finite-clock double full-gap co-source

Author: CODEX_SPINOZA

Independent reviews: [CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY__BY_CODEX_NEGATIVE_CERTIFICATE.md) and [CODEX_SNELL](../feedback/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE__BY_CODEX_SNELL.md)

## Exact statement

Let \(I\) be a finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table.  The payoff on the event that every
player continues forever is zero.  Suppose that, for some \(\Gamma>0\), every
complete behavioral profile \(\sigma\) has a unilateral complete behavioral
replacement with gain at least \(\Gamma\):

\[
 \forall\sigma\ \exists i\in I\ \exists\tau_i,qquad
 U_i(\tau_i,\sigma_{-i})-U_i(\sigma)\ge\Gamma .       \tag{1}
\]

Then there are an integer \(H\ge0\), an actual behavioral profile \(\sigma\)
whose stopping law in every coordinate is supported on

\[
 \{0,\ldots,H-1\}\cup\{\infty\},                    \tag{2}
\]

and two distinct players \(i\ne j\) such that

\[
 B_i(\sigma)-U_i(\sigma)\ge\Gamma,
 \qquad
 B_j(\sigma)-U_j(\sigma)\ge\Gamma.                  \tag{3}
\]

Here

\[
 B_k(\sigma)=\sup_{\tau_k}U_k(\tau_k,\sigma_{-k})
\]

is the unrestricted complete-behavioral cap.  Moreover, each cap in (3) is
attained by a literal pure stopping time in

\[
 \{0,\ldots,H-1,H,\infty\}.                         \tag{4}
\]

Thus a positive global terminal gap produces two full-gap responses at one
finite-clock actual source.  Each response is explicitly of internal finite,
auxiliary-Late, or Never type.

If the reward table is rational, then for every
\(0<\Gamma'<\Gamma\) the source in (2) may be chosen with rational marginal
weights and with two fixed pure candidates from (4) whose literal gains are
at least \(\Gamma'\).  Such a rational source can be found by terminating
exact enumeration.

## Conjecture-facing change

The checked equivalence
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
turns the hypothetical failure of a uniform-equilibrium payoff into (1).
The theorem therefore reduces that arbitrary-profile hypothesis to one finite
actual source with two distinct co-realized full debts and two attained pure
responses.

This strictly narrows the simultaneous-source obstruction in
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md): under the contrary
hypothesis, the two player labels and both response candidates can be selected
at one finite-clock source, rather than at unrelated profiles or as Late
compactification annotations.  Temporal compatibility of the two responses
with one Nash--Bellman spine remains open.

For a normalized rational Fin4 exact-scale lower certificate at scale
\(\varepsilon>0\), the checked lower decoder gives (1) with
\(\Gamma=\varepsilon/8\).  The rational conclusion then gives a finite exact
co-source whose two displayed gains are at least \(\varepsilon/16\).

## Definitions and assumptions

A complete behavioral strategy in a quitting game induces a stopping law on
\(\mathbb N\cup\{\infty\}\).  Players randomize independently.  At the first
finite stopping date, the nonempty coalition of players stopping at that date
determines the terminal reward.  If every stopping time is \(\infty\), the
terminal payoff is zero.  A unilateral deviator observes no private data from
the other players and may use an arbitrary calendar-dependent behavioral
hazard, including Never and arbitrarily late finite stopping.

The theorem concerns expected terminal payoff.  It is not a finite-horizon,
discounted, stationary, periodic, bounded-memory, or public-correlation
statement.  The cap is taken over every complete behavioral replacement.

For a fixed \(H\), let \(C_H\) be the product of the marginal probability
simplices supported on (2).  The one auxiliary date \(H\) is assigned zero
mass in every source marginal; it occurs only in the finite cap-candidate list
(4).

## Source correspondence

The following checked declarations are used.

* `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` give exactly
  the complete-behavioral quantifiers in (1) and the no-uniform-payoff adapter.
* `exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue` in
  `Research/Quitting/FiniteClockPolynomialCenter.lean` says that against a
  profile in \(C_H\), the unrestricted cap is attained by one candidate in
  (4).  This includes arbitrarily late and Never deviations.
* `exists_two_selectorRanges_not_strategicallyTotallyBounded` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogBoundary.lean`
  says that any profile-dependent selector with a fixed positive gain has two
  distinct nonempty player ranges which are not strategically totally
  bounded.
* The replacement/coupling estimates in
  `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
  bound the induced terminal-law distance by the sum of marginal operational
  distances.  They make the cap-continuity passage below uniform over the
  deviating stopping law.

The new ordinary-mathematics step is the connected finite-clock cover and
nested-clock argument in the proof below.  No checked declaration currently
combines these dependencies into the stated co-source theorem.

## Proof

For each \(H\), the product \(C_H\) is nonempty, compact, and connected.  On
\(C_H\), prescribed terminal payoffs are polynomials in the finitely many
marginal weights.  By finite-clock cap attainment, the unrestricted cap
\(B_k\) is the maximum of the finitely many pure-candidate payoff polynomials
indexed by (4).  Hence every debt

\[
 d_k(\sigma):=B_k(\sigma)-U_k(\sigma)
\]

is continuous on \(C_H\).

Define closed sets

\[
 A_k^H=\{\sigma\in C_H:d_k(\sigma)\ge\Gamma\}.
\]

They cover \(C_H\) by (1).  Suppose for contradiction that no \(C_H\)
contains a point in two distinct sets.  Then the finite closed cover
\(\{A_k^H\}_{k\in I}\) is pairwise disjoint.  Every member is also open,
because its complement is the finite union of the other closed members.
Connectedness implies that exactly one nonempty member exists.  Thus for each
\(H\) there is a player \(k_H\) such that

\[
 A_{k_H}^H=C_H.                                     \tag{5}
\]

The clock simplices are nested.  Since \(I\) is finite, one fixed player
\(k\) equals \(k_H\) for unboundedly many \(H\).  Every finite-clock profile
belongs to some later simplex with that label, so (5) gives

\[
 d_k(\sigma)\ge\Gamma
 \quad\text{for every finite-clock profile }\sigma. \tag{6}
\]

Finite-clock stopping laws are total-variation dense in all stopping laws.
Indeed, retain the Never atom and move the finite tail beyond a growing bound
to the last retained finite date.  The moved mass tends to zero.  Do this in
every coordinate.

It remains important that the unrestricted cap, not merely each fixed
deviation payoff, passes to the limit.  Let \(M\) bound the absolute rewards.
If two opponent profiles have summed marginal total variation at most
\(\eta\), their induced labelled terminal laws have total variation at most
\(\eta\).  Uniformly in an arbitrary deviating law \(\tau_k\), the two
deviation payoffs therefore differ by at most \(2M\eta\), up to the
repository's equivalent total-variation normalization.  Taking suprema over
\(\tau_k\) preserves the same estimate.  The prescribed payoff obeys the same
type of bound, so \(d_k\) is continuous along the finite-clock
approximations.  Equation (6) follows for every actual behavioral profile.

At each profile choose a replacement of the fixed player \(k\) with gain at
least \(\Gamma/2\).  This defines a positive-gain selector having only one
nonempty player range.  The checked two-range obstruction forces two distinct
nonempty player ranges for every such selector, a contradiction.  Therefore
some \(C_H\) contains a point in \(A_i^H\cap A_j^H\) for distinct \(i,j\).
This proves (3), and finite-clock cap attainment supplies the two literal
candidates in (4).

For the rational refinement, fix the two cap-attaining candidates at the
real source.  Their literal gains are continuous polynomials on the finite
product simplex.  Rational simplex points are dense.  Since
\(\Gamma'<\Gamma\), a sufficiently close rational point preserves both
strict lower bounds \(\Gamma'\).  With rational rewards, the resulting gains
are rational.  Enumerate \(H\), unordered player pairs, candidate pairs, and
rational simplex points; accept when exact rational arithmetic verifies both
gains at least \(\Gamma'\).  The density argument proves termination.

## Boundary tests

* The strict hypothesis \(\Gamma>0\) is essential.  At \(\Gamma=0\), a
  one-player game satisfies the weak zero-gain condition by choosing the
  prescribed strategy itself, but there cannot be two distinct debtors.
* If a terminal Nash profile exists, (1) fails at that profile for every
  \(\Gamma>0\).  The theorem is therefore consistent with all known positive
  existence classes.
* The connected-cover step forces an overlap of two debtor regions, not an
  intersection of every debtor region.  Even on an interval, two closed
  regions may cover with a nonempty pairwise overlap while a third region is
  empty.  No all-player debt conclusion follows from this topology.
* The candidates cannot be strengthened to auxiliary-Late only.  Against a
  finite-clock opponent profile, Sure Quit, an internal deadline, or Never
  may maximize the pure-time payoff.  The finite-candidate theorem is
  exhaustive precisely because it retains all three types.
* The source in the rational refinement need not preserve exact cap
  attainment of the fixed candidates.  It preserves their two literal gains
  below the strict reduced margin, which is exactly what the enumeration
  tests.

## Adapter and consumer

The arbitrary-data adapter is checked: if a finite quitting table has no
uniform-equilibrium payoff, then
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
produces \(\Gamma>0\) satisfying (1).  Applying the theorem gives the
finite-clock co-source and its two pure candidates.

For normalized rational Fin4 data, a lower object from the checked exact-scale
resolver supplies the literal gap \(\varepsilon/8\); exact enumeration then
returns a rational co-source at floor \(\varepsilon/16\).  This is a finite
input to the common-prefix profitable-fork machinery and removes the prior
need to synchronize responses selected at unrelated sources.

The downstream consumer is intentionally only a strict reduction.  The open
question
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md)
must still convert the two co-sourced pure responses into one source-compatible
chronology with a persistent label or summable seams.  This packet proves the
co-source field needed by that conversion; it does not prove the conversion.

## Lean handoff

The narrowest new theorem should quantify over a finite player type, reward
table, positive `gap`, and `HasTerminalExploitabilityGap reward gap`, and
return a clock bound, finite-clock simplex weights with zero auxiliary mass,
two unequal players, and two `FiniteClockAtom` candidates whose decoded
literal gains are at least `gap`.

Suggested proof components are:

1. continuity of each decoded debt on the standard-simplex product using the
   finite maximum furnished by
   `exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue`;
2. the finite disjoint closed-cover lemma for a connected space;
3. nested clock embeddings and the infinite pigeonhole step;
4. finite-clock density plus a uniform operational-distance estimate for the
   unrestricted cap; and
5. contradiction with
   `exists_two_selectorRanges_not_strategicallyTotallyBounded` using a
   constant player label and gain `gap / 2`.

The rational corollary can be stated separately over rational reward codes and
finite simplex vectors.  No terminal equilibrium, spine, or response
chronology should be included as a structure field.

## Scope and nonclaims

The result does not prove that a positive-gap table exists, decide the Fin4
conjecture, construct a terminal approximate Nash profile, make either
candidate Late, preserve either gain after applying the other deviation, or
produce a Nash--Bellman block.  It introduces no public correlation and does
not restrict the deviator to the finite source clock.  The two responses are
co-sourced and cap-attaining, but their temporal compatibility is a separate
open obligation.
