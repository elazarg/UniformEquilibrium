# Review of the finite-clock double full-gap source

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed object:
`notes/CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`,
Section 6.

## Verdict

**PASS.**  Theorem 6.1, its rational approximation, and the effective
enumeration corollary are mathematically sound.  I found no counterexample in
the closed-cover, nesting, density, cap-attainment, or two-range steps.

One proof clarification should be retained in any export packet: continuity
of the unrestricted cap is not obtained from the false general claim that an
arbitrary supremum of continuous functions is continuous.  It holds here
because bounded quitting payoffs give a total-variation estimate uniform over
the deviating stopping law.  The exact expansion is recorded below.  This is
a clarification of a valid step, not a change in the theorem.

## Claim checked

Assume a finite zero-Never quitting game has a literal global gap
`Gamma>0`: at every actual behavioral profile some player has some complete
behavioral replacement with gain at least `Gamma`.  Theorem 6.1 claims that
one finite-clock actual profile has two distinct player debts at least
`Gamma`, and that each unrestricted cap is attained by a pure response from
the finite list of internal dates, the one auxiliary date, and Never.

## Closed cover and connectedness

For a fixed clock bound `H`, the product `C_H` of marginal simplices supported
on `{0,...,H-1} union {Never}` is nonempty, compact, and connected.  The
checked theorem
`exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue` in
`Research/Quitting/FiniteClockPolynomialCenter.lean` applies because the
auxiliary atom at date `H` has prescribed mass zero.  It identifies each
unrestricted cap with the maximum of the pure candidates
`{0,...,H-1,H,Never}`.  Thus every debt coordinate is continuous on `C_H`.

The sets

```text
A_i^H={sigma in C_H : d_i(sigma)>=Gamma}
```

are closed and cover `C_H`.  If no point has two distinct full debts, these
sets are pairwise disjoint.  A finite pairwise-disjoint closed cover of a
connected space has only one nonempty member: each member is also open
because its complement is the finite union of the other closed members.
Hence some `A_(i_H)^H` equals all of `C_H`.  Empty debt regions cause no
problem.

## Nested clocks and the repeated label

The simplices are nested under the literal support convention: a law
supported on `{0,...,K-1,Never}` belongs to every `C_H` with `H>=K` by adding
zero masses.  Since the player set is finite, one identity `i` occurs as
`i_H` for unboundedly many clock bounds.  Given any finite-clock profile,
choose one later bound carrying this repeated identity.  The equality
`A_i^H=C_H` then gives `d_i>=Gamma` at that profile.  This passage does not
require a consecutive subsequence of bounds or a limit of the profiles.

## Density and the unrestricted cap

For any stopping law on `Option Nat`, retain its Never atom and move all
finite mass after `H-1` to date `H`.  The general total variation from the
original law is the moved finite-tail mass, which tends to zero.  Applying
this coordinatewise gives finite-clock profiles converging in product total
variation to every actual profile.

Here is the needed uniform cap estimate.  Let `M` bound the absolute terminal
rewards.  If two opponent profiles have summed marginal total variation at
most `eta`, their induced labelled terminal laws have total variation at most
`eta` by the replacement/coupling estimate in
`StoppingLawOperationalDistance.lean`.  Therefore, for every fixed
deviating stopping law `tau_i`, the two deviation payoffs differ by at most
`2*M*eta` (up to the repository's equivalent TV normalization).  The bound
does not depend on `tau_i`.  Taking suprema preserves it:

```text
|B_i(sigma)-B_i(rho)| <= 2*M*eta.
```

The prescribed payoff has the same type of bound.  Consequently the debt is
continuous along the finite-clock approximants, and the full inequality
`d_i>=Gamma` passes to every actual profile.  There is no nonattainment or
lower-semicontinuity gap.

## Two-range contradiction

If one fixed identity `i` has debt at least `Gamma` at every profile, the
definition of supremum lets one choose at each profile a literal complete
replacement with gain strictly greater than `Gamma/2`.  Classical choice
therefore yields a selector with constant player label `i` and uniform
positive gain `Gamma/2`.

The checked theorem
`exists_two_selectorRanges_not_strategicallyTotallyBounded` (equivalently the
late-mass strengthening
`exists_two_player_selectorRanges_lateFiniteMass_escape`) in
`StrategicallyPrecompactWatchdogBoundary.lean` forces two distinct nonempty
player ranges for every such selector.  A constant-label selector has only
one nonempty range, contradiction.  This use has the correct sign and needs
neither measurability nor attainment of the arbitrary-profile cap.

Thus some `C_H` contains a point in `A_i^H intersect A_j^H` for distinct
players.  The finite-clock candidate theorem then attains both caps in the
claimed finite list.  The two candidates may be internal, auxiliary-Late, or
Never; the proof correctly makes no Late-only conclusion.

## Rational and effective corollaries

At the real double-debt source, fix the two cap-attaining candidates.  Their
literal gain functions are polynomials in the finite marginal weights.
Rational points are dense in the relative simplex face where the auxiliary
profile mass is zero.  Any strict lower target `Gamma'<Gamma` is therefore
preserved by a sufficiently close rational point.  For a rational reward
table, the resulting gains are rational and exactly decidable.

Enumeration over clock bounds, player pairs, candidate pairs, and rational
simplex points is countable and effective.  The density result guarantees
eventual acceptance at the reduced margin.  For a Fin4 lower tree with gap
`epsilon/8`, the note's rational floor `epsilon/16` is valid.

## Scope checks

- The theorem needs no positive-gap witness selector as input; it constructs
  the contradiction selector only after the repeated-label argument.
- “Finite player set” may be written “finite nonempty player set” in a formal
  statement.  The global-gap hypothesis already implies nonemptiness.
- The source profile is actual and finite-clock; no public correlation or
  compactified Late atom is introduced.
- The two debts coexist at one profile, but the theorem does not make either
  cap-attaining response be the auxiliary Late deadline.
- The theorem is a consequence of a global gap, not evidence that any
  concrete Fin4 table has such a gap.

No mathematical revision is required.

## Export-candidate freeze delta

**PASS** for `/tmp/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md` at exact
SHA-256
`1e47d5615dd3ae1a29d2ab4aca8f8eb353c10a9570e4bf8c79d73b883269a539`.
The candidate's proof is the reviewed connected-cover/nested-clock argument,
including the requested deviation-uniform total-variation justification for
cap continuity.  The final metadata names and links both completed reviews.
Both links resolve from the future `exports/` location, all mandatory packet
headings are present, and the control-byte scan is clean.  I found no proof,
scope, source, or formatting change requiring a revised verdict.
