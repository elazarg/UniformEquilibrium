# Second review of the escape-aware quantile-clock hierarchy

Reviewer: `CODEX_RAMSEY`

Material reviewed:

- [`CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../notes/CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md);
- the broadened finite-player packet
  [`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__EXPORT_DRAFT.md`](../notes/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__EXPORT_DRAFT.md).

Verdict: **REVISE -> PASS.**  The unrestricted-strategy mathematics passes
my independent falsification attempt, including the broadened nonempty finite
player statement.  The packet needs one bounded definition repair and three
ministerial repairs listed in Section 8.  No mathematical re-review is needed
after those edits.

## 1. Quantile endpoints and cell count

Let `C_i(t)` be finite cumulative mass through date `t`.  If a gap between
marked dates had mass greater than `1/m`, one of the grid levels `j/m` would
have its first crossing inside that gap.  The two endpoint cases are also
valid:

- if no first crossing occurs, total finite mass is at most `1/m`;
- after the last distinct marked date, if that date crosses levels through
  `j/m`, failure to cross `(j+1)/m` leaves at most `1/m` mass in the terminal
  finite gap.  This includes a proper law whose cumulative mass approaches
  the next grid level without attaining it.

A single large atom may cross many levels, but all those levels select the
same singleton date.  Thus there are at most `nm` distinct marked dates, at
most `nm+1` nonempty complementary intervals, and hence at most

\[
  2nm+1
\]

finite cells.  `Never` is not part of the finite cumulative function and is
not merged with the terminal finite gap.  The Fin4 specialization is
`K_m=8m+1`.

## 2. Product law, ties, and prescribed payoff

The construction pushes each marginal law through the same ordered cell map;
it does not push an arbitrary joint coalition law.  Independence is therefore
preserved.  Off the event that a player pair lands in the same unmarked gap,
the strict order and equality pattern of all finite clocks is preserved.
Ties at marked singleton dates are preserved literally, and all-`Never`
remains all-`Never`.

For a fixed pair, independence and the gap bound give

\[
  \sum_G \mu_i(G)\mu_j(G)\le {1\over m}.
\]

There are `n(n-1)/2` pairs.  Multiplication by the normalized reward diameter
two gives

\[
  \lVert U(\mu)-U(\mu^{(m)})\rVert_\infty
     \le {n(n-1)\over m}.
\]

This includes atoms exactly at a quantile crossing: the atom is a marked
singleton and is not charged as a gap collision.

## 3. Both unrestricted-cap directions

Fix deviator `i`.  Map an original deterministic date to its compressed cell.
A mismatch requires either two of the `n-1` opponent clocks in one unmarked
gap, or an opponent clock in the deviator's gap.  The respective union bounds
are

\[
 {\binom{n-1}{2}\over m}
 \quad\hbox{and}\quad
 {n-1\over m}.
\]

Their sum is `n(n-1)/(2m)`; reward diameter two gives
`n(n-1)/m`.

The reverse direction also passes.  A genuine compressed cell has an original
integer representative.  For a padded compressed date after all genuine
cells, choose an original date after the last marked singleton, not a
nonexistent date after all original support.  Put every opponent clock in the
entire unbounded terminal gap into the second bad event.  Its probability is
at most `(n-1)/m`.  Off this event, all finite opponent clocks precede both
deviations, while all opponent-`Never` gives the same deviator singleton in
both profiles.  Opponent-pair gap collisions cost the first term above.

Compare `Never` to `Never`; then only opponent-pair gap collisions remain.
Thus both pointwise comparisons have the stated error, and taking suprema is
legitimate even when the original supremum is not attained.  The checked
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` upgrades this to every
unilateral behavioral deviation.

For `n=1` both collision counts vanish.  Compression preserves finite versus
`Never` mass, which determines prescribed payoff, and there are no opponent
clocks in the cap.  Hence the advertised zero error is exact.

## 4. Finite semialgebraic center

For product marginals supported below `K`, the displayed first-coalition
formula is correct: `x_(i,t)` is unconditional mass at `t`, and
`s_(j,t+1)` is the probability that outsider `j` stops strictly after `t` or
never.  The all-Continue mass is the product of the `Never` coordinates.

The payoff-distinct pure deviations are dates `0,...,K-1`, one date `K`
strictly after finite opponent support, and `Never`.  Once their polynomial
values are defined, the finite maximum graph

\[
 B_i\ge V_{i,\tau}\quad(\forall\tau),\qquad
 \prod_\tau(B_i-V_{i,\tau})=0
\]

is exact on zero-probability faces and at ties: the inequalities give an upper
bound and the product forces one tight candidate.  The marginal simplex is
compact, and the stopping-law reconstruction theorem makes every feasible
marginal tuple behaviorally executable.  Thus `A_K` is compact rational
semialgebraic.  Adding a zero-mass date preserves the old after-support value,
so `A_K` embeds in `A_(K+1)`.

There is one literal definition gap in the draft: equation (21) sums only
through `K-1`, so the value for the auxiliary deviation `tau=K` is not
literally obtained by replacing the deviator's marginal in that displayed
formula.  The repair is routine but mandatory: define `V_(i,K)` by adjoining
the auxiliary date `K` for the deviator (with opponents still supported below
`K`), or display its equivalent explicit polynomial.  This does not affect
the proof or constants.

## 5. Carrier intersection and bracket directions

Every actual pair lies in every closed neighborhood `N_m`; hence its closure,
the terminal semantic carrier, lies in every `R_M`.  Conversely, membership
in every `R_M` supplies actual centers `a_m in A_(K_m)` with distance at most
`n(n-1)/m`, so `a_m` converges to the candidate and proves carrier membership.
No realization of the limiting carrier point is inferred.

The direction of the objective bracket is correct:

- minimizing over the outer set gives `L_M <= eta`;
- minimizing over actual finite-clock centers gives `eta <= U_M`;
- every actual point of `A_(K_M)` lies in all earlier neighborhoods and hence
  in `R_M`, so `L_M <= U_M`.

The exploitability function is `2`-Lipschitz in semantic sup norm.  Since
`R_M` is contained in `N_M`, a minimizer of `F` on `R_M` has an `A_(K_M)`
center within `n(n-1)/M`, giving

\[
  0\le U_M-L_M\le {2n(n-1)\over M}.
\]

For Fin4 this is exactly `24/M`.  Nestedness of `R_M`, exact carrier
intersection, and continuity give `sup_M L_M=eta`; the same bracket gives the
upper error bound.  If `eta=0`, the finite centers give terminal approximate
Nash profiles at all errors, which are valid input to
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.
This is correctly stated as conditional on the zero-gap branch.

## 6. Exact verification and source audit

At fixed `M`, all marginal, payoff, cap, neighborhood, and max constraints are
finite rational real-algebraic constraints.  Compactness makes

\[
  \gamma\le L_M
  \quad\Longleftrightarrow\quad
  \{z\in R_M:F(z)<\gamma\}=\varnothing.
\]

Real quantifier elimination/CAD therefore decides the finite assertion
exactly.  The packet correctly requires an exact algebraic trace or another
independently checkable real-algebraic certificate, not floating-point solver
output.  This semidecides `eta>0`; it does not decide equality to zero.

I checked the named source chain:

- unrestricted pure-time extremality in
  `BehaviorPureTimeExtremality.lean`;
- complete stopping-law realization in
  `StrategicallyPrecompactWatchdogProperBoundary.lean`;
- carrier closure, compactness, and sequential approximation in
  `TerminalSemanticPair.lean`;
- semantic exploitability and the carrier lower-bound relation in
  `TerminalSemanticEqualityStratum.lean`;
- the closest elementary-tail approximation in
  `ElementaryTailSemanticReduction.lean` and its finite-word carrier use in
  `TerminalSemanticGlobalDebtBarrierCertificate.lean`.

The elementary-tail theorem allows an accuracy-dependent cutoff and does not
supply the profile-independent `O(nm)` clock support, simultaneous explicit
`O(1/m)` semantic modulus, or the nested finite semialgebraic bracket.  A
narrow symbol and phrase search found no checked common-quantile construction
or `2n(n-1)/M` bracket.  The novelty claim is therefore appropriately narrow.

## 7. Export significance

The result is export-worthy as an exact reduction which strictly narrows the
escape-aware certificate-search obligation: it replaces the unrestricted
infinite-clock inner optimization by a convergent sequence of finite rational
semialgebraic outer problems, with an actual-profile map, exact unrestricted
objective, exact product/`Never` provenance, and a uniform computable error
modulus.  It also supplies the conditional zero-gap terminal-approximation
consumer.

It is not Output 1 or 2 of the maintained question, does not eliminate the
Fin4 hard residual, and must not be advertised as a terminating zero test or
as realizing carrier points.  The packet states these nonclaims accurately.

## 8. Required packet edits

Before movement to `exports/`:

1. define the auxiliary after-support polynomial `V_(i,K)` as explained in
   Section 4;
2. repair the malformed `|...|le` relations in Lemmas C and D to `\le`;
3. replace the header's single-review/pending-review text by plural review
   metadata linking both independent reviews, including this one; and
4. render Theorem A's `R_(M+1) subset R_M` as the unambiguous mathematical
   relation `R_{M+1}\subseteq R_M`.

After these bounded edits, my final mathematical and whole-packet verdict is
**PASS**, with no further falsification objection.
