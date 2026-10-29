# Independent review of exact continuation fibres

Reviewer: FIBER_REVIEW. Ordinary mathematics; no Lean build was run.

Reviewed canonical artifact:
`math/notes/CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md`.
SHA256: `b8a4301204706ffa6c3277eb79e32630b78e21ab02bca83e1708b9623aa0d128`.
Scope: all of Section10, plus its statements in the introduction and final
source/remaining-target discussion. The independent finite-calendar
classification in Section8 is outside this review's approval scope.

Verdict: PASS for the full statement and its marked-source application.
No unresolved mathematical objection. This is an exact-fibre approximation
theorem and a necessary-source hierarchy, not a new raw reward-class UE
theorem or an assertion that every compact semantic point is attained.

## Claim checked

For n>=2, absolute reward bound M, and any annotation (u,b,e,N) in the
closure of actual independent quitting profiles, each k>=1 admits one actual
profile on at most 2n(n+1)k+4n^2 consecutive available dates with

    U=u, e_prescribed=e, N_prescribed=N,
    ||B-b||_infinity <= n(n-1)M/k.

The cap is the supremum over every unilateral behavioral replacement,
equivalently every deterministic finite deadline and literal Never. In Fin4
this gives 40k+64 dates and 12M/k cap error. For zero-debt diagonal sources,
all prescribed and Never-response payoffs and all marginal Never masses are exact;
the actual total debt is at most48M/k.

## Independent proof audit

1. Quantile marks. The union has at most nk dates. A gap carrying more
   than1/k for one law contains the first crossing of a grid level, a
   contradiction. This includes the infinite final finite-time gap. If a
   grid level is approached but never attained, the weak mass bound remains
   valid. Never must remain a separate cell, as it does in the proof.

2. Moment dimension. Varying only player i makes all n prescribed payoffs
   and n-1 other Never-response payoffs affine; e_i is constant. Adjoining
   the indicators of K_i positive cells gives affine dimension at most
   K_i+2n-2. The bounded countable barycentre lies in the ordinary convex
   hull: a proper supporting face containing the mean contains every
   positive-mass vector, allowing finite dimension descent. Caratheodory
   therefore gives at most K_i+2n-1 old support actions, with all moments
   and cell masses exact. Later owner replacements preserve the same full
   moment vector. There is one product law throughout, no mixture of
   product laws or shared randomization.

3. Support count. Every positive cell requires a support action. Hence
   each player has at most2n-1 excess actions beyond one per positive
   cell. Marked cells and Never are singletons. Finite gap support is at
   most g_i+2n-1. Counting each shared marked date once gives

       d <= m + sum_i(g_i+2n-1)
         <= (n+1)m+2n^2 <= n(n+1)k+2n^2.

   The fact that some owners have zero mass in a cell only improves this
   estimate. There is no illicit multiplication of all marked dates by n.

4. Complete response control. Couple each old and new marginal in the
   same cell, independently between players. At one fixed deadline t,
   disagreement of terminal coalitions requires either an opponent pair
   sharing a finite gap or an opponent in the gap containing t. Pair
   probabilities are at most1/k. The union bound is

       [choose(n-1,2)+(n-1)]/k = n(n-1)/(2k).

   Multiplication by2M gives the claimed cap radius. If t is marked or
   Never, the second event is absent. No restriction to supported own
   deadlines is made. Uniform pointwise response comparison permits taking
   both suprema, even when neither cap has an attaining deadline.

5. Retiming. The initial gap is retained exactly when the first occupied
   date is positive; an internal gap is retained exactly when consecutive
   occupied dates differ by more than one. Thus every atom/gap/after-last/
   Never response class exists on both calendars. For every player the
   weak-order comparisons against all occupied opponent dates agree.
   Extra points occupied only by that player subdivide identical response
   classes and cause no problem. This proves exact preservation of all
   caps, U, e, and N during retiming. The largest new occupied date is at
   most2d-1, proving the stated literal calendar bound.

6. Closure. Fix k BEFORE taking limits. The compressed laws all lie in
   one finite product of probability simplexes. U,e,N are polynomial there;
   B is a finite maximum of polynomial replies at every available date,
   plus the first date after the prescribed calendar and Never. In
   particular, disappearing atoms do not destroy continuity. Subsequence
   extraction proves the exact moment equalities at every compact source,
   with the same uniform cap bound. Letting k vary does not assert one
   finite profile with exact caps.

7. Native marked source. Section10's marked-source application specializes to Fin4
   before using the coefficient14 and exponent1/4 in the existing repair
   bound. Positive least-Never mass implies every N_i>0. The preserved
   inequality d_i>=N_i(B_i-e_i), together with zero debt, gives U=B=e.
   The theorem therefore approximates the SAME selected source while
   keeping its marked payoff and original Never product exactly fixed.
   Neither exact Nash of the approximants nor finite-calendar minimality
   is inferred.

8. Hierarchy. At each k, the simplex/moment/reply requirements are finite
   polynomial conditions of degree at most n. The all-k conditions are
   equivalent to (v,v,v,N) lying in the annotation closure: the forward
   implication is the theorem, and the reverse implication takes the
   actual annotations with caps in[v,v+n(n-1)M/k] to their limit. This is
   a countable equivalence, not finite termination or UE decidability.

## Falsification attempts and exact checks

- Dense ranking without gap retention is false. If an opponent quits at
  date1, an owner with solo reward1 and joining reward0 can preempt at0.
  Moving the opponent to0 deletes that option and changes the cap. The
  reviewed retiming rule preserves the initial gap and avoids this error.
- Exhaustively checked294 calendar shapes: n=2,3,4; every1-to4-element
  subset of dates0,...,6. For each shape, enumerated every opponent tuple
  over its finite dates plus Never and compared the SETS of full terminal
  coalition signature vectors over all pure response dates. Original and
  gap-preserving calendars agree exactly. These are finite verification
  controls; the all-calendar proof is item5 above.
- A big atom does not invalidate the coupling: every unmarked gap has
  total mass at most1/k, so a larger atom must be a common marked singleton
  and is retained literally by cell-mass matching.
- The sharp infinite-support cap obstruction in the canonical geometry
  note is consistent: finite exact U,e,N preservation can require a
  positive cap error. No zero-error finite realization is claimed here.

## Source and scope audit

Read the exact statements of
`hasEscapeAwareQuantileClockCompressionAtBound` and
`HasEscapeAwareQuantileClockPayoffTransportAtBound` in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`, and
the finite-clock semantic carrier in
`UniformEquilibrium/Quitting/Paths/FiniteClockTerminalSemantics.lean`.
The existing theorem supplies the same quantitative radius, but changes
the payoff moments. The new simultaneous exact moment preservation is not
its stated conclusion. Existing exact prescribed-outcome compression does
not preserve caps. The new result combines these two distinct ingredients
without conflating either with the other.

Also inspected the named stopping-law payoff, calendar-order, and finite
opponent atom/gap reply sources cited in the reviewed draft. Their use is
consistent with unrestricted behavioral deviations and the first-Quit-law
model. No fresh Lean coverage is asserted.

No new reward-table class is shown excluded. The justified gain is a
stronger actual approximation normal form for a fixed compact minimizing
source and an exact hierarchy for its fibre. Internal-note placement is
appropriate until a further argument consumes these constraints to exclude
a surviving source mode or reward class.
