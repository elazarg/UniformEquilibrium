# Review of the escape-aware quantile-clock semialgebraic hierarchy

Reviewer: `CODEX_MINER`

Note reviewed:
[`CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../notes/CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md)

Verdict: **PASS as ordinary mathematics.**  I attempted to falsify the
quantile boundary cases, both directions of cap compression, the finite max
graph on zero faces, the carrier intersection, and the lower-bound direction.
I found no mathematical defect.  The result is a genuine unrestricted-
behavior finite-dimensional reduction, not a fixed-horizon search.

I recommend a narrow export packet after a second independent unrestricted-
strategy review.  The export claim should be the computable convergent
semialgebraic hierarchy and its `24/M` bracket, not a terminating zero-versus-
positive decision algorithm and not an answer eliminating the Fin4 hard
residual.

## 1. Quantile cells and terminal-gap boundary

For one player let

\[
 C(t)=\sum_{s\le t}\mu(s)
\]

be finite-time cumulative mass.  A marked date is the first finite crossing
of `j/m`, when such a crossing exists.  If a nonsingleton gap carried mass
strictly greater than `1/m`, some grid level would be crossed at a date inside
that gap, which would mark the date.  This proves `mu_i(G)<=1/m`.

The two delicate endpoint cases also pass.

- Before the first marked date, cumulative mass is below `1/m`.
- After the last marked date, let `j/m` be the last crossed grid level.  Total
  finite mass is at most `(j+1)/m` when the next level is not crossed, while
  cumulative mass at the marked date is at least `j/m`.  The residual is at
  most `1/m`.  Equality can occur when the next level is approached but never
  attained; the lemma correctly uses `<=`, not `<`.

A large atom may cross several levels, but all of those levels select the same
singleton date.  This only lowers the number of distinct marks.  Taking the
union over four players subdivides the individual gaps and cannot increase
their mass.  Hence `|H|<=4m`, with at most `|H|` singleton cells and
`|H|+1` nonempty gaps, so `K_m=8m+1` is valid.

`Never` is not part of the finite cumulative function and remains a separate
atom.  In particular, a proper law whose cumulative mass tends to one without
ever reaching one has a terminal finite gap of mass at most `1/m`; it is not
mistaken for Never.

## 2. Prescribed payoff and the `12/m` constant

Under the coordinatewise cell-map coupling, the relative order and equality
pattern of the four clocks is unchanged unless two finite clocks occupy the
same nonsingleton gap.  Marked singleton ties remain literal equal-date ties,
and all-Never remains all-Never.

For a fixed player pair,

\[
 \sum_G\mu_i(G)\mu_j(G)
 \le (\max_G\mu_i(G))\sum_G\mu_j(G)
 \le1/m.
\]

There are six pairs, so the mismatch event has probability at most `6/m`.
Two normalized terminal rewards differ by at most two.  Therefore

\[
 \|U(\mu)-U(\mu^{(m)})\|_\infty\le12/m.
\]

No independence is lost: the coupling is only a proof device, while the
compressed law itself is the product of the four separately pushed-forward
marginals.

## 3. Both cap-compression directions

Fix deviator `i`, leaving three opponent laws.

### Original time to compressed time

Map a deterministic original time `t` to its cell.  Off the union of

1. two opponents occupying one nonsingleton gap, and
2. an opponent occupying the nonsingleton gap containing `t`,

the earliest opponent coalition and its relation to the deviator's time are
unchanged.  The first event has probability at most `3/m`, one for each
opponent pair.  The second has probability at most `3/m`.  Multiplying the
resulting `6/m` mismatch probability by payoff diameter two gives `12/m`.
If `t` is a marked singleton, the second event is empty.

### Compressed time to original time

For a genuine singleton cell use its marked date; for a genuine gap use any
integer in that nonempty gap.  The same bad events and bound apply.  A padded
compressed date, or the explicit date after compressed support, is compared
with any original date after the last marked singleton.  The original terminal
gap may be unbounded and may have no last support point, but this causes no
failure: put the event that any opponent lies in that entire terminal gap into
the second bad event.  Its probability is at most `3/m`; off it, all finite
opponent stops lie in earlier cells and the two deviations have identical
outcomes.  Thus no nonexistent “date after all original support” is being
used.

Never is compared with Never.  Only opponent-pair gap collisions can change
its payoff, already bounded by `3/m`.  Taking suprema after the two pointwise
comparisons yields

\[
 |B_i(\mu)-B_i(\mu^{(m)})|\le12/m.
\]

The checked pure-time extremality theorem makes this an unrestricted
behavioral cap statement.  No best response is assumed attained.

## 4. Exact finite semialgebraic center

For opponents supported on `0,...,K-1,Never`, every finite deviation at or
after `K` has the same payoff.  Thus the complete pure-time list is

\[
 0,\ldots,K-1,K,Never.
\]

Prescribed payoffs and every listed deviation value are polynomials in the
four marginal simplexes.  The graph

\[
 B_i\ge V_{i,\tau}\quad\forall\tau,
 \qquad\prod_\tau(B_i-V_{i,\tau})=0
\]

is exact: the inequalities make `B_i` an upper bound, and the product equation
forces equality with at least one candidate.  This remains true when some
marginal coordinates are zero, when several candidates coincide, and when a
candidate is never used by the prescribed mixed law.  Pure-time extremality
then identifies it with the full behavioral cap.

The marginal simplex is compact and the semantic map is continuous, so its
image `A_K` is compact as well as rational semialgebraic.  Adding a new final
date with zero mass preserves every semantic coordinate.  The old
after-support value becomes the value at the new zero-mass date and remains
equal to the new after-support value, proving `A_K subset A_(K+1)` on boundary
faces too.

## 5. Outer hierarchy and exact carrier intersection

Every executable pair has an `A_(K_m)` center within `delta_m=12/m`.  Since
`N_m` is a closed neighborhood, it contains the closure of executable pairs,
not only the realized image.  Hence the carrier lies in every `R_M`.

Conversely, membership in all `R_M` implies membership in each individual
`N_m`.  Choose `a_m in A_(K_m)` at distance at most `12/m`.  These are actual
finite-clock pairs and converge to `z`, so `z` lies in the carrier.  Thus

\[
 \bigcap_M R_M=\operatorname{Carrier}(r).
\]

This argument correctly avoids asserting that `z` itself is realized.  The
checked positive-debt nonattainment regression therefore causes no problem.

## 6. Bound direction and constants

For coordinate sup norm,

\[
 F(u,b)=\max(0,\max_i(b_i-u_i))
\]

is `2`-Lipschitz.  Since actual semantic pairs lie in `R_M`, minimizing over
the outer set gives the required lower direction `L_M<=eta`.  Since `A_(K_M)`
consists of actual profiles, `eta<=U_M`.

Also `R_M subset N_M`.  If `z` minimizes `F` on `R_M`, take its center
`a in A_(K_M)` with distance at most `12/M`.  Then

\[
 L_M=F(z)\ge F(a)-24/M\ge U_M-24/M.
\]

Therefore `0<=U_M-L_M<=24/M`.  Together with the bracket this gives both
`sup_M L_M=eta` and `|U_M-eta|<=24/M`.  The monotonicity of `L_M` follows from
the definition `R_(M+1)=R_M intersect N_(M+1)`; the individual `N_m` need not
be nested.

For rational input, `gamma<=L_M` is exactly the infeasibility of a finite
rational real-closed-field system with `F(z)<gamma`.  CAD/quantifier
elimination can decide it exactly; an implementation should retain an exact
algebraic trace or another independently checkable real-algebraic certificate,
not merely a solver verdict.

## 7. Novelty audit

The closest checked results are:

- `exists_elementaryCompressedProfile_terminalSemantics_close` and
  `terminalSemanticCarrier_eq_closure_finiteElementarySemanticReachable` in
  the elementary-tail/global-barrier chain; these give escape-complete finite
  approximation but no profile-independent support-cardinality bound or
  `O(1/m)` semialgebraic bracket;
- `TerminalSemanticGlobalDebtBarrierCertificate.Certificate` and its global
  floor consumer; these give an inductive certificate schema, not the explicit
  monotone finite outer hierarchy here; and
- general stopping-law tightness/TV files, which do not provide a common
  ordered quantile quotient preserving all product ties and the full pure-time
  cap with the stated uniform rate.

The narrow phrase/symbol search found no prior common-quantile clock theorem,
no sets `A_K,N_m,R_M`, and no existing `24/M` terminal-exploitability bracket.
The theorem is therefore not a duplicate of the checked barrier schema or of
finite-deadline Nash material.

## 8. Scope and export assessment

The result proves that `eta(r)` for every rational normalized Fin4 table is a
uniformly computable real: exact semialgebraic lower and upper bounds have a
certified gap at most `24/M`.  It semidecides the positive-gap branch, passes
all five mandatory regressions, and gives an actual finite-clock upper witness
at every level.  If `eta=0`, those upper witnesses have exploitability at most
`24/M`, hence form the all-errors terminal approximate-Nash input used by the
existing uniform-payoff selection theorem.

It does **not** decide in finite time whether this computable real equals zero,
and it does not establish which branch holds for the Fin4 hard residual.  It
therefore must not be described as the terminating algorithm requested in
Output 2 or the residual elimination requested in Output 3.

Nevertheless, it clears the general export criterion of an exact reduction
that strictly narrows a named live algorithmic obligation: the unrestricted
infinite-clock adversary is reduced, with a proved uniform modulus, to a
nested sequence of finite rational semialgebraic problems carrying both an
actual-data map and the exact semantic objective.  This is substantially more
than a bounded-horizon verifier, since the lower outer sets contain every
actual profile and converge exactly to the carrier.

Because the statement covers unrestricted behavioral deviations, obtain one
further independent falsification review before export.  A packet should
prominently preserve the zero-test limitation and should not claim that a
positive certificate has already been found.

