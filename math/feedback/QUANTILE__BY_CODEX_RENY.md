# Independent review of quantile and common-clock compression

Reviewer: CODEX_RENY. Ordinary mathematical review, not new Lean verification.

Verdict: **PASS at the stated scope.** No mathematical repair is required.
The uniform rational net and common-clock independent-mixture theorem are
correct. The positive-gap certificate scheme is sound and complete, but its
main Fin4 conclusion is already covered by checked compression and
semidecision sources. It supplies neither a positive-gap table nor a
zero-gap decision procedure or cross-face equilibrium compiler.

## Reviewed inputs and execution scope

Read both complete documents before consulting other reviews:

- `gpt/QUANTILE.md`, 544 lines, SHA-256
  `f28bfa0de099c88555d7ebf7c2864ceb74b51c324bec315e259b12b662e9ad48`.
- `gpt/QUANTILE_CLOCK_COMPRESSION.md`, 201 lines, SHA-256
  `afa8417acf568a98a10632b210447e59a64ac814ab8ba7c36f240a15035b7e00`.
- `gpt/QUANTILE_CLOCK_COMPRESSION.zip`, SHA-256
  `a6465fd7ae93465f0d817dc7b470f942747441e9465f1336add3ef61c819c216`.

Archive inventory was inspected first. It contains exactly three ordinary
files under `face_compilation/`: the companion markdown (7592 bytes),
`check_compression.py` (5726 bytes), and `check_shared_mixtures.py` (1515
bytes). No absolute paths, traversal paths, symlinks, or other entries occur.
The archived markdown is byte-identical to the supplied standalone copy.

Both scripts were read completely before execution. They use local standard
library exact fractions, finite enumeration, and seeded random checks, with
no network access or file mutation. They were executed directly from the
archive in memory; originals were not extracted or modified. Results:

- 120 exact-rational profile regressions passed;
- 100 independent-coordinate mixture regressions passed;
- the supplied adjacency/long-gap regression passed.

These finite tests corroborate but do not prove the unbounded-law claims.
The review below independently checks those claims. The introductory
literature remarks are not used in any proof or novelty conclusion here.

## 1. Full behavioral caps are controlled by the CDF distance

There are finitely many players, arbitrary signed terminal rewards bounded
by M, independent stopping laws on the nonnegative integers plus Never,
and reward zero on all-Never. Every unilateral replacement law is allowed.

Fix all other pure stopping times while changing player j's law. If their
first finite date is t with coalition S, the observed payoff is A before t,
B at t, and C after t, including Never. Its expectation is exactly

    C + (A − B)F(t−1) + (B − C)F(t).

Thus a CDF discrepancy δ costs at most 4Mδ. If everyone else chooses Never,
the expression is r_i({j}) times the finite stopping probability. Taking the
limit of the finite CDFs bounds its change by Mδ. This treats the atom at
Never without a tightness assumption.

Conditioning and integrating over arbitrary independent opponent laws is
legal because the integrand is bounded. For a deviator i the same bound
holds uniformly over its entire replacement law; only coordinates j ≠ i
are changed. Consequently

    |ΔU_i| ≤ 4M Σ_j δ_j,
    |ΔB_i| ≤ 4M Σ_(j≠i) δ_j.

Taking a supremum requires neither an attained best response nor a finite
mean stopping time. There is no illicit exchange of pointwise convergence
and a response supremum: the bound already holds for every replacement.

Boundary test: take three payoff levels A=C=M and B=−M, with the fixed
other player stopping at date 1. Replacing half mass at 0 and half at 2 by
sure mass at 1 gives CDF distance 1/2 and payoff difference 2M. Hence the
4M coefficient in this coordinate estimate is genuinely attainable; ties
cannot simply be ignored.

## 2. Quantization and exact clock shortening

The midpoint empirical quantiles satisfy

    F_quantized(t) = #{k : (2k−1)/(2K) ≤ F(t)}/K.

This gives discrepancy at most 1/(2K), including a quantile level equal to
the limiting finite mass but never attained at a finite date. Such a
quantile is correctly assigned Never. Arbitrary Never mass is rounded,
not preserved exactly; a coordinate which is identically Never is preserved.

The resulting payoff, cap, and maximum-debt errors are respectively
2nM/K, 2(n−1)M/K, and (4n−2)M/K. Each coordinate has at most K atoms in
total, including Never.

For the finite union D of the quantized support dates, the proposed map
preserves order, ties, and the existence of every nonempty interval before
or between support dates. It also preserves a finite date after the last
support and Never as distinct response classes. Every pure response in
either clock has a representative in the other clock with exactly the
same outcomes against every supported pure opponent tuple. This proves
two-sided cap equality, not merely one-sided safety. An empty support union
is handled separately by the unchanged all-Never profile.

With L support dates the last image is at most 2L−1; hence the stated
prescribed menu of length 2nK is correct. Removing unused dates beyond what
the rule specifies would not be sound.

Exact adversarial tests, independently recomputed: let player 0 choose
Never, and let its reward be 1 when it quits alone, −1 on the collision
{0,1}, and 0 when only player 1 quits. Set all player-1 rewards to zero.

- Against half mass at date 0 and half at date 1, player 0's cap is 0.
  Moving the second atom to date 2 inserts a gap and raises the cap to 1/2.
- Against sure date 1 the cap is 1, by preemption at 0. Collapsing that
  first date to 0 reduces the cap to 0.
- Against half date 0 and half Never, both Quit-at-0 and Never give 0,
  but any strictly later finite date gives 1/2.

These falsify the nearby incorrect clock rules and truncated test menus,
not the rules in the submitted packet.

## 3. Uniformity over every independent crossed mixture

Quantize each coordinate of each of the m supplied profiles, then shorten
the union of all their support dates by one fixed map. For any weights
chosen independently at each coordinate, mixing the pre-shortening laws
preserves the CDF discrepancy 1/(2K). Pushforward through the fixed map
commutes with these mixtures. All crossed profiles have support contained
in the same union, so the exact cap argument in Section 2 applies to every
choice of weights, with no new choice of clock.

Thus the claimed uniform bounds and clock length 2mnK hold. The profile
remains a product law: this is not a common random source label. Immediate
date-zero deviations retain their meaning, including when the first
support date is positive. Applying the same CDF bound separately to a
quiet child and to the ambient immediate outsider payoff proves the stated
child error and outsider-gain estimates.

Important limit: the quantifier is every mixture of a **fixed finite source
family**, not one bounded clock for an infinite sequence of sources. Nor
does the theorem preserve an externally supplied prefix, the numerical
reach of a chosen nonzero source cut, or arbitrary finite-horizon payoff
processes. It controls the displayed terminal quantities. No such stronger
claim is needed for the theorem actually stated.

## 4. Exact finite certificates and their limits

There are 2nK+1 possible atoms per coordinate, including Never. Distributing
K indistinguishable units among these atoms gives exactly

    |G_K| = binomial((2n+1)K,K)^n.

For any grid profile, dates 0 through 2nK together with Never include every
payoff-distinct pure response. The final finite test is outside the
prescribed menu and is indispensable, as the last test in Section 2 shows.
All maxima and product expectations are rational for rational reward data.

Writing η=inf E over all behavioral product laws and a_K=min_(G_K) E,
the compression of each arbitrary profile gives

    max(0,a_K−(4n−2)M/K) ≤ η ≤ a_K.

This proves both soundness and completeness of the strict finite positive
certificate. Non-nesting of the grids is immaterial. For η>0 choose K with
(4n−2)M/K<η; then a_K≥η supplies the strict test. Conversely the certified
lower bound is global, not a restricted-profile lower bound. At η=0 this
positive-certificate search need not halt. Nash's theorem for a fixed
prescribed menu cannot eliminate its omitted late response date.

The reward perturbation estimate |η(r)−η(s)|≤2‖r−s‖∞ is valid. Rational
perturbation within a quarter of a positive gap preserves at least half
that gap. Cardinal minimality is retained because *all* smaller reward
tables were assumed to have equilibrium, not because particular face
profiles survive the perturbation. This produces no actual counterexample.

## 5. Cross-face splice regression

For a fixed product prefix the complete cap is the maximum of the best
response inside the prefix and the continuing response branch. That branch
has coefficient λ_i, the opponents' survival probability. The prescribed
tail payoff has coefficient c, the joint survival probability. Thus the
submitted formulas (1)–(3) are correct. For an empty prefix, omit the
inside-prefix branch rather than assigning a nonexistent real maximum.

All six proper-face source choices in the displayed three-player table are
exact child equilibria: participating players attain their maximum
available child reward. Each listed outsider gains 1 immediately.
Independent exact arithmetic confirms the ambient vectors for x and y and

    U_1(P*x)=B_1(P*x)=1,
    U_1(P*y)=3/2,  B_1(P*y)=2.

The common protected player therefore acquires debt 1/2 although its child
debt is zero in both sources. This exactly realizes (λ_1−c)ΔU_1.

The regression does not satisfy the positive parent-gap assumption: all
three players quitting at date zero is an exact parent equilibrium. The
packet explicitly says this. It refutes error-only splice accounting, not
the actual cardinal-minimal-source implication in the live question.

## 6. Narrow source correspondence and relevance

The lookup followed the quantile entries of `docs/TOOLKIT.md` and the named
sources below; no whole-tree audit was used.

- `Research/Quitting/EscapeAwareQuantileClockTransport.lean`:
  `hasEscapeAwareQuantileClockCompressionAtBound` and
  `hasEscapeAwareQuantileClockCompression_of_normalized` already compress
  every finite-player behavioral profile with full cap control, including
  unbounded deviations and exact retention of arbitrary Never atoms.
  `quittingQuantileClockCompressedLaws_none` records the latter distinction.
- `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`:
  `escapeAwareQuantileClock_normalized_quantitative_bracket` already gives
  the general-player objective bracket; the Fin4 specialization
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` has support
  8K+1 and bracket 24/K. The present rational net gives support 8K and
  bracket 14M/K, but rounds Never mass and uses a different finite center.
- `Research/Quitting/FiniteClockPolynomialCenter.lean`:
  `exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue`
  and `finiteClockPolynomialSemanticImage_eq_reachable` already identify
  unrestricted caps with the complete finite response list and preserve
  product-law provenance.
- `Research/Quitting/FinFourExactScaleResolution.lean`:
  `exists_finFourExactScaleStep` already gives termination at every positive
  rational accuracy for every normalized rational Fin4 table.
  `Research/Quitting/FinFourFixedTableCounterexampleSearch.lean`:
  `exists_finFourFixedTableCounterexampleStep_of_infimum_pos` already gives
  the positive-gap fixed-table semidecision.
- `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`:
  `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` is exactly
  the generic 2-Lipschitz estimate. The Fin4 rationalization and global
  existential search are already supplied by
  `exists_normalizedRationalFinFourRewardCode_exploitabilityInf_pos` in
  `Research/Quitting/FinFourPositiveRationalRewardApproximation.lean` and
  `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` in
  `Research/Quitting/FinFourCounterexampleSemidecision.lean`.
- `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`:
  `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  already give actual finite-menu approximation with unrestricted error
  and fixed-target control. They do not give the same uniform rational
  support/denominator bound as this elementary construction.

The specific midpoint-CDF proof, exact gap-preserving finite-family clock,
and uniform independent-coordinate-mixture formulation were not found as
named declarations in this bounded lookup. They are a useful elementary
reformulation/extension of the existing finite verification architecture,
not a newly discovered global strategic reduction. The general-cardinality
exhaustive grid is also explicit without the Fin4-specific executable
certificate machinery. No worldwide novelty conclusion follows.

Neither `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md` nor
`questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md` is answered: the former
requires a positive instance or total zero-versus-positive decision, and
the latter requires actual cross-face construction/cardinal descent. No
choice of mixture weights with small parent debt is produced. Consequently
this correct packet does not warrant a new conjecture-facing export merely
for reestablishing complete finite verification. Retain its proof and
regressions as useful source material; no new owned research note is needed
to duplicate the supplied mathematical text.
