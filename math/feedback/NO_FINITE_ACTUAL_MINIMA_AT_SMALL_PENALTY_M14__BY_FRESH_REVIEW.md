# Fresh whole-proof review: complete finite actual source exclusion

Verdict: PASS as ordinary mathematics, with no unresolved objection. Conditional export admission is affirmed for the exact restricted source mode stated below.

Reviewed final self-contained packet: `math/exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md`, SHA256 `d7018b8746ad1b1b8c2f60337f22bdf392203ae60d37832d127c1af11b1ce96a` (390 lines).

Reviewed and rerun exact checker: `math/experiments/CODEX_NO_CHILD__FINITE_SOURCE_CHECK.py`, SHA256 `934310bffd8bb44a06b989c05f05e22d7b34dfd6bf351083c3c47d30a173a428`.

This supersedes my review of the earlier 195-line proof. All final proof lines and the complete checker were inspected. The new semantic-tail descent, collar and native-Nash classification, and simplified penultimate-root limit were reviewed independently; they do not inherit approval from the earlier argument or its longer actual-tail dependency.

## Exact claim and remaining inputs

Fix the specified native M14 table and the compact closure H of all actual augmented tuples (U,B,e,N). Let C be its zero-observer-debt subset, and suppose its nonempty absorbing face has minimum pivot debt m>0. There exists r0>0 such that, for every 0<r<min(m,r0), no actual global C-minimum satisfying the explicit incoming conditions (2) has finitely many occupied dates. The number and placement of those dates are unrestricted.

The source profile must minimize over C, including its semantic limit points. Minimizing merely over actual observer-exact profiles would not justify the new semantic competitor. C is not the closure of only exact-observer actual profiles. The packet correctly states both distinctions.

The assumptions m>0, actual realization, and the incoming source conditions remain visible. This theorem does not produce them, assert the same finite exclusion at r=m/2, eliminate infinite calendars or nonrealized inherited endpoints, or prove original-game UE. Failure of the conclusion supplies a sequence of finite actual source minima at penalties tending to zero; existence at every penalty is unnecessary.

## Whole-proof verification

1. **Full behavior and prefix closure.** Independent stopping laws price every private behavioral response along the unique live history. The root payoff, cap maximum, Never value and marginal-Never maps (3) are exact and continuous, so prefixing actual approximants preserves H. ALL-END passes to conditional tails: positive H_i and B'=e' in (3) force B_i=e_i in the tail. Formula (4) then transfers zero observer debts through positive joint survival. This avoids treating conditional tails as global minima.

2. **Uniform survival and first activity.** The pivot-only first-root contradiction uses B2>mu, tail membership in C, and the exact affine objective recursion. It requires neither strict observer-cap positivity nor the old first-support classification. Compactness of the same augmented C implies that d2->0 keeps nu bounded away from zero, since otherwise an absorbing zero-debt point contradicts m>0. Every individual Continue factor and finite joint-survival prefix is at least nu, giving uniformly bounded odds and a uniform conditional-debt bound d_tail<=d_whole/eta.

3. **Collar and complete native-Nash uniqueness.** For a last ALL-END root, C(x)<=0 and the positive inverse A imply x<=AR(x). If s=max x_i<=1, then R_i<=20s^2 and max(A1)<1, so a nonzero root has s>=1/20. Thus last roots cannot disappear in a limit. A nonempty proper native Nash root is full support: singleton support violates a successor's quiet comparison; at larger supports an active owner missing its predecessor has a strictly negative contact expression. The displayed phi parametrization, legal denominators, strict monotonicity, quadratic branch endpoint z_*, resultant, sign changes and endpoint signs prove a unique nonempty proper Nash root x_alpha. No full last-root classification is silently imported.

4. **No-prefix obstruction.** The rational rectangle gives strictly positive B_alpha and the displayed lower bound. The positive inverse and t=min x_i would force t>37/1000+(36/5)t^2 for any C(x)=B_alpha, contradicting discriminant -41/625. Any nonempty Nash prefix against B_alpha must have full support by predecessor closure, so the equality obstruction excludes every proper support case as well.

5. **Produced semantic axis tail.** For fixed t, the N actual identical roots have odds (t/N)(4,5,1,3). Observer passive offers are exactly zero. Every observer deadline payoff and cap is O(1/N), and summing N prescribed O(1/N^2) stage payoffs gives U_i=O(1/N). For pivot2 the Quit offer is negative and the passive offer is positive, making Never the full maximizer. Exact geometric sums and product limits yield B=e=b(t)e2, U=u(t)e2, and N_i=exp(-w_i t). Therefore the augmented limit Q_t belongs to C despite the approximants not being observer-exact. This is a semantic point, not an executed continuation after infinitely many dates.

6. **Local one-date descent.** Near x_alpha, D=DC is invertible and the implicit root repair C(x(t))=[b(t)-g]e2 preserves all observer contacts and the pivot gap. Prefix closure puts the repaired tuple in C. Since b'(0)=u'(0)=11 and nu(Q_t)'(0)=-13, direct differentiation gives exactly (10). The three positive Bernstein certificates prove its strict negativity for every r>0 and g>=0 in the box, including g=0. This local result is sufficient because every last root in the contradiction converges to x_alpha; no global one-date curve coverage is needed. Initial empty dates are harmless here because the relevant caps are strictly positive near x_alpha, including the repaired prefix caps.

7. **Terminal limit and penultimate observer root.** Vanishing conditional debt, the collar, bounded odds, and passage of all inequalities and complementarity identities imply that every terminal-root limit is the nonempty proper native Nash root x_alpha. A one-date subsequence is excluded by the local semantic descent. There are then at least two observer-active dates: the first cannot be pivot-only, and the last cannot be pivot-only because C0=14x2>0. Between the penultimate observer date and the terminal root, only pivot2 can be active.

8. **Unbounded calendar lengths.** The exact pivot-only block identity d_block=(1-s)v2_last+s d_last holds regardless of its length. Since d_block->0 and v2_last->B_alpha,2>0, it forces s->1 and the whole block cap tends to B_alpha. At the penultimate observer root, a fixed active observer can be selected along a subsequence. Its contact value tends to a positive coordinate of B_alpha, so the bounded root odds cannot converge to zero. All observer complementarity identities pass to the limit. Uniform positive opponent survival and vanishing conditional pivot debt give q2[v2-C2]->0, precisely the remaining pivot complementarity. A separate lower bound on the pivot hazard is unnecessary. The resulting nonempty proper Nash prefix contradicts item4.

This proves one sufficiently small penalty range excluding every finite calendar simultaneously.

## Exact checks and falsification attempts

The complete checker passed after its final additions. Its tensor conversion uses the correct power-to-Bernstein formula on the entire closed rational box; every coefficient is tested, with 81+256+135=472 strictly positive coefficients. Its symbolic determinants, adjugate expressions, resultant and sign arithmetic match the proof, with no floating tolerance or sampling. The final checker also reconstructs the cap lower bounds from Gamma and the root box and verifies the inverse-row-sum upper bound used in the collar.

I independently reproduced the inverse, axis products, every rational phi/root/cap bound, and the no-prefix discriminant. An independent direct enumeration of raw quitting coalitions at rational hazards also verified the finite approximants' passive/Quit offers, every distinct finite-response cap, and pivot Never optimality. Symbolic differentiation independently gives b'(0)=u'(0)=11 and (b-u)''(0)=11. The descent formula was rederived from the root objective rather than inferred from checker success.

Explicit attempted falsifiers included an increasing number of dates, a vanishing last root, a rare penultimate observer, a pivot hazard vanishing in the penultimate limit, long pivot-only blocks, disappearing support coordinates, initial empty dates, and non-exact finite approximants. The collar, complementarity formulation and exact block identity handle these cases without imposing a date budget or a uniform active-hazard lower bound. The actual finite native Nash root x_alpha is a positive-Never zero-debt boundary example; it is excluded only as a source minimum, by semantic descent.

The final curation removes its external finite-or-I4 theorem sentence. Its proved conclusion is infinite occupied-date support. A coordinator may combine that conclusion with a separately established support partition outside this packet; that partition is not a hidden premise here.

## Source audit and conditional export gate

The stopping-law/behavioral payoff and full-cap bridges in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`, `quittingTerminalSemanticPair_rootThenContinuation` in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and the root maximum in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` match the semantic calculus used here. The inspected `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt` and `exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff` concern semantic minima; they do not establish this augmented observer-objective source, actual realization, or the new finite-mode exclusion. No Lean build or L/A/C seal is asserted.

I affirm the conditional exception's independent value: this closes the entire finite actual source mode at selectable sufficiently small penalties, strictly beyond the prior one- and two-date restrictions. The final packet states its unproduced inputs, produces its own semantic comparisons, proves all required finite algebra, gives exact boundary tests and a concrete consumer/handoff, and contains no conference-file mathematical dependency. It neither relabels an inherited point as an actual profile nor counts this as a completed source-to-UE chain.
