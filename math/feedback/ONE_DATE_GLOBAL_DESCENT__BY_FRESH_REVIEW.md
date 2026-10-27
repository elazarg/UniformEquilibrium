# Independent whole review: M14 one-date global descent

Verdict: PASS for the ordinary mathematical residual-class exclusion in the reviewed artifact. No unresolved mathematical objection was found. This is not a UE theorem, a finite-clock elimination, or a fixed-cap descendant replacement.

## Exact scope and bytes

Reviewed the complete one-date source manuscript, now the first part of
`math/notes/CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md`. Its source SHA256 is

    624876f3f0d866cc8188d2268a229bba614693d86bc27842725a8a0de833438a

and its entire exact checker `math/experiments/CODEX_NO_CHILD__ONE_DATE_DESCENT_CHECK.py`, SHA256

    8050db7255045e9339e304ccd3ebff700c00f2f4864889c33ecde1d1720f9106.

The needed existing dependency was read in full mathematical context: the one-date admissible-root classification and complete M14 cap-sign partition in `math/notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md`, full-file SHA256

    6c49b68e8a6bbe56a6420aebf9d8746697c500b67b8d936b3d65e04d73cf9bd3.

Its exact resultant/sign checker `math/experiments/CODEX_NO_CHILD__LAST_ROOT_PARTITION_CHECK.py` has SHA256

    4e28ad010bfa350f77210e92fb8920f353eb529ae9f41802c36bce6ff0dbdb9b.

This is a fresh whole-proof audit. I did not author the descent construction, its rational tail choice, or its sign certificate. No earlier component approval was substituted for this review. During review the proof's support-2/02 explanatory sentence was clarified; I reread the whole current artifact at the pinned final hash above.

## Claim checked

For the exact native M14 table, every positive-cap, positive-Never, one-occupied-date actual profile that is ALL-END and has zero debts on observers {0,1,3} admits an actual competing profile with smaller d2+r nu, for every r>0. The new profile changes the complete profile and includes an explicit infinite tail. For the stated selected source, this excludes all actual finite global minima with at most one occupied date. It leaves finite profiles with two or more occupied dates, inherited head constraints, other endpoints, and UE open.

## Actual tail and regularity

I independently reconstructed the raw root polynomials by enumerating the M14 coalition rewards. They give exactly C=(J-Gamma)x-R and the displayed DC. Independent exact matrix arithmetic verifies

    h=(52,49,46,58)/615, zeta=1/3,
    (Gamma-zeta J)h=(3/205)e2,
    Gamma h/zeta=(21,52,92,49)/205,
    sum h/zeta=1,
    (Jh)2=83/205.

The observer block determinant is -970. Its characteristic polynomial is precisely the positive multiple 970u^3+493u^2+52u+1. The strict cubic Hurwitz inequality 493*52>970 gives negative real parts, hence the stated inverse norm for A exists.

The local contact map is analytic: the raw offers are polynomial, and the relevant finite-dimensional implicit derivative is invertible. Thus the remainder R has the bounded higher derivatives used by the C2 contraction, not merely a pointwise O(|q|^2) estimate. In the weighted C2 norm, the linear composition has norm kappa*lambda^2. The difference of the nonlinear compositions has norm O(epsilon) on a fixed bounded ball: the potentially unweighted second-derivative term is multiplied by R_q=O(s), while changes of R_qq are controlled by analyticity. The weighted space with u(0)=u'(0)=0 is complete. A large fixed ball and then small epsilon yield the claimed actual C2 graph. The tangent relation is exact, and all four leading hazards are positive.

The observer contact identities iterate to actual Never values because the annotations tend to zero. Finite deadlines have exactly the same values. A unilateral behavioral deviation against independent private opponent clocks is an arbitrary private stopping law; averaging its deadlines and Never therefore establishes the full behavioral cap, not a restricted deviation claim.

For the pivot, the uniform O(s^2) remainder follows from summable geometric hazard remainders and the probability of two or more finite clock events. The positive linear margin is exactly 9s/205. It applies at every conditional tail parameter lambda^n s, so Never dominates every finite deadline. The exact debt recurrence is correct. Its remaining term tends to zero because the total finite-clock mass of T_t is O(t) and all rewards are bounded; summing its O(t^2) forcing then gives e(s)=O(s^2). Joint Never mass is 1-s+O(s^2).

No unproved global stable-manifold extension, absorbing-gap input, or tail-selection oracle is used. For the attachment argument, the expansions v(s)=ks+O(s^2), e(s)=O(s^2), and nu(s)=1-s+O(s^2) already suffice. One may apply the smooth local inverse of C to v(s)-g e2; no stronger unproved differentiability of the infinite-tail cap is required.

## Root attachment, endpoint, and objective

At an old one-date root C_O=0 and C2=-g, g>=0. The attachment C(x(s))=v(s)-g e2 makes each observer exactly indifferent at the new root and preserves its actual tail optimality. The pivot's Continue cap exceeds Quit by H2*g. Consequently the whole profile remains actual, ALL-END, positive-Never, and exact-observer. Positivity of the old root and caps persists for sufficiently small s. This is a legal global competitor; it does not purport to keep an inherited head's observer caps fixed.

I checked the exact debt recursion directly from the actual root endpoints:

    d2(s)=nu0(x(s))[x2(s)g+e(s)].

Both inherited pivot debt and tail Never mass carry joint root survival. There is no missing opponent-survival or (1-q2) factor. Differentiation gives exactly

    J'_r(0)/nu0(x)
      =g(e2^T-z n^T)DC(x)^-1k-r[1+n^TDC(x)^-1k].

At g=0 the attachment keeps a literal root tie. The new tail's positive pivot debt is only quadratic, whereas the strict negative r term is linear. Thus the endpoint is included for every r>0, without relying on g>0 or an unstated numerical bound on r.

## Entire class and certificate

The active-observer predecessor argument leaves supports 2,02,012,0123. Support2 has negative observer-0 Never payoff; support02 cannot satisfy observer-0 contact; support012 has negative observer-0 cap. The existing complete last-root theorem then identifies the entire positive-cap full-support branch as alpha<=z<rho0, including g=0 at alpha. It is not a selected numerical branch.

I checked the use of that theorem, its positive denominators, and the scalar monotonicity. The endpoint Bernstein signs place x3 in (13/100,17/100). Both phi and its self-composition increase in z and y on this whole legal rectangle: denominator positivity follows at its upper corner and monotonicity, and the displayed corner values place x0,x1 inside the claimed box. Thus the four-dimensional box covers the full branch, including its endpoint.

I read and executed the complete new checker. It derives DC from L and the actual quadratic/cubic terms, forms the three stated determinant/adjugate polynomials, and uses the exact tensor Bernstein conversion on the stated rational box. Its coefficient degrees, counts, and minimum values all reproduce the proof:

- det DC: degrees (2,2,2,2), 81 coefficients, minimum 695509964106293/62500000000;
- A: degrees (3,3,3,3), 256 coefficients, minimum 8503628877474398758391/4882812500000000;
- B: degrees (3,3,4,3), 320 coefficients, minimum 46778584435393895821/195312500000000.

All are strictly positive. The determinant sign and the adjugate identities give both required strict inverse inequalities with the correct signs. The checker also verifies the rational box inclusion. Separately, the canonical complete last-root checker passed its exact resultant identities and rational sign partition.

Independent raw-table/tangent arithmetic also reconstructed C and DC, the rational tangent, observer spectrum, and formal actual-objective derivative. Only the canonical reproducible checker is retained; the probabilistic and functional-analytic arguments were separately reviewed above.

## Attempted falsifiers and limits

I specifically tested for: an error at the pivot tie g=0; replacement of actual caps by algebraic continuations; loss of observer indifference after attachment; an incorrect joint/deleted survival factor in the debt recurrence; nonsummable tail errors; an unjustified C2 graph contraction; circular use of global minimality; omission of part of the positive-cap last-root branch; a determinant-sign reversal; and application to a descendant without pricing its head. None survives in the pinned proof.

The strategic inputs are all produced for the stated one-date theorem: the actual infinite tail, its hazards and full caps, the perturbing root, and a strictly improving whole profile. The theorem is conditional only on the explicitly stated old actual profile, as a residual-profile exclusion should be. The selected-source corollary uses the canonical benchmark's prior positive-cap source conclusion and does not assert new source attainment.

Initial empty dates can be deleted when applying the result to the selected source: positive caps already dominate their extra solo-Quit value zero, while prescribed outcomes and Never mass are unchanged. The competitor may have infinitely many occupied dates, which is permitted for a global minimum over the actual exact-observer carrier. Therefore the conclusion really excludes every one-occupied-date source profile, rather than merely a fixed finite-format variation.

The source correspondence read was `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, for the full behavioral root cap. The goal endpoint `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` was also inspected; this descent result does not reach it. No Lean or build commands were run, and no L/A/C seal is claimed.

The draft deliberately uses its canonical conference classification dependency and is not a standalone export packet. Internal retention is appropriate without duplicating that complete classification. This review approves its precise residual-class exclusion, not raw-table UE existence or arbitrary Fin4 closure.

The proof and checker were copied byte-for-byte into their canonical paths above. The canonical benchmark subsequently gained cross-references to this result; its classification and resultant proof used here are unchanged.

The one-date source at the pinned hash is also preserved in commit `9bde2e4a`. Its complete proof now forms the first part of the finite-descent note; only headings were changed when the independently reviewed two-date extension was appended.
