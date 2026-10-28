# Independent whole-proof and export review: chronological two-owner exclusion

Reviewer: root_obstruction. Verdict: PASS, including export admission as a
strict residual-mode reduction. No unresolved mathematical objection remains.
The reviewer did not contribute to this theorem or its concrete raw control.

Reviewed complete artifact:
math/notes/CODEX_COORDINATOR__CHRONOLOGICAL_TWO_OWNER_TAIL_EXCLUSION.md
SHA256: 12d62db590c5befdb6497cc7b90ea9f8eebddbaae58ff40f933e6f0351c3919a.
The intended frozen destination is
math/exports/CHRONOLOGICAL_TWO_OWNER_TAIL_EXCLUSION.md with identical bytes.
This review covers the entire final artifact, not merely its chronological
lemma or an earlier draft.

## Claim and scope

The raw finite test excludes every actual independent ALL-END profile with
positive marginal Never masses, zero observer debts, and an eventual pair
of infinite-support owners p,i. It uses the displayed quiet-row signs and
three affine implications. Higher rewards are arbitrary finite numbers.
The concrete open raw region excludes all three possible partners at pivot0.
This is not a UE existence theorem, does not eliminate the other actual or
inherited cases, and does not supply a positive-gap counterexample.

## Whole-proof verification

1. Conditioning at a finite positive-survival cut preserves independence,
   ALL-END, and zero observer debts. A profitable suffix response could be
   pulled back through the old live history; zero total observer debt then
   forces zero conditional debt. No conditional-tail minimality is used.

2. The quiet-row expansion has error at most 6M f_p f_i: at most 3M for
   replacing the Never payoff by singleton terms, and at most 3M for the
   immediate-Quit expansion. It applies to every date. Because 0<=q<=f,
   its linear part is bounded above by the effective coefficients gh,dh
   and gk,dk. The directions of these inequalities are correct. Absorbing
   the vanishing quadratic errors gives exactly the positive two-sided
   ratio bound (RB). This independently supplies comparability; neither
   dispersion nor a positive global gap is hidden in the principal theorem.

3. The exact active-observer identity is J alpha<=G P, with equality at
   every positive partner atom. Thus common atoms have alpha=rho P;
   partner-only dates are impossible, and the solo rate inequality reverses
   correctly when J<0. ALL-END for the pivot gives C z<=A. Infinite support
   gives x,z<1 at each occupied date. The normalized finite-tail ratio has
   the exact updates (7)--(8); it is not replaced by the slightly different
   conditional finite-probability ratio without an error estimate.

4. The bounded ratios give subsequential compactness. Dividing the quiet
   comparison by f_i leaves error O(f_p), which tends to zero regardless
   of the size or sign of higher rewards. Every accumulation point lies
   in the appropriate closed polyhedron. This proves the uniform eventual
   margins (10)--(11), including when one type of date occurs only finitely
   often. The closed t=0 boundaries only strengthen the raw certificate.

5. Every sufficiently late common atom sends its output above tau+delta/2;
   every sufficiently late pivot-only atom would require input at most
   tau+delta/4. Empty dates cannot change the ratio and common dates multiply
   it by at least a/(a-eta/2)>1. Therefore, after one late common atom, no
   subsequent pivot-only atom can occur. Infinitely many partner atoms then
   force unbounded ratios, contradicting (RB). This handles sparse calendars,
   arbitrary empty-date gaps, and arbitrary earlier heads.

6. The concrete data give the claimed polyhedra, exact margins 9/235,
   19/940 and 1/100, overlapping input projections, and failure of the other
   two partners' necessary contact ratios. Uniform boundedness of the two
   polyhedra near the control and strict margins justify an open neighborhood;
   this is not inferred merely from sampling. The late cut may depend on the
   arbitrary finite higher rewards, as the statement expressly permits.

## Exact controls and attempted falsification

Independent exact rational/Sympy checks verified the singleton determinant,
printed inverse, positive inverse columns, all principal pair/triple minors,
all positive LCP support candidates at offset -e0 and their omitted slacks,
the unique inverse-positive child and its negative outside weights, the three
chronological margins, and the leading vector E=(19/10,0,9/100,39/400).
The old interval is exactly [30/47,1), and its solo alternative is nonempty.
Thus the example genuinely passes the older pair screen. The feasible leading
one-date contact vector precludes exclusion by any separating weights using
only those same instantaneous inequalities.

I attempted to falsify the theorem through J<0, empty-date gaps, infinitely
sparse partner atoms, rates tending to1, finite pivot-only support, arbitrary
large signed higher rewards, and a limit approaching the polyhedron boundary.
The proof explicitly handles each possibility. The rate gap is essential:
with the same control except Y_h=-3, equal normalized tails u_n=v_n=u0*2^-n
and equal atoms of relative rate1/2 yield normalized quiet-gap numerators
H_h=u_n/2+u_n^2/4 and H_k=u_n/5-u_n^2/15 when the relevant higher rewards
are zero. For small u0 these give an actual neutral-rate pair tail. This
modified table fails (3), as required; it does not falsify the theorem.
This check also confirms why the chronological result cannot be read as a
universal exclusion of all locally admissible common-support cells.

## Source, overlap, and export gate

I inspected the named definitions quittingStoppingLawExpectedPayoff and
quittingStoppingLawReplacementPayoffCap in
UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean,
and quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. Their independent
complete-law and full behavioral-response semantics agree with the packet.
The listed source paths are tracked. No Lean command was run.

I also checked the applicable earlier interval/O screen, the pointwise
multiplier region, and the actual-source assumptions in the maintained
residual partition. Narrow searches found no implemented or accepted packet
with this same chronological exclusion. The supplied exact control certifies
strict improvement over those applicable source screens; the singleton audit
places it in the surviving matrix region. This review does not assert failure
of every collision-dependent UE criterion for arbitrary completions.

The actual incoming I2 source already has precisely the positive Never,
ALL-END, observer-exact, eventual-support properties required here. The new
hypotheses are finite raw reward inequalities, with explicit constants for
the control. No strategy, tail calendar, recurrent return, cap realization,
or auxiliary minimizing witness is an unproduced input to the exclusion.
The allegedly existing actual profile is the object contradicted, not a
strategic witness assumed to obtain a producer. No exceptional conditional
admission is needed.

I affirm export admission under the strict-residual-reduction category:
the result closes the complete two-owner mode at the stated pivot on a
nonempty open raw region, beyond the earlier interval and instantaneous
multiplier screens. The self-contained raw proof, precise full-response
semantics, exact control, actual-source consumer, and proposed formalization
lemmas meet the gate. This is ordinary mathematical evidence only; it supplies
no new Lean seal and no arbitrary Fin4 closure.
