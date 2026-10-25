# Independent review of the universal penalty transition

Reviewer: CODEX_GLOBAL_PLATEAU_REVIEW.

**PASS for Section 7 and its used source adapters**, as ordinary mathematics,
at full-file SHA-256
`55fc081f9202b3a23231f773239032a4faf78457b5e3d4856d24858986725e51`
of [the boundary reduction](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Sections 1--6 retain their separately recorded reviews; this is not a fresh
whole-file approval, a Lean check, an export, or a Fin4 closure.
Section 8 is excluded from this review: I authored its underlying argument,
and its independent reviews are recorded separately.

The checked claim is the alternative between an observer-END absorbing
global minimum and a finite first penalty plateau with an attained
positive-Never minimizer. At a strict inverse-column pivot, the first
branch is strengthened to an ALL-END absorbing minimum with
N_p<1/(1+mS). The review covers this strengthening, the strict pivot margin
for every positive penalty, and the all-END/mass conclusions for the
critical positive-Never branch. I found no mathematical objection.

## Compact carrier and source

The zero-Never identification is valid for the entire augmented tuple, not
only its payoff/cap projection. Given actual tuples approaching joint Never
mass zero, move a smallest marginal Never mass to one finite date. That
mass tends to zero. Independent-law coupling controls every prescribed
payoff, every complete response payoff and its supremum, and each pure-Never
value; the Never-vector change also tends to zero. The new laws absorb.
Thus the zero-Never part of H is exactly the augmented absorbing closure.

The positive partial-Nash minimum supplies the source needed for (7.1).
Indeed, if the compact absorbing carrier had zero minimum maximum debt, it
would contain an all-zero-debt point, contradicting m>0. Its global gap is
therefore positive. Sections 2--3 of the cited absorbing partial-Nash note
apply to every minimum, without a positive observer-margin hypothesis.
Its nonnegative-cap root budget, negative singleton-column argument, and
first-zero/solo-prefix contradiction establish B_p>m.

For the optional strict-column conclusion, the positive native absorbing
SUM gap follows from that same compact positive gap. Part II of
[the strict-column source packet](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
supplies a strict inverse column at this same native table. Part III
records the adapter from an arbitrary hypothetical original counterexample.
The section correctly allows selecting such a pivot; it does not assert
that every pivot has a strict column.

## Transition and strict critical face

The inequality d_i>=N_i(B_i-e_i) makes every positive-Never point of C
observer-END. If the absorbing minimum set misses this closed END set,
compactness excludes d_p<m points whose positive Never masses approach
zero. Hence the positive ratios in (7.5) lie in one compact collar. AllNever
gives a positive ratio, so the stated finite maximum is attained, and its
maximizer proves both strict pre-plateau values and the plateau. The
left derivative is the maximum slope among compact minimizing points;
the zero-Never minimizers supply the zero right derivative.

For every r>0, mu=f(r)>0: a zero value would force d_p=nu=0. Finite
observer-Nash prefixing gives exactly J_r'=R_p+c mu. The shifted Nash-root
estimate therefore proves B_p>=mu. On B_p=mu, the zero-observer comparison
retains its q_p factor: each other observer hazard is at most
(eta/mu)q_p, and the adverse-event term is at most 4M eta q_p/mu. Thus
positive Delta_ip is impossible even when q_p tends to zero.

The critical face contains no zero-Never point, including when mu=m,
by (7.1). It is compact, so its least N_p is attained and positive.
A sufficiently small solo-pivot root is observer-Nash, keeps B_p=mu,
keeps J_r=mu, and strictly reduces N_p. This is a contradiction on the
same face. It proves (7.9) without a global Never collar or r<A.
AllNever then excludes lambda_*=m. This argument also verifies the
claimed uniqueness of AllContinue at continuation B-f(r)e_p.

## Strengthened ALL-END absorbing alternative

The new subsection is valid without assuming absence of observer-END
absorbing minima. Along r_n tending to infinity, minimizing points have
nu<=m/r_n. A compact cluster point lies in C0 with debt at most m, so its
debt is m. Since d_p(Y_n)<=f(r_n)<=m, this proves f(r) increases to m;
one does not need to assume r_n nu(Y_n) tends to zero in advance.

Below the first plateau every minimizer has positive nu and hence is
ALL-END with the inverse-axis mass bound. If the plateau never begins,
their compact limit is an ALL-END member of M0 with N_p=0. At a finite
first plateau lambda0, continuity gives f(lambda0)=m and the prior
AllNever argument gives lambda0>m. Left minimizing limits remain ALL-END,
minimize J_lambda0, and satisfy N_p<=1/(1+lambda0 S). A zero-Never limit
therefore supplies the claimed strict bound at an absorbing minimum;
a positive-Never limit supplies the critical alternative.

If M0 misses the closed ALL-END set, critical positive-Never minimizers
have a uniform positive Never collar by compactness. The attained ratio
formula then follows directly from J_lambda0>=m and equality at one such
point. No assertion that every positive-Never point of C is ALL-END is
used. I checked both the infinite-threshold case and a finite threshold
whose left minimizing limits are all absorbing; neither is omitted.

## Full-cap graft and falsification attempts

I checked Section 2 of the cited constrained-repair proof: fine independent
discrete clocks give the displayed inverse-axis integrals uniformly over
the full response menu. Censoring finite head tails and inserting an empty
final head query retains its old END value. Diagonal limits therefore give
(7.10) in the same H, including for semantic old points. Observer payoff,
cap and END are unchanged. A strict pivot cap/END gap permits small-T
descent. At equality, differentiating the complete increment gives
nu[1/N_p-1-rS], hence (7.11).

The attempted failure cases were an unattained cap, a vanishing selected
Nash hazard, zero observer caps, a zero-Never critical point at mu=m, and
nonactual plateau minimizers. The preceding bounds and carrier arguments
cover each; none requires cap attainment or executing a continuation after
infinitely many dates. The two alternatives may overlap, and the first
is not excluded by a strict observer margin at a different minimum.

For semantic correspondence I inspected
`quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. This was static
inspection only. No new result was attributed to a checked Lean theorem.
