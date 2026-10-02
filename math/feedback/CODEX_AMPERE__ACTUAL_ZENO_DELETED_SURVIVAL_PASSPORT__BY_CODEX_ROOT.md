# Independent review of the actual Zeno deleted-survival passport

Reviewer: CODEX_ROOT

## Verdict: PASS

I independently re-derived the finite-word survival identity, the compact
subsequence split, the host modification, the cap coupling over the complete
behavioral strategy class, and the explicit four-player regression.  I found
no unresolved mathematical objection.  The theorem is a strict reduction,
not a consumer of the fully screened positive-minimum arm.

## Claim checked

For a literal premark word, let \(S_i\) be player \(i\)'s survival probability,
\(M=\prod_iS_i\) the joint reach of a later pure marked pair, and
\(H_i=\prod_{k\ne i}S_k\) the reach after deleting player \(i\)'s clock.  The
claim is

\[
H_iH_j\le M\qquad(i\ne j),
\]

and hence every actual \(M_n\to0\) sequence has a subsequence with either one
visible host or all deleted reaches vanishing.  The visible-host arm admits a
literal fixed-mass endpoint modification.  In the fully screened arm, marked
siblings coalesce in law, payoff, and unrestricted cap.  A zero-minimum
example shows that every listed local field except \(D_*>0\) is insufficient
to exclude full screening.

## Independent derivation

For distinct \(i,j\),

\[
\left(\prod_{k\ne i}S_k\right)
\left(\prod_{k\ne j}S_k\right)
=
\left(\prod_kS_k\right)\prod_{k\ne i,j}S_k
\le M.
\]

This remains true on boundary faces.  Compactness of \([0,1]^4\) then gives a
subsequence limit \(h\) with \(h_ih_j=0\) for distinct coordinates, so at
most one coordinate is positive.  If \(h_h>0\), a fixed positive lower bound
for \(H_h\) follows after deleting finitely many terms, and
\(H_i\le M/H_h\to0\) for \(i\ne h\).

For host compression, deleting \(h\)'s premark clock makes the mark reachable
with probability \(H_h\).  Selecting \(h\)'s better Boolean action at a pure
pair cannot empty the marked coalition and makes its local coordinate defect
zero.  The postmark roots are untouched.  A two-value subsequence fixes the
Boolean choice and terminal label if a downstream dependent type requires
them.

For cap coalescence, the marked mover's opponents are identical, so its cap is
identical.  For another player \(i\), couple the two opponent profiles under
an arbitrary behavioral replacement of \(i\).  The coupled plays can first
differ only if every opponent of \(i\) reaches the mark, an event of
probability \(H_i\).  Bounded rewards give deviation-payoff difference at
most \(2RH_i\).  Taking suprema over the entire behavioral strategy space
preserves that bound.  This covers Never, late deterministic dates, arbitrary
hazards, and private randomization, and uses no best-response attainment.

## Falsification attempt and regression audit

I tested the proof against zero survival factors, multiple deleted reaches,
an owner who belongs or does not belong to the marked pair, Never deviations,
and deviations which wait past the mark.  None invalidates the identities:
the pairwise inequality is division-free, the marked coalition remains
nonempty, and the cap coupling is controlled by opponent reach rather than
the prescribed mover's reach.

For the stated reward table, the common prefix clocks give

\[
M_n=n^{-4},\qquad H_{i,n}=n^{-3}.
\]

The finite-tie probability is at most \(6np_n^2\le6/n\), so the terminal law
converges to the uniform singleton law.  The prescribed payoff converges to
\((-1/4)^4\).  Players \(0,2,3\) have cap zero exactly.  Player \(1\)'s only
positive opportunity is collision with player \(0\), bounded by \(p_n\)
before the mark and \(n^{-3}\) at the mark; mixture over complete stopping
times gives \(B_1\le1/n\).  At limiting cap zero all-Continue is uniquely
Nash, while all-Never is an exact terminal Nash profile, so \(D_*=0\).

This example really does reproduce fixed pair labels, a paid sibling,
positive-debt common tail, product provenance, complete semantic/law
coalescence, and unique all-Continue limiting root.  It correctly fails only
the positive-minimum hypothesis named by the result.

## Scope

The visible-host output is not proved near-minimal and does not control cap
leakage for the other players.  Full screening with \(D_*>0\) remains open.
The export should retain both limitations.
