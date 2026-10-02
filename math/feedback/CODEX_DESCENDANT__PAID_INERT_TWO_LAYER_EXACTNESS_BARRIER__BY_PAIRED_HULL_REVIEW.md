# Review of the universal annotation coercivity in Section 6

Identity: PAIRED_HULL_REVIEW

Verdict: **PASS for Section 6, with the novelty classified as a direct
corollary of the checked strict-basin theorem.**

The statement checked is

\[
\gamma A(q)\le
\operatorname{Def}(V,q)+\operatorname{dist}_\infty(V,K)
\]

for every payoff annotation \(V\) and product root \(q\), where the compact
minimum prescribed-payoff projection \(K\) has an open strict
all-Continue basin \(N\), the checked basin estimate is

\[
cA(q)\le\operatorname{Def}(V,q)\qquad(V\in N),
\]

and \(\operatorname{dist}_\infty(V,K)<\rho\) implies \(V\in N\).

The proof is exact. With \(\gamma=\min\{c,\rho\}\):

- inside the \(\rho\)-tube,
  \(\gamma A(q)\le cA(q)\le\operatorname{Def}(V,q)\);
- outside it, \(A(q)\le1\) gives
  \(\gamma A(q)\le\gamma\le\rho\le\operatorname{dist}_\infty(V,K)\).

The total-defect convention is also correct. `Def` is
`quittingRootTotalNashDefect`, so an ordinary \(\eta\)-Nash root on Fin4
has \(\operatorname{Def}(V,q)\le4\eta\). This yields the displayed Fin4
corollary with constant \(4\). For an exact positive-absorption root, being
inside \(N\) would force \(cA(q)\le0\), hence the root lies outside \(N\);
the chosen tube implication then gives distance at least \(\rho\).

No carrier or punishment-floor hypothesis on \(V\) is used in this
two-case argument. Those hypotheses enter only later if one wants to
realize or consume the annotation.

Mathematically, Section 6 is useful global packaging, but it is not an
independent new coercivity mechanism: it is the immediate tube-completion of
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
and the abstract compact strict-basin theorem. Its honest novelty is the
explicit universal distance-to-\(K\) formulation and its interpretation as
an annotation-seam toll. It remains a supplied-row inequality, not a source
producer or terminal consumer.
