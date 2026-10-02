# Review of Section 62

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The compactness argument, closed-root limit, two uses of minimum
debt rigidity, and vanishing-absorption conclusion are correct under the
stated two-distinct-debtor hypothesis.

If absorption does not tend to zero, a subsequence has absorption bounded
below by a fixed `c>0`.  The finite product of Boolean mixed-action simplices
is compact, so a further subsequence converges to a product root `q_*`.
Semantic source convergence gives `U_r->U_*`, and the assumed
`||V_r-U_r||_infinity->0` gives `V_r->U_*`.  Exact endpoint-Nash conditions
are finitely many closed support/endpoint inequalities, hence pass to the
limit: `q_*` is exact at `U_*`.  Absorption is a continuous polynomial in the
root probabilities, so its limit remains at least `c`.

The named rigidity theorem applies exactly here.  Its tail argument is the
prescribed part `pair.1=U_*`; it also uses carrier membership and global
minimum total debt of the full pair `base`, both supplied in the statement.
Applying it to positive debtor `a` forces every player other than `a`, in
particular `b`, to Continue purely.  Applying it to distinct positive debtor
`b` forces every player other than `b`, including `a`, to Continue purely.
Together the two conclusions make every player pure Continue, contradicting
the positive limiting absorption.

Thus every exact-root family at floor tails asymptotic to the actual source
payoff has vanishing one-row absorption.  The scope statement is exact: the
argument needs two distinct positive debt coordinates.  It does not treat a
unique positive-debt owner, exact roots at nonlocal tails, or a multi-edge
path whose charged edge leaves the local source neighborhood and later
returns.

## Addendum: proposed paid-source provenance corollary

**REJECTED as stated.**  The declaration
`potentialCoDecrease_minimumFiberDeflation_or_paidFirstDisagreement` does
select `mover` and a distinct
`other in frontier.positiveDebtSupport.erase mover`, so the original minimum
pair `frontier.base` has two positive debtors.  But its paid rows are based at

```text
frontier.fullReplacementProfile mover (endpoint.subseq rank),
```

whose semantic pairs converge to the strictly off-minimum
`endpoint.cluster`, not to `frontier.base`.  Proposition 62 requires the
actual profile semantics to converge to the minimizing pair to which debtor
rigidity is applied.  The two support witnesses at the original base therefore
do not make Proposition 62 applicable to the paid-row source subsequence; the
endpoint cluster may have a different positive-debt support and is not a
minimum pair.

It is true that the broader
`HasQuittingStoppingLawFiniteSupportRankAlternative` paid arm forgets the
companion `other`.  That interface distinction does not repair the preceding
source mismatch.  A valid corollary may exclude fixed-charge roots at tails
near the **original tangent source payoff** using its two debtors, but it may
not call this a no-go at the off-minimum paid-row source without a new theorem
transporting minimum rigidity to that cluster.
