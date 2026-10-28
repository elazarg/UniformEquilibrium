# Independent review of the inherited self-repetition test

Reviewer: I2_CONTACT_DYNAMICS. I did not author this result. Ordinary
mathematical review; no Lean change or build.

Reviewed artifact: Section12 of
math/notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md, beginning with
"## 12. Complete self-repetition test for three zero observer caps" and
ending immediately before "## Verification and next obligations".
Exact section SHA256: 047bce920402a654a0de8c750512ea0821feff66464eb2552b9a4165588f3353.

Verdict: PASS for the complete stated necessary-condition and all-repetition
characterization. No unresolved objection. The result does not eliminate
the endpoint pattern or supply an arbitrary-table equilibrium producer.

## The head and graft semantics

I checked the retained-query graft identity in
CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION,
Section2, and the actual-head formula in the zero-observer boundary note.
It retains the old cap through a maximum and multiplies each original Never
coordinate. The candidate uses that operation, rather than treating an
abstract continuation as executable after infinitely many dates.

All observer tail payoffs and caps remain exactly zero under every self-graft.
Consequently every replacement leaves the head's three complete observer
comparisons unchanged and stays in the constrained carrier. For k>=1 the
new positive pivot tail cap is at least b. Since the original Y is ALL-END,
e_p(P)+h_P b>=B_p(P); therefore its continuation-through-tail cap branch
really does remain maximal. At k=0 that argument is unavailable, and the
candidate correctly retains the old maximum through g.

Writing h_P=s lambda, I recomputed

 [J_r(Phi_P(Q^k))-J_r(Y)]/s
   =lambda b sum_(j=1)^(k-1) h^j
      -u sum_(j=1)^(k-1) v^j+r(v^k-v)
   =sum_(j=1)^(k-1)[lambda b h^j-A v^j].

Thus k=2 is exactly A<=lambda b/n. Conversely, for every j>=1,
h^j/v^j=n^(-j)>=1/n, so this single test makes each summand nonnegative.
The removal comparison k=0 is exactly A>=lambda b-g/s. Since h,v<1,
the convergent sums and compact retained-query limits also cover k=infinity.
The separate absorbing comparison of Q^infinity to m is correctly retained.

## Strictness and compact selection

The coupling bound |U_p-e_p|<=2M(1-N_p) holds on actual profiles and
passes to the augmented carrier by continuity. If n=1, u=b and h=v<1;
self-repetition then has an absorbing limit with zero pivot and observer
debts, contradicting m>0. Hence 0<n<1 and 0<v<h<1.

The global minimizing fibre is nonempty and compact. Its objective value
is at most r<m, so every point in it has positive joint Never mass: a
zero-Never point would have objective at least m. The continuous pivot
Never coordinate therefore attains its least value on that fibre. If the
upper test were equality at this chosen minimum, k=2 would retain objective
mu while multiplying its pivot Never mass by n<1, a contradiction.
This selection does not assert that an arbitrary chosen minimum has least
pivot Never mass; the candidate states the selection premise explicitly.

## Arithmetic strictness control and scope

Exact rational calculation gives

 b/(1-h)-u/(1-v)=27/38>3/5,
 A=49/200>9/50=lambda b,
 N_p(Y)=3/4<4/5=1/(1+rS),
 A=49/200>1/5=lambda b/n.

The previous removal, absorbing-ratio and inverse-axis scalar inequalities
therefore do not imply the new upper test. The example is explicitly an
arithmetic separation, not an actual game, endpoint or positive-gap source.

The inspected finite splice declarations are
quittingTerminalSemanticPair_rootThenContinuation in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean and
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. The new comparison
uses already established retained-query closure mathematics; this review
confers no new Lean or consumer seal.

## Final canonical-section check

I reread the complete canonical section and verified that its exact bytes
match the stated section of the living residual partition. Comparison with
the previously reviewed candidate shows only heading/status, source-link,
and remaining-obligation edits; the mathematical hypotheses, formulas,
proof, strictness selection, and arithmetic control are unchanged.
The final verdict applies to this exact canonical section.
