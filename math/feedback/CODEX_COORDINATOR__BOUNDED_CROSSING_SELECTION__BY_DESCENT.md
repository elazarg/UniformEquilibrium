# Independent review: head-and-tail descent in the actual carrier

Reviewer: DESCENT_REVIEW. Ordinary mathematics; no Lean build or certification.
Verdict: PASS. No unresolved mathematical objection within the scope below.

Reviewed canonical note:
`math/notes/CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md`
SHA256 `91274701c34f963f59251cd4a163f8d4691fcefb8db675b0ee50861ab9cab4a4`.
Scope: the entire new Section11, its introductory status statement, and the
closing verification/scope statement. This is not a new review of Sections1–10
or Section12's separate global-comparison proofs.

Reviewed and executed checker:
`math/experiments/CODEX_COORDINATOR__ACTUAL_CONTINUATION_GEOMETRY_CHECK.py`
SHA256 `9ab5a6f028381b7fba703f5cd93b292ce95428a4c7f2bd16dec12b24c6d97cfe`.
Command: `python math/experiments/CODEX_COORDINATOR__ACTUAL_CONTINUATION_GEOMETRY_CHECK.py`.
All four reported groups passed. The new fourth group uses exact symbolic
arithmetic, not numerical root search.

## Claim and actual-source scope

The claim starts with a zero-debt tail W in the closure C of actual independent
annotations, w>=0, positive original Never masses, and a proper regular Nash
head q whose output has a strictly negative payoff, or a zero payoff whose
constructed derivative is strictly negative. An eligible zero-payoff owner j
gives an explicit tail insertion. Invertibility of the active head
Jacobian and inward derivatives at every tied quiet comparison allow the
head to be adjusted. The finite test L_j>0 then yields a marked zero-debt
point in the SAME C with strictly smaller ORIGINAL Never product.

This is a source-consuming implication for supplied heads and tails. It does
not produce those hypotheses from an arbitrary counterexample, assert an
exact actual realization of a closure tail, or prove a uniform equilibrium.
For a nonrealized W, finite prefixes act on its actual approximants and the
claimed exact competitor is their annotation limit in C.

## Independent proof checks

For a solo-j inserted period, owner j is indifferent because its own singleton
and w_j are both zero. Each other gap is exactly

    t[Z_k({k,j})-Gamma_kj]-(1-t)w_k.

Eligibility covers every other zero w_k. The finitely many positive w_k
remain strict for sufficiently small t. This proves full Nash status of the
new tail using the complete prefix max identity. The nonnegative w guard is
essential: at t=0 the inserted empty period adds an immediate zero Quit
response. The text explicitly retains this response. Later w(t) may become
negative without invalidating the proved gap comparisons.

For each active head owner the gap is polynomial in q and affine in its own
continuation value. The implicit function theorem gives the claimed C1 curve
and differentiation yields J b=diag(H)a with the displayed sign. Active
hazards remain proper. Initially strict quiet comparisons persist; a tied
quiet gap with strictly negative propagated derivative becomes favorable to
Continue for all sufficiently small positive t. A zero derivative is not
silently accepted. The argument remains valid if inserted owner j is active
in the retained head: its two independent hazard factors occur at different
dates and both are counted in its marginal Never mass.

A zero-debt tail followed by a Nash root has full cap equal to prescribed
payoff because the complete cap is max(Q_i,P_i+H_i B_i). All later finite
deadlines and Never are therefore controlled. The finite max formula is
continuous on actual annotations, proving prefix preservation of C.
The relevant semantic declarations were inspected in place:
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).
No assertion of a newly checked Lean theorem is made.

The exact Never product is h(q(t))(1-t)nu(W). Its logarithmic derivative
is -L_j. Strict negativity of an original payoff retains the mark by
continuity. The new zero-mark extension also passes: writing v=F(q,w),
the chain rule gives v'_a=D_q F_a(q,w)b+h(q)a_a. If v_a=0 and this derivative
is strictly negative, then v_a(t)<0 for every sufficiently small positive t.
A zero derivative is correctly left unresolved. Original marginal Never
coordinates remain positive. Thus the
strict decrease genuinely contradicts global marked least-Never selection,
not merely a different fixed-calendar or local minimum problem.

The finite-word version is valid by backward composition. At each head the
already constructed tail derivative enters through h(q^k)a^(k+1), while
the adjusted hazard contribution is D_qF b^k. All tied quiet derivatives
are checked at their own head. Finiteness lets all local intervals be
intersected. The log Never derivatives add exactly. In the zero-mark variant, a^1 is
precisely the full entrance payoff derivative, so a^1_a<0 at w^1_a=0 is the
correct one-sided mark condition. No corresponding uniform inverse bound or
infinite-word IFT is asserted.

## Concrete verification and remaining sign obstruction

The new retained checker reconstructs the entire native reward table,
computes the old all-active tail from literal Quit/Continue offers, and
then computes the inserted period and revised head from those actual
continuation values. The last tail has U=B=e=(0,1,1,1), with every Never
mass1/2. The head has payoff (2/9,-5/9,-5/9,-5/9), active Jacobian with
zero diagonal and unit off-diagonal, and Never product1/54.

For 0<=t<4/11, the inserted quiet gaps are (11/4)t-1<=0; the head quiet0
gap is strictly negative because z<1/2; and all active head comparisons
are equalities. Thus the backward checks certify the COMPLETE finite-clock
and Never menu, not a selected-support substitute. They give

    nu(t)=32(1-t)/(12+9t)^3,
    (log nu)'(0)=-13/4.

The retained checker explicitly verifies the existing pure123 absorbing
equilibrium, so the text correctly assigns no new reward-table coverage to
the example.

The slope test remains an additional condition: the proof does not derive
L_j>0 from active-Jacobian regularity or quiet-comparison strictness.

The introduction and final scope correctly state that eligibility, regularity,
quiet-tie signs, the descent sign, and the existence of a qualifying finite
head are not universally supplied. Singular heads, failed signs, infinite
heads, and zero marked outputs failing the new payoff-derivative test remain.
Fin4 is not claimed solved.

## Frontier claim check

Reviewed the corresponding actual-domain Section11 summary in
`math/notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`, SHA256
`0ddce6148a61e7d984c36ff599c4c860ab0f5713f105b4c9a4d31338ba7e4d31`.
It accurately states the eligible insertion, head adjustment, inward quiet
ties, finite-word extension, and all-four-active-tail control. It explicitly
retains the extra eligibility, regularity and sign hypotheses and claims no
entire source case or new raw reward class closed. The following Section12
paragraph identifies positive absorbing debt and separate generic dispersion
assumptions, and correctly refers to a boundary POINT minimizing its exact
payoff fibre, rather than minimization on an entire zero-payoff face.
This frontier check does not replace the separate proof review of Section12.
The final canonical revision was re-read, including the zero-mark extension
reviewed above. The checked program is unchanged; the introduction and closing
scope retain the same limits.
