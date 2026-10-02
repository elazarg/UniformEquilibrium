# Independent cross-review of the finite cap-threshold packet

Reviewer: CODEX_NOETHER_SUPPORT.
Reviewed packet: [finite cap-threshold theorem](../notes/CODEX_FRECHET_CYCLE__FINITE_CAP_THRESHOLD_DESCENT_PACKET_DRAFT.md).
Initial complete text audited at SHA-256
`00a928ab69635858dcd4d81e4bfa3ed7b1548d8e1bb616d39a4443c706621b3e`.

Verdict: T1, T1q, T2, and T3 pass independent mathematical review, including
complete behavioral caps, the first crossing, arbitrary signed Fin4, and
finite-source renewal. No unresolved mathematical objection was found.
This review requested self-contained boundary data and final packet-format
cleanup before a final-byte check; those changes are not mathematical gaps.
No Lean compiler or theorem-level axiom audit was run.

## Independent derivation

The exact response cap after a prefix is max(Q_i,H_i+β_iB_i), because a
complete deviator can Continue then use any old replacement law. This
holds for β_i=0 and for an unattained old supremum. The source cap need
not exceed its own singleton; the proof uses B_i>s_i only in the branch
where every initial margin exceeds the positive threshold.

Fix C=max(D,L_i), θ=C/[32(M+C)], z=4Mθ. If D≤C/2 the empty word is
already adequate. If a cap margin is ≤z, the direct auxiliary branch
applies, including when that low cap belongs to the owner. In the
remaining branch all initial caps exceed their singletons by z.

At any required solo row, an outsider with old cap B_j>s_j+4Mθ has
Continue cap at least B_j−2Mθ>s_j+2Mθ, whereas its Quit endpoint is
at most s_j+2Mθ. Thus the same Continue branch is selected on the first
crossing row itself. Multiple simultaneous crossings cause no problem.
The owner cap is fixed because its positive initial margin persists.

The complete debt calculation is exact through that crossing:

    D_m=(1−θ)^mD+[1−(1−θ)^m]L_i≤C.

In particular it does not falsely assert that the owner debt or total debt
decreases from D when L_i>D. The strict preemptor gives a geometric
outsider-cap limit below its singleton, so a finite first hit is forced.
The displayed time bound has a positive logarithm, since 0<ell≤2M.
At the crossing its cap margin lies strictly above 2Mθ and at most 4Mθ.
The recurrence is not continued beyond that index.

At the auxiliary root, h=C/2 and the crossing annotation lies at most
s_j−3C/8. Exact Nash gives a≥3C/(16M+3C). The coefficient D_m−h is
positive in this branch, so substituting that lower bound has the correct
direction. The resulting affine bound is increasing in D_m and may be
evaluated at C, giving the claimed decrement 3C²/(32M+6C).

For the rational root, k(C)/(4n)<3C/32 because n≥2. The absorption
floor halves and total root regret is at most k(C)/4, leaving k(C)/4
of the original decrease. The row count and tolerance are consistent.
The grid argument is constructive for finite rational sources. It does
not purport to compute an arbitrary infinite source's cap supremum.

## Minimum limit and signed extension

At a global positive minimum d the ordinary cap margin is at least d.
Choose positive θ→0 and stop each finite block at its first crossing.
The exact whole-debt formula bounds each resulting carrier point between
d and L_i. Compactness and finitely many crossing players yield a limit Y
with B_j(Y)=s_j and d≤D(Y)≤L_i. All objects remain in the same closure
of actual payoff/cap pairs. Actual realization of Y is never inferred.

At B(Y)−d/2 a forced auxiliary coordinate gives a≥d/(4M+d). Global
minimality and the complete ledger give

    d≤[4M/(4M+d)]D(Y)+[d/(4M+d)]d/2,

so D(Y)≥d+d²/(8M). This proves the owner cap and payoff collars, not
the nonexistence of a positive minimum. A nonnegative-singleton owner
without a preemptor has an explicit stationary solo approximate-equilibrium
alternative, so every such owner meets the collar's preemptor hypothesis.

I inspected the actual declaration
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
and `SingletonColumnBlockerCertificate`
(`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`).
Under exactly four players and no uniform payoff, it supplies for every
owner an off-diagonal singleton preemptor with a common positive gap;
there is no singleton-sign premise. Therefore the signed Fin4 extension
has the required adapter. It does not follow merely from the elementary
nonnegative-owner solo alternative, and the packet keeps these proofs separate.

## Actual renewal and horizons

Under all-singleton nonnegativity, the seed has U=0, B=s, D₀=Σ_i s_i.
The weak payoff witness at every finite iterate gives L_i≤d_i≤D. Each
new literal finite source therefore re-enters T1q with C=D. Reciprocal
iteration proves the phase bound. Multiplying by the uniform row bound
over ε<D≤D₀ gives T3. This is genuine production on the stated class,
not a verifier or a proof that the class contains every table.

The no-preemptor finite branch chooses its approximation tolerance at
ε/n, explicitly controlling total debt rather than just the largest
coordinate. The finite cap computation scans every displayed date, a
post-cutoff finite date, and Never. Late positive singleton rewards
cannot gain from horizon truncation, so the uniform deviation estimate
is valid and selects one fixed payoff before the requested accuracy.

## Independent falsification tests

Here are two small complete examples I calculated independently of the
packet author's examples.

First take three players with s=(−1,0,0). At each nonempty coalition use
the own singleton for participants and −1 for outsiders, except
r({1,2})=(1,1,1) and r({0,1,2})=(2,−1,−1). This is a complete M=2
table. The pure {1,2} source has U=(1,1,1), B=(2,1,1), D=1, and
owner-0 margin L₀=3. Owner 0 is preempted by player 1. The theorem uses
C=3, θ=3/160, threshold z=3/20. Its first crossing is exactly m=30,
as direct rational recursion verifies. Up to that crossing,

    B_j(m)=−1+2(157/160)^m  (j=1,2),
    D_m=3−2(157/160)^m>1  (m>0).

The crossing cap lies in (3/40,3/20]. This refutes replacing C by D
without the extra L_i≤D premise. The stated theorem passes.

Second take two players with
r({0})=(1,1), r({1})=(−1,1), r({0,1})=(−1,−1), M=1.
The pure joint-quit source has U=(−1,−1), B=(−1,1), D=2. Owner 1
is preempted by player 0, but the outsider's cap is below its singleton:
B₀=−1<s₀=1. Thus unconditional singleton-cap lower bounds are false.
The initial low-cap branch correctly skips the solo block; the auxiliary
root q=(1,0) at B−1 has new U=B=(1,1) and debt zero.

These are exact ordinary calculations; the three-player first-hit values
were additionally checked with Python `Fraction` arithmetic in memory.
They neither construct nor assume a game with positive minimum debt.

## Source and overlap audit

I also inspected the relevant actual-pair, auxiliary-budget, and uniform
consumer declarations in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
and `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The qualitative four-player strict-minimum theorem in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`
was read as well. These establish the exact source meaning and explain why
the packet claims quantitative finite production and a collar, not a new
qualitative solution of general Fin4.

The companion [payoff-exclusion selector packet](../notes/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md)
contains the strict-deficit exact every-suffix result and a different weak
selector with signed outsiders in a witnessing-subset formulation and no
inverse preemptor-gap constant. The cap-threshold packet improves the
all-nonnegative fixed-table date bound and supplies arbitrary-source finite
blocks plus the stronger minimum collar. Neither packet should duplicate
the weaker Φ/Λ margin result as a third export.

Final-byte verification will be appended after the author's requested
self-contained example and formatting revisions.

## Final-byte acceptance

Accepted final mathematical packet:
[FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md](../notes/FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md),
SHA-256 `3b579e7796de1c8302c0c77766c2da0c6e0e00c3cfdf32745c45549c3f7321ec`.

I compared the complete final text against the initially reviewed draft.
The mathematical statements and proofs of T1, T1q, T2, and T3 are unchanged.
The final packet includes complete data for its positive regression and the
two independently derived negative tests above, resolves its review links,
credits supplied sources without indispensable GPT-file links, and removes
the provisional lifecycle and next-check text. The ε/n total-debt scaling
remains explicit.

The new source-comparison paragraph was separately checked against the exact
statements of `eventually_capResponseSegment_debtSum_ge_min_add`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentCollar.lean`) and
`eventually_capResponseSegment_exactRoot_debtDrop_and_absorption`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentExactRootExpenditure.lean`).
The first assumes a supplied family whose owner's cap converges to its
singleton; the second additionally assumes cap-attaining responses and a
positive owner-debt floor. Their stated supplied-data conclusions do not
duplicate the packet's arbitrary-source first-hit producer. This inspection
was static and does not assert a new Lean build result.

There is no remaining mathematical, source-correspondence, probability-mode,
or packet-scope objection to these exact final bytes.
