# Independent complete intake of R

Reviewer: `CODEX_FRECHET_CYCLE`.

Status: mathematical PASS, with substantial existing-source overlap and
precisely limited unsuperseded refinements. No universal reverse-S.3 proof,
arbitrary Fin4 source producer, or positive-gap table is supplied. The
submission corrects its own initial novelty claim and later corrects its
assessment of the four-player implication; those corrections are valid.

## 1. Exact input and independent reading

I read ALL 1333 lines of `gpt/R.md` before sending any mathematical
assessment. Frozen input SHA-256:

    bc35abd855ba89f228c50079d08524d44b8964d8e893257e71062c7c6fe66593

The file contains three distinct responses: a padding/hardness construction,
its explicit source-overlap correction, and a quantitative source repair
with a final four-player correction. I did not read another review of R.
No source or other author's file was edited. The current production
declarations below were inspected under their imports, not freshly compiled.

## 2. Verdict by distinct claim

| Claim | Verdict and exact status |
| --- | --- |
| Universal reverse S.3 is equivalent to general finite quitting approximate existence, even on stationary exact every-restart sources | Valid; already in production, with the one-added-player shift |
| Pointwise unrestricted projection and MAX-gap retraction | Valid; already in production with the sharper actual reward-width factor |
| New dummy-priority collision table and fully mixed vanishing-error sources | Valid ordinary variant; narrower source restriction, not new main hardness equivalence |
| Positive finite-history reach using a fixed geometric dummy clock | Valid elementary modification of the existing padding, not substantive new hardness |
| Exact preservation of global SUM-debt infimum for sufficiently large penalty | Valid direct consequence of the same pointwise coupling; no named SUM equality found in the inspected padding sources |
| Source-preserving repair with one survival-weighted abnormality term | Valid quantitative refinement, preserved separately below |
| Square-root lower bound under O(ε) source-payoff preservation | Valid exact two-player fixture; does not obstruct unconstrained equilibrium selection |
| Four-player reverse-S.3 implication | Valid composition of existing same-table normal-residual and normal-source compilers; not unconditional Fin4 equilibrium existence |

No mathematical counterexample to a final qualified claim was found. The
first response's presentation of the main equivalence as new progress is
superseded by the second response; the latter correctly identifies its
existing home. The final response does NOT resolve universal R.

## 3. Current existing homes for the main reduction

The narrow route was the passive-padding and normal-source rows of
`docs/TOOLKIT.md` and the literal reverse-S.3 discussion in `docs/FRONTIER.md`.
The production file
`UniformEquilibrium/Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`
contains:

- `QuittingPayoffTable.HasStationaryExactEveryRestartRowPerfectSource`;
- `QuittingPayoffTable.oneDummyPadding_has_stationaryExactEveryRestartSource`;
- `QuittingPayoffTable.ReverseSequentiallyPerfectAbsorbing`;
- `QuittingPayoffTable.oneDummyPadding_project_exploitability_le`;
- `stationaryExactEveryRestartSource_sum_punit_implies_approximateEquilibriumExistence`;
- `reverseSequentiallyPerfectAbsorbing_sum_punit_implies_approximateEquilibriumExistence`;
- `universalStationaryExactEveryRestartSource_iff_approximateExistence`;
- `universalReverseSequentiallyPerfectAbsorbing_iff_universalApproximateEquilibriumExistence`.

I inspected the actual definitions and reduction proofs, including the
empty-player case. The statement ranges over arbitrary Never payoffs and
complete behavioral replacements. Its hard direction adds PUnit, so a
five-player reverse implication already contains arbitrary four-player
existence; there is no same-cardinality equivalence.

`QuittingPayoffTable.oneDummyPadding_project_exploitability_le` gives
E_old≤(1+W/K)E_padded, where W is the normalized reward width including
Never. Thus W≤2M in the first response's range-bound setting. The exact
global MAX-infimum comparisons are
`retractionFactor_mul_quittingTerminalExploitabilityInf_le_padding` and
`quittingTerminalExploitabilityInf_padding_le` in
`Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`.
The file uses infima and quiet lifts, not minimizing-profile attainment.

The paper-facing wrapper
`universal_stationaryExactEveryRestartSource_iff_terminalApproximateExistence`
is in `Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`; its proof
delegates to that production theorem. In the same file,
`hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table` proves that the
small-error-threshold wording is not a different source predicate.

The earlier ordinary conference home is
`formalized/AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS.md`.
The main reduction should be referenced at its production home rather than
republished from R as a new theorem.

## 4. Padding variants: exact remaining content and qualifications

For the first response's variant, every coalition containing the new player
dagger pays (M·1,−K), every original-only coalition pays (r(S),0), and
Never is (z,0). This DIFFERS from production padding: an old quitter has
priority there, so collisions containing an old player retain the old
coalition reward and pay the dummy zero. Only dummy-only absorption pays
the upper endpoint and −K. The literal production cases were checked in
the `oneDummyPadding_terminal_*` declarations.

For arbitrary actual profiles in the new variant, let α be the probability
dagger belongs to the absorbing coalition. Its cap is exactly zero, and
its debt is Kα. Coupling old stopping laws gives

    0≤U_i(padded)−U_i(projected)≤2Mα,
    B_i(projected)≤B_i(padded).

The second inequality uses a FRESH coupling under each old-player deviation:
the exceptional event can change, but replacing its payoff by M can never
hurt that deviator. No false uniform bound on the deviated exceptional
probability is assumed. Therefore

    d_i(projected)≤d_i(padded)+(2M/K)d_dagger,
    E(projected)≤(1+2M/K)E(padded).

This includes collisions, original Never, arbitrarily late deviations and
all nonstationary laws. The quiet lift preserves all original debts and
gives dagger zero debt. Thus both displayed MAX-infimum inequalities are
valid without any attained supremum or infimum.

A fixed root with dagger hazard 1/2 and all old players Continue has every
tail payoff (M·1,−K), exact row perfection, and survival 2^(−t). It is
not full Nash: dagger's Never response gains K. Positive live reach is also
obtained in production padding simply by replacing its sure dummy root by
any hazard h∈(0,1). There old-player Quit pays its own singleton even in a
collision, which is at most the production upper endpoint; Continue pays
that endpoint. Hence this property is not a new hardness mechanism.

The fully mixed variant is the one additional source restriction worth
retaining. For n old players, set q_dagger=1−t, q_i=t, 0<t<1/2, and
b=(1−t)^n. Then

    joint Continue = t b <1/2,
    U_dagger=−K(1−t)/(1−t b),
    C_dagger−Q_dagger=K(1−b)/(1−t b)≤2Knt,
    Q_i,C_i∈[M−2Mt,M] for every old i.

Thus every supported endpoint lies within
ε_t=2t max(M,Kn) of its prescribed root payoff. All coordinates have
positive Quit and Continue probabilities; every finite live history has
positive reach; joint termination is uniformly geometric across this
family. Deleting any one player still leaves a geometrically terminating
opponent clock for each FIXED t. The deleted clock for dagger is NOT
uniformly contracting as t→0: its Continue factor b tends to one.
Its full debt tends to K nonetheless. This shows that adding qualitative
termination under every unilateral deviation does not turn the supplied
row-perfect sources into approximate equilibria.

This fully mixed proof cannot be transferred unchanged to the production
collision rule: its old-player Quit limit is the own singleton, while
Continue approaches the upper endpoint. The source-property variant is
valid ordinary mathematics but not a different resolution of universal R.
The preceding formulas preserve its complete useful content for retirement
of the original packet; no separate export is proposed.

For SUM debt, summing the playerwise inequality gives exact infimum equality
when K≥2Mn. The same argument works for production padding with the sharper
K≥Σ_i w_i, where w_i is the old coordinate's full range width including
Never. Here the exceptional event is dummy-only absorption, and

    d_i(old)≤d_i(padded)+w_i α,
    d_dagger=Kα.

Therefore D(old)≤D(padded) under that penalty bound, while quiet lifts
give the reverse infimum inequality. This is a rigorous direct corollary
of the existing coupling, not a new conjecture reduction. No named SUM
equality was found by the narrow search in the padding/nearby existence
subtrees, so it is retained here as ordinary mathematics rather than called
already formalized.

## 5. Quantitative repair: independent proof audit

The entire useful refinement, with a complete reconstruction, is preserved
in `notes/CODEX_FRECHET_CYCLE__R_SURVIVAL_WEIGHTED_SOURCE_REPAIR.md`, SHA
`3bbe490b56cbe7985fc20c224a06ab77858ec178d489713ff9637efeb8df9153`.

The proof passes the following independent checks:

- Translating terminal AND Never payoffs preserves debts, row perfection,
  P−s, and source-payoff differences. Actual restarted tails are bounded,
  including those at zero prescribed reach.
- Initial absorption on finitely many independent clocks forces some
  individual survival to zero. The first positive crossing K therefore
  exists. The logarithmic sum excludes its last row, correctly handling a
  sure Quit and K=1 without taking log zero.
- The exact ledger increment is b_i(t)(C_t^i−γ_t^i). Row perfection gives
  both the ε bound and the 2εq_t^i bound used before the crossing.
- If the exceptional value is below min(P_i,s_i)−h, the Quit upper
  inequality forces opponent absorption greater than
  (h−ε)/(2M). Thus the scan terminates, and its WEIGHTED error is at most
  εβ/c, not its duration times ε.
- One approximate punishment infimum is sufficient. Its opponents are
  independently selected and fixed, with full cap≤P_i+ε. No shared
  random tail and no exact punishment attainment is used.
- Responses before the cutoff, exactly at it, arbitrarily later, and Never
  are all bounded. Each nonexceptional deviator is screened by the crossed
  player's own survival, regardless of what happens during the scan.
- Replacing the prescribed tail changes payoffs by at most
  2M times JOINT prefix reach≤ε. The scan estimate then yields exactly
  the constants printed in (8) and (9).

The surviving error is β(P_i−s_i)₊. Under a positive global full-regret
floor g it yields the stated lower bound on that product. Independence
also validates the source singleton-atom bound: the relevant event is that
i quits at a date strictly below K while all opponents survive TO K.
The phrase “through K” should be read with the displayed products over
dates k<K, not as an extra date. This is only an indexing clarification.

The two-player lower-bound fixture is exact. For singleton rewards zero,
joint reward (−1,0), Never zero and root (1/2,h),

    U₁=−h/(1+h),   ε_h=h²/(1+h),   B₁=0.

For every actual profile, not just stationary ones, d₁=−U₁ because Never
guarantees zero and every reward is nonpositive. Any ε_h-payoff-preserving
repair therefore has debt at least h(1−h)/(1+h), whose ratio to √ε_h
tends to one. The conclusion extends to any fixed O(ε_h) payoff tolerance.
This is not a lower bound on unrestricted equilibrium production: all
Continue is exact Nash on the same table.

## 6. Novelty is the combined refinement, not square-root existence alone

The current generic normal compiler is already in
`Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
I inspected `opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`,
`quittingLedger_add_le_of_supportApproxNash`,
`exists_normalSupportDelayedSwitch`,
`exists_isεAsymptoticNash_of_normalSupportDelayedSwitch`, and the terminal
and uniform wrappers. Its extra scan rows are charged by their count.

The prior checked
`exists_isεAsymptoticNash_of_completelyAbsorbing_supportRationalPath` in
`Quitting/Paths/SupportWitnessPathCompiler.lean` ALREADY gives
2δ+r+√δ(2+7·quittingRewardBound), under all-date rationality error r.
Furthermore the reviewed ordinary HILBERT floor-amplification lemma in
`CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md`
supplies O(√ε) source floors under normality. Thus a general square-root
terminal error in the normal case is not by itself new here.

The precise package not found in the narrow existing-source search is:
ε source-payoff preservation, O(ε log(1/ε)) nonexceptional debts, one
survival-weighted abnormality term, and the corresponding constrained
repair lower bound. It is worth a second review if it is to be promoted;
this intake does not self-export it or reopen the abnormal-player problem.

## 7. Four-player correction and the paper claim

The final correction is valid. On the SAME zero-Never Fin4 table,
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
constructs a residual containing `all_punishmentNormal`. Then
`FinFourQuantitativeFullSupportHardResidual.exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing`
in `Diagnostics/Quitting/Collision/SingletonPacket/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
consumes the supplied S.3 source. Thus S.3 and no UE cannot coexist in
four players. Arbitrary Never payoffs are handled by coordinate translation.
This proves four-player R, but it does not produce S.3 for arbitrary
four-player data and does not prove the full Fin4 conjecture.

The publisher's current displayed Theorem 3.4 includes reverse S.3;
Theorem 3.5 asserts supplied-profile approximate optimality from absorbing
row perfection. I checked these displayed statements directly in
[Absorption paths and equilibria in quitting games](https://link.springer.com/article/10.1007/s10107-022-01807-6).
Their project-semantic status is not inferred from the paper assertion:
`sequentialPerfectionErrorExponentClaim_is_false` in the literature owner
records the checked supplied-profile refutation. The separate corrected
`terminatingTails_and_rowPerfection_imply_subgameEquilibrium_or_stationaryEquilibrium`
requires `QuittingUnitSoloExit` and zero Never. The padded negative
singleton −K violates that hypothesis, exactly as R's correction says.
Failure of printed Theorem 3.5 is not by itself a refutation of universal R.

## 8. Preservation/retirement handoff

The original R bytes were not moved, deleted, or edited. For coordinator-led
recoverable retirement, all useful material now has a home:

- Main hardness, quantitative MAX retraction, threshold equivalence and
  Fin4 reverse implication: existing production declarations above.
- Geometric/full-mixing source qualifications and the SUM-infimum
  corollary: exact formulas and distinctions retained in Section 4 here.
- The substantive source-payoff-preserving refinement and lower bound:
  the complete owned preservation note cited in Section 5.

Nothing in the review asserts a new universal source producer, removal of
the abnormality term, a positive-gap example, or a new proof of the full
finite-quitting conjecture. No additional research was started from R.
