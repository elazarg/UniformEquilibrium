# Review: debt-to-actual-reach selection (Theorem 11.1, Proposition 11.2)

Reviewer: CLAUDE_FABLE
Date: 2026-08-31
Scope: Sections 10-11 of
`../notes/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT.md`, per
item 1 of the resumption order in
`../notes/CODEX_ROOT__FIN4_TWO_CHAMBER_PAUSE_STATUS.md`.

## Claim checked

Theorem 11.1: a player with debt at least \(\Delta>0\) at any behavioral
profile admits a paid first-disagreement row with gain \(\Delta/4\),
prescribed own survival at least \(\Delta/(4M)\) through the row start,
opponents-only live mass at least \(\Delta/(8M)\), hence actual joint reach
at least \(\Delta^2/(32M^2)\). Proposition 11.2: the same selection yields
one executable stopping-law replacement with gain above \(\Delta^2/(16M)\)
and a literal common prefix strictly before the cut.

## Verdict: correct

I re-derived every step independently before reading the note's proof; the
derivations agree.

1. The bad-set mass bound: from \(0\le C-f\le2M\) and
   \(\mathbb E_\nu[C-f]\ge\Delta\), splitting at \(\Delta/2\) gives
   \(\nu(A)\ge\Delta/(4M)\). Valid; also proves \(M>0\).
2. The case split for the source witness is exhaustive and the subtle case
   works: if all supported bad mass is at Never, then
   \(f(\infty)\le C-\Delta/2\) forces every near-cap receiver \(r\) with
   \(f(r)>C-\Delta/4\) to be finite, so the cut \(t=\min(s,r)\) is finite in
   every case.
3. Own survival through \(t\): all supported bad choices are at times
   \(\ge s\) or Never, and survival is antitone, so survival through
   \(t\le s\) dominates \(\nu(A)\). Valid in both cases.
4. The opponents-survival floor comes from the row's own division-free
   field (`gain_le_liveMass`), not from a new estimate. Valid.
5. The factorization of joint reach as opponents-weight times own prefix is
   the checked prefix bridge. Valid.
6. Proposition 11.2's transported law is a probability law (the receiver is
   not in the bad set), its payoff is governed by the checked affine
   identity, and the common-prefix claim follows because the two laws agree
   strictly before \(t\) and positive own survival makes the hazard rows
   before \(t\) well defined and equal. Valid.

The limitation statements (not an absorption car; not an exact
Nash-Bellman edge; selection not nested under outward prefixing) are
accurate and important; Corollary 11.4's use with Theorem 4.2 of the
recentering note is correctly scoped.

## Formalization: completed and kernel-checked (scratch lane)

All three stages compile under Lean 4.32.2 via `lake env lean`, with no
`sorry`, no forbidden constructs, and every declaration depending only on
`propext`, `Classical.choice`, `Quot.sound` (verified by an independent
`#print axioms` pass over all six declarations, in addition to the
implementing agents' own audits). Files live in `../fable/lean/`; `math/`
is gitignored and nothing imports them: **not integrated**, no `A` or `C`
seals. Module imports resolve by precompiling to olean and extending
`LEAN_PATH`:

```text
cd /home/elazarg/UniformEquilibrium
mkdir -p math/fable/lean/olean
lake env lean -o math/fable/lean/olean/FableStoppingSelection.olean \
  math/fable/lean/FableStoppingSelection.lean
lake env sh -c 'LEAN_PATH="$LEAN_PATH:math/fable/lean/olean" \
  lean math/fable/lean/FableDebtActualReach.lean'      # likewise ProfitableFork
```

1. `FableStoppingSelection.lean` (287 lines):
   `quittingStoppingLaw_badMass_lowerBound` (division-free
   \(\Delta\le4M\cdot\mathrm{badMass}\));
   `quittingStoppingLaw_exists_leastBad_survival_lowerBound`;
   `quittingStoppingLaw_badMass_le_survival_of_noFiniteBad`.
2. `FableDebtActualReach.lean` (182 lines):
   `positiveDebt_exists_actualReach_paidFirstDisagreementRow` — any player
   with debt \(\ge\Delta>0\) at any behavioral profile has a
   `QuittingPaidFirstDisagreementRow` with gain \(\Delta/4\),
   \(\Delta\le4M\cdot\mathrm{ownSurvival}(\mathrm{row.start})\), and
   \(\Delta\le8M\cdot\mathrm{row.liveMass}\);
   `positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` —
   \(\Delta^2\le32M^2\cdot\mathrm{quittingSurvivalPrefix}(\mathrm{row.start})\):
   Theorem 11.1's actual joint reach, division-free.
3. `FableProfitableFork.lean` (215 lines):
   `positiveDebt_exists_profitableStoppingLawFork` —
   \(\Delta^2\le16M\cdot(\text{payoff of the transported-law
   replacement}-U)\): the payoff-gain half of Proposition 11.2, via
   `PMF.map` transport of the bad mass and the checked affine realization
   identities, the pair-concentration kernel, and Theorem A of the
product-base export.

Scope, kept precise:

- Theorem 11.1's clause 1 (the source witness lies in the positive support
  of the prescribed stopping law) is implicit in the construction but is
  **not** an exported conjunct of the Lean statement; a consumer needing
  it should request a strengthened variant.
- Proposition 11.2's common-prefix clause (literal identity of the
  live-root profiles strictly before the cut) is **not** formalized; only
  the payoff-gain half is.
- Constants are division-free; the note's (29) and (40) follow by
  positivity arithmetic.

Reusable gotcha for this lane: inside `namespace GameTheory`, write
`open _root_.Math.Probability` for `expect` once `UniformEquilibrium.*`
modules are imported; the plain `open` silently resolves to
`GameTheory.Math` and breaks.

Resumption-order item 1 is herewith: reviewed **and** formalized (scratch).
"Treat actual reach as supplied in the full-debt question" is available to
consumers, modulo promotion of these files into a proper lane by an
integration agent.

## Addendum (2026-08-31): the remaining Section-10 statements, kernel-checked

Four further files, same lane and rules. My independent consolidated
`#print axioms` audit covers all 25 public theorems of these four files:
every one depends only on `propext`, `Classical.choice`, `Quot.sound`.

4. `FableUniformEntrance.lean` (120 lines): `prod_one_sub_ge_exp_neg_div`
   and `QuittingTerminalExploitabilityWitness.uniform_prefixSurvival_lowerBound`
   — the note's estimate (19), with the floor hypothesis **dropped** (the
   repo's `quittingPunishmentValue_le_finitePrefixValue` derives it) and the
   value-box hypothesis kept deliberately (the canonical reward bound is a
   sum, so carrier membership does not imply the box for arbitrary `M`).
5. `FableTimeEscapeRegression.lean` (343 lines): the Theorem 7.1 core —
   the all-Continue fixed point (delegated to the pre-existing repo lemma
   `quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap`,
   discovered during implementation), profile-level pair invariance, the
   prefix iterate, **unconditional** outcome-law invariance (two new
   all-Continue simp lemmas), and the pure-time shift
   `quittingPureTimeDeviationPayoff_allContinuePrefix_shift` by direct
   profile congruence.
6. `FableFullDebtGeometry.lean` (180 lines):
   `fullDebtMinimum_eventually_punishmentFloorSafe_of_semanticTendsto` and
   `nearFullDebtMinimum_markedExactOrbit_debtSupport_lowerBound` — the
   note's Section 2 floor safety and Section 5 full-debt persistence (the
   positivity hypothesis in the latter is mathematically redundant; kept
   stylistically).
7. `FableCommonPrefixFork.lean` (437 lines):
   `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` — the FULL
   package: one paid row and one transported law with the gain
   \(\Delta^2\le16M\cdot\text{gain}\), the own-survival and liveMass
   floors, AND the common-prefix clause: the realized strategies agree at
   every history strictly below `row.start`. This supersedes the scope
   caveat above — Proposition 11.2's common-prefix clause is now
   formalized.
8. `FableActualReachSupport.lean` (213 lines):
   `positiveDebt_exists_actualReach_paidRow_withSupport` and
   `positiveDebt_exists_actualJointReach_paidRow_withSupport` — Stage B's
   two theorems with the source-witness support clause exported (a
   supported finite source time with positive stop mass, or a Never
   source with positive Never mass). This discharges the Theorem 11.1
   clause-1 caveat: **no stated caveat of the original ledger remains**.
   Verified 2026-08-31: clean compile through its olean chain, lexical
   scan clean, axioms `propext, Classical.choice, Quot.sound` only.
9. `FableWordAction.lean` (179 lines): `fableRootWordProfile` (finite root
   words acting on behavior profiles), `fableRootWordProfile_semanticPair`
   (the pair of a word-prefixed profile is the word's fold of the checked
   one-row semantic action — the graft calculus of the recentering note,
   at word level), `fableRootWordProfile_outcomeMass` (the same for the
   outcome law, reusing the repo's explicit
   `quittingTerminalOutcomeLawPrefix`), the replicate/all-Continue
   alignment, and the window-deletion pair identity and debt-sum
   comparison under the solo-cap condition. Independently verified
   2026-08-31 (compile retried past a concurrent `.lake` cache rebuild;
   lexical scan clean; the implementing agent's `#print axioms` reports
   the three permitted axioms on all seven declarations).
10. `FablePureTimeContinuity.lean` (453 lines): the analytic groundwork
    for the recentering note's §13 — deleted per-date absorption masses
    with telescoping; `fableNeverCollect` (reusing the repo's live
    ledger); finite-time determination and coordinatewise continuity of
    pure-time deviation values (explicit finite-polynomial route through
    the checked ledger identity
    `quittingRootSequencePureTimeTerminalValue_some_eq`); the Never-tail
    truncation bound; and the quit-value row estimate (the Lean form of
    that note's Lemma 12.3). All four target statements verbatim.
    Independently verified 2026-08-31: clean compile, lexical scan clean;
    agent `#print axioms` reports only the three permitted axioms.
11. `FableBubbleSign.lean` (547 lines, 15 theorems): the recentering
    note's §13, kernel-checked — `fable_bestResponse_usc` (caps cannot
    jump up under pointwise root convergence when the observer's solo
    reward is nonnegative), `fable_payoff_escape_decomposition` (the
    exact escaped-payoff decomposition, with the profile-level
    reward-moment identity discovered to be definitional — no assumed
    hypotheses), `fable_bubble_social_sign` (escaping mass carries
    nonnegative aggregate social value), and `fable_bubble_attainment`
    (for socially nonpositive tables the exploitability infimum is
    attained by the limit profile). The Never-chase constant is
    \(4M\varepsilon\) in place of the note's \(3R\varepsilon\)
    (immaterial; inequalities only). Independently verified 2026-08-31:
    clean compile through olean-h, lexical scan clean; agent
    `#print axioms` reports only the three permitted axioms on all four
    headline declarations.
12. `FableSocialMoatChamber.lean` (205 lines): the social-moat chamber —
    `fable_socialNonpositive_exists_uniformEquilibriumPayoff` (nonneg
    solos + all coalition socials nonpositive, \(n\ge2\) ⇒ a
    uniform-equilibrium payoff exists: a chamber previously closed only
    by attainment is closed by existence) and
    `fable_counterexample_minimum_socialPayoff_lowerBound` (every
    counterexample's debt-minimal carrier pair has aggregate payoff at
    least aggregate solos plus \((n-1)D_*\) — dossier fact R15; per a
    subsequent external review this inequality is essentially the
    checked `TerminalSemanticMinimumAggregateSurplus` certificate at the
    full player set, so the weighted costate family is the genuinely new
    content). Uses
    the checked singleton moat, the debt-inf equivalence, the
    pre-existing carrier-inf bridge
    (`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`,
    found by the agent), and the reward-moment lemma
    (`quittingTerminalRewardMoment_outcomeMass`). Independently verified
    2026-08-31: clean compile, lexical scan clean; agent
    `#print axioms` reports only the three permitted axioms.
13. `FableWeightedSocialMoat.lean` (284 lines): the strictly positive
    costate generalization —
    `fable_positiveCostate_socialNonpositive_exists_uniformEquilibriumPayoff`
    (a strictly positive costate \(\theta\) with
    \(\theta\cdot r(S)\le0\) for every coalition and
    \(\theta\cdot s\ge0\) forces a uniform-equilibrium payoff: the
    polyhedral chamber) and
    `fable_counterexample_weightedMinimum_socialPayoff_lowerBound`
    (the per-costate quantitative bound at weighted minima). The
    genuinely new content per the external review. Independently
    verified: clean compile, lexical scan clean; agent `#print axioms`
    reports only the three permitted axioms.

14. `FableResetDispatchRadius.lean` (86 lines): Assembly B — the
    uniform-radius reset-dispatch boundary
    `fable_fixedLawResetDispatch_uniformRadius` (general \(\iota\)): at
    any positive global carrier minimum there is a table-level
    \(\varepsilon>0\), chosen before any dispatch data, such that every
    `QuittingFixedLawResetDispatch` out of the minimum satisfies
    \(D_*+\varepsilon<D(\text{returned})\) or stalls at the exact
    all-Continue face (`IsεQuittingRootNash` at the returned cap plus
    all-Continue prefix fixity). Composes the checked radius theorem
    (`exists_pos_nearMinimum_capNash_eq_allContinue_radius`), carrier
    membership of the returned point
    (`terminalSemanticLawCarrier_fst_mem_carrier`), `dynamic_exit`, and
    `quittingRootAbsorptionMass_allContinueRoot`. Sharpens
    `allContinue_of_target_debt_le_source` to an open neighbourhood; a
    boundary sharpening, not a chamber consumption. Independently
    verified: clean compile, lexical scan clean, line lengths clean, own
    `#print axioms` run reports only the three permitted axioms.

15. `FableTightCoordinateDichotomy.lean` (143 lines): the tight-coordinate
    dichotomy at a unique-all-Continue cap (general \(\iota\)) —
    `fable_uniqueAllContinueCapNash_tight_exists_tightEagerJoiner`
    (every coordinate whose solo reward equals the cap recruits a
    distinct tight coordinate with strictly positive
    `quittingCollisionMatrix` entry, on pain of a solo stationary exact
    Nash root contradicting uniqueness),
    `fable_uniqueAllContinueCapNash_strict_singletonGap_of_noTightEagerPair`
    (no tight eager pair forces the strict singleton gap at every
    coordinate), and
    `fable_uniqueAllContinueCapNash_exists_uniform_singletonGap_of_noTightEagerPair`
    (the uniform gap \(\delta>0\) feeding
    `eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap`).
    Post-formalization audit: the main theorem and the eager cycle are
    already integrated as
    `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`
    and `exists_quittingSingletonCapBindingCollisionCycle`; the file
    delegates to them via the bridge
    `fable_quittingCollisionMatrix_eq_singletonCollisionGain`, and the
    genuinely new content is the two no-tight-eager-pair corollaries.
    Ordinary-math record:
    `../fable/TIGHT_COORDINATE_DICHOTOMY.md`. Independently verified:
    clean compile, lexical scan clean, line lengths clean, own
    `#print axioms` run on all three theorems reports only the three
    permitted axioms.

16. `FablePremarkAbsorptionFloor.lean` (249 lines): the pre-mark
    absorption floor (general \(\iota\)) —
    `fable_nearTight_coordinate_premark_opponentAbsorption_floor`
    (a coordinate whose whole cap is within \(\sigma\) of its solo
    reward while the post-mark all-Continue spine tail clears the solo
    by \(\gamma>0\) forces the opponents-of-that-coordinate live-word
    continue product below \((2M+\sigma)/(2M+\gamma)\)), the exact
    \(\sigma=0\) corollary
    `fable_tight_coordinate_premark_opponentAbsorption_floor`, the
    one-step Continue-arm floor
    `fable_semanticPrefix_envelope_ge_opponentSurvival`, the live-word
    telescoping `fable_envelope_ge_liveWord_opponentSurvival` (through
    the checked factorization
    `quittingTerminalSemanticPair_spine_eq_prefix`), and the
    definitional mass bridge
    `fable_quittingRootOpponentContinueMass_eq_stationaryFixedOpponents`.
    Ordinary-math record: `../fable/PREMARK_ABSORPTION_FLOOR.md`.
    Independently verified: clean compile, lexical scan clean, line
    lengths clean, own `#print axioms` run on all five public
    declarations reports only the three permitted axioms.

17. `FableLimitTightAbsorptionFloor.lean` (146 lines): the sequential
    limit corollary of entry 16 —
    `fable_limitTight_premark_opponentAbsorption_eventual_floor`
    (general \(\iota\)): along profiles whose cap coordinate tends to
    the solo reward and whose post-mark spine-tail debts tend to the
    global carrier minimum, for every \(\gamma\) below the minimum and
    \(\sigma>0\), eventually the opponents-of-that-coordinate live-word
    continue product is at most \((2M+\sigma)/(2M+\gamma)\).
    Instantiates the near-minimum singleton floor
    (`nearMinimumTerminalSemantic_cap_sub_singleton_ge`) with
    \(q=(\gamma+D_*)/2\), \(\varepsilon=d^2/(2M+d+1)\), \(d=(D_*-\gamma)/2\).
    Imports entry 16 through the scratch olean+LEAN_PATH mechanism.
    Independently verified: dependency olean rebuilt, clean compile,
    lexical scan clean, line lengths clean, own `#print axioms` run
    reports only the three permitted axioms.

18. `FableNeverMassCeiling.lean` (174 lines): the Never-mass side of the
    pre-mark package (general \(\iota\)) —
    `fable_neverMass_le_liveWord_opponentSurvival` (hypothesis-free:
    every profile's Never mass is at most the opponents-of-any-player
    live-word continue product through any date; via
    `quittingLiveMassLimit_le`, the live-mass recursion, and
    `quittingStationaryContinueMass_le_update_pure_false`),
    `fable_nearTight_neverMass_ceiling` (chained with entry 16), and
    `fable_limitTight_neverMass_eventual_ceiling` (chained with entry
    17): under limit tightness and tail-debt convergence, eventually
    Never mass \(\le(2M+\sigma)/(2M+\gamma)\). Imports entries 16–17
    through the scratch olean chain. Independently verified: own olean
    rebuilds, clean compile, lexical scan clean, line lengths clean, own
    `#print axioms` run on all three declarations reports only the
    three permitted axioms.

19. `FableMarkedRowCapDefectFloor.lean` (270 lines): the marked-row
    cap-defect floor (general \(\iota\)) —
    `fable_strictInert_markedRow_capDefect_floor` (a uniform stage-mass
    floor \(\kappa\) at the marks plus tail-cap convergence to a
    unique-all-Continue cap force one \(\mathrm{moat}>0\) with,
    eventually, \(\mathrm{moat}\le\) the marked live root's total Nash
    defect against the tail cap) and
    `fable_strictInert_markedRow_capDefect_floor_of_minimumTailLimit`
    (uniqueness discharged by the table-level radius when the tails
    converge to a carrier pair at the global minimum debt). Composes
    the robust absorption moat, plus the ledger corollary
    `fable_strictInert_wholeDebt_excess_floor` (eventually
    \(\kappa\cdot\mathrm{moat}+\text{liveMass}\cdot D(\tau_n)\le D(\pi_n)\):
    the whole-debt excess above the surviving tail debt is uniformly
    charged at the mark) through the summed directed-transport ledger
    (private helper `fable_debtSum_eq_sum_liveMass_totalDefect_add_tail`
    over `debt_zero_eq_sum_reached_defect_add_tail`). Also composes
    (`exists_eventually_absorptionNashDefect_moat_of_unique_allContinue`),
    the stage-mass factorization, and
    `quittingRootCoalitionMass_le_absorptionMass_of_nonempty`.
    Ordinary-math record: `../fable/MARKED_ROW_CAP_DEFECT_FLOOR.md`.
    Independently verified: clean compile, lexical scan clean, line
    lengths clean, own `#print axioms` run on both theorems reports
    only the three permitted axioms.

20. `FableMarkedDateMultiplicity.lean` (292 lines): the marked-date
    multiplicity bound (general \(\iota\)) —
    `fable_markedDate_multiplicity_bound` (at a unique-all-Continue cap
    there are \(\mathrm{moat}>0\) and one neighborhood \(U\) such that
    for EVERY profile and every finite set \(F\) of dates carrying
    stage mass \(\ge\kappa\) at a fixed terminal with post-date spine
    tail caps in \(U\): \(|F|\cdot\kappa\cdot\mathrm{moat}\le
    D(\text{profile})\)) and
    `fable_markedDate_multiplicity_bound_of_minimumTailLimit`
    (uniqueness discharged by the table-level radius at a minimum-debt
    carrier tail). The uniform-\(U\) form makes one neighborhood serve
    every profile. Ordinary-math record:
    `../fable/MARKED_DATE_MULTIPLICITY_BOUND.md`. Independently
    verified: clean compile, lexical scan clean, line lengths clean,
    own `#print axioms` run on both theorems reports only the three
    permitted axioms.

21. `FableCollisionPairBound.lean` (83 lines): delegating shim for the
    collision-concentration kernel of the product-base program. All
    three statements are already production-owned — the pair-sum bound
    is `quittingRootCollisionMass_le_pairMulSum`, the
    \(\binom{n}{2}a^2\) bound is
    `quittingRootCollisionMass_le_choose_card_mul_absorption_sq`
    (both `Quitting/AbsorptionPath/CollisionConcentration.lean`, over
    the `MathUE` Bonferroni product bounds) — plus one new
    `linarith`-level corollary
    (`fable_absorption_sub_singletonSum_le_choose_two_mul_absorption_sq`,
    absorption minus singleton sum \(\le\binom{n}{2}a^2\)). No new
    mathematics; recorded so the product-base assembly cites the
    canonical owners. Independently verified: clean compile, lexical
    scan clean, line lengths clean, own `#print axioms` run on all
    three reports only the three permitted axioms.

22. `FableThroughMarkLedger.lean` (539 lines): the through-mark ledger
    adapters requested by the exactification note (general \(\iota\);
    imports entries 16–18 via the scratch olean chain) — the
    charge-normalized moat
    `fable_throughMark_ledger_ge_absorption_mul_minimum`
    (\((1-\text{surv})D_*-e\le C\), hypothesis-light), the
    floor-to-defect eventual bound
    `fable_limitTight_throughMark_ledger_eventual_floor`
    (eventually \(a_0D_*-\varepsilon\le C_n\) with
    \(a_0=(\gamma-\sigma)/(2M+\gamma)\)), the exact-stack no-go
    `fable_exactStack_absorption_le_excess_ratio` (exact words over a
    near-minimum base have absorption \(\le e/(D_*+e)\)), the
    option-budget bound
    `fable_throughMark_ledger_le_singletonMass_add_literalDefect`
    (\(C\le2M\cdot\mathrm{Sing}+E\)), and the split
    `fable_throughMark_singleton_or_literal_split`
    (\(c\le C\Rightarrow \mathrm{Sing}\ge c/(4M)\lor E\ge c/2\)); with
    three notation defs and `rfl` unfolding lemmas. Ordinary-math
    record: `../fable/THROUGH_MARK_LEDGER_ADAPTERS.md`. Independently
    verified: clean compile through the three-olean chain, lexical scan
    clean, line lengths clean, own `#print axioms` run on all five
    theorems reports only the three permitted axioms.

23. `FableLawStageDecomposition.lean` (169 lines): the law
    stage-decomposition identities for the product-base program
    (general \(\iota\)) — the stage `HasSum`/`tsum` forms
    (`fable_hasSum_stageCoalitionMass_absorbedMassLimit`,
    `fable_terminalOutcomeMass_some_eq_tsum_stage`) delegate to the
    production owners `hasSum_quittingStageCoalitionMass` and
    `tsum_quittingStageCoalitionMass`
    (`TerminalSemanticPlateauTimeDisintegration.lean`); new content is
    the Never complement
    `fable_hasSum_liveMass_mul_absorption_one_sub_neverMass`
    (\(\sum_t L_t\,a_t=1-\mu(\text{Never})\), by telescoping the live
    mass) and the singleton form
    `fable_hasSum_liveMass_mul_singletonCoalition_singletonLawMass`
    (\(\sum_t L_t\,b_{t,i}=\mu(\{i\})\)). Independently verified: clean
    compile, lexical scan clean, line lengths clean, own
    `#print axioms` run on all four declarations reports only the three
    permitted axioms.

24. `FablePairConcentration.lean` (282 lines): the local-concentration
    limit kernel of the product-base program (general \(\iota\)) —
    `fable_vanishing_singletonRatio_pairConcentration` (root sequences
    with positive absorption and singleton-to-absorption ratio bounded
    by \(\delta_n\to0\) have a subsequence on which some fixed pair's
    quit-probability product tends to one), with the quit-vector box
    bridges `fable_absorptionMass_eq_boxAbsorption` and
    `fable_coalitionMass_singleton_eq` (both new in the quit-rate
    coordinate; content delegated to
    `quittingStationaryContinueMass_eq_prod_continueProbability` and
    `Math.PMFProduct.coalitionMass`), continuity lemmas, and
    `fable_absorptionMass_le_one`. Independently verified: clean
    compile, lexical scan clean, line lengths clean, own
    `#print axioms` run reports only the three permitted axioms.

25. `FableProductBaseLaw.lean` (648 lines): **Theorem A of the
    twice-audited product-base export** (general \(\iota\); imports
    entries 23–24 via the scratch olean chain) —
    `fable_zeroNever_zeroSingleton_law_productBase`: a coordinatewise
    limit of behavioral terminal laws with zero Never and zero
    singleton mass is exactly one product-root law with at least two
    sure quitters (\(w_i=w_j=1\), law \(=\) the box-coalition
    polynomial at \(w\)). Assembles the first-efficient-root selection
    (total `Nat.find` selector past an eventual threshold), the
    law/stage decomposition (entry 23), the pair-concentration kernel
    (entry 24), and a profile-local one-date approximation lemma
    (\(|\mu(\text{some }S)-\text{coalMass}|\le(1-L)+L'\)); public
    companions include `fableBoxCoalition` with continuity, the
    coalition box bridge, and `fable_pairProduct_le_boxAbsorption`;
    the selection-exporting refactor adds
    `fable_zeroNever_zeroSingleton_exists_selectionData` (the sure
    pair, the strict index map, the efficient-date selector, live-root
    convergence to \(w\), and vanishing pre-date absorption), with
    the original statement preserved byte-for-byte and re-derived from
    it.
    Ordinary-math source:
    `../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`
    (Theorem A). Independently verified: clean compile through the
    two-olean chain, lexical scan clean, line lengths clean, own
    `#print axioms` run reports only the three permitted axioms.

26. `FablePaddedOneDateProfile.lean` (620 lines, 25 public theorems):
    the padded one-date profile and its exact pure-time anatomy
    (general \(\iota\); imports entry 5's time-escape shifts via the
    scratch olean chain) — `fablePaddedOneDateProfile` (t all-Continue
    rows, then a root, then all-Continue) with exact pure-time
    deviation values (solo before the root, the quit endpoint at it,
    the augmented continue endpoint after it, the continue endpoint at
    Never), the exact cap formula
    `fableQuittingContinuationBestResponseValue_paddedOneDateProfile`
    (\(\max(s,Q,C+h\max(0,s))\) for positive padding), the sandwich
    within \(hR\) of \(\max(s,Q,C)\), and the sure-quitter case
    (`fableOppContinue_eq_zero_of_sureQuitter`, unpadded cap
    \(=\max(Q,C)\)). The dependency's pure-time shift lemmas carry no
    side conditions. Independently verified: clean compile through the
    olean chain, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 25 theorems reports only the three
    permitted axioms.

27. `FableProductBaseRealization.lean` (1340 lines, 42 public
    theorems): **Theorem B of the twice-audited product-base export**
    (general \(\iota\); imports entries 25–26 via the scratch olean
    chain) —
    `fable_zeroNever_zeroSingleton_semantic_productBase_realization`:
    under the Theorem A hypotheses plus semantic convergence to \(z\)
    and strict singleton margins (\(s_k<z.2\,k\), automatic at positive
    global minima), the one-date-then-Never profile at the selected
    product root realizes the complete limit — same law, same
    prescribed payoff, same unrestricted cap vector, with the sure
    pair displayed. The comparison runs directly on the source's own
    pure-time values at the selected dates (three regime estimates,
    \(4R\,E+R\,h\) total cap defect), with the endpoints expanded as
    box polynomials through the production Möbius adapter
    (`quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass`);
    the padded intermediary of entry 26 was not needed in the final
    route. Ordinary-math source: the export's Theorem B (strict-margin
    form). Independently verified: clean compile through the five-olean
    chain, lexical scan clean, line lengths clean, own `#print axioms`
    run on all 42 public theorems reports only the three permitted
    axioms.

28. `FableSureCoreSoftening.lean` (694 lines, 13 public theorems):
    **the softening step of Theorem C** (general \(\iota\); imports
    entry 27's chain) — `fable_sureCore_softening_step`: at a
    full-debt global-minimum product realization with sure core
    \(K\), \(|K|\ge2\), softening one sure quitter \(p\) yields the
    exact dichotomy: an off-minimum pure member-leaving target with
    prescribed gain exactly \(d_p\), or a full-debt minimum child with
    sure core exactly \(K\setminus\{p\}\), gain \(\theta d_p\), and
    all debts positive. With
    `fable_sureCore_softening_singletonMass` (at \(|K|=2\) the child's
    singleton law mass is exactly
    \(\theta\prod_{j\notin K}(1-v_j)>0\)) and the reusable **general
    unpadded cap formula**
    `fableQuittingContinuationBestResponseValue_oneDateThenNever`
    (\(\max(Q,\,C+h\max(0,s))\), no sure-quitter hypothesis).
    Convexity of the debt sum along the softening segment (max-affine
    minus affine) plus global minimality force the monotone dichotomy.
    Ordinary-math source: the export's Proof of C. Independently
    verified: clean compile through the six-olean chain, lexical scan
    clean, line lengths clean, own `#print axioms` run on all 13
    public theorems reports only the three permitted axioms.

29. `FableSureCoreDescent.lean` (278 lines): **the descent wrapper
    completing Theorem C** (general \(\iota\); imports entry 28's
    chain) — the chain inductive `FableSofteningReaches` (each step one
    second-arm softening child, stated sure-set-free), its invariants
    (debt-sum preservation, box bounds, full debt, transfer of global
    minimality along the chain), the terminal predicates
    `FableSofteningOffMinimum` / `FableSofteningPositiveSingleton`,
    the main descent `fable_sureCore_descent`
    (\(n+1\le|K|\) softenings reach an off-minimum pure
    member-leaving target or a positive-singleton minimum) and the
    Fin 4 corollary `finFour_fable_sureCore_descent` (\(n\le3\)).
    With entries 21 and 23–28 this completes the kernel-checking of
    the entire twice-audited product-base export (Theorems A, B, and
    C). Independently verified: clean compile through the seven-olean
    chain, lexical scan clean, line lengths clean, own `#print axioms`
    run reports only the three permitted axioms.

30. `FableOneSureOwnerResponse.lean` (362 lines, 16 public theorems):
    the owner-response block of the one-sure handoff export (general
    \(\iota\); imports entry 28's chain) — the owner's response profile
    (the pure-time strategy `some 1`/`none` by the solo sign), its
    exact payoff `fable_oneSure_ownerResponse_payoff` (= the augmented
    continue value, no hypotheses), the own-update cap invariance
    `fable_continuationBestResponseValue_update_self` (three lines via
    `Function.update_idem` on the cap's sSup range — fully general),
    and at a sure owner with positive debt: prescribed = quit endpoint,
    cap = augmented continue value, response gain = the killed debt,
    and target owner debt = 0; plus the strict/equality debt-sum
    dichotomy under global minimality. Ordinary-math source:
    `../revisit/ONE_SURE_PRODUCT_MINIMUM_EXACT_OWNER_RESPONSE_HANDOFF.md`
    §§1–2. Independently verified: clean compile through the
    seven-olean chain, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 16 theorems reports only the three
    permitted axioms.

31. `FableMinimumChildLeakage.lean` (597 lines, 5 public theorems):
    the leakage-rate laws on the minimum-child softening segment
    (general \(\iota\); imports entry 28's chain) — interval constancy
    of the debt sum (`fable_minimumChild_debtSum_const`, convexity of
    max-affine sums with equal endpoint values at the global minimum),
    per-coordinate affinity (`fable_minimumChild_debt_affine`, each
    convex summand of a constant sum is affine), the mover's exact law
    \(d_p(\theta)=(1-\theta)d_p\) on all of \([0,1]\)
    (`fable_minimumChild_mover_debt`), the recipients' law
    \(\sum_{i\ne p}\Delta d_i(\theta)=\theta d_p\)
    (`fable_minimumChild_leakage_sum`), and the explicit rate family
    (`fable_minimumChild_leakage_rates`: fixed reals summing to
    \(d_p\)). Ordinary-math record:
    `../fable/MINIMUM_CHILD_LEAKAGE_RATES.md`. Independently verified:
    clean compile through the olean chain, lexical scan clean, line
    lengths clean, own `#print axioms` run on all 5 theorems reports
    only the three permitted axioms.

32. `FableOneSureEqualityArm.lean` (620 lines, 26 public theorems):
    **the equality-arm block completing the one-sure handoff export**
    (imports entry 30's chain) — the minimum singleton margin at the
    realized pair, the quantitative nonnegative-solo incidence bound
    (\(D_*\le2R\,a_{-k}\), general \(\iota\)) with its positivity
    corollary, the Fin 4 negative-solo incidence positivity (via the
    hard-residual finite-atom theorem at the equality target, with the
    residual bundle taken verbatim), the combined equality-arm
    incidence, and the reset re-anchor
    `fable_finFour_oneSure_equality_resetRigidChamber`:
    `Nonempty (QuittingLawTightResetRigidChamber ...)` anchored with
    source = origin = minimum = point at the literal response target —
    no reselection. With entry 30 this kernel-checks the entire
    one-sure handoff export (§§1–4): one-sure product minima reach an
    off-minimum paid target or enter the reset-rigid chamber at the
    same literal joint point. Independently verified: clean compile
    through the olean chain, lexical scan clean, line lengths clean,
    own `#print axioms` run on all 26 theorems reports only the three
    permitted axioms.

33. `FableFiniteClockPurification.lean` (488 lines, 8 public
    theorems): the finite-clock purification kernel (general
    \(\iota\); imports entry 30's chain) — `FableDeadlineBounded`
    (live roots pure-continue beyond a deadline), the tail constancy
    of pure-time values, cap attainment by a pure time \(\le T+1\) or
    Never (`fable_exists_deadlineBounded_pureTime_eq_cap`), the
    purification edge `fable_deadlineBounded_purification` (gain
    exactly the observer's debt and target debt zero — proved with NO
    debt hypothesis, stronger than briefed), its strict positive-debt
    form, and the zero-debt support attainment/purification (every
    stopping-law support point is cap-attaining; purifying through one
    preserves the payoff and keeps debt zero) via the own-law mixture
    identity and the MathUE zero-expectation lemma. Kernel for the
    anchored-erasure/deadline-descent chain. Independently verified:
    clean compile through the olean chain, lexical scan clean, line
    lengths clean, own `#print axioms` run on all 8 theorems reports
    only the three permitted axioms.

34. `FableCanonicalPureTime.lean` (769 lines, 29 public theorems):
    the canonical pure-time interface (general \(\iota\); imports
    entry 33's chain) — canonical profiles from time vectors, their
    live roots as literal pure-set roots
    (`fableCanonicalProfile_liveRoot`), deadline-boundedness, the
    exact deviation-value table against deterministic opponents (solo
    before the earliest opponent deadline, the joined coalition at it,
    the opponents' coalition after it or at Never, with the
    trichotomy), the cap formulas with and without an opponent
    deadline, the margin collapse with attainment in
    \(\{\text{QuitAt }u,\text{Never}\}\), the all-Never case, and the
    deadline-support inclusion for the response targets. Ordinary-math
    source: §§3–4 of the twice-reviewed anchored-erasure note.
    Independently verified: clean compile through the olean chain,
    lexical scan clean, line lengths clean, own `#print axioms` run on
    all 29 theorems reports only permitted axioms (24 on the full
    triple, 5 on strict subsets).

35. `FableDeadlineDescentStep.lean` (484 lines, 7 public theorems):
    the singleton-minimum response step (general \(\iota\); imports
    entry 34's chain) — the own-value identity for canonical profiles,
    the (4.1) profile facts at a singleton-earliest canonical minimum
    (prescribed = solo, owner debt = the whole debt sum, all other
    debts zero), the deadline response `fable_singletonMinimum_response`
    (gain exactly the debt sum, killed owner debt, off-minimum excess
    or strict `fableDateFinset` drop with the earliest date erased),
    and the all-Never case with the UNCONDITIONAL off-minimum exit.
    Independently verified: clean compile through the olean chain,
    lexical scan clean, line lengths clean, own `#print axioms` run on
    all 7 theorems reports only the three permitted axioms.

36. `FableDeadlineDescentCapstone.lean` (517 lines, 4 public
    theorems): **the anchored-erasure and finite-descent capstone**
    (general \(\iota\); imports entry 35's chain) — the average-debt
    paid response at any positive-debt canonical profile
    (`fable_positiveDebt_canonicalProfile_averagePaidResponse`), the
    nonemptiness of the date support at positive canonical minima, the
    anchored-erasure induction
    (`fable_anchoredErasure_offMinimum_or_singleton`: off-minimum
    sibling or the singleton-earliest endpoint, date support never
    growing), and the capstone
    `fable_canonicalMinimum_offMinimum_paidPort`: every canonical
    pure-time global minimum with positive debt yields an actual
    off-minimum canonical profile carrying a pure-time response with
    gain at least the target's average debt (hence \(>D_*/|\iota|\)).
    With entries 33–35 this kernel-checks the twice-reviewed
    anchored-erasure/deadline-descent result end to end.
    Independently verified: clean compile through the olean chain,
    lexical scan clean, line lengths clean, own `#print axioms` run on
    all 4 theorems reports only the three permitted axioms.

37. `FablePurificationDescent.lean` (444 lines, 6 public theorems):
    **the mixed-background purification iteration** (general \(\iota\);
    imports entry 36's chain) — the average-debt paid response at any
    positive-debt deadline-bounded profile
    (`fable_positiveDebt_deadlineBounded_averagePaidResponse`), the
    one-coordinate purification step (pure-time overwrite bounded one
    date past the deadline, target bounded at `deadline+1`, minimality
    inherited from the carrier), the fuel iteration
    `fable_deadlineBounded_minimum_purify_or_paidPort` (either a
    canonical global minimum at the very same debt value, or an
    off-minimum bounded profile with the average paid response), and
    the composed corollary
    `fable_deadlineBounded_minimum_offMinimum_paidPort`: every
    deadline-bounded profile at a positive global debt minimum yields
    a profile strictly above the minimum carrying a pure-time or Never
    response with gain at least that profile's average debt. Completes
    Proposition 9.3 and the finite-clock corollary of the
    anchored-erasure note at general finite \(\iota\). Independently
    verified: clean compile through the olean chain, lexical scan
    clean, line lengths clean, own `#print axioms` run on all 6 public
    theorems reports only the three permitted axioms.

38. `FableSupportCounterfactual.lean` (268 lines, 3 public theorems):
    **the support counterfactual and first-disagreement composition**
    (general \(\iota\); imports entry 37's chain, the production
    decoder, and the production bounded-support averaging lemma
    `exists_mem_support_le_expect`) — at any positive-debt coordinate
    of a deadline-bounded profile, a cap-attaining pure plan and a
    strictly positive-mass component of the prescribed stopping law
    differ by at least that coordinate's debt
    (`fable_positiveDebt_support_counterfactual`, via the own-law
    mixture identity), the pair enters the production paid
    first-disagreement decoder at the debt as gain floor
    (`..._paidRow`), and the capstone composition
    (`fable_deadlineBounded_minimum_offMinimum_supportCounterfactualRow`):
    every deadline-bounded positive global debt minimum yields an
    off-minimum deadline-bounded profile, a responder, and the
    counterfactual pair with gap at least the average debt, carrying
    the literal paid first-disagreement row. Completes §6 of the
    finite-clock export. Independently verified: clean compile through
    the olean chain, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 6 declarations reports only the three
    permitted axioms.

39. `FablePostmarkAtomBlock.lean` (314 lines, 11 theorems and one
    Prop definition): **the postmark immediate-atom-or-reached-block
    producer** (general \(\iota\); production imports only) — §§1–3
    of the postmark note: the per-date estimates (stage mass =
    survival × root coalition mass, dominated by the survival drop
    and by the root's total marginal quit rate), finite-prefix
    survival domination, the truncation (tail above \(5\mu/8\) below
    a small immediate atom), the survival floor at date one, the
    finite exit cut with block stage mass above \(\mu/2\), the
    packaged `FablePostmarkBlockData` with the hazard floor, the
    per-profile dichotomy `fablePostmark_immediate_atom_or_blockData`
    (date-zero stage atom of at least \(\mu/8\), or block data), and
    the strictly monotone sequence wrapper from an eventual
    law-coordinate floor. The §4 two-cut instantiation is out of
    scope for this file. Ordinary-math source: §§1–3 of the postmark
    note, PASS-reviewed. Independently verified: clean compile on
    production imports, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 11 theorems reports only the three
    permitted axioms.

40. `FablePostmarkTwoCutInstantiation.lean` (790 lines, 28
    declarations): **the §4 two-cut instantiation of the postmark
    producer** (general \(\iota\) except the final Fin 4 packaging;
    imports entry 39 and the production two-cut/paid-splice modules)
    — the canonical live-root bridges (semantic-pair preservation,
    generalizing the reward-pinned production proof
    `terminalSemanticPair_rootSequence_profileLiveRoot`; joint
    survival weight = live mass), the later-arm
    `QuittingUniformlyReachedPostMarkTwoCutBlock` instance
    (markedRow 0, entryCut 1, exitCut from the block data, reach and
    hazard floors \(\mu/2\)), its coercivity output (exit-suffix
    excess \((e^{\mu/2}-1)/2\) times the minimum, or an entry payer
    debt above \((1-e^{-\mu/2})D/(2|\iota|)\)), the general-\(\iota\)
    paid splice at tolerance \(K/(4|\iota|)\) (one literal unilateral
    update, pre-entry live roots unchanged, whole-profile gain equal
    to the exact payer debt decrease and above reach × tolerance),
    the padded immediate arm (one all-Continue row; the entry pair is
    literally the source's own pair; the padding is payoff-invisible
    but NOT cap-invisible — the padded parent's envelope coordinate
    rises to the singleton quitting reward when needed, priced
    exactly by `fablePostmark_paddedParent_debt_eq`), its coercivity
    and paid splice at floor \(\mu/8\), and the Fin 4 later-arm
    packaging at the note's literal \(K/16\) tolerance with
    whole-profile gain above \(\mu K/32\). The sequence-level
    packaging of the note's (4.5)–(4.6) (one arm along a subsequence,
    payer fixed by a finite-label subsequence) is not compiled.
    Ordinary-math source: §4 of the postmark note. Independently
    verified: clean compile through the olean chain, lexical scan
    clean, line lengths clean, own `#print axioms` runs on all 28
    declarations report only the three permitted axioms.

41. `FablePostmarkSequencePackaging.lean` (355 lines, 13
    declarations): **the sequence-level postmark packaging** (general
    \(\iota\) except the Fin 4 splice packaging; imports entries 39
    and 40) — generic extraction utilities (frequently/eventually
    dichotomy split, finite pigeonhole to a constant subsequence, and
    their stacking), the four output predicates carrying literally
    the entry 40 constants, the per-arm packagings, the four-way
    combiner `fablePostmark_exists_strictMono_twoCut_packaging` (one
    strict extraction with the source arm, the output arm, and — in
    the paid arms — one payer all uniform), and the Fin 4 later-arm
    splice packaging at the note's \(K/16\) tolerance with one fixed
    payer and per-step deviation/splice witnesses. With entries 39–40
    this compiles the postmark note end to end at its stated source
    boundary (the eventual law floor and the positive carrier minimum
    are supplied, not derived). Independently verified: clean compile
    through the olean chain, lexical scan clean, line lengths clean,
    own `#print axioms` run on all 13 declarations reports only the
    three permitted axioms.

42. `FableUniformWordSurvival.lean` (253 lines, 13 declarations):
    **the table-uniform word-survival floor** (general \(\iota\);
    production imports only) — §§2–3 of the uniform exact-port-reach
    note in the scope its review confirmed: the charge-to-log
    conversion \(-\log c\le(1-c)/r\) on \([r,1]\), the one-root
    Continue-product floor \(r=(\gamma/4M)^{|\iota|}\) under the
    checked exact punishment-floor root margin, positivity of the
    canonical reward bound from the terminal gap, and the uniform
    floor `fableUniformSurvivalFloor_le_prefixContinueProduct`:
    every compatible `QuittingPunishmentFloorFinitePrefix`
    certificate, of every depth, keeps joint Continue product at
    least \(\lambda=e^{-C/r}\), with the joint-survival-weight
    alignment. Stated only over prefix certificates (the review's
    quantifier discipline); the §4 composition with the actual-reach
    row is not part of this file. Independently verified: clean
    compile on production imports, lexical scan clean, line lengths
    clean, own `#print axioms` run on all 13 declarations reports
    only the three permitted axioms.

43. `FableFloorRepairSoftening.lean` (473 lines, 17 declarations):
    **the per-profile core of the unique-debtor floor repair**
    (general \(\iota\); production imports only) — the softened
    profile via the production
    `quittingStoppingLawMixtureBehaviorStrategy` (complete
    stopping-law mixture, not a pointwise hazard mixture), the exact
    affine mover payoff (K1), exact mover cap invariance through the
    production `quittingContinuationBestResponseValue_update_self`
    (K2), the uniform nonmover bounds (K3): every behavioral
    deviation of a nonmover sees payoff change at most \(2M\theta\)
    (by commuting the two updates and running the mixture affinity at
    the deviated profile) with the csSup transfer to the nonmover
    cap — the estimate the note's PASS review requested — the exact
    per-outcome terminal-law mixture including Never (K4), the
    retained paid pure-time pair with a support source witness and
    retained approximate cap optimality (K5), and the packaged
    per-profile punishment floor (K6, sequence-free: the note's
    \(\theta=2f/a\) choice arrives as a hypothesis). The
    sequence-level entrance and the exact-port invocation are not
    part of this file. Ordinary-math source: §§2–3 of the
    minimum-floor repair note, PASS-reviewed. Independently
    verified: clean compile on production imports, lexical scan
    clean, line lengths clean, own `#print axioms` run on all 17
    declarations reports only the three permitted axioms.

44. `FableZeroZeroLawSeam.lean` (294 lines, 6 declarations): **the
    zero-Never/zero-singleton law-face contraction** (general
    \(\iota\) with `1 < Fintype.card ι`; imports entries 27 and 38's
    chains plus production carrier modules) — the composite seam of
    the paired-hull composition note: a joint semantic/law carrier
    point \((z,\mu)\) at a positive global debt minimum with zero
    Never coordinate and all singleton coordinates zero is realized
    exactly by the one-date-then-Never profile at a product root
    with two sure quitters, and that realization reaches an actual
    off-minimum profile with a pure-time/Never response of gain
    strictly above \(D_*/|\iota|\)
    (`fable_minimumJointLaw_zeroNever_zeroSingleton_exists_offMinimumPaidPort`);
    the row form (`..._offMinimumPaidRow`) adds the
    cap-attainer/support-source counterfactual pair and the literal
    paid first-disagreement row at the off-minimum average-debt
    floor. Glue: strict margins from the production
    `minimumTerminalSemantic_singletonMargin`, the sequential-closure
    extraction from joint-carrier membership, the production joint
    projection, and deadline boundedness at 0 of the
    one-date-then-Never profile. Kernel-checks the composition
    note's §7 handoff at general \(\iota\) (the note asked for
    Fin 4), eliminating the zero/zero law face of the reset-rigid
    chamber into the off-minimum paid port. Independently verified:
    clean compile through the olean chain, lexical scan clean, line
    lengths clean, own `#print axioms` run on all 6 declarations
    reports only the three permitted axioms.

45. `FableSilentPaddingAdapter.lean` (673 lines, 29 declarations):
    **the universal silent-padding two-cut constructor** (general
    \(\iota\); imports entries 39–40 plus the production margin
    module) — part 1 of the silent-padding export's Lean handoff:
    window truncation at an arbitrary threshold \(\chi\) strictly
    below the law coordinate (no dichotomy, no date-zero split), the
    window hazard floor, the padded block instance
    `fableSilentPaddingTwoCutBlock` (markedRow 0, entryCut 1,
    exitCut window+1, reach floor one, hazard floor \(\chi\)) with
    its field lemmas and existence form, the date-generic padded
    suffix-pair shift (generalizing entry 40's date-2 lemma), the
    (2.7) identities — entry pair = source pair, exit pair = source
    window suffix pair, parent payoff = source payoff, parent
    envelope = max(singleton reward, source cap) — plus the law
    invisibility `fableSilentPadding_paddedParent_absorbedMassLimit_eq`
    (every terminal label's mass unchanged, the silent row carrying
    no stage mass), cap neutrality in hypothesis form with the
    near-minimum connecting chain through the production singleton
    margin (the sequence-level eventuality deliberately not formed),
    and the coercivity/paid-splice corollaries rewritten to speak
    about the source's own pairs with no reach factor. Part 2 of the
    handoff (the `FinFourMinimumReturnPacket` adapter over
    `Research/`) is not part of this file. Ordinary-math source: the
    reviewed silent-padding export. Independently verified: clean
    compile through the olean chain, lexical scan clean, line
    lengths clean, own `#print axioms` run on all 29 declarations
    reports only the three permitted axioms.

46. `FableFloorRepairEntrance.lean` (800 lines, 30 declarations):
    **the §2 minimum inequalities and the sequence-level floor-repair
    entrance** (general \(\iota\); imports entry 43 plus production
    margin modules) — the carrier computations: the (2.1) payoff
    margin and its tail-sum form, carrier debt bounded by the debt
    sum (through the production
    `quittingTerminalSemanticDebt_nonneg_of_mem_carrier`, no
    nonnegativity hypothesis anywhere), the (2.3) punishment-floor
    transfer under normality with its quantitative margin, and the
    (2.4) two-debtor strict tail (needing only carrier membership —
    a strengthening); then the sequence level: the named deficit
    \(f_n\), gain \(a_n\), and clamped weight
    \(\theta_n=\max(0,\min(1,2f_n/a_n))\) with proved bounds, the
    eventual mover gain floor \(a_n\ge D_*/2\), deficit and weight
    vanishing, the (3.4) repair inequality with the clamp inactive
    late, softened-sequence payoff and cap retention ((3.7)–(3.9)
    in limit form through entry 43's K2/K3), the eventually retained
    paid pair at gap \(\ge D_*/2\), and the packaged entrance
    (`fableFloorRepairEntranceProfile`, `fableFloorRepair_entrance`):
    eventually all-player punishment floors at the softened profiles
    with the incoming minimum packet retained in the limit.
    Convergence is supplied coordinatewise; no profile sequence is
    constructed and no exact-port consumer is invoked.
    Ordinary-math source: §§2–3 of the minimum-floor repair note,
    PASS-reviewed. Independently verified: clean compile through the
    olean chain, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 30 declarations reports only the
    three permitted axioms.

47. `FableShiftedRowComposition.lean` (640 lines, 27 declarations):
    **the §4 shift composition** (general \(\iota\); imports entry 42
    and the actual-reach chain plus the production summable-port
    module) — the outward word-prefix constructor
    `fableWordPrefixProfile` (iterated literal splicing, the
    continuation retained as the literal suffix at every depth), the
    (4.3) survival factorization (joint survival at depth+offset =
    the word's Continue product × the continuation's joint survival,
    with the entry 42 floor \(\lambda\) applied uniformly), the
    (4.4) paid-gap scaling (the shifted pure-time difference equals
    the observer-deleted word survival times the original
    difference, dominated below by \(\lambda\)), the one-equation
    compatibility interface `IsFableCompatiblePrefixCertificate`
    (inner boundary = the continuation's cap; later-stage agreement
    derived from the certificate's policy and exact-Nash fields, not
    assumed), the per-stage debt scaling with coordinatewise
    antitonicity and the (4.5) sandwich, and the packet
    `fable_positiveDebt_compatibleWord_shifted_paidRow_and_debtSandwich`:
    behind any compatible certificate of any depth, an actual source
    with observer debt at least \(\Delta\) carries a shifted paid
    first-disagreement row of gain \(\lambda\Delta/4\), a joint
    entry floor \(\lambda\Delta^2/(32M^2)\) at the row's own start,
    and total debt sandwiched between the global minimum and the
    source's own. The §4.1 fork lift and §§5–6 are not part of this
    file. Ordinary-math source: §4 of the uniform exact-port-reach
    note, review-confirmed. Independently verified: clean compile
    through the olean chain (the entry-era
    `FableStoppingSelection`/`FableDebtActualReach` oleans rebuilt
    into it first), lexical scan clean, line lengths clean, own
    `#print axioms` run on all 27 declarations reports only
    permitted axioms (26 on the full triple, one on a strict
    subset).

48. `FableFloorRepairExactPort.lean` (363 lines, 10 declarations):
    **the exact-port invocation of the minimum-floor repair**
    (general \(\iota\); imports entry 46 plus the production
    exact-port module) — the note's boxed (4.1): the six-field
    `QuittingPaidRowFloorSafeSource` packaging from a pure-time pair
    and the all-player floor (`fableFloorRepairFloorSafeSource` with
    field lemmas and existence form), the invocation of the
    production
    `QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
    with its disjunction restated verbatim (uniform-equilibrium
    payoff, or a summable all-Continue semantic port with positive
    paid-suffix reach on the marked exact orbit), the entrance
    composition (`fableFloorRepair_eventually_exactPort_alternative`:
    for all late indices the softened entrance profile carries the
    packaging at gain \(D_*/4\), strictly below the retained
    \(D_*/2\) gap, with the source witness supported by the mover's
    original stopping law), and the lifted case split
    (`fableFloorRepair_exactPort_alternative_of_entrance`: a uniform
    payoff exists outright, or every late softened entrance profile
    is the literal paid suffix of such a port). With entries 43 and
    46 this compiles the minimum-floor repair note end to end at its
    stated boundary (source attachment as external provenance; no
    forward exact spine and no completely absorbing family claimed).
    Independently verified: clean compile through the olean chain,
    lexical scan clean, line lengths clean, own `#print axioms` run
    on all 10 declarations reports only the three permitted axioms.

49. `FableForkLift.lean` (373 lines, 13 declarations): **the §4.1
    whole-strategy fork lift** (general \(\iota\); imports entries 42
    and 47 with the scratch fork chain and the production stationary
    payoff module) — the payoff cancellation
    `fableWordPrefixProfile_terminalPayoff_sub_eq_survivalPrefix_mul`
    (for ANY two continuations, the word-prefixed payoff difference
    equals the word's Continue product times the original difference;
    the root-stage contributions cancel via the production
    root-then-continuation payoff recursion), the lifted strategy
    `fableWordLiftedStrategy` with the update-form identity
    (`fableWordPrefixProfile_update_eq_update_liftedStrategy`:
    prefixing an updated profile IS the unilateral update of the
    prefixed profile by the lifted strategy — no coordinate-lemma
    fallback needed), the certificate-floor form (lifted gain
    \(\ge\lambda\cdot\) gain), and the (4.7) composition
    `fable_positiveDebt_compatibleWord_exists_lifted_profitableStoppingLawFork`:
    behind any compatible certificate of any depth, the common-prefix
    fork lifts to a literal unilateral edge with whole-profile gain
    at least \(\lambda\Delta^2/(16M)\)-shaped (the scratch fork's
    constant scaled by the floor, stated division-free), pre-row
    agreement of the replacement, nonmover coordinates unchanged,
    and the (4.5) debt sandwich. With entries 42 and 47 this
    completes the review-confirmed scope of the uniform
    exact-port-reach note (§§2–4 including 4.1). Independently
    verified: clean compile through the olean chain (the
    `FableProfitableFork`/`FableCommonPrefixFork` oleans rebuilt into
    it), lexical scan clean, line lengths clean, own `#print axioms`
    run on all 13 declarations reports only the three permitted
    axioms.

50. `FableCapSeam.lean` (337 lines, 14 theorems): **the exact first
    cap seam** (general \(\iota\); production imports only) — §2 of
    the two-block fork-seam note, in the checked defect currency:
    the own-coordinate congruence and affinity of the Continue
    endpoint (through the production
    `quittingRootContinuePayoff_update_add` and the uncited
    congruence source
    `quittingRootExpectedPayoff_eq_absorbingContribution_add`), the
    (2.1) endpoint displacement in both cap-pair and update forms,
    the (2.2) alignment (the production
    `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
    is literally the display), the combined cap-shifted defect form,
    complementarity at mixed coordinates, the (2.3) seam
    \(\delta_j(b',x)=q_jH_j\Delta_j\) with its exact-root form, the
    signed (2.3a)
    \(q_jH_j(\Delta)_+ + c_jH_j(-\Delta)_+\) (S3 now derived from
    it), the (2.4) pure-Quit formula with no sign hypothesis, and
    the pure-Continue monotonicity. (2.3b) is sequence-level and not
    formalized. Ordinary-math source: §2 of the fork-seam note (not
    yet reviewed; the box-calculus derivations verified directly
    before delegation). Independently verified: clean compile on
    production imports, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 14 theorems reports only the three
    permitted axioms.

51. `FableThinSliceToken.lean` (488 lines, 17 declarations): **the
    certified thin-slice debtor token and the golden-ratio chord
    obstruction** (general \(\iota\); production imports only) —
    §§1–3 of the thin-slice note: the hypothesis-form certificate
    `FableCertifiedExploitabilityFloor` with the bridge from the
    checked max-coordinate exploitability functional, debt
    nonnegativity at actual profiles (production
    `quittingTerminalDeviationDebt_nonneg`), the thin-slice token
    ((6)–(7): under the certificate, a slice of width
    \(\varepsilon<\gamma\) has exactly one \(\gamma\)-scale debtor,
    all other debts summing to \(\varepsilon\)), the replacement
    facts ((8)–(9): own-update cap invariance, gain = the mover's
    debt, non-principal gains at most \(\varepsilon\)), the boxed
    (12) exit-or-rotate dichotomy, the stopping-law chord profile
    with mover-debt affinity and nonmover chord bounds (consumed
    from the production `TerminalSemanticStoppingLawDebtConvexity`
    module, not reproved), and the capstone
    `fableThinSlice_principalDebtor_response_exits_slice` ((22)):
    under the certificate and the golden-ratio inequality
    \(\varepsilon^2+\gamma\varepsilon-\gamma^2<0\), a
    principal-debtor exact best-response target has total debt
    strictly above \(\gamma+\varepsilon\) — debtor rotation is
    impossible in a sufficiently thin slice; the response must make
    a quantitative off-minimum excursion. Ordinary-math source:
    §§1–3 of the thin-slice note (not yet reviewed; the chord
    arithmetic verified directly before delegation). Independently
    verified: clean compile on production imports, lexical scan
    clean, line lengths clean, own `#print axioms` run on all 17
    declarations reports only the three permitted axioms.

52. `FableMovingCapChart.lean` (460 lines, 33 named declarations plus
    the chain structure's fields): **the moving cap-chart cocycle and
    the conditional forward-packet lift** (general \(\iota\);
    production imports only) — §§2–5 and 7 of the moving-cap note:
    the (2.1) successor difference identity (aligned to the
    production `quittingRootSuccessorPayoff_sub_eq_continueMass_mul`),
    the (2.2) cap-prefix identity at exact cap-Nash roots, punishment
    below every literal cap, the chart `quittingMovingCapChart`, the
    literal chain structure `QuittingMovingCapChain` (actual sources,
    exact roots, one-player replacements of the prefixed profiles),
    the (2.4) mover-zero leakage, the exact cocycle
    `chartError_succ` with its unfolded (3.4) prefix-sum form, the §4
    support transport through the production
    `isQuittingRootSupportApproxNash_of_tail_close`, the compact
    chart carrier, Theorem 5.1 (`toForwardPacket` and
    `nonempty_forwardPacket`: uniform chart error at most
    \(\varepsilon\) and cumulative exact-root absorption at least
    \(A\) instantiate the production `QuittingFiniteForwardPacket`),
    the §7 two-row form, and Corollary 5.2
    (`quittingGame_exists_uniformEquilibriumPayoff_of_movingCapChains`)
    composing with the production finite-forward-packet compiler.
    The uniform smallness hypothesis is carried, not discharged — a
    consumer interface, per the note's own status line.
    Ordinary-math source: the moving-cap note (not yet reviewed; the
    cocycle algebra and interface alignments verified directly
    before delegation). Independently verified: clean compile on
    production imports, lexical scan clean, line lengths clean, own
    `#print axioms` run on all 33 named declarations reports only
    the three permitted axioms (the delegating agent additionally
    swept all 65 local constants with `Lean.collectAxioms`, same
    result).

53. `FableDebtMinimaSeparation.lean` (718 lines, 22 theorems): **the
    universal debt-minima separation and the ratio-chamber paid
    port** (general \(\iota\); imports entry 51's chain) — §§9–10 of
    the thin-slice note, twice PASS-reviewed: the real-arithmetic
    kernels (an affine-limit lemma replacing the note's continuity
    and pigeonhole steps, the port arithmetic, ratio monotonicity),
    the 2M debt bound and ζ-best-response existence from the cap
    sSup (attainment-free, per the reviews' binding caveat), the §9
    per-profile exclusion (`fableDebtMinima_add_lt_debtSum`: under
    the certificate and \(h^2+4Mh-\eta^2<0\), every actual profile
    has total debt above \(\eta+h\)) and the (33) bound
    (`fableDebtMinima_sqrt_separation`:
    \(\eta+\sqrt{4M^2+\eta^2}-2M\le D(\sigma)\) for every actual
    profile, with unconditional positivity of the margin), and the
    §10 port theorems: \(\eta<d_p(\sigma)\) below the two-debtor
    threshold (by a single explicit chord parameter, no limit), the
    general residual-debt bound
    `fableDebtPort_debtSum_le` (response debt carried as a free
    real, so the \(o(1)\) and exact forms are specializations), the
    note's (42) in both bounds
    (`fableDebtPort_debtSum_le_of_exact`, `..._of_exact_ratio`), and
    the attainment-free packagings
    (`fableDebtPort_exists_response_debtSum_le`,
    `..._exists_response_near_port`). Together with entry 51 this
    compiles the thin-slice note's theorem surface (§§1–3, 9–10) in
    full; the entire ratio chamber \(1<D_*/\eta<2\) feeds the
    off-minimum paid port at the explicit floor. Independently
    verified: clean compile through the olean chain, lexical scan
    clean, line lengths clean, own `#print axioms` run on all 22
    theorems reports only permitted axioms.

54. `FableSpineCanonicityBootstrap.lean` (189 lines, 7
    theorems): **the persistent-spine quantifier bootstrap**
    (general \(\iota\) except the Fin 4 composition, matching the
    production theorem's generality; production imports only) —
    §§2–3 of the spine-audit note: the marginal-to-absorption
    comparison, joint-survival vanishing from every suffix start
    under a nonsummable marginal, the transversality corollary
    (values = the root-schedule terminal values), the bootstrap
    `fableSpine_canonical_of_bounded_of_not_summable` (an exact
    Bellman/Nash spine bounded by ANY finite constant with a
    persistent marginal already satisfies the canonical reward-cube
    bound, hence is an `IsCanonicalExactQuittingNashBellmanSpine`),
    and the composed (5)
    (`finFour_all_marginalQuitHazards_summable_of_no_uniformPayoff_of_bounded_spine`
    with its persistence-facing restatement): without a
    uniform-equilibrium payoff, EVERY bounded exact Nash–Bellman
    spine has every marginal summable — the arbitrary-bound wording
    gap of the persistent-spine question is closed. Ordinary-math
    source: the spine-audit note (a composition of three named
    checked declarations, verified directly before delegation).
    Independently verified: clean compile on production imports,
    lexical scan clean, line lengths clean, own `#print axioms` run
    on all 7 theorems reports only permitted axioms.

Entries 1–13 cover every formalization-sized statement of the source
note's Section 10 list plus the packaged common-prefix fork and the
support-clause strengthening. Entries 14–22 cover the uniform-radius
dispatch boundary, the tight-coordinate corollaries, the pre-mark
absorption/Never package with its limit forms, the marked-row and
marked-date charging theorems, and the through-mark ledger adapters.
Entries 21 and 23–29 kernel-check the entire twice-audited
product-base export: Theorems A and B, the softening step, and the
descent, with their supporting kernels.
Entries 30–38 kernel-check the one-sure owner-response handoff with
its equality-arm chamber re-anchor and leakage-rate laws, and the
complete anchored-erasure/deadline-descent chain through the
mixed-background purification iteration and the
support-counterfactual first-disagreement composition.
Entries 39–41 kernel-check the postmark immediate-atom-or-reached-block
producer dichotomy, its sequence wrapper, the two-cut instantiation
of both arms, and the sequence-level packaging with a
pigeonhole-fixed payer.
Entry 42 kernel-checks the table-uniform word-survival floor for
exact punishment-floor prefix certificates.
Entry 43 kernel-checks the per-profile core of the unique-debtor
floor-repair softening, including the uniform nonmover cap bounds.
Entry 44 kernel-checks the zero-Never/zero-singleton law-face
contraction: every such joint global minimum realizes by a product
root-then-Never profile and exits to the off-minimum paid port.
Entry 45 kernel-checks the universal silent-padding two-cut
constructor with cap neutrality and law invisibility.
Entry 46 kernel-checks the minimum floor inequalities and the
sequence-level floor-repair entrance with vanishing clamped weights.
Entry 47 kernel-checks the §4 shift composition: compatible
certificate words scale the actual-reach paid row by the uniform
survival floor, with the debt sandwich.
Entry 48 kernel-checks the exact-port invocation, compiling the
minimum-floor repair end to end into the production alternative.
Entry 49 kernel-checks the whole-strategy fork lift behind
compatible certificate words, completing the exact-port-reach
note at its review-confirmed scope.
Entry 50 kernel-checks the exact first cap seam, signed form
included, in the production defect currency.
Entry 51 kernel-checks the certified thin-slice debtor token and
the golden-ratio chord obstruction: below the golden-ratio slice
width, a principal-debtor exact response must exit the slice.
Entry 52 kernel-checks the moving cap-chart cocycle and the
conditional forward-packet lift into the production compiler.
Entry 53 kernel-checks the universal debt-minima separation and
the ratio-chamber paid port, completing the thin-slice note's
theorem surface.
Entry 54 kernel-checks the persistent-spine quantifier bootstrap:
bounded exact spines are canonical under a persistent marginal, so
the no-persistent-marginal theorem holds at arbitrary bounds.
All are kernel-checked in the scratch lane and independently verified.
Integration into a proper lane remains for an integration agent.
