# Final export gate for `NORMAL_UNIQUE_PERSISTENT_NASH_BELLMAN_SPINE`

Reviewer: `CODEX_SOURCE_GATE`

Target:
[`NORMAL_UNIQUE_PERSISTENT_NASH_BELLMAN_SPINE.md`](../formalized/NORMAL_UNIQUE_PERSISTENT_NASH_BELLMAN_SPINE.md)

## Verdict

**PASS.** The current packet satisfies all eight mandatory criteria in
[`exports/README.md`](../exports/README.md). I found no mathematical,
source/API, strategy-class, or scope objection requiring repair. The generic
normal unique-persistent-spine theorem is complete ordinary mathematics, and
the strengthened Fin4 conclusion really is the all-spines, all-marginals
summability statement claimed in the packet.

This review does not confer Lean status. The generic spine wrapper and its
Fin4 hard-residual corollary remain work for an external formalization agent.

## Eight-item export checklist

1. **Exact self-contained statement — PASS.** The packet quantifies the
   finite player set, reward table, product roots, bounded value sequence,
   common bound, persistent owner, all outsider summability assumptions, and
   punishment-normality. It now defines the Bellman expectation \(F_x(w)\)
   and expands exact root Nash as the inequality against every replacement
   Quit/Continue marginal. The payoff target \(r(\{p\})\) is fixed.

2. **Complete definitions and proof — PASS.** The Bellman decomposition,
   summable-tail estimate, singleton-row convergence, pure-Quit coupling,
   stationary solo cap, positive-date extraction, near-punishment selection,
   finite solo-prefix splice, and fixed-target terminal conclusion are all
   proved. No mathematical lemma is deferred. The final semantic step is a
   correctly named already-checked consumer, not an assumed new lemma.

3. **Probability/information/strategy audit — PASS.** The packet explicitly
   records independent product randomization, the single live public-history
   chronology, the reduction of an unrestricted behavioral replacement to a
   time-dependent randomized stopping law on
   \(\mathbb N\cup\{\infty\}\), the first-nonempty-coalition stopping rule,
   zero payoff on nonabsorption, and both coupling probability modes. Never
   and arbitrarily late randomized stopping are included. It also states the
   correct uniformity order: the target precedes the accuracy, while the
   selected profile and its parameters may depend on the accuracy and must
   work at all sufficiently late finite horizons.

4. **Named adapter and conjecture-facing consumer — PASS.** The same-table
   adapter is
   `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
   whose residual supplies punishment-normality for every Fin4 player and a
   terminal exploitability witness. The unique-persistent branch reaches the
   named target through
   `isUniformEquilibriumPayoff_soloReward_of_approximate_caps`; the
   two-persistent branch reaches existence through the chronological
   certificate consumer. The packet strictly narrows the maintained question
   in
   [`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md):
   instead of producing two persistent labels, it is now enough to produce
   any one nonsummable marginal on an exact canonical spine.

5. **Positive and negative boundaries — PASS.** The positive one-player
   \(r_p(\{p\})=1\) case checks the no-outsider boundary. The exact
   \(r_p(\{p\})=-1\) example falsifies deletion of punishment-normality and
   explains the necessity of the actual punishment tail. The canonical
   all-Continue phantom correctly fences the zero-persistent case.

6. **Source, literature, and novelty audit — PASS.** Every declaration named
   in the packet exists in the cited file and has the asserted role. The
   source section now identifies `IsQuittingNormalPlayer` and its exact
   translation, says explicitly that no external-paper result is used, and
   compares the new theorem with the deleted-clock consumer, the
   summable-clock value-convergence theorem, and the one-owner obstruction.
   The new content is therefore correctly isolated as the derivation of the
   singleton target and outsider cap hypotheses from a normal uniquely
   persistent exact spine, plus the Fin4 hard-residual composition.

7. **Independent review and falsification — PASS.** All three linked reviews
   exist and are substantive. The adversarial review reconstructed the proof
   against arbitrary behavioral deviations and supplied the sharp failure
   without normality. The earlier target-forgetting API objection is resolved
   by citing the target-preserving consumer. The strengthening request is
   resolved by the all-marginals-summable Fin4 corollary. The earlier markup
   objection is also resolved. No review leaves a mathematical objection
   open.

8. **Lean handoff — PASS.** The proposed generic theorem uses the actual
   `IsCanonicalExactQuittingNashBellmanSpine`, `Summable`/`¬ Summable`,
   `quittingMarginalQuitHazard`, `IsQuittingNormalPlayer`, and fixed singleton
   target. The hard-residual theorem shape is also honest: the residual's
   terminal exploitability witness supplies the contradiction to either
   uniform-payoff consumer. The four genuinely new local obligations are
   listed without smuggling the desired conclusion into a certificate field.

## Mathematical recheck

Let \(R=r(\{p\})\), let

\[
a_t=\prod_{j\ne p}(1-q_{t,j}),\qquad c_t=1-a_t,
\]

and let \(G_t\) be the unnormalised contribution from root outcomes containing
an outsider. The product union bound gives

\[
0\le c_t\le \sum_{j\ne p}q_{t,j},\qquad \sum_t c_t<\infty.
\]

Bellman evaluation is exactly

\[
v_t=a_t((1-q_{t,p})v_{t+1}+q_{t,p}R)+G_t,
\qquad \lVert G_t\rVert_\infty\le Kc_t.
\]

After subtracting \(R\), iteration kills the bounded terminal term because
the owner's nonsummable hazard makes every suffix product vanish, and it
leaves

\[
\lVert v_t-R\rVert_\infty
\le 2K\sum_{s\ge t}c_s\longrightarrow0.
\]

At any late date with positive owner hazard, deleting the outsider marginals
changes an outsider's forced-Quit payoff only on an outsider-Quit event. Exact
root Nash and the preceding target estimate therefore give the cap error

\[
\eta_t=\lVert v_t-R\rVert_\infty
       +2K\sum_{j\ne p}q_{t,j}\longrightarrow0.
\]

Repeating the resulting solo root stationarily makes its full behavioral cap
the maximum of the immediate-Quit endpoint and \(R_i\). The sampled positive
hazards and errors satisfy the exact hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps`. The expanded
finite-prefix proof is consistent with that checked consumer: outsider
deviations pay at most \(\eta_t+4K\rho\), owner deviations at most
\(\delta+2K\rho\), and prescribed payoff delivery misses \(R\) by at most
\(2K\rho\). No punishment infimum attainment and no lower bound on the
sampled positive hazards are used.

For the strengthened Fin4 corollary, fix any canonical exact spine in a hard
residual and suppose some player \(p\) has a nonsummable marginal. If all
other marginals are summable, the generic theorem and
`all_punishmentNormal p` produce the singleton uniform payoff. Otherwise a
second distinct nonsummable marginal exists;
`HasTwoPersistentQuittingMarginals.survival`,
`nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine`, and
`quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
produce some uniform payoff. Either conclusion contradicts the residual's
terminal exploitability witness. Hence every player's marginal is summable
on every canonical exact spine. This is stronger than merely excluding one
persistent label and exactly supports the packet's remaining-producer claim.

## Source/API and file-integrity recheck

The following critical declarations and paths were re-resolved directly:

- `IsCanonicalExactQuittingNashBellmanSpine` and
  `canonicalPhantom_isExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
- `quittingMarginalQuitHazard`,
  `HasTwoPersistentQuittingMarginals.survival`, and
  `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero` in
  `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`;
- `quittingStationaryUnilateralCap_solo_other` and
  `quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix` in the two
  stationary/exceptional files cited by the packet;
- `quittingBestReplyValue_stationary`,
  `quittingPunishmentValue_eq_stationaryPunishmentValue`, and
  `exists_stationaryRoot_cap_lt_punishmentValue_add` in their cited min--max
  and support-witness files;
- `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  in their cited target-preserving consumer files;
- both chronological two-persistent declarations; and
- `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` and its
  no-uniform-payoff producer in
  `FullSupportProjectiveQBarResidual.lean`.

All four Markdown links in the packet resolve. The current file is valid
UTF-8, its 27 display-math openings and closings balance, and a byte scan found
no forbidden control character. The previous vertical-tab corruption,
`rhoho` typo, missing TeX backslashes, and malformed delimiters are absent.

## Required repairs

None. The packet is ready to remain in `exports/` and be handed to an external
Lean formalization agent as reviewed ordinary mathematics.
