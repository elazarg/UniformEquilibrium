# Independent support-weight review

Identity: CODEX_NOETHER_SUPPORT.

Status: the independent first derivation below was recorded before opening
the candidate or any other review. The full 333-line candidate and the
original-paper/source audit now pass substantive review without an unresolved
mathematical objection. See the
[full review](../feedback/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_NOETHER_SUPPORT.md).
Final export-format byte reconciliation also passes at SHA-256
`38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`.
This is ordinary mathematics and static source inspection, not a Lean check.

## Exact question

Let I be finite and nonempty. A nonempty terminal coalition S pays r_i(S) to
player i; Never pays zero. Players use independent private behavioral
randomization and one deviator may replace their entire strategy. Put
s_i = r_i({i}) and assume s_i ≥ 0. For every nonempty A ⊆ I suppose there are
weights w_i ≥ 0 on A, summing to one, such that for every nonempty S ⊆ A,
Σ_{i∈S} w_i(r_i(S) − s_i) ≤ 0. The weights are chosen once per A.

The requested conclusion is periodic terminal ε-Nash play at every positive
ε, from every live suffix, against all behavioral deviations, followed by one
fixed uniform-equilibrium payoff. Necessity is not claimed.

## Independent calculations

For one independent root q, let A = {i : q_i > 0}; write Q_i for player i's
payoff from Quit against q_{−i}. Product expansion gives the exact identity

Σ_{i∈A} w_i q_i(Q_i − s_i)
= Σ_{∅≠S⊆A} P_q(S) Σ_{i∈S} w_i(r_i(S) − s_i) ≤ 0.

Since Σ w_i q_i > 0, some active player with positive weight has Q_i ≤ s_i.
At an exact root Nash profile every supported Quit action earns the mixed
payoff, including q_i = 1. Therefore an absorbing exact Nash root has an
active player with mixed payoff at most their singleton. This calculation
allows zero weights; it does not choose separate weights for each S.

After unit-singleton normalization, this supplies the classical low-payoff
root condition. An independent construction sketch is as follows. Work in
the compact reward cube restricted by min_i x_i ≤ 1. If an exact root has
absorption at least δ, retain it. Otherwise every q_i < δ and every Continue
action is supported. Exact Nash then gives x_i ≥ 1 − O(Mδ). Replace the root
by a sole small-probability quitter at a minimizing coordinate. Its output
still has minimum at most one and every supported action has O(Mδ) regret.
A finite mesh produces a cycle of these roots. Root absorption at least δ
makes the actual periodic tail differ from the mesh labels by at most the
mesh error divided by δ. Thus support perfection is against actual tails.
This is a proof sketch pending quantitative manuscript checking.

Normalization cannot silently shift Never. Taking
r'_i(S) = (r_i(S) + c_i)/(s_i + c_i), with c_i > 0, makes own singletons one;
weights transform by w'_i proportional to w_i(s_i + c_i). For an actual
profile its transformed payoff is scale times original payoff plus shift
times actual absorption probability. The shift cancels for finite-date
deviations and an absorbing prescribed profile only.

The nonnegative singleton assumption supplies the missing all-behavior
step: against fixed independent opponents, Quit at late finite dates has
limiting payoff U_i(Never) + s_i P(opponents never quit) ≥ U_i(Never).
Consequently finite-date reply bounds also bound Never; independent mixtures
of finite dates and Never bound every behavioral deviation. This covers
s_i = 0 without division by s_i. A periodic unit-singleton ε-Nash profile at
ε < 1 cannot be all Continue, hence absorbs from every suffix. The stationary
repair permitted by the extraction theorem also has this property.

## Initial falsification tests

For two players with s_1 = s_2 = 1, coalition premiums (1, −1) satisfy the
weighted condition with equal weights while violating playerwise joint-exit
capping. Thus no inference back to capped joint exit is legitimate.

Weights picked separately for each coalition would not prove the displayed
weighted expectation inequality. Negative singleton payoffs would reverse
the required late-Quit versus Never domination. Ordinary mixed regret would
not imply supported-action perfection when the quitting probability is tiny.
These are explicit potential failed implications to inspect in the candidate.

## Sources inspected before manuscript access

- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`).
- `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  and its dichotomy in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`:
  its hypothesis is unit own singleton; capped joint exit is absent.
- `quittingTerminalPayoff_playerwiseAffine` and
  `quittingTerminalPayoff_finiteTime_playerwiseAffine`
  (`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- `docs/TOOLKIT.md`, root and conference instructions, `SOURCES.md`,
  `GOAL.md`, both research methods, and `exports/README.md`.

## Manuscript comparison

The candidate uses a simpler direct perturbation for zero singletons than the
blind argument above. It takes t = ε/4, adds t only at terminal outcomes, and
uses the pointwise bound 0 ≤ U(r+t,π) − U(r,π) ≤ t for every actual profile π.
This controls complete deviations, including Never, without requiring the
extracted profile to absorb and without needing late-Quit domination.
The blind normalization discussion is retained as independent research
history, not as an additional hypothesis imposed on the accepted proof.

The manuscript's hazard increase also improves the initial construction
sketch: raising the selected active-low player's hazard by δ(1−q_i) preserves
that player's exact supported optimality and gives the explicit 4Rδ bound
for everyone else. No split into high- and low-absorption roots is needed.

The final export-format manuscript and explicit Lean handoff were reconciled
with the reviewed proof; exact acceptance is appended to the full review.
No other review verdict was consulted. Next requested check: external
formalization should implement the finite support predicate and the exact
product identity before connecting the existing extraction consumer.
