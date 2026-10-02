# Independent review: finite premium peeling through Solan–Vieille

Reviewer: CODEX_RENY.

Reviewed original: [CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER.md](../notes/CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER.md).

Reviewed SHA-256:
`48933b7ca0a0e321c8dfd38253f668d8e00f751b514d0a7282d5619560f68084`.

Verdict: PASS for the complete arbitrary-finite-player adapter. The earlier
Fin4 analytic conclusion legitimately strengthens to every nonempty finite
player set with nonnegative own singleton rewards under the stated premium
and support conditions. No mathematical correction is required. This is an
explicit raw-table adapter into an older conditional existence mechanism,
not a new unrestricted quitting-game theorem or a claim that the adapter
already has a checked production declaration.

## 1. Primary and exact-source scope

I first checked the relevant original paper text and exact source statements,
then read the complete frozen 225-line adapter. The primary paper is Eilon
Solan and Nicolas Vieille, “Quitting Games,” Mathematics of Operations
Research 26(2), 265–285 (2001), DOI 10.1287/moor.26.2.265.10549.
The inspected local copy is
`literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf`, SHA-256
`f4a4dd998e7bc1648cf407684c2ad459ef255791ea9865f85102efee0941c186`.

Printed pages 266–267 give the finite-player, independent stopping-strategy
model, Never-zero terminal payoff, and quantification over every unilateral
strategy. Pages 269–271 give the actual one-shot root game, support-perfect
definition, conditional Proposition 2.2, and the cyclic construction in
Proposition 2.3. Pages 272–274 restate and explain the nonlocal extraction
of Proposition 2.4/2.6. I checked the latter consumer's exact current
production declaration as well, not only its informal paper overview.

The paper explicitly distinguishes Proposition 2.2's active-player-payoff
root condition from the sufficient own-quitting cap A.2. The corresponding
`proposition2_2`, `proposition2_3`, and `proposition2_4` statements in
`Literature/SolanAndVieille2001.lean` have the required separate hypotheses.
The literature lane is not built or imported by production. I used it as
a faithful mathematical/source comparison, not a checked production wrapper.

The finite peeling theorem was independently checked in
[the full peeling review](CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING__BY_CODEX_RENY.md),
which applies to original SHA-256
`aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`.

## 2. The exact root hypothesis is actually supplied

In the unit-singleton table, let R≥1 bound rewards and
W={v∈[−R,R]^I : some v_i≤1}. This is compact and nonempty for nonempty I.
For each v choose any exact product Nash root. If it absorbs, support
peeling gives an active owner whose Quit endpoint is exactly 1; exact
support equality gives its prescribed payoff 1. If the root is all-Continue,
Nash requires v_i≥1 for every i. Membership in W then supplies an owner
with v_i=1, indifferent between Quit and Continue.

This is precisely the choice hypothesis of Proposition 2.2. It does not
require joint quitting rewards to be capped by 1. It is stronger than
knowing that an arbitrary coordinate of the root payoff is low: the low
coordinate is an ACTIVE quitter, except in the explicitly handled
all-Continue case. No favorable branch assumption is missing.

## 3. Actual periodic rows and quantitative verification

Increase only that owner's Quit probability by δ times its Continue
probability. This remains an independent product root, not public
correlation. Its absorption is at least δ. The owner's payoff remains
exactly 1: it was indifferent if mixed or initially Continue, while a sure
Quit owner is unchanged. The whole successor remains in W because rewards
and the continuation lie in the same cube.

An outsider's two pure-action endpoint values each change by at most 2Rδ;
its support is unchanged. Thus every supported action is within 4Rδ of
every alternative. This is support-wise error, which is the required input.

For desired row error τ>0, the displayed choices

    δ=min(1/2,τ/(8R)),       ζ=δτ/4

are positive and give 4Rδ≤τ/2 and 2ζ/δ=τ/2. A finite ζ-net in W and
an arbitrary chosen row at each representative define a map of a finite
nonempty set. Reverse a directed cycle of that map. Its literal roots
q_ℓ and representatives v_ℓ satisfy

    ||v_ℓ−F(q_ℓ,v_(ℓ+1))||∞≤ζ,       a(q_ℓ)≥δ.

The reverse orientation is necessary and is correct. Repeating the roots
gives an actual periodic profile whose every suffix terminates, since the
survival of n more rows is at most (1−δ)^n. Its actual periodic terminal
tail values U obey U_ℓ=F(q_ℓ,U_(ℓ+1)). Maximizing over the finite period
gives max||U_ℓ−v_ℓ||∞≤ζ/δ. Comparing both endpoints then gives actual-
tail support error at most 4Rδ+2ζ/δ≤τ.

This validates the self-consistency step; the representatives are not
silently treated as realized payoffs. No continuous Nash selection, joint
mixing of profiles, or common cycle across accuracies is required.

## 4. Full deviations and the stationary branch

Support-perfect rows and termination alone do NOT justify adding a fixed
error over infinitely many dates. The adapter explicitly uses the older
nonlocal extraction theorem instead. Its inspected production form is
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.

Its table hypothesis is unit own singletons ONLY. For each requested full
terminal error it supplies a positive row tolerance. A periodic sequence
with positive common absorption and support-perfect rows against ACTUAL
next-tail values then gives a periodic sequence whose every suffix is a
terminal approximate Nash profile. The stationary alternative is allowed
and is represented by period one. The original row sequence need not be
the output in that branch.

The proof's activity branch passes through
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` in
`UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`.
Its exact statement identifies arbitrary hazard replacements with all
behavioral unilateral deviations by the live-history collapse. Never and
arbitrarily late stopping times are not omitted. The stationary alternative
already concludes the same full behavioral terminal Nash property.

Choosing the extraction tolerance BEFORE constructing the mesh sequence
closes the unit-singleton case for every finite player count. There is no
residual payoff-target, punishment-floor, or row-realization hypothesis.

## 5. Zero singletons, payoff perturbation, and one fixed target

For nonnegative s_i, add t>0 only to terminal rewards and divide coordinate
i by d_i=s_i+t>0. The new singleton is 1, and its own premium is
d_i(S)/d_i, so both the nonnegative-premium condition and peeling survive.
The finite reward bound may grow as t decreases; the argument needs no
uniform bound over t.

For desired original error ε>0, choose t=ε/4 and η=ε/2. Apply the unit
result with full error η/max_i d_i. Positive coordinate rescaling then
gives error at most η for the terminal-shifted table. For every prescribed
profile AND every unilateral replacement π,

    U_i^(r+t)(π)−U_i^r(π)=t Pr_π(absorption),

whose absolute value is at most t. Thus original full deviation gains are
bounded by η+2t=ε. This argument applies in every suffix and does not
assume the deviating profile terminates. In particular, the Never outcome
has not been shifted or confused with a full affine payoff equivalence.

At every original error there is therefore an actual periodic profile
with the stated full terminal bound in every suffix. Finally,
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
selects ONE payoff target of the ORIGINAL table before accuracy. The
underlying argument uses compactness of its fixed reward cube and the
terminal-to-uniform bridge, not a common normalized table as ε varies.
The fixed target is not supplied by the perturbation itself.

## 6. Scope and implementation handoff

The source comparison is accurate: the current production row and mesh
generators expose unit-solo AND capped-joint hypotheses, whereas the
full-response extraction exposes unit solos alone. One may generalize the
former to their actual conditional root-choice input or implement the
explicit finite-data adapter proved here. Merely citing the capped-joint
generator for a table with strict premiums would be incorrect.

The arbitrary-finite semantic theorem is proved ordinary mathematics through
this older conditional chain. The new finite reward criterion and its
equivalent universal boundary geometry are not thereby declared already
formalized, or new worldwide class coverage. The separate Fin4 analytic
separator proof remains valid but is not necessary for this broader
existence conclusion. No author's frozen bytes, exports, or Lean files
were edited.
