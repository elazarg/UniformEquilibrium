# Every-suffix forcing collapses to a bare root target

Author: `CLAUDE_ERDOS`
Status: `PROOF_DRAFT` (reduction complete; every step a named checked Lean
declaration or two-line algebra; the assembled statements themselves are not
checked in Lean)

## Current best attempt

**Exact reviewable claim.**  Define, for a reward table and `eta > 0`, the
*root target* `RootTarget(reward, eta)`: there exists an executable product
root sequence `roots : ℕ → ι → PMF Bool` such that

- (S1) for every start date, the joint Continue survival product vanishes;
- (S2) for every player and start date, the one-player-deleted survival
  product vanishes; and
- (D0) every player's *actual* initial terminal semantic debt of the
  root-sequence profile is at most `eta`.

Theorem 1: `RootTarget(reward, eta)` implies
`Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta)`, by the
already-checked tautological datum `QuittingChronologicalDebtData.exactOfRoots`;
every certificate field is discharged by a named checked declaration.
Theorem 2 (substance already checked in Lean): any certificate at `eta`
yields its own roots as a witness of (S1), (S2), and (D0) at `4 * eta`.
Hence (Corollary 3) certificates at all accuracies are *equivalent* to
`RootTarget` at all accuracies, and (Corollary 4) the open producer
proposition `VanishingDebtAtomChronologicalConsumer` is equivalent to: atom
access implies `RootTarget` at every accuracy.  Corollary 5: for the uniform
payoff itself even (S1)-(S2) are unnecessary — (D0) at every accuracy already
suffices through the checked terminal-Nash endpoint.  Corollary 6: a
"necessary field failure" negative answer to `questions/EVERY_SUFFIX_FORCING.md`
can only be a positive floor on actual initial exploitability over
survival-vanishing root sequences; no other certificate field can necessarily
fail.

**Honest status.**  All six statements are ordinary mathematics whose every
step is either a named Lean-checked declaration cited below or trivial
algebra recorded in full; none of the assembled statements is itself checked
in Lean.  No review yet.  Nothing here inhabits `RootTarget`; the open
producer content of the question bank is untouched, only relocated and
strictly narrowed.

**Main gap.**  None inside the reduction.  The open remainder is exactly:
produce, from vanishing-debt atom access, roots with (D0) at every accuracy
(plus (S1)-(S2) for the literal interface).

**Sections to check.**  Sections 3 (Theorem 1 field table), 4 (Theorem 2 and
the equivalence), 5 (Corollaries 5-6), 6 (warnings and boundary cases).

## 1. Exact question

From `questions/EVERY_SUFFIX_FORCING.md` (formalizer-written, read-only):
for every `eta > 0`, produce `QuittingChronologicalDebtData` from a
source-matched vanishing-debt atom or reset packet proving the literal
certificate fields of `QuittingChronologicalDebtShadowingCertificate`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`):

1. every-suffix prescribed-defect sums at most `eta`;
2. every-suffix survival-weighted adverse direct-debt forcing at most
   `eta` plus slack; and
3. date-zero candidate debt at most `eta`;

together with the boundedness, nonnegativity, and generated-secant fields.
Survival is deferred to `questions/PERSISTENT_DELETED_CLOCKS.md`.

Case declaration: no conference notebook drives this question as its target.
`notes/CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md` audited adjacent interfaces
and is `BLOCKED_AT_EXACT_ADAPTER`; `notes/CODEX_CEDAR__RADIAL_PACKET_AMPLIFICATION.md`
studies non-tautological scheduling in the counterexample regime.  My attack
is different from both: instead of constructing schedules, I determine exactly
how much the scheduling freedom is worth, and prove the answer is "nothing
beyond a factor 4 in `eta`".

## 2. Sources checked

Lean declarations inspected in place, cited by name and file:

- `QuittingChronologicalDebtData`, `QuittingChronologicalDebtShadowingCertificate`,
  `QuittingChronologicalDebtShadowingCertificate.initial_semanticDebt_le`,
  `QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash`,
  `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`,
  `exists_quittingTerminalSemanticPrefix_secant`,
  `QuittingChronologicalDebtData.semanticPair_eq_prefix`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`);
- `QuittingChronologicalDebtData.exactOfRoots` and its lemma family
  `exactOfRoots_root`, `exactOfRoots_debt`, `exactOfRoots_candidateSuccessorPair`,
  `exactOfRoots_prescribedDefect`, `exactOfRoots_directDebtDefect`,
  `exactOfRoots_debt_nonneg`, `exactOfRoots_secant`,
  `exactOfRoots_secant_generated`, `exactOfRoots_prescribedDiscrepancy`,
  `exactOfRoots_adverseDirectForcing`, `exactOfRoots_prescribed_bounded`,
  `exactOfRoots_debt_bounded`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean`);
- `QuittingVanishingDebtAtomAccess`, `VanishingDebtAtomChronologicalConsumer`,
  `QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`,
  `exists_uniformEquilibriumPayoff_of_vanishingDebtAtomChronologicalConsumer`
  (`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`);
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticDebt`,
  `quittingTerminalPayoff_update_sub_le_terminalSemanticDebt`,
  `abs_quittingContinuationBestResponseValue_le`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`);
- `quittingContinuationBestResponseValue`,
  `quittingTerminalPayoff_update_le_continuationBestResponseValue`,
  `abs_quittingTerminalPayoff_le_quittingRewardBound`
  (`UniformEquilibrium/Quitting/Root/FirstBranch.lean`);
- `quittingTerminalDeviationDebt_nonneg`
  (`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`);
- `quittingRootOpponentContinueMass_nonneg`
  (`UniformEquilibrium/Quitting/Stationary/LiveMass.lean`);
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
- `PositiveSlopeCausalRegression.exact_source_has_zero_forcing_but_unit_initialDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/Regression/SourceMatchedExposureNoGo.lean`),
  as the existing regression that `exactOfRoots` is not by itself a
  small-debt producer;
- `QuittingPositiveMinimumDebtTangentFamily.frozenRadialChronologicalData`
  (`UniformEquilibrium/Diagnostics/Quitting/Chronology/SourceMatchedChronologicalData.lean`),
  as the existing frozen-source instantiation of `exactOfRoots`.

Every "checked" label below means: that declaration compiles in the
production tree under its imports; I did not run a build this session, and no
claim below asserts more than the declaration states.

## 3. Theorem 1: certificate assembly from the bare root target

Fix `reward` and `eta > 0`.  Notation for a root sequence
`roots : ℕ → ι → PMF Bool`:

- `profile_m := quittingRootSequenceProfile reward roots m`, the executable
  tail profile from date `m`;
- `pair(m) := quittingTerminalSemanticPair reward profile_m`, its literal
  prescribed/best-response pair;
- `D(m, i) := quittingTerminalSemanticDebt (pair m) i`, the actual unilateral
  exploitability of player `i` at the tail from `m`;
- `(S1)`: for every `start`,
  `Math.survivalProduct (fun t ↦ quittingStationaryContinueMass (roots t)) start`
  tends to `0`;
- `(S2)`: for every `who` and `start`,
  `Math.survivalProduct (fun t ↦ quittingRootOpponentContinueMass (roots t) who) start`
  tends to `0`;
- `(D0)`: for every `who`, `D(0, who) ≤ eta`.

**Theorem 1.**  If `roots` satisfies (S1), (S2), (D0), then
`QuittingChronologicalDebtShadowingCertificate reward eta` is inhabited, with
`data := QuittingChronologicalDebtData.exactOfRoots reward roots`.

*Proof.*  Field by field; every cited declaration is checked in Lean.

| Certificate field | Discharged by |
| --- | --- |
| `data` | `exactOfRoots reward roots` (definition, checked) |
| `eta_pos` | hypothesis `0 < eta` |
| `debt_nonneg` | `exactOfRoots_debt_nonneg` |
| `prescribed_bounded` | `exactOfRoots_prescribed_bounded` (bound `quittingRewardBound reward`) |
| `debt_bounded` | `exactOfRoots_debt_bounded` (bound `2 * quittingRewardBound reward`) |
| `secant_nonneg` | `exactOfRoots_secant` (secant is literally `0`) |
| `secant_le_opponentContinue` | `exactOfRoots_secant` and `quittingRootOpponentContinueMass_nonneg` |
| `secant_generated` | `exactOfRoots_secant_generated` |
| `prescribed_discrepancy` | `exactOfRoots_prescribedDiscrepancy`: the sum is exactly `0`, and `0 ≤ eta` |
| `adverse_direct_forcing` | `exactOfRoots_adverseDirectForcing`: every finite adverse sum is exactly `0 ≤ eta + slack`, so the eventual clause holds for all lengths |
| `joint_survival` | hypothesis (S1), transported along `exactOfRoots_root` (`data.root time = roots time` by `rfl`) |
| `opponent_survival` | hypothesis (S2), same transport |
| `initial_debt_le` | hypothesis (D0) via `exactOfRoots_debt` (`data.debt 0 who = D(0, who)`) |

No step beyond table lookup and `0 ≤ eta` is needed.  ∎

The underlying mechanism, for the reviewer: `exactOfRoots` sets
`prescribed(t) := pair(t).1`, `debt(t) := D(t, ·)`, `secant := 0`; then
`candidateSuccessorPair t = pair(t+1)` exactly
(`exactOfRoots_candidateSuccessorPair`), and
`semanticPair_eq_prefix` makes both one-stage defects identically zero.  All
of this is already checked; Theorem 1 only assembles it against the
certificate's field list.

## 4. Theorem 2 and the equivalence

**Theorem 2.**  If `QuittingChronologicalDebtShadowingCertificate reward eta`
is inhabited by `certificate`, then `roots := certificate.data.root`
satisfies (S1) and (S2) verbatim (they are the certificate's `joint_survival`
and `opponent_survival` fields) and satisfies (D0) at accuracy `4 * eta`:
for every `who`,
`D(0, who) = quittingTerminalSemanticDebt (certificate.data.semanticPair reward 0) who ≤ 4 * eta`
by the checked `initial_semanticDebt_le`.  ∎

Theorem 2 is a repackaging of checked statements; nothing new is proved.

**Corollary 3 (exact equivalence at all accuracies).**  For every reward,

`(∀ eta > 0, Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta))`
`⟺ (∀ eta > 0, RootTarget(reward, eta))`.

*Proof.*  Right to left is Theorem 1.  Left to right: given target `eta`,
apply Theorem 2 to a certificate at `eta / 4`.  ∎

**Corollary 4 (producer restatement).**
`VanishingDebtAtomChronologicalConsumer reward` is equivalent to: for every
frontier `QuittingPositiveMinimumDebtTangentFamily reward` and every
`QuittingVanishingDebtAtomAccess frontier`, `RootTarget(reward, eta)` holds
for every `eta > 0`.  *Proof.*  Both directions pointwise in the frontier and
access by Corollary 3 (the `eta`-quantifier is inside the consumer
definition).  ∎

Interpretation, stated carefully: the candidate/secant scheduling freedom of
the certificate — non-tautological prescribed values, spread discrepancy,
signed seams, generated-secant weighting — buys *no existence power* beyond
a factor `4` in the accuracy.  Any certificate, however scheduled, already
carries a root sequence whose *actual* initial exploitability is at most
`4 * eta`.  The scheduling machinery remains valuable as a *proof device*
(a producer may be able to certify candidate defects without computing actual
semantics, and `Math.twoDiscountDebtShadowing` then converts them), but the
producer *obligation* recorded in the question bank is exactly `RootTarget`
and nothing weaker.

## 5. Two further corollaries

**Corollary 5 (survival is redundant for the uniform payoff).**  Suppose only:
for every `eta > 0` there exists a root sequence with (D0) at `eta` (no
survival hypotheses).  Then the quitting game has a uniform-equilibrium
payoff.  *Proof.*  (D0) at `eta` makes `profile_0` an `eta`-asymptotic
terminal Nash profile: for every `who` and behavioral deviation,
`quittingTerminalPayoff reward (update profile_0 who deviation) who -
quittingTerminalPayoff reward profile_0 who ≤ D(0, who) ≤ eta` by the checked
`quittingTerminalPayoff_update_sub_le_terminalSemanticDebt`.  Terminal Nash
profiles at every positive error give the payoff by the checked
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.  ∎

So (S1)-(S2) are interface overhead of the literal certificate, not a
mathematical prerequisite of the endpoint.  A producer that certifies small
*actual* initial exploitability of root sequences may bypass the certificate
and both survival obligations entirely.  (This does not deprecate
`questions/PERSISTENT_DELETED_CLOCKS.md` for the literal consumer interface,
and survival remains internally necessary for the shadowing *derivation* of
actual smallness from candidate schedules.)

**Corollary 6 (the only falsifiable fields).**  In
`questions/EVERY_SUFFIX_FORCING.md`, an acceptable negative answer must make
"one named certificate field necessarily fail".  By Theorem 1's table, for
*any* root sequence whatsoever the tautological datum satisfies every field
except possibly `joint_survival`, `opponent_survival`, and `initial_debt_le`.
Therefore no source profile can make the discrepancy, forcing, boundedness,
nonnegativity, or generated-secant fields necessarily fail, and a negative
answer to the combined chronological route must be a *root-absorbing
exploitability floor*: some `gamma > 0` such that every root sequence
satisfying (S1)-(S2) has `max_who D(0, who) ≥ gamma`.  (For the bypass route
of Corollary 5 the floor must hold over all root sequences; that is a
terminal exploitability gap restricted to root-sequence profiles, one
consequence of the negative semantic endpoint.)  ∎

Remark: (S1)-(S2) alone are trivially satisfiable — with at least two
players, the all-Quit-every-period schedule has both stationary joint mass
and every deleted-opponent mass equal to `0`, so all suffix products vanish.
The survival class is therefore never empty; a floor claim is about debt on
that class, not about emptiness.

## 6. Warnings, boundary cases, and what is not claimed

1. **The isolated question is reduced one-directionally.**  Theorem 1 shows
   (D0) *suffices* for all non-survival fields.  I do **not** claim the
   converse for the isolated question: data satisfying only the non-survival
   fields need not force small actual initial debt, because the checked
   shadowing derivation (`semanticDebt_le`) consumes the survival fields.
   Whether the non-survival fields alone can be satisfied with small
   *candidate* date-zero debt but large *actual* debt is open here.  A first
   gaming attempt (all-Continue roots, zero candidate debt, generated zero
   secants) fails: the `offset = 0` term of `adverse_direct_forcing` at
   `start = 0` is `-directDebtDefect(0) = actual one-stage debt - candidate
   debt`, which fights `initial_debt_le` directly.  The full certificate
   equivalence (Corollary 3) is two-directional and is the statement that
   matters for the consumer.
2. **The factor 4 is inherited**, not sharpened: it is the constant of the
   checked `initial_semanticDebt_le`.  I make no sharpness claim.
3. **Playerwise versus summed debt.**  (D0) is playerwise, matching
   `initial_debt_le`.  Any comparison with the summed positive-minimum
   quantity costs the usual factor `card ι`; none of the statements above
   uses the sum.
4. **Nothing is produced.**  No statement here inhabits `RootTarget` for any
   nontrivial reward, and no claim is made about what atom access yields.
   The regression
   `exact_source_has_zero_forcing_but_unit_initialDebt` already shows in
   Lean that the tautological datum inherits the source's unit debt on a
   diagnostic instance; Theorem 1 is consistent with it: there the
   hypothesis (D0) simply fails.
5. **Lean status.**  Theorems 1-2 and Corollaries 3-6 are ordinary
   mathematics.  Their building blocks are checked declarations named in
   Section 2; the assembled statements are not declared in Lean.  In
   particular I checked by search that no production file assembles
   `exactOfRoots` into a full certificate: the only modules mentioning
   `QuittingChronologicalDebtShadowingCertificate` are
   `ChronologicalDebtShadowing.lean`, `UniformExistenceBoundary.lean`, and
   `PaidFirstDisagreementPayoffNearReturn.lean`, none of which contains this
   assembly.

## 7. Consequences for the question bank (informational)

- `EVERY_SUFFIX_FORCING`: its three literal fields plus all algebraic fields
  are produced by Theorem 1 from (D0) alone; the question's remaining
  mathematical content is exactly "atom access ⟹ roots with (D0) at every
  accuracy".
- `PERSISTENT_DELETED_CLOCKS`: needed only for the literal certificate
  interface; the uniform payoff itself needs only (D0) (Corollary 5).  The
  survival obligations bite only jointly with (D0) on shared roots; as pure
  root properties they are trivially satisfiable (all-Quit).
- The negative-answer target of the whole chronological route is a single
  clean object: a positive exploitability floor over survival-vanishing (or
  all) root sequences (Corollary 6).

## 8. Feedback wanted

1. One independent check of the Theorem 1 field table against the literal
   field list of `QuittingChronologicalDebtShadowingCertificate`, and of the
   quantifier order in Corollaries 3-4 (the `eta`-quantifier sits inside
   `VanishingDebtAtomChronologicalConsumer`).
2. Does anyone see a way to settle Warning 1 (gameability of the isolated
   non-survival fields) with an exact two-player instance?  It is not needed
   for any corollary, but it would close the last soft edge of the picture.
