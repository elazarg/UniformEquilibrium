/-
The whole-strategy fork lift behind an exact punishment-floor prefix word.

This file formalizes section 4.1 of the note
`CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION`, the
(4.6)-(4.7) fork lift, in the scope confirmed by its review.

A unilateral behavioral replacement of one mover is lifted behind a supplied
root word spliced outward by `fableWordPrefixProfile`: the mover plays the
word's own prescribed actions through the word and only then switches to the
replacement, while every opponent is unchanged.  Three literal facts carry the
lift:

* the whole-profile terminal payoff difference between two continuations
  spliced behind one common word is the word's joint Continue product times
  the original difference, for every player (the note's (4.7) cancellation);
* splicing is coordinatewise, so the lifted profile is literally the
  word-prefix of the updated profile, and equals a single-coordinate
  `Function.update` of the unlifted word-prefix at an explicitly described
  lifted strategy; and
* behind a punishment-floor certificate word the Continue product carries the
  table-uniform floor `fableUniformSurvivalFloor`, so a nonnegative source
  gain survives scaled by at least that floor.

Composing with the checked scratch common-prefix fork turns a positive mover
debt into a source-indexed actual behavioral edge behind any compatible
certificate of any depth, with the fork's own constants.

Quantifier discipline.  The floor quantifies only over punishment-floor prefix
certificates, never over arbitrary root words; the payoff cancellation and the
coordinate identities hold for arbitrary words and need no compatibility.  The
selected row, its stopping law, and its dates depend on the source profile.

Nothing here makes the rows after the lifted first disagreement exact
Nash-Bellman roots, and nothing here concerns the post-mark orientation
obstruction of section 5.
-/
import FableShiftedRowComposition
import FableCommonPrefixFork
import UniformEquilibrium.Quitting.Stationary.Payoff

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## R1.  Payoff cancellation through a common prefix word -/

omit [DecidableEq ι] in
/-- One splicing stage is affine in the continuation's terminal payoff, with
coefficient the stage's joint Continue mass. -/
private theorem fable_terminalPayoff_rootThenContinuation_eq_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      quittingRootAbsorbingContribution reward root who +
        quittingStationaryContinueMass root *
          quittingTerminalPayoff reward continuation who := by
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]

omit [DecidableEq ι] in
/-- **(4.7), payoff cancellation.**  Behind one common root word every
word-stage terminal contribution cancels, so the whole-profile terminal
payoff difference of two continuations spliced behind that word is the word's
own joint Continue product times the original difference.  This holds for
every player, for arbitrary words, and uses no compatibility. -/
theorem fableWordPrefixProfile_terminalPayoff_sub_eq_survivalPrefix_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι)
    (depth : ℕ) :
    quittingTerminalPayoff reward
          (fableWordPrefixProfile reward word first depth) who -
        quittingTerminalPayoff reward
          (fableWordPrefixProfile reward word second depth) who =
      quittingSurvivalPrefix word depth *
        (quittingTerminalPayoff reward first who -
          quittingTerminalPayoff reward second who) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [fableWordPrefixProfile_succ, fableWordPrefixProfile_succ,
        fable_terminalPayoff_rootThenContinuation_eq_add,
        fable_terminalPayoff_rootThenContinuation_eq_add,
        quittingSurvivalPrefix_succ]
      linear_combination quittingStationaryContinueMass (word depth) * ih

/-! ## R2.  The lifted unilateral edge -/

/-- The mover's lifted strategy: play the word's own prescribed actions
through the word, then use `tail`.  This is the note's
"player `p` uses its prescribed `W`-actions through the word and then uses
`τ_p`". -/
noncomputable def fableWordLiftedStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool) (who : ι)
    (tail : (quittingGame reward).BehaviorStrategy who) :
    ℕ → (quittingGame reward).BehaviorStrategy who
  | 0 => tail
  | depth + 1 => fun
      | 0, _ => word depth who
      | t + 1, h =>
          fableWordLiftedStrategy reward word who tail depth t
            (Fin.tail h.1, h.2)

omit [DecidableEq ι] in
@[simp] theorem fableWordLiftedStrategy_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool) (who : ι)
    (tail : (quittingGame reward).BehaviorStrategy who) :
    fableWordLiftedStrategy reward word who tail 0 = tail := rfl

omit [DecidableEq ι] in
@[simp] theorem fableWordLiftedStrategy_succ_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool) (who : ι)
    (tail : (quittingGame reward).BehaviorStrategy who) (depth : ℕ)
    (hist : (quittingGame reward).Hist 0) :
    fableWordLiftedStrategy reward word who tail (depth + 1) 0 hist =
      word depth who := rfl

omit [DecidableEq ι] in
@[simp] theorem fableWordLiftedStrategy_succ_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool) (who : ι)
    (tail : (quittingGame reward).BehaviorStrategy who) (depth time : ℕ)
    (hist : (quittingGame reward).Hist (time + 1)) :
    fableWordLiftedStrategy reward word who tail (depth + 1) (time + 1) hist =
      fableWordLiftedStrategy reward word who tail depth time
        (Fin.tail hist.1, hist.2) := rfl

omit [DecidableEq ι] in
/-- **Splicing is coordinatewise.**  The word-prefix profile's `who`
coordinate is the lifted strategy built from the continuation's own `who`
coordinate; it does not see any other coordinate of the continuation. -/
theorem fableWordPrefixProfile_apply_eq_liftedStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (depth : ℕ) :
    fableWordPrefixProfile reward word terminal depth who =
      fableWordLiftedStrategy reward word who (terminal who) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext time hist
      cases time with
      | zero => rfl
      | succ time => exact congrFun (congrFun ih time) _

omit [DecidableEq ι] in
/-- Two continuations agreeing at one coordinate have word-prefixes agreeing
at that coordinate, at every depth. -/
theorem fableWordPrefixProfile_apply_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι)
    (hwho : first who = second who) (depth : ℕ) :
    fableWordPrefixProfile reward word first depth who =
      fableWordPrefixProfile reward word second depth who := by
  rw [fableWordPrefixProfile_apply_eq_liftedStrategy,
    fableWordPrefixProfile_apply_eq_liftedStrategy, hwho]

/-- **The lifted edge is unilateral.**  Splicing a common word outward
commutes with a unilateral replacement: the word-prefix of the updated profile
is the single-coordinate update of the word-prefix at the mover's lifted
strategy.  In particular the two prefixed profiles are literally equal at
every opponent coordinate. -/
theorem fableWordPrefixProfile_update_eq_update_liftedStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (replacement : (quittingGame reward).BehaviorStrategy mover) (depth : ℕ) :
    fableWordPrefixProfile reward word
        (Function.update profile mover replacement) depth =
      Function.update (fableWordPrefixProfile reward word profile depth) mover
        (fableWordLiftedStrategy reward word mover replacement depth) := by
  funext who
  by_cases hwho : who = mover
  · subst hwho
    rw [Function.update_self, fableWordPrefixProfile_apply_eq_liftedStrategy,
      Function.update_self]
  · rw [Function.update_of_ne hwho]
    exact fableWordPrefixProfile_apply_congr reward word _ _ who
      (Function.update_of_ne hwho _ _) depth

/-- Every opponent coordinate is untouched by the lift. -/
theorem fableWordPrefixProfile_update_apply_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (replacement : (quittingGame reward).BehaviorStrategy mover) (depth : ℕ)
    (other : ι) (hother : other ≠ mover) :
    fableWordPrefixProfile reward word
        (Function.update profile mover replacement) depth other =
      fableWordPrefixProfile reward word profile depth other :=
  fableWordPrefixProfile_apply_congr reward word _ _ other
    (Function.update_of_ne hother _ _) depth

/-- **(4.7), exact scaling of the whole-profile gain.**  The lifted two-profile
edge's whole-profile gain is exactly the word's joint Continue product times
the source gain of the unilateral replacement. -/
theorem fableWordPrefixProfile_update_terminalPayoff_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (replacement : (quittingGame reward).BehaviorStrategy mover) (who : ι)
    (depth : ℕ) :
    quittingTerminalPayoff reward (fableWordPrefixProfile reward word
          (Function.update profile mover replacement) depth) who -
        quittingTerminalPayoff reward
          (fableWordPrefixProfile reward word profile depth) who =
      quittingSurvivalPrefix word depth *
        (quittingTerminalPayoff reward
            (Function.update profile mover replacement) who -
          quittingTerminalPayoff reward profile who) :=
  fableWordPrefixProfile_terminalPayoff_sub_eq_survivalPrefix_mul reward word
    (Function.update profile mover replacement) profile who depth

namespace QuittingTerminalExploitabilityWitness

/-- **(4.7), the uniform floor.**  A nonnegative unilateral source gain
survives the lift behind every finite exact punishment-floor certificate of
every depth, scaled by at least the table-uniform survival floor.  No
compatibility of the certificate with the profile is used. -/
theorem fableUniformSurvivalFloor_mul_le_wordPrefix_update_terminalPayoff_sub
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (replacement : (quittingGame reward).BehaviorStrategy mover)
    (gain : ℝ) (hgain : 0 ≤ gain)
    (hedge : gain ≤ quittingTerminalPayoff reward
        (Function.update profile mover replacement) mover -
      quittingTerminalPayoff reward profile mover) :
    witness.fableUniformSurvivalFloor * gain ≤
      quittingTerminalPayoff reward (fableWordPrefixProfile reward cert.roots
          (Function.update profile mover replacement) cert.horizon) mover -
        quittingTerminalPayoff reward
          (fableWordPrefixProfile reward cert.roots profile cert.horizon)
          mover := by
  rw [fableWordPrefixProfile_update_terminalPayoff_sub_eq]
  exact (mul_le_mul_of_nonneg_right
      (witness.fableUniformSurvivalFloor_le_prefixSurvivalPrefix cert)
      hgain).trans
    (mul_le_mul_of_nonneg_left hedge
      (quittingSurvivalPrefix_nonneg cert.roots cert.horizon))

/-! ## R3.  Composition with the checked common-prefix fork -/

/-- **(4.6)-(4.7), the composed fork lift.**  An actual source with mover
continuation debt at least `Δ > 0` carries a paid first-disagreement row of
gain `Δ / 4` and one complete stopping law whose induced behavior strategy is
literally the mover's own at every date strictly before that row's start.
Behind any compatible finite exact punishment-floor certificate of any depth,
the word-prefixed replacement is an actual unilateral behavioral edge of the
whole prefixed profile — the two prefixed profiles differ only at the mover's
coordinate, at the explicitly lifted strategy — whose whole-profile mover gain
carries the fork's own constant scaled by the table-uniform survival floor.
The source's prefixed total debt stays sandwiched between the global semantic
minimum and the source's own total debt. -/
theorem fable_positiveDebt_compatibleWord_exists_lifted_profitableStoppingLawFork
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
      quittingTerminalPayoff reward profile observer)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert profile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate, candidate ∈ quittingTerminalSemanticCarrier reward →
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      ∃ law : PMF (Option ℕ),
        witness.fableUniformSurvivalFloor * (Δ * Δ) ≤
            16 * quittingRewardBound reward *
              (quittingTerminalPayoff reward
                  (fableWordPrefixProfile reward cert.roots
                    (Function.update profile observer
                      (quittingStoppingLawBehaviorStrategy reward observer law))
                    cert.horizon) observer -
                quittingTerminalPayoff reward
                  (fableWordPrefixProfile reward cert.roots profile
                    cert.horizon) observer) ∧
          fableWordPrefixProfile reward cert.roots
              (Function.update profile observer
                (quittingStoppingLawBehaviorStrategy reward observer law))
              cert.horizon =
            Function.update
              (fableWordPrefixProfile reward cert.roots profile cert.horizon)
              observer
              (fableWordLiftedStrategy reward cert.roots observer
                (quittingStoppingLawBehaviorStrategy reward observer law)
                cert.horizon) ∧
          (∀ other, other ≠ observer →
            fableWordPrefixProfile reward cert.roots
                (Function.update profile observer
                  (quittingStoppingLawBehaviorStrategy reward observer law))
                cert.horizon other =
              fableWordPrefixProfile reward cert.roots profile cert.horizon
                other) ∧
          (∀ u, u < row.start → ∀ history,
            quittingStoppingLawBehaviorStrategy reward observer law u history =
            quittingStoppingLawBehaviorStrategy reward observer
              (quittingBehaviorStoppingLaw reward (profile observer))
              u history) ∧
          quittingTerminalSemanticDebtSum minimum ≤
            quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableWordPrefixProfile reward cert.roots profile
                cert.horizon)) ∧
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableWordPrefixProfile reward cert.roots profile
                cert.horizon)) ≤
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) := by
  obtain ⟨row, law, hforkGain, -, -, hforkPrefix⟩ :=
    positiveDebt_exists_commonPrefix_profitableStoppingLawFork reward profile
      observer Δ hΔ hdebt
  obtain ⟨hlower, hupper⟩ := fableCompatible_debtSum_sandwich cert profile
    hcompat minimum hminimum cert.horizon le_rfl
  have hM : 0 ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
  have hsourceGain : 0 ≤ quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingStoppingLawBehaviorStrategy reward observer law)) observer -
      quittingTerminalPayoff reward profile observer := by
    nlinarith [mul_pos hΔ hΔ]
  have hlift :=
    fableUniformSurvivalFloor_mul_le_wordPrefix_update_terminalPayoff_sub
      witness cert profile observer
      (quittingStoppingLawBehaviorStrategy reward observer law) _ hsourceGain
      le_rfl
  refine ⟨row, law, ?_, ?_, ?_, hforkPrefix, hlower, hupper⟩
  · calc witness.fableUniformSurvivalFloor * (Δ * Δ)
        ≤ witness.fableUniformSurvivalFloor *
            (16 * quittingRewardBound reward *
              (quittingTerminalPayoff reward
                  (Function.update profile observer
                    (quittingStoppingLawBehaviorStrategy reward observer law))
                  observer -
                quittingTerminalPayoff reward profile observer)) :=
          mul_le_mul_of_nonneg_left hforkGain
            witness.fableUniformSurvivalFloor_pos.le
      _ = 16 * quittingRewardBound reward *
            (witness.fableUniformSurvivalFloor *
              (quittingTerminalPayoff reward
                  (Function.update profile observer
                    (quittingStoppingLawBehaviorStrategy reward observer law))
                  observer -
                quittingTerminalPayoff reward profile observer)) := by ring
      _ ≤ 16 * quittingRewardBound reward *
            (quittingTerminalPayoff reward
                (fableWordPrefixProfile reward cert.roots
                  (Function.update profile observer
                    (quittingStoppingLawBehaviorStrategy reward observer law))
                  cert.horizon) observer -
              quittingTerminalPayoff reward
                (fableWordPrefixProfile reward cert.roots profile
                  cert.horizon) observer) :=
          mul_le_mul_of_nonneg_left hlift (by linarith)
  · exact fableWordPrefixProfile_update_eq_update_liftedStrategy reward
      cert.roots profile observer _ cert.horizon
  · exact fun other hother =>
      fableWordPrefixProfile_update_apply_of_ne reward cert.roots profile
        observer _ cert.horizon other hother

end QuittingTerminalExploitabilityWitness

end GameTheory
