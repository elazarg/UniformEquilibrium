/-
Shift composition of an exact punishment-floor prefix word with an actual
paid row.

This file formalizes section 4 of the note
`CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION`,
through 4.5 and excluding the 4.1 whole-strategy fork lift, in the scope
confirmed by its `SOCIAL_WEIGHT_REVIEW` review.

A supplied root word is prefixed outward to a fixed actual continuation by
iterated literal splicing, `fableWordPrefixProfile`.  Three literal identities
then transport a paid row of the continuation to the shifted date:

* joint survival to date `depth + offset` at the prefixed profile factorizes
  as the word's own Continue product times the continuation's joint survival
  to `offset` (the note's (4.3));
* the pure-time payoff difference between two shifted deterministic quit times
  is the observer-deleted Continue product of the word times the original
  difference (the note's (4.4)); and
* under exact cap-Nash compatibility every terminal-semantic debt coordinate
  is scaled by the joint Continue product, hence is nonincreasing, so a global
  minimum sandwiches the prefixed total debt (the note's (4.5)).

Quantifier discipline.  The word is the root sequence of a
`QuittingPunishmentFloorFinitePrefix` certificate, so the checked table-uniform
floor `fableUniformSurvivalFloor` of `FableUniformWordSurvival` applies to it,
uniformly over certificates and depths.  The row data, its dates, and its
witnesses may depend on the source profile.  Compatibility is stated as one
inner-boundary equation: the certificate's `value 0` is the continuation's
prescribed cap; the running agreement at every later stage is derived, not
assumed.

Nothing here concerns the post-mark orientation obstruction of section 5.
-/
import FableUniformWordSurvival
import FableDebtActualReach
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapLiftedSummablePort

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Prefixing a supplied root word to a fixed actual continuation -/

/-- Prefix a supplied root word outward while retaining the continuation as
the literal suffix at every finite depth.  At depth `d` the profile plays
`word (d - 1)` at date `0`, ..., `word 0` at date `d - 1`, and then
`terminal`; this is the note's `q_{d-1} ⋆ ⋯ ⋆ q_0 ⋆ σ`. -/
noncomputable def fableWordPrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) :
    ℕ → (quittingGame reward).BehaviorProfile
  | 0 => terminal
  | depth + 1 => quittingRootThenContinuationProfile reward (word depth)
      (fableWordPrefixProfile reward word terminal depth)

omit [DecidableEq ι] in
@[simp] theorem fableWordPrefixProfile_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) :
    fableWordPrefixProfile reward word terminal 0 = terminal := rfl

omit [DecidableEq ι] in
@[simp] theorem fableWordPrefixProfile_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    fableWordPrefixProfile reward word terminal (depth + 1) =
      quittingRootThenContinuationProfile reward (word depth)
        (fableWordPrefixProfile reward word terminal depth) := rfl

/-! ## N1.  Joint survival factorizes through the prefixed word -/

omit [DecidableEq ι] in
private theorem fable_survivalPrefix_rootThenContinuation_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (fuel : ℕ) :
    quittingSurvivalPrefix (quittingProfileLiveRoot reward
        (quittingRootThenContinuationProfile reward root continuation))
        (fuel + 1) =
      quittingStationaryContinueMass root *
        quittingSurvivalPrefix
          (quittingProfileLiveRoot reward continuation) fuel := by
  unfold quittingSurvivalPrefix
  rw [Finset.prod_range_succ']
  simp [mul_comm]

omit [DecidableEq ι] in
/-- **Literal root-word factorization of joint survival.**  Joint survival of
the prefixed profile to date `depth + offset` is the word's own joint Continue
product times the continuation's joint survival to `offset`.  This is the
identity behind the note's (4.3); no compatibility of the word with the
continuation is used. -/
theorem fableWordPrefixProfile_survivalPrefix_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) (depth offset : ℕ) :
    quittingSurvivalPrefix (quittingProfileLiveRoot reward
        (fableWordPrefixProfile reward word terminal depth))
        (depth + offset) =
      quittingSurvivalPrefix word depth *
        quittingSurvivalPrefix
          (quittingProfileLiveRoot reward terminal) offset := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [fableWordPrefixProfile_succ,
        show depth + 1 + offset = (depth + offset) + 1 by omega,
        fable_survivalPrefix_rootThenContinuation_succ, ih,
        quittingSurvivalPrefix_succ]
      ring

omit [DecidableEq ι] in
private theorem fable_jointSurvivalWeight_zero_eq_survivalPrefix
    (rows : ℕ → ι → PMF Bool) (fuel : ℕ) :
    quittingJointSurvivalWeight rows 0 fuel = quittingSurvivalPrefix rows fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  exact Finset.prod_congr rfl (fun time _ => by simp only [Nat.zero_add])

omit [DecidableEq ι] in
/-- The same factorization in the checked joint-survival-weight vocabulary. -/
theorem fableWordPrefixProfile_jointSurvivalWeight_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) (depth offset : ℕ) :
    quittingJointSurvivalWeight (quittingProfileLiveRoot reward
        (fableWordPrefixProfile reward word terminal depth)) 0
        (depth + offset) =
      quittingJointSurvivalWeight word 0 depth *
        quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward terminal) 0 offset := by
  simp only [fable_jointSurvivalWeight_zero_eq_survivalPrefix]
  exact fableWordPrefixProfile_survivalPrefix_shift reward word terminal depth offset

namespace QuittingTerminalExploitabilityWitness

/-- The table-uniform word survival floor in survival-prefix vocabulary. -/
theorem fableUniformSurvivalFloor_le_prefixSurvivalPrefix
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    witness.fableUniformSurvivalFloor ≤
      quittingSurvivalPrefix cert.roots cert.horizon :=
  witness.fableUniformSurvivalFloor_le_prefixContinueProduct cert

/-- **(4.3).**  Prefixing a finite exact punishment-floor certificate to an
actual profile scales joint survival at the shifted date by at least the
table-uniform survival floor.  The floor holds for every certificate of every
depth; compatibility with the continuation is not used here, and is needed
only for the debt statements below. -/
theorem fableUniformSurvivalFloor_mul_le_wordPrefix_survivalPrefix
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile) (offset : ℕ) :
    witness.fableUniformSurvivalFloor *
        quittingSurvivalPrefix
          (quittingProfileLiveRoot reward terminal) offset ≤
      quittingSurvivalPrefix (quittingProfileLiveRoot reward
        (fableWordPrefixProfile reward cert.roots terminal cert.horizon))
        (cert.horizon + offset) := by
  rw [fableWordPrefixProfile_survivalPrefix_shift]
  exact mul_le_mul_of_nonneg_right
    (witness.fableUniformSurvivalFloor_le_prefixSurvivalPrefix cert)
    (quittingSurvivalPrefix_nonneg _ _)

/-- The same floor in joint-survival-weight vocabulary. -/
theorem fableUniformSurvivalFloor_mul_le_wordPrefix_jointSurvivalWeight
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile) (offset : ℕ) :
    witness.fableUniformSurvivalFloor *
        quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward terminal) 0 offset ≤
      quittingJointSurvivalWeight (quittingProfileLiveRoot reward
        (fableWordPrefixProfile reward cert.roots terminal cert.horizon)) 0
        (cert.horizon + offset) := by
  simp only [fable_jointSurvivalWeight_zero_eq_survivalPrefix]
  exact witness.fableUniformSurvivalFloor_mul_le_wordPrefix_survivalPrefix
    cert terminal offset

end QuittingTerminalExploitabilityWitness

/-! ## N2.  The shifted pure-time paid gap -/

private theorem fable_opponentSurvivalWeight_zero_eq_prod
    (word : ℕ → ι → PMF Bool) (who : ι) (depth : ℕ) :
    quittingOpponentSurvivalWeight word who 0 depth =
      ∏ time ∈ Finset.range depth,
        quittingStationaryFixedOpponentsContinueMass (word time) who := by
  unfold quittingOpponentSurvivalWeight
  refine Finset.prod_congr rfl (fun time _ => ?_)
  simp only [Nat.zero_add]
  rfl

private theorem fable_opponentSurvivalWeight_zero_succ
    (word : ℕ → ι → PMF Bool) (who : ι) (depth : ℕ) :
    quittingOpponentSurvivalWeight word who 0 (depth + 1) =
      quittingOpponentSurvivalWeight word who 0 depth *
        quittingStationaryFixedOpponentsContinueMass (word depth) who := by
  rw [quittingOpponentSurvivalWeight_succ]
  simp only [Nat.zero_add]
  rfl

/-- **Literal opponent-survival scaling of a shifted pure-time comparison.**
The difference of two shifted deterministic quit-time payoffs at the prefixed
profile is the observer-deleted Continue product of the word times the
original difference.  This is the identity behind the note's (4.4). -/
theorem fableWordPrefixProfile_pureTimeDeviationPayoff_sub_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (word : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (depth : ℕ) (first second : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
          (fableWordPrefixProfile reward word terminal depth) who
          (quittingCapLiftPureTimeShift depth first) -
        quittingPureTimeDeviationPayoff reward
          (fableWordPrefixProfile reward word terminal depth) who
          (quittingCapLiftPureTimeShift depth second) =
      quittingOpponentSurvivalWeight word who 0 depth *
        (quittingPureTimeDeviationPayoff reward terminal who first -
          quittingPureTimeDeviationPayoff reward terminal who second) := by
  induction depth with
  | zero =>
      rw [fableWordPrefixProfile_zero]
      simp [quittingCapLiftPureTimeShift, quittingOpponentSurvivalWeight]
  | succ depth ih =>
      rw [fableWordPrefixProfile_succ]
      have hshift : ∀ choice : Option ℕ,
          quittingCapLiftPureTimeShift (depth + 1) choice =
            quittingCapLiftPureTimeShift 1
              (quittingCapLiftPureTimeShift depth choice) := by
        intro choice
        cases choice with
        | none => rfl
        | some value =>
            simp [quittingCapLiftPureTimeShift, quittingAbsolutePureTime]
            omega
      rw [hshift first, hshift second,
        quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one,
        ih, fable_opponentSurvivalWeight_zero_succ]
      ring

namespace QuittingTerminalExploitabilityWitness

/-- Opponents-only survival through a certified word dominates joint survival,
so it carries the same table-uniform floor. -/
theorem fableUniformSurvivalFloor_le_prefixOpponentSurvivalWeight
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) (who : ι) :
    witness.fableUniformSurvivalFloor ≤
      quittingOpponentSurvivalWeight cert.roots who 0 cert.horizon := by
  refine (witness.fableUniformSurvivalFloor_le_prefixContinueProduct cert).trans ?_
  rw [fable_opponentSurvivalWeight_zero_eq_prod]
  exact Finset.prod_le_prod
    (fun time _ => quittingStationaryContinueMass_nonneg _)
    (fun time _ =>
      quittingStationaryContinueMass_le_fixedOpponentsContinueMass _ _)

/-- **(4.4).**  A nonnegative pure-time paid gap of the actual profile
survives every finite exact prefix certificate of every depth, scaled by at
least the table-uniform survival floor.  Compatibility with the continuation
is not used here. -/
theorem fableUniformSurvivalFloor_mul_le_wordPrefix_pureTimePayoff_sub
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (sourceTime receivingTime : Option ℕ) (gain : ℝ) (hgain : 0 ≤ gain)
    (hedge : gain ≤
      quittingPureTimeDeviationPayoff reward terminal who receivingTime -
        quittingPureTimeDeviationPayoff reward terminal who sourceTime) :
    witness.fableUniformSurvivalFloor * gain ≤
      quittingPureTimeDeviationPayoff reward
          (fableWordPrefixProfile reward cert.roots terminal cert.horizon) who
          (quittingCapLiftPureTimeShift cert.horizon receivingTime) -
        quittingPureTimeDeviationPayoff reward
          (fableWordPrefixProfile reward cert.roots terminal cert.horizon) who
          (quittingCapLiftPureTimeShift cert.horizon sourceTime) := by
  rw [fableWordPrefixProfile_pureTimeDeviationPayoff_sub_shift]
  exact (mul_le_mul_of_nonneg_right
      (witness.fableUniformSurvivalFloor_le_prefixOpponentSurvivalWeight
        cert who) hgain).trans
    (mul_le_mul_of_nonneg_left hedge
      (quittingOpponentSurvivalWeight_nonneg cert.roots who 0 cert.horizon))

end QuittingTerminalExploitabilityWitness

/-! ## N3.  Compatible prefixing and the debt sandwich -/

/-- The note's compatibility condition for a finite exact punishment-floor
certificate and the actual profile it is prefixed to: the certificate's inner
boundary is that profile's prescribed cap.  Agreement at every later stage is
derived from this and the certificate's own exact fields. -/
def IsFableCompatiblePrefixCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile) : Prop :=
  cert.value 0 = (quittingTerminalSemanticPair reward terminal).2

/-- Under compatibility the certificate's annotation at every certified stage
is the running prefixed profile's prescribed cap. -/
theorem fableCompatible_value_eq
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (time : ℕ) (htime : time ≤ cert.horizon) :
    cert.value time = (quittingTerminalSemanticPair reward
      (fableWordPrefixProfile reward cert.roots terminal time)).2 := by
  induction time with
  | zero => exact hcompat
  | succ time ih =>
      have hlt : time < cert.horizon := by omega
      have hprev := ih (by omega)
      have hnash := cert.exactNash time hlt
      rw [hprev] at hnash
      rw [cert.policy time hlt, hprev, fableWordPrefixProfile_succ,
        quittingTerminalSemanticPair_rootThenContinuation]
      exact (quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (quittingTerminalSemanticPair reward
          (fableWordPrefixProfile reward cert.roots terminal time))
        (cert.roots time) hnash).symm

/-- Under compatibility every certified root is exact cap-Nash against the
running prefixed profile's own cap. -/
theorem fableCompatible_exactNash
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (time : ℕ) (htime : time < cert.horizon) :
    IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal time)).2 0
      (cert.roots time) := by
  have hnash := cert.exactNash time htime
  rwa [fableCompatible_value_eq cert terminal hcompat time htime.le] at hnash

/-- One compatible prefix stage scales every debt coordinate by that stage's
joint Continue mass. -/
theorem fableCompatible_debt_succ
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (who : ι) (time : ℕ) (htime : time < cert.horizon) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal (time + 1))) who =
      quittingStationaryContinueMass (cert.roots time) *
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (fableWordPrefixProfile reward cert.roots terminal time)) who := by
  rw [fableWordPrefixProfile_succ,
    quittingTerminalSemanticPair_rootThenContinuation,
    quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal time))
      (cert.roots time) who
      (fableCompatible_exactNash cert terminal hcompat time htime)]

/-- Total debt of the compatibly prefixed profile is the word's joint Continue
product times the original total debt. -/
theorem fableCompatible_debtSum_eq
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (depth : ℕ) (hdepth : depth ≤ cert.horizon) :
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal depth)) =
      quittingSurvivalPrefix cert.roots depth *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      have hlt : depth < cert.horizon := by omega
      have hstep : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableWordPrefixProfile reward cert.roots terminal (depth + 1))) =
          quittingStationaryContinueMass (cert.roots depth) *
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (fableWordPrefixProfile reward cert.roots terminal depth)) := by
        unfold quittingTerminalSemanticDebtSum
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun who _ =>
          fableCompatible_debt_succ cert terminal hcompat who depth hlt)
      rw [hstep, ih (by omega), quittingSurvivalPrefix_succ]
      ring

/-- **(4.5), coordinatewise.**  Compatible exact prefixing makes every
semantic-debt coordinate nonincreasing in the prefix depth. -/
theorem fableCompatible_debt_le
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (who : ι) (depth : ℕ) (hdepth : depth ≤ cert.horizon) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal depth)) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward terminal) who := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      have hlt : depth < cert.horizon := by omega
      have hprev := ih (by omega)
      have hnonneg : 0 ≤ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (fableWordPrefixProfile reward cert.roots terminal depth)) who :=
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
          (quittingTerminalSemanticPair_mem_carrier reward _) who
      have hmass := quittingStationaryContinueMass_le_one (cert.roots depth)
      have hmassNonneg :=
        quittingStationaryContinueMass_nonneg (cert.roots depth)
      rw [fableCompatible_debt_succ cert terminal hcompat who depth hlt]
      nlinarith

/-- Total debt is likewise nonincreasing under compatible exact prefixing. -/
theorem fableCompatible_debtSum_le
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (depth : ℕ) (hdepth : depth ≤ cert.horizon) :
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (fableWordPrefixProfile reward cert.roots terminal depth)) ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_le_sum (fun who _ =>
    fableCompatible_debt_le cert terminal hcompat who depth hdepth)

/-- **(4.5).**  At a global minimum of total terminal-semantic debt, every
compatible finite exact prefix of every depth is sandwiched: its total debt is
at least the minimum and at most the source's. -/
theorem fableCompatible_debtSum_sandwich
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate, candidate ∈ quittingTerminalSemanticCarrier reward →
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (depth : ℕ) (hdepth : depth ≤ cert.horizon) :
    quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableWordPrefixProfile reward cert.roots terminal depth)) ∧
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableWordPrefixProfile reward cert.roots terminal depth)) ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) :=
  ⟨hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _),
    fableCompatible_debtSum_le cert terminal hcompat depth hdepth⟩

/-! ## N4.  The packaged shifted paid row -/

private theorem fable_shift_absolute_contradiction
    {depth start shiftedStart : ℕ} {later shiftedLater : Option ℕ}
    (hlater : IsQuittingStrictlyLaterDelay later)
    (hshiftedLater : IsQuittingStrictlyLaterDelay shiftedLater)
    (hfirst : quittingAbsolutePureTime shiftedStart shiftedLater =
      quittingCapLiftPureTimeShift depth (some start))
    (hsecond : (some shiftedStart : Option ℕ) =
      quittingCapLiftPureTimeShift depth
        (quittingAbsolutePureTime start later)) :
    False := by
  cases later with
  | none =>
      simp [quittingAbsolutePureTime, quittingCapLiftPureTimeShift] at hsecond
  | some delay =>
      have hdelay : 0 < delay := hlater
      cases shiftedLater with
      | none =>
          simp [quittingAbsolutePureTime,
            quittingCapLiftPureTimeShift] at hfirst
      | some shiftedDelay =>
          have hshiftedDelay : 0 < shiftedDelay := hshiftedLater
          simp [quittingAbsolutePureTime,
            quittingCapLiftPureTimeShift] at hfirst hsecond
          omega

/-- **The first disagreement of a witness-shifted row is shifted by exactly
the prefix depth.**  Only the two rows' chronology and strict-delay fields are
used, so this applies to any pair of profiles. -/
theorem fable_shiftedRow_start_eq
    {terminal receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {gain shiftedGain : ℝ} {depth : ℕ}
    (row : QuittingPaidFirstDisagreementRow reward terminal observer gain)
    (shifted : QuittingPaidFirstDisagreementRow reward receiving observer
      shiftedGain)
    (hsource : shifted.sourceWitness =
      quittingCapLiftPureTimeShift depth row.sourceWitness)
    (hreceiving : shifted.receivingWitness =
      quittingCapLiftPureTimeShift depth row.receivingWitness) :
    shifted.start = depth + row.start := by
  have hold := row.chronology
  have hnew := shifted.chronology
  cases hearlier : row.receivingEarlier with
  | false =>
      rw [hearlier] at hold
      cases hshiftedEarlier : shifted.receivingEarlier with
      | false =>
          rw [hshiftedEarlier] at hnew
          rw [hnew.1, hold.1] at hsource
          simpa [quittingCapLiftPureTimeShift,
            quittingAbsolutePureTime] using hsource
      | true =>
          rw [hshiftedEarlier] at hnew
          rw [hnew.2, hold.1] at hsource
          rw [hnew.1, hold.2] at hreceiving
          exact absurd (fable_shift_absolute_contradiction row.later_strict
            shifted.later_strict hsource hreceiving) not_false
  | true =>
      rw [hearlier] at hold
      cases hshiftedEarlier : shifted.receivingEarlier with
      | true =>
          rw [hshiftedEarlier] at hnew
          rw [hnew.1, hold.1] at hreceiving
          simpa [quittingCapLiftPureTimeShift,
            quittingAbsolutePureTime] using hreceiving
      | false =>
          rw [hshiftedEarlier] at hnew
          rw [hnew.2, hold.1] at hreceiving
          rw [hnew.1, hold.2] at hsource
          exact absurd (fable_shift_absolute_contradiction row.later_strict
            shifted.later_strict hreceiving hsource) not_false

namespace QuittingTerminalExploitabilityWitness

/-- **(4.3) and (4.4) at one shifted row.**  At any actual profile whose
observer carries continuation debt at least `Δ > 0`, and behind any finite
exact punishment-floor certificate of any depth, the shifted paid row has pure
-time gain at least `λ · Δ / 4` and joint entry at its own start date at least
`λ · Δ² / (32 M²)`.  Both floors are uniform in the certificate and its depth.
-/
theorem fable_positiveDebt_wordPrefix_exists_shifted_paidRow
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤
      quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ shifted : QuittingPaidFirstDisagreementRow reward
        (fableWordPrefixProfile reward cert.roots profile cert.horizon)
        observer (witness.fableUniformSurvivalFloor * (Δ / 4)),
      witness.fableUniformSurvivalFloor * (Δ * Δ) ≤
        32 * quittingRewardBound reward * quittingRewardBound reward *
          quittingSurvivalPrefix (quittingProfileLiveRoot reward
            (fableWordPrefixProfile reward cert.roots profile cert.horizon))
            shifted.start := by
  obtain ⟨row, hreach⟩ :=
    positiveDebt_exists_actualJointReach_paidFirstDisagreementRow reward
      profile observer Δ hΔ hdebt
  have hfloorPos := witness.fableUniformSurvivalFloor_pos
  have hgainPos : 0 < witness.fableUniformSurvivalFloor * (Δ / 4) :=
    mul_pos hfloorPos (by linarith)
  have hedge : Δ / 4 ≤
      quittingPureTimeDeviationPayoff reward profile observer
          row.receivingWitness -
        quittingPureTimeDeviationPayoff reward profile observer
          row.sourceWitness :=
    row.gain_le_paid.trans_eq row.edge_identity.symm
  obtain ⟨shifted, hsource, hreceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward
      (fableWordPrefixProfile reward cert.roots profile cert.horizon) observer
      (quittingCapLiftPureTimeShift cert.horizon row.sourceWitness)
      (quittingCapLiftPureTimeShift cert.horizon row.receivingWitness)
      (witness.fableUniformSurvivalFloor * (Δ / 4)) hgainPos
      (witness.fableUniformSurvivalFloor_mul_le_wordPrefix_pureTimePayoff_sub
        cert profile observer row.sourceWitness row.receivingWitness (Δ / 4)
        (by linarith) hedge)
  refine ⟨shifted, ?_⟩
  rw [fable_shiftedRow_start_eq row shifted hsource hreceiving]
  have hbound : 0 ≤ 32 * quittingRewardBound reward *
      quittingRewardBound reward := by
    nlinarith [mul_self_nonneg (quittingRewardBound reward)]
  calc witness.fableUniformSurvivalFloor * (Δ * Δ)
      ≤ witness.fableUniformSurvivalFloor *
          (32 * quittingRewardBound reward * quittingRewardBound reward *
            quittingSurvivalPrefix
              (quittingProfileLiveRoot reward profile) row.start) :=
        mul_le_mul_of_nonneg_left hreach hfloorPos.le
    _ = 32 * quittingRewardBound reward * quittingRewardBound reward *
          (witness.fableUniformSurvivalFloor *
            quittingSurvivalPrefix
              (quittingProfileLiveRoot reward profile) row.start) := by ring
    _ ≤ 32 * quittingRewardBound reward * quittingRewardBound reward *
          quittingSurvivalPrefix (quittingProfileLiveRoot reward
            (fableWordPrefixProfile reward cert.roots profile cert.horizon))
            (cert.horizon + row.start) :=
        mul_le_mul_of_nonneg_left
          (witness.fableUniformSurvivalFloor_mul_le_wordPrefix_survivalPrefix
            cert profile row.start) hbound

/-- **The section 4 composition packet.**  Behind any compatible finite exact
punishment-floor certificate of any depth, a near-minimum actual source
co-realizes a shifted paid row of gain `λ · Δ / 4`, a joint entry floor
`λ · Δ² / (32 M²)` at that row's own start date, and a total debt sandwiched
between the global minimum and the source's own debt.  The three floors are
uniform over compatible certificates and depths; the row and its dates depend
on the source. -/
theorem fable_positiveDebt_compatibleWord_shifted_paidRow_and_debtSandwich
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤
      quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer)
    (hcompat : IsFableCompatiblePrefixCertificate reward cert profile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate, candidate ∈ quittingTerminalSemanticCarrier reward →
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ shifted : QuittingPaidFirstDisagreementRow reward
        (fableWordPrefixProfile reward cert.roots profile cert.horizon)
        observer (witness.fableUniformSurvivalFloor * (Δ / 4)),
      witness.fableUniformSurvivalFloor * (Δ * Δ) ≤
          32 * quittingRewardBound reward * quittingRewardBound reward *
            quittingSurvivalPrefix (quittingProfileLiveRoot reward
              (fableWordPrefixProfile reward cert.roots profile cert.horizon))
              shifted.start ∧
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableWordPrefixProfile reward cert.roots profile
              cert.horizon)) ∧
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableWordPrefixProfile reward cert.roots profile cert.horizon)) ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) := by
  obtain ⟨shifted, hentry⟩ :=
    witness.fable_positiveDebt_wordPrefix_exists_shifted_paidRow cert profile
      observer Δ hΔ hdebt
  obtain ⟨hlower, hupper⟩ := fableCompatible_debtSum_sandwich cert profile
    hcompat minimum hminimum cert.horizon le_rfl
  exact ⟨shifted, hentry, hlower, hupper⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
