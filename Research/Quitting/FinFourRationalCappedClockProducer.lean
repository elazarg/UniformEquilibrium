/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockChildProducer
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFinFourExistence
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderRestriction

/-!
# Rational child search with a literal capped-clock parent consumer

For a rational Fin4 table, an owner is displayed as the `none` player by the
same reindexing used by the capped-clock existence criterion. A checked
child-only code is transported to the literal deleted child of that reindexed
parent and then lifted by the supplied capped-clock certificate.

The executable threshold is `error / amplification`. The amplification is a
positive rational number supplied together with a proof that it bounds the
certificate's real multiplier. Thus the search comparison remains exact
rational arithmetic even when the certificate itself has real weights.
-/

noncomputable section

namespace GameTheory

open StochasticGame

namespace FinFourRationalCappedClockProducer

open FinFourRationalFiniteClockChildProducer

/-- The survivor equivalence induced by displaying `owner` as the `none`
coordinate of `Option (QuittingDeletedPlayer owner)`. -/
def ownerChildEquiv (owner : Fin 4) :
    {who : Fin 4 // who ≠ owner} ≃
      {who : Option {who : Fin 4 // who ≠ owner} // who ≠ none} :=
  quittingChildSomeEquiv (fun player => player = owner)

private instance ownerOptionChildNonempty (owner : Fin 4) :
    Nonempty {who : Option {who : Fin 4 // who ≠ owner} // who ≠ none} := by
  fin_cases owner
  · exact ⟨⟨some ⟨1, by decide⟩, Option.some_ne_none _⟩⟩
  all_goals exact ⟨⟨some ⟨0, by decide⟩, Option.some_ne_none _⟩⟩

/-- Deleting `none` from the literal owner-reindexed Fin4 table is exactly the
reindexing of the original owner-deleted table along `ownerChildEquiv`. -/
theorem quittingDeleteReward_finFourOwnerOptionReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) :
    quittingDeleteReward (quittingFinFourOwnerOptionReward reward owner)
        (fun who => who = none) =
      quittingRewardReindex (ownerChildEquiv owner)
        (quittingDeleteReward reward (fun player => player = owner)) := by
  funext coalition who
  change reward _ _ = reward _ _
  congr 1
  · apply Subtype.ext
    ext player
    by_cases hplayer : player = owner
    · subst player
      simp [quittingExtendDeletedCoalition, quittingCoalitionEquiv,
        ownerChildEquiv, quittingChildSomeEquiv, Finset.mem_map_equiv]
    · simp [quittingExtendDeletedCoalition, quittingCoalitionEquiv,
        ownerChildEquiv, quittingChildSomeEquiv, Finset.mem_map_equiv, hplayer]
  · cases hwho : who.1 with
    | none => exact absurd hwho who.2
    | some child =>
        simp [ownerChildEquiv, quittingChildSomeEquiv, hwho]

/-- Transport an actual profile of the original owner-deleted game to the
literal deleted child of the owner-reindexed parent table. -/
def ownerOptionChildProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (profile : (quittingGame
      (quittingDeleteReward reward (fun player => player = owner))).BehaviorProfile) :
    (quittingGame
      (quittingDeleteReward (quittingFinFourOwnerOptionReward reward owner)
        (fun who => who = none))).BehaviorProfile :=
  quittingProfileOfRewardEq
    (quittingDeleteReward_finFourOwnerOptionReward reward owner)
    (quittingProfilePushforward (ownerChildEquiv owner)
      (quittingDeleteReward reward (fun player => player = owner)) profile)

/-- Pull the literal quiet lift of the displayed owner back to the original
Fin4 labels. -/
def ownerRawParentProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (profile : (quittingGame
      (quittingDeleteReward reward (fun player => player = owner))).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingProfilePullback (Equiv.optionSubtypeNe owner).symm reward
    (quittingLiftDeletedProfile
      (quittingFinFourOwnerOptionReward reward owner)
      (fun who => who = none)
      (ownerOptionChildProfile reward owner profile))

/-- The owner is exactly deterministic Never in the pulled-back raw Fin4
parent profile. -/
theorem quittingBehaviorStoppingLaw_ownerRawParentProfile_owner
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (profile : (quittingGame
      (quittingDeleteReward reward (fun player => player = owner))).BehaviorProfile) :
    quittingBehaviorStoppingLaw reward
        (ownerRawParentProfile reward owner profile owner) = PMF.pure none := by
  let reindex : Fin 4 ≃ Option {who : Fin 4 // who ≠ owner} :=
    (Equiv.optionSubtypeNe owner).symm
  let optionProfile := quittingLiftDeletedProfile
    (quittingFinFourOwnerOptionReward reward owner)
    (fun who => who = none) (ownerOptionChildProfile reward owner profile)
  change quittingBehaviorStoppingLaw reward
      (quittingProfilePullback reindex reward optionProfile owner) = PMF.pure none
  calc
    _ = quittingBehaviorStoppingLaw
        (quittingFinFourOwnerOptionReward reward owner)
        (optionProfile (reindex owner)) :=
      quittingBehaviorStoppingLaw_profilePullback reindex reward optionProfile owner
    _ = quittingBehaviorStoppingLaw
        (quittingFinFourOwnerOptionReward reward owner)
        (optionProfile none) := by
      rw [show reindex owner = none from
        Equiv.optionSubtypeNe_symm_self owner]
    _ = PMF.pure none :=
      quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
        (quittingFinFourOwnerOptionReward reward owner)
        (fun who => who = none) (ownerOptionChildProfile reward owner profile) rfl

/-- Pulling the displayed parent profile back to the original Fin4 labels
preserves unrestricted terminal exploitability exactly. -/
theorem quittingTerminalExploitability_ownerRawParentProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (profile : (quittingGame
      (quittingDeleteReward reward (fun player => player = owner))).BehaviorProfile) :
    quittingTerminalExploitability reward
        (ownerRawParentProfile reward owner profile) =
      quittingTerminalExploitability
        (quittingFinFourOwnerOptionReward reward owner)
        (quittingLiftDeletedProfile
          (quittingFinFourOwnerOptionReward reward owner)
          (fun who => who = none)
          (ownerOptionChildProfile reward owner profile)) := by
  exact quittingTerminalExploitability_profilePullback
    (Equiv.optionSubtypeNe owner).symm reward
      (quittingLiftDeletedProfile
        (quittingFinFourOwnerOptionReward reward owner)
        (fun who => who = none)
        (ownerOptionChildProfile reward owner profile))

/-- The literal deleted-child transport preserves unrestricted terminal
exploitability exactly. -/
theorem quittingTerminalExploitability_ownerOptionChildProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4)
    (profile : (quittingGame
      (quittingDeleteReward reward (fun player => player = owner))).BehaviorProfile) :
    quittingTerminalExploitability
        (quittingDeleteReward (quittingFinFourOwnerOptionReward reward owner)
          (fun who => who = none))
        (ownerOptionChildProfile reward owner profile) =
      quittingTerminalExploitability
        (quittingDeleteReward reward (fun player => player = owner)) profile := by
  let childReward :=
    quittingDeleteReward reward (fun player => player = owner)
  let optionChildReward :=
    quittingDeleteReward (quittingFinFourOwnerOptionReward reward owner)
      (fun who => who = none)
  let transported := ownerOptionChildProfile reward owner profile
  have hgap (who : {who : Fin 4 // who ≠ owner}) :
      max 0
          (quittingBehaviorDeviationPayoffCap optionChildReward transported
              (ownerChildEquiv owner who) -
            quittingTerminalPayoff optionChildReward transported
              (ownerChildEquiv owner who)) =
        max 0
          (quittingBehaviorDeviationPayoffCap childReward profile who -
            quittingTerminalPayoff childReward profile who) := by
    unfold transported ownerOptionChildProfile optionChildReward childReward
    rw [quittingBehaviorDeviationPayoffCap_profileOfRewardEq,
      quittingTerminalPayoff_profileOfRewardEq,
      quittingBehaviorDeviationPayoffCap_profilePushforward,
      quittingTerminalPayoff_profilePushforward]
  unfold quittingTerminalExploitability
    QuittingBoundaryHolonomy.finitePlayerMax
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro optionWho _
    let who := (ownerChildEquiv owner).symm optionWho
    change max 0
        (quittingBehaviorDeviationPayoffCap optionChildReward transported
            optionWho -
          quittingTerminalPayoff optionChildReward transported optionWho) ≤ _
    rw [← (ownerChildEquiv owner).apply_symm_apply optionWho, hgap who]
    exact Finset.le_sup'
      (fun candidate : {who : Fin 4 // who ≠ owner} =>
        max 0
          (quittingBehaviorDeviationPayoffCap childReward profile candidate -
            quittingTerminalPayoff childReward profile candidate))
      (Finset.mem_univ who)
  · apply Finset.sup'_le Finset.univ_nonempty
    intro who _
    change max 0
        (quittingBehaviorDeviationPayoffCap childReward profile who -
          quittingTerminalPayoff childReward profile who) ≤ _
    rw [← hgap who]
    exact Finset.le_sup'
      (fun candidate :
          {who : Option {who : Fin 4 // who ≠ owner} // who ≠ none} =>
        max 0
          (quittingBehaviorDeviationPayoffCap optionChildReward transported
              candidate -
            quittingTerminalPayoff optionChildReward transported candidate))
      (Finset.mem_univ (ownerChildEquiv owner who))

/-- The literal rational algorithm: search at the exact child threshold
`error / amplification`, decode the actual child, transport it to the literal
owner-reindexed child, and append deterministic Never. The supplied rational
amplification bounds the capped-clock certificate's real multiplier. -/
theorem exists_checkedChildCandidateAt_and_parentTerminalNash
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (certificate : CappedClockParentRewardCertificate
      (quittingFinFourOwnerOptionReward reward.realReward owner))
    (error amplification : ℚ) (herror : 0 < error)
    (hamplificationBound :
      max 1 (∑ player, certificate.weight player) ≤ (amplification : ℝ)) :
    ∃ stage, ∃ code : RationalFinFourFiniteClockProfileCode,
      ∃ hvalid : code.Valid,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt reward owner
          (error / amplification) stage = some code ∧
        0 < code.clockBound ∧
        (∀ atom, code.mass owner atom = if atom = none then 1 else 0) ∧
        (quittingGame
          (quittingFinFourOwnerOptionReward reward.realReward owner)).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingFinFourOwnerOptionReward reward.realReward owner))
          (error : ℝ)
          (quittingLiftDeletedProfile
            (quittingFinFourOwnerOptionReward reward.realReward owner)
            (fun who => who = none)
            (ownerOptionChildProfile reward.realReward owner
              (code.toDeletedChildProfile reward hvalid owner))) := by
  have hamplificationReal : 0 < (amplification : ℝ) :=
    lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 (∑ player, certificate.weight player)).trans
        hamplificationBound)
  have hamplification : 0 < amplification := by
    exact_mod_cast hamplificationReal
  have hthreshold : 0 < error / amplification := div_pos herror hamplification
  obtain ⟨stage, code, hrow, hclock, hpureMass⟩ :=
    exists_checkedChildCandidateAt reward owner
      (error / amplification) hthreshold
  obtain ⟨hvalid, _, hexploit⟩ :=
    RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt_sound
      reward owner (error / amplification) stage code hrow
  let childProfile := code.toDeletedChildProfile reward hvalid owner
  let optionChildProfile := ownerOptionChildProfile reward.realReward owner
    childProfile
  have hoptionExploit : quittingTerminalExploitability
      (quittingDeleteReward
        (quittingFinFourOwnerOptionReward reward.realReward owner)
        (fun who => who = none)) optionChildProfile <
      ((error / amplification : ℚ) : ℝ) := by
    rw [quittingTerminalExploitability_ownerOptionChildProfile]
    exact hexploit
  have hchildNash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    optionChildProfile hoptionExploit.le
  have hthresholdNonneg : 0 ≤ ((error / amplification : ℚ) : ℝ) := by
    exact_mod_cast hthreshold.le
  have hparentNash := isεAsymptoticNash_quietLift_of_cappedClockCertificate
    (quittingFinFourOwnerOptionReward reward.realReward owner) certificate
    hthresholdNonneg optionChildProfile hchildNash
  have hcastThreshold : ((error / amplification : ℚ) : ℝ) =
      (error : ℝ) / (amplification : ℝ) := by
    norm_cast
  have hscaled :
      max 1 (∑ player, certificate.weight player) *
          ((error / amplification : ℚ) : ℝ) ≤ (error : ℝ) := by
    calc
      _ ≤ (amplification : ℝ) *
          ((error / amplification : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hamplificationBound hthresholdNonneg
      _ = (error : ℝ) := by
        rw [hcastThreshold]
        field_simp [hamplificationReal.ne']
  refine ⟨stage, code, hvalid, hrow, hclock, hpureMass, ?_⟩
  exact StochasticGame.IsεAsymptoticNash.mono hparentNash hscaled

/-- The checked child search produces a terminal approximate Nash profile for
the original raw Fin4 table, with the selected owner exactly Never. -/
theorem exists_checkedChildCandidateAt_and_rawParentTerminalNash
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (certificate : CappedClockParentRewardCertificate
      (quittingFinFourOwnerOptionReward reward.realReward owner))
    (error amplification : ℚ) (herror : 0 < error)
    (hamplificationBound :
      max 1 (∑ player, certificate.weight player) ≤ (amplification : ℝ)) :
    ∃ stage, ∃ code : RationalFinFourFiniteClockProfileCode,
      ∃ hvalid : code.Valid,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt reward owner
          (error / amplification) stage = some code ∧
        0 < code.clockBound ∧
        (∀ atom, code.mass owner atom = if atom = none then 1 else 0) ∧
        (quittingGame reward.realReward).IsεAsymptoticNash
          (quittingTerminalPayoff reward.realReward) (error : ℝ)
          (ownerRawParentProfile reward.realReward owner
            (code.toDeletedChildProfile reward hvalid owner)) ∧
        quittingBehaviorStoppingLaw reward.realReward
            (ownerRawParentProfile reward.realReward owner
              (code.toDeletedChildProfile reward hvalid owner) owner) =
          PMF.pure none := by
  obtain ⟨stage, code, hvalid, hrow, hclock, hpureMass, hoptionNash⟩ :=
    exists_checkedChildCandidateAt_and_parentTerminalNash reward owner
      certificate error amplification herror hamplificationBound
  let childProfile := code.toDeletedChildProfile reward hvalid owner
  let optionProfile := quittingLiftDeletedProfile
    (quittingFinFourOwnerOptionReward reward.realReward owner)
    (fun who => who = none)
    (ownerOptionChildProfile reward.realReward owner childProfile)
  have herrorNonneg : 0 ≤ (error : ℝ) := by
    exact_mod_cast herror.le
  have hoptionExploit : quittingTerminalExploitability
      (quittingFinFourOwnerOptionReward reward.realReward owner)
      optionProfile ≤ (error : ℝ) := by
    exact quittingTerminalExploitability_le_of_isεAsymptoticNash
      (quittingFinFourOwnerOptionReward reward.realReward owner)
      optionProfile herrorNonneg hoptionNash
  have hrawExploit : quittingTerminalExploitability reward.realReward
      (ownerRawParentProfile reward.realReward owner childProfile) ≤
        (error : ℝ) := by
    rw [quittingTerminalExploitability_ownerRawParentProfile]
    exact hoptionExploit
  have hrawNash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (ownerRawParentProfile reward.realReward owner childProfile) hrawExploit
  refine ⟨stage, code, hvalid, hrow, hclock, hpureMass, hrawNash, ?_⟩
  exact quittingBehaviorStoppingLaw_ownerRawParentProfile_owner
    reward.realReward owner childProfile

/-- A real capped-clock certificate always admits a rational amplification
bound, so the original-table producer has no hidden rational-bound input. -/
theorem exists_rationalAmplification_checkedChildCandidateAt_and_rawParentTerminalNash
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (certificate : CappedClockParentRewardCertificate
      (quittingFinFourOwnerOptionReward reward.realReward owner))
    (error : ℚ) (herror : 0 < error) :
    ∃ amplification : ℚ,
      max 1 (∑ player, certificate.weight player) ≤ (amplification : ℝ) ∧
      ∃ stage, ∃ code : RationalFinFourFiniteClockProfileCode,
        ∃ hvalid : code.Valid,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt reward owner
          (error / amplification) stage = some code ∧
        0 < code.clockBound ∧
        (∀ atom, code.mass owner atom = if atom = none then 1 else 0) ∧
        (quittingGame reward.realReward).IsεAsymptoticNash
          (quittingTerminalPayoff reward.realReward) (error : ℝ)
          (ownerRawParentProfile reward.realReward owner
            (code.toDeletedChildProfile reward hvalid owner)) ∧
        quittingBehaviorStoppingLaw reward.realReward
            (ownerRawParentProfile reward.realReward owner
              (code.toDeletedChildProfile reward hvalid owner) owner) =
          PMF.pure none := by
  obtain ⟨naturalBound, hnaturalBound⟩ :=
    exists_nat_gt (max 1 (∑ player, certificate.weight player))
  let amplification : ℚ := naturalBound
  have hamplificationBound :
      max 1 (∑ player, certificate.weight player) ≤ (amplification : ℝ) := by
    simpa only [amplification, Rat.cast_natCast] using hnaturalBound.le
  obtain ⟨stage, code, hvalid, hrow, hclock, hpureMass, hrawNash,
      hownerNever⟩ :=
    exists_checkedChildCandidateAt_and_rawParentTerminalNash reward owner
      certificate error amplification herror hamplificationBound
  exact ⟨amplification, hamplificationBound, stage, code, hvalid, hrow,
    hclock, hpureMass, hrawNash, hownerNever⟩

end FinFourRationalCappedClockProducer

end GameTheory
