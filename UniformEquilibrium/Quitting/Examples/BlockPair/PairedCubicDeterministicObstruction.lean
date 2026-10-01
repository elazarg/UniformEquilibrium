import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCubicStationaryExample
import UniformEquilibrium.Quitting.Paths.PureTimeMembershipToggleObstruction

/-! # Literal coalition toggles in the paired cubic table

The canonical complete pure-clock consumer retains every hidden later date and
Never. These obstructions do not negate mixed terminal Nash or uniform equilibrium.
Recipient shifts preserve nonempty toggle gains, but Never is checked separately.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

open Math.Finset

def toggleOwner (row : Fin 15) : Fin 4 :=
  ![3, 3, 0, 0, 2, 2, 0, 0, 2, 2, 0, 3, 0, 1, 0] row

def toggleGain (row : Fin 15) : ℝ :=
  ![3, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5, 4, 4, 1] row

def toggledCoalition (row : Fin 15) : Finset (Fin 4) :=
  if toggleOwner row ∈ finFourCoalitionOfRow row then
    (finFourCoalitionOfRow row).erase (toggleOwner row)
  else insert (toggleOwner row) (finFourCoalitionOfRow row)

theorem toggledCoalition_nonempty (row : Fin 15) : (toggledCoalition row).Nonempty := by
  fin_cases row <;>
    norm_num +decide [toggledCoalition, toggleOwner, finFourCoalitionOfRow]

theorem toggle_reward_difference (row : Fin 15) :
    reward ⟨toggledCoalition row, toggledCoalition_nonempty row⟩ (toggleOwner row) -
      reward (finFourCoalitionRowEquiv row) (toggleOwner row) = toggleGain row := by
  fin_cases row <;>
    norm_num +decide [toggledCoalition, toggleOwner, toggleGain, finFourCoalitionRowEquiv,
      finFourCoalitionOfRow, reward, rationalQuittingRewardToReal, rationalReward]

theorem toggleGain_one_le (row : Fin 15) : 1 ≤ toggleGain row := by
  fin_cases row <;> norm_num [toggleGain]

theorem literalToggleGap_one : HasQuittingPureTimeMembershipToggleGap reward 1 := by
  constructor
  · exact ⟨0, by norm_num +decide [reward, rationalQuittingRewardToReal, rationalReward]⟩
  · intro coalition
    obtain ⟨row, rfl⟩ := finFourCoalitionRowEquiv.surjective coalition
    let owner := toggleOwner row
    have hgain := toggle_reward_difference row
    have hlower := toggleGain_one_le row
    by_cases hmember : owner ∈ finFourCoalitionOfRow row
    · have hremaining : ((finFourCoalitionOfRow row).erase owner).Nonempty := by
        simpa only [toggledCoalition, owner, ite_eq_left hmember]
          using toggledCoalition_nonempty row
      right
      refine ⟨owner, hmember, hremaining, ?_⟩
      change reward (finFourCoalitionRowEquiv row) owner + 1 ≤
        reward ⟨(finFourCoalitionOfRow row).erase owner, hremaining⟩ owner
      have htoggled : toggledCoalition row = (finFourCoalitionOfRow row).erase owner :=
        ite_eq_left hmember
      have hterminal :
          (⟨toggledCoalition row, toggledCoalition_nonempty row⟩ :
            {S : Finset (Fin 4) // S.Nonempty}) =
          ⟨(finFourCoalitionOfRow row).erase owner, hremaining⟩ := Subtype.ext htoggled
      rw [hterminal] at hgain
      change _ - _ = toggleGain row at hgain
      linarith
    · left
      refine ⟨owner, hmember, ?_⟩
      change reward (finFourCoalitionRowEquiv row) owner + 1 ≤
        reward ⟨insert owner (finFourCoalitionOfRow row),
          Finset.insert_nonempty owner (finFourCoalitionOfRow row)⟩ owner
      have htoggled : toggledCoalition row =
          insert owner (finFourCoalitionOfRow row) := ite_eq_right hmember
      have hterminal :
          (⟨toggledCoalition row, toggledCoalition_nonempty row⟩ :
            {S : Finset (Fin 4) // S.Nonempty}) =
          ⟨insert owner (finFourCoalitionOfRow row),
            Finset.insert_nonempty owner (finFourCoalitionOfRow row)⟩ :=
        Subtype.ext htoggled
      rw [hterminal] at hgain
      change _ - _ = toggleGain row at hgain
      linarith

private theorem affine_literalToggleGap (scale : ℝ) (hscale : 0 < scale)
    (shift : Payoff (Fin 4)) (hshift : 0 ≤ shift 0) :
    HasQuittingPureTimeMembershipToggleGap
      (quittingPlayerwiseAffineReward reward (fun _ => scale) shift) scale := by
  constructor
  · refine ⟨0, ?_⟩
    have hsolo : reward (quittingSingletonTerminal 0) 0 = 1 := by
      norm_num +decide [reward, rationalQuittingRewardToReal, rationalReward,
        quittingSingletonTerminal]
    change scale ≤ scale * reward (quittingSingletonTerminal 0) 0 + shift 0
    rw [hsolo, mul_one]
    linarith
  · intro coalition
    rcases literalToggleGap_one.toggle coalition with
      ⟨outsider, hnot, hgain⟩ | ⟨member, hmem, hremaining, hgain⟩
    · left
      refine ⟨outsider, hnot, ?_⟩
      have hscaled := mul_le_mul_of_nonneg_left hgain hscale.le
      change scale * reward coalition outsider + shift outsider + scale ≤
        scale * reward
          ⟨insert outsider coalition.1, Finset.insert_nonempty outsider coalition.1⟩
          outsider + shift outsider
      nlinarith only [hscaled]
    · right
      refine ⟨member, hmem, hremaining, ?_⟩
      have hscaled := mul_le_mul_of_nonneg_left hgain hscale.le
      change scale * reward coalition member + shift member + scale ≤
        scale * reward ⟨coalition.1.erase member, hremaining⟩ member + shift member
      nlinarith only [hscaled]

theorem canonical_literalToggleGap_one :
    HasQuittingPureTimeMembershipToggleGap canonicalReward 1 := by
  exact affine_literalToggleGap 1 (by norm_num) canonicalShift (by norm_num [canonicalShift])

theorem normalized_literalToggleGap_quarter :
    HasQuittingPureTimeMembershipToggleGap normalizedReward (1 / 4) := by
  exact affine_literalToggleGap (1 / 4) (by norm_num)
    (fun who => canonicalShift who / 4) (by norm_num [canonicalShift])

/-- Every complete deterministic clock profile fails exact terminal Nash. -/
theorem not_exact_terminalNash_pureTime (times : QuittingPureTimeProfile (Fin 4)) :
    ¬(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingPureTimeProfileBehavior reward times) :=
  literalToggleGap_one.not_isεAsymptoticNash_zero (by norm_num) times

theorem canonical_not_exact_terminalNash_pureTime
    (times : QuittingPureTimeProfile (Fin 4)) :
    ¬(quittingGame canonicalReward).IsεAsymptoticNash
      (quittingTerminalPayoff canonicalReward) 0
      (quittingPureTimeProfileBehavior canonicalReward times) :=
  canonical_literalToggleGap_one.not_isεAsymptoticNash_zero (by norm_num) times

theorem normalized_not_exact_terminalNash_pureTime
    (times : QuittingPureTimeProfile (Fin 4)) :
    ¬(quittingGame normalizedReward).IsεAsymptoticNash
      (quittingTerminalPayoff normalizedReward) 0
      (quittingPureTimeProfileBehavior normalizedReward times) :=
  normalized_literalToggleGap_quarter.not_isεAsymptoticNash_zero (by norm_num) times

end GameTheory.PairedCubicStationaryExample
