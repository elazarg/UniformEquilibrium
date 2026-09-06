import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumForwardTrichotomy
import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumUniformPayoffEquivalence
import UniformEquilibrium.Quitting.Classification.InstantPunishmentSureQuitterPayoff
import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketTranslation
import UniformEquilibrium.Quitting.Projective.SequentiallyPerfectAbsorbingForwardPacket
import UniformEquilibrium.Quitting.Projective.StationaryAbsorptionWeightedForwardPacket

/-! # Fixed-box forward characterization for normal four-player quitting games

Under normality and one positive singleton payoff, uniform-payoff existence is
equivalent to either absorption-weighted finite forward packets in the fixed
reward box enlarged by two or the finite exact sure-root condition. The
sure-root arm is consumed through its literal payoff theorem; no repeatability
of that root is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingLCPClassification

private theorem rewardBound_pos_of_positiveSingleton
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    0 < rewardBound := by
  obtain ⟨who, hsingleton⟩ := hpositive
  have hle := hreward (quittingSingletonTerminal who) who
  linarith [le_abs_self (reward (quittingSingletonTerminal who) who)]

/-- For normal four-player quitting games with a positive singleton payoff,
uniform-payoff existence is equivalent to the fixed-box weighted-packet arm
or the finite exact sure-root arm. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) ∨
        HasQuittingPunishmentVectorNashRootWithSureQuitter reward := by
  let table := repositoryQuittingPayoffTable reward
  have hzeroReward : table.zeroNeverReward = reward := by
    funext terminal player
    simp [table, QuittingPayoffTable.zeroNeverReward,
      repositoryQuittingPayoffTable]
  constructor
  · intro huniform
    have htableUniform : ∃ payoff : Payoff (Fin 4),
        (quittingGame table.zeroNeverReward).IsUniformEquilibriumPayoff none payoff := by
      rw [hzeroReward]
      exact huniform
    have happrox :=
      (table.approximateEquilibriumExistence_iff_exists_zeroNeverUniformPayoff).2
        htableUniform
    rcases table.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing
      happrox with hstationary | hinstant | hsequential
    · left
      have hstationaryRaw := (table.stationaryεEquilibriumExistence_iff).1
        hstationary
      rw [hzeroReward] at hstationaryRaw
      exact hasAbsorptionWeightedFiniteForwardPackets_of_stationary reward
        rewardBound hreward hstationaryRaw hpositive
    · right
      have hinstantRaw := (table.instantPunishmentεEquilibriumExistence_iff).1
        hinstant
      rw [hzeroReward] at hinstantRaw
      exact
        (quittingInstantPunishmentεEquilibriumExistence_iff_sureQuitterPunishmentVectorNashRoot
          reward).1 hinstantRaw
    · left
      have hsequentialRaw :=
        (table.sequentiallyεPerfectAbsorbingExistence_iff).1 hsequential
      rw [hzeroReward] at hsequentialRaw
      exact hasAbsorptionWeightedFiniteForwardPackets_of_exact reward rewardBound
        (hasExactFiniteForwardPackets_of_normal_of_sequentiallyPerfect reward
          rewardBound hreward hnormal hsequentialRaw hpositive)
  · intro hbranches
    rcases hbranches with hweighted | hsureRoot
    · have hrewardBound :=
        rewardBound_pos_of_positiveSingleton reward rewardBound hreward hpositive
      exact quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets
        reward (rewardBound + 2) (by linarith)
          (fun terminal player ↦ (hreward terminal player).trans (by linarith))
          hweighted
    · obtain ⟨_quitter, _root, _hquit, _hdefect, huniform, _hfloor⟩ :=
        exists_punishmentSureRootTarget_of_hasPunishmentVectorNashRootWithSureQuitter
          reward hsureRoot
      exact ⟨_, huniform⟩

/-- If the finite sure-root alternative fails, every uniform payoff existence
witness produces weighted packets in the same fixed enlarged reward box. -/
theorem hasFixedBoxPackets_of_uniformEquilibriumPayoff_of_noSureRoot
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hpositive : ∃ who, 0 < reward (quittingSingletonTerminal who) who)
    (huniform : ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnoSureRoot : ¬ HasQuittingPunishmentVectorNashRootWithSureQuitter reward) :
    HasAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) := by
  rcases
      (quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot
        reward rewardBound hreward hnormal hpositive).1 huniform with
    hweighted | hsureRoot
  · exact hweighted
  · exact False.elim (hnoSureRoot hsureRoot)

end GameTheory

