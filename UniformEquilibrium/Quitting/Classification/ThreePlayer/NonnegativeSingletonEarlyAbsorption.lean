import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazardAllSigns
import UniformEquilibrium.Quitting.Terminal.SingletonJointNeverDebt
import UniformEquilibrium.Quitting.Transform.SingletonCoordinateIncrease

/-! # Low-player laws with small regret and small joint Never

A nonnegative own singleton suffices. The profile is selected internally in
the perturbed game and evaluated at the original rewards; neither a child
target nor favorable supplied laws are assumed.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At most three players and one nonnegative singleton produce the same
original-game laws with regret at most `delta + delta²` and joint Never at most
`delta`. There is no upper restriction on the positive scale. -/
theorem exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card ι ≤ 3) (pivot : ι)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal pivot) pivot)
    {delta : ℝ} (hdelta : 0 < delta) :
    let : Nonempty ι := ⟨pivot⟩
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤ delta + delta ^ 2 ∧
      (∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal) ≤ delta := by
  let : Nonempty ι := ⟨pivot⟩
  let bumped := quittingSingletonCoordinateIncrease reward pivot delta
  have hsource := QuittingThreePlayerStrategyClass.of_card_le_three bumped hcard
    (sq_pos_of_pos hdelta)
  have hselected : ∃ profile : (quittingGame bumped).BehaviorProfile,
      (quittingGame bumped).IsεAsymptoticNash
        (quittingTerminalPayoff bumped) (delta ^ 2) profile := by
    rcases hsource with ⟨root, hnash⟩ | ⟨roots, _, hnash⟩
    · exact ⟨quittingStationaryProfile bumped root, hnash⟩
    · exact ⟨quittingRootSequenceProfile bumped roots 0, hnash⟩
  obtain ⟨profile, hnash⟩ := hselected
  have hexploit := quittingTerminalExploitability_le_of_isεAsymptoticNash
    bumped profile (sq_nonneg delta) hnash
  have hcharge := prod_stoppingLaw_none_mul_singleton_le_terminalExploitability
    bumped profile pivot
  have hbounds := quittingSingletonCoordinateIncrease_le_and_close reward pivot hdelta.le
  have horiginal := IsεAsymptoticNash.of_nonnegative_reward_perturbation
    reward bumped profile hdelta.le hbounds.1 hbounds.2 hnash
  have horiginalExploit := quittingTerminalExploitability_le_of_isεAsymptoticNash
    reward profile (add_nonneg (sq_nonneg delta) hdelta.le) horiginal
  have hneverNonneg : 0 ≤
      ∏ who, (quittingBehaviorStoppingLaw bumped (profile who) none).toReal :=
    Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hnever : (∏ who, (quittingBehaviorStoppingLaw bumped (profile who) none).toReal)
      ≤ delta := by
    simp only [bumped, quittingSingletonCoordinateIncrease_singleton] at hcharge
    nlinarith [mul_nonneg hneverNonneg hsingleton]
  refine ⟨profile, ?_, ?_⟩
  · simpa only [add_comm] using horiginalExploit
  · exact hnever

end GameTheory
