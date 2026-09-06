import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor

/-! # Literal cap-child deadline absorption -/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A sure owner Quit at the displayed deadline makes the child's prescribed
live mass vanish immediately after that deadline. -/
theorem quittingLiveMass_succ_eq_zero_of_sure_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ)
    (hsure : quittingProfileLiveRoot reward profile deadline owner =
      PMF.pure true) :
    quittingLiveMass reward profile (deadline + 1) = 0 := by
  rw [quittingLiveMass_succ]
  have hcontinue : quittingJointContinueMass reward profile deadline = 0 := by
    have hzero := quittingStationaryContinueMass_of_sureQuitter
      (quitter := owner) hsure
    rw [quittingJointContinueMass_eq_product]
    convert hzero using 1
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rfl
  rw [hcontinue, mul_zero]

/-- Every literal cap child in the actual positive-survival recursion has
zero owner debt and is terminal immediately after its displayed deadline. -/
theorem quittingPureTimeCapChild_owner_zeroDebt_and_deadlineAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hpositive : ∀ depth, 0 < quittingStationaryContinueMass (roots depth))
    (hbase : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles 0) owner 0) owner =
      quittingContinuationBestResponseValue reward (profiles 0) owner) :
    ∀ depth,
      quittingTerminalDeviationDebt reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth) owner = 0 ∧
        quittingLiveMass reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth)
          (depth + 1) = 0 := by
  have hfacts := quittingPureTimeCapChild_source_facts
    reward profiles roots owner hnested hexact hpositive hbase
  intro depth
  exact ⟨hfacts.2.1 depth,
    quittingLiveMass_succ_eq_zero_of_sure_owner reward _ owner depth
      (hfacts.2.2.1 depth)⟩

end GameTheory
