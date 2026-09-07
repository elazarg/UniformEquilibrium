import UniformEquilibrium.Diagnostics.Quitting.ActualExactPrefixRayRestart
import UniformEquilibrium.Quitting.Root.NestedImmediateQuitCapExactPrefixExit

/-! # Exact-prefix restart from a literal late-reset child -/

noncomputable section
namespace GameTheory

open Math.Probability

/-- A literal reset child recursively produces an actual exact-prefix ray.
If every selected root survives, the reset owner's profitable `Quit0` cap
shifts from that unchanged child.  Otherwise the old finite sure/zero-debt
anchor identifies the last zero root, whose unique sure quitter carries the
full game-level gap and starts a shifted cap tail at its literal child. -/
theorem finFour_lateResetChild_exists_directShiftedCapRestart
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {gap debtFloor : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap) (hdebtFloor : 0 < debtFloor)
    (child : (quittingGame reward).BehaviorProfile)
    (oldAnchor newOwner : Fin 4) (deadline : ℕ)
    (hsureBy : ∃ time ≤ deadline,
      quittingProfileLiveRoot reward child time oldAnchor = PMF.pure true)
    (hanchorDebt : quittingTerminalDeviationDebt reward child oldAnchor = 0)
    (hcap : ImmediateQuitAttainsTerminalCap reward child newOwner)
    (hdebt : debtFloor ≤
      quittingTerminalDeviationDebt reward child newOwner) :
    ∃ ray : QuittingActualExactPrefixRay reward child,
      (∀ depth, ∃ time ≤ deadline + depth,
        quittingProfileLiveRoot reward (ray.profiles depth) time oldAnchor =
          PMF.pure true) ∧
      (∀ depth,
        quittingTerminalDeviationDebt reward (ray.profiles depth) oldAnchor = 0) ∧
      (((∀ depth,
          0 < quittingStationaryContinueMass (ray.roots depth)) ∧
        ∃ tail : QuittingActualExactPrefixRay.ShiftedCapTail ray,
          tail.start = 0 ∧ tail.owner = newOwner ∧
          tail.initialChoice = some 0 ∧ newOwner ≠ oldAnchor ∧
          debtFloor ≤ quittingTerminalDeviationDebt reward child newOwner) ∨
        ∃ (last : ℕ) (owner : Fin 4)
            (tail : QuittingActualExactPrefixRay.ShiftedCapTail ray),
          quittingStationaryContinueMass (ray.roots last) = 0 ∧
          ray.roots last owner = PMF.pure true ∧
          (∀ other, other ≠ owner →
            ray.roots last other ≠ PMF.pure true) ∧
          owner ≠ oldAnchor ∧ tail.start = last + 1 ∧ tail.owner = owner ∧
          (tail.initialChoice = none ∨
            ∃ time ≤ deadline + (last + 1),
              tail.initialChoice = some time) ∧
          gap ≤ quittingTerminalDeviationDebt reward
            (ray.profiles (last + 1)) owner) := by
  have hnot :=
    quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward hgap hexploit
  obtain ⟨ray⟩ := exists_quittingActualExactPrefixRay reward child
  have hclassification := ray.initial_or_lastZero_uniqueSure_shiftedCapTail
    reward hexploit hgap child oldAnchor deadline hsureBy hanchorDebt
  refine ⟨ray, hclassification.1, hclassification.2.1, ?_⟩
  rcases ray.positiveSurvival_or_exists_zeroSurvival with hpositive | hzero
  · have hsummable :=
      finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff
        reward hnot ray.profiles ray.roots ray.profiles_succ ray.roots_exact
    have hcapRay : quittingTerminalPayoff reward
        (Function.update (ray.profiles 0) newOwner
          (quittingPureTimeBehaviorStrategy reward newOwner (some 0))) newOwner =
      quittingContinuationBestResponseValue reward (ray.profiles 0) newOwner := by
      simpa [ImmediateQuitAttainsTerminalCap, ray.profiles_zero] using hcap
    have hdebtRay : 0 < quittingTerminalDeviationDebt reward
        (ray.profiles 0) newOwner := by
      simpa [ray.profiles_zero] using hdebtFloor.trans_le hdebt
    obtain ⟨tail, htailStart, htailOwner, htailChoice⟩ :=
      QuittingActualExactPrefixRay.nonempty_shiftedCapTail_of_attainedCap
        ray 0 newOwner (some 0) hcapRay hdebtRay (by simpa using hpositive)
          hsummable
    have hownerNe : newOwner ≠ oldAnchor := by
      intro heq
      rw [heq, hanchorDebt] at hdebt
      linarith
    exact Or.inl ⟨hpositive, tail, htailStart, htailOwner, htailChoice,
      hownerNe, hdebt⟩
  · right
    rcases hclassification.2.2 with hinitial | hlast
    · obtain ⟨tail, htailStart, -, -, -⟩ := hinitial
      obtain ⟨depth, hdepthZero⟩ := hzero
      have hdepthPos := tail.roots_positive depth
      rw [htailStart, zero_add, hdepthZero] at hdepthPos
      linarith
    · exact hlast

end GameTheory
