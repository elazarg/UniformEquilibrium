import UniformEquilibrium.Quitting.Root.ExactCapClockTransport

/-! # Residual debt of copied-root cap responses -/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Copying the prescribed root marginal and installing an actual suffix cap
leaves exactly own Quit probability times the new transported debt. -/
theorem quitting_copiedCapResponse_debt_eq_quitProbability_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player) 0 root)
    (hcontinue : 0 < (root who false).toReal)
    (hattains : quittingTerminalPayoff reward
        (Function.update continuation who strategy) who =
      quittingContinuationBestResponseValue reward continuation who) :
    let prefixed := quittingRootThenContinuationProfile reward root continuation
    let copied := Function.update prefixed who
      (quittingRootAndContinuationDeviation reward (root who) strategy)
    quittingTerminalDeviationDebt reward copied who =
      (root who true).toReal *
        quittingTerminalDeviationDebt reward prefixed who := by
  dsimp only
  let prefixed := quittingRootThenContinuationProfile reward root continuation
  let copied := Function.update prefixed who
    (quittingRootAndContinuationDeviation reward (root who) strategy)
  have htransport := quitting_exactCapAttainer_rootThen_continue_transport
    reward root continuation who strategy hnash hcontinue hattains
  have hgain := quitting_copiedRootResponse_gain_eq_jointSurvival_mul
    reward root continuation who strategy
  have hsuffixGain : quittingTerminalPayoff reward
        (Function.update continuation who strategy) who -
      quittingTerminalPayoff reward continuation who =
        quittingTerminalDeviationDebt reward continuation who := by
    rw [hattains]
    rfl
  have hcap : quittingContinuationBestResponseValue reward copied who =
      quittingContinuationBestResponseValue reward prefixed who := by
    dsimp [copied]
    exact quittingContinuationBestResponseValue_update_self
      reward prefixed who _
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hjoint := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    root who
  unfold quittingTerminalDeviationDebt
  dsimp [copied, prefixed] at hcap
  rw [hcap]
  rw [hsuffixGain, hjoint] at hgain
  unfold quittingTerminalDeviationDebt at htransport hgain
  unfold quittingRootOpponentContinueMass at htransport
  calc
    quittingContinuationBestResponseValue reward prefixed who -
          quittingTerminalPayoff reward copied who =
        (quittingContinuationBestResponseValue reward prefixed who -
            quittingTerminalPayoff reward prefixed who) -
          (quittingTerminalPayoff reward copied who -
            quittingTerminalPayoff reward prefixed who) := by ring
    _ = quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) *
          (quittingContinuationBestResponseValue reward continuation who -
            quittingTerminalPayoff reward continuation who) -
        quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) *
          (root who false).toReal *
          (quittingContinuationBestResponseValue reward continuation who -
            quittingTerminalPayoff reward continuation who) := by
      rw [htransport.2, hgain]
    _ = (root who true).toReal *
        (quittingContinuationBestResponseValue reward prefixed who -
          quittingTerminalPayoff reward prefixed who) := by
      rw [htransport.2]
      have hprob : (root who false).toReal = 1 - (root who true).toReal := by
        linarith
      rw [hprob]
      ring

/-- When Quit also has positive support, the copied response's residual debt
is the exact coordinate Nash defect of the old root evaluated at the raised
cap-tail coordinate. -/
theorem quitting_capTail_coordinateDefect_eq_copiedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player) 0 root)
    (hcontinue : 0 < (root who false).toReal)
    (hquit : 0 < (root who true).toReal) :
    let tail := fun player => quittingTerminalPayoff reward continuation player
    let capTail := Function.update tail who
      (quittingContinuationBestResponseValue reward continuation who)
    quittingRootCoordinateNashDefect reward capTail root who =
      (root who true).toReal *
        quittingRootOpponentContinueMass root who *
          quittingTerminalDeviationDebt reward continuation who := by
  dsimp only
  let tail : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  have hold : quittingRootEndpointDifference reward tail root who = 0 :=
    quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward tail root who
        ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
          reward tail 0 root).mpr hnash) hcontinue hquit
  have hbest : quittingContinuationBestResponseValue reward continuation who =
      tail who + debt := by
    dsimp [tail, debt, quittingTerminalDeviationDebt]
    ring
  have hnew : quittingRootEndpointDifference reward
        (Function.update tail who
          (quittingContinuationBestResponseValue reward continuation who))
        root who = -quittingRootOpponentContinueMass root who * debt := by
    rw [hbest]
    unfold quittingRootEndpointDifference
    rw [quittingRootQuitPayoff_continuation_invariant reward
      (Function.update tail who (tail who + debt)) tail root who,
      quittingRootContinuePayoff_update_add]
    unfold quittingRootEndpointDifference at hold
    linarith
  have hmass := quittingRootOpponentContinueMass_nonneg root who
  have hdebt := quittingTerminalDeviationDebt_nonneg reward continuation who
  have hdebt' : 0 ≤ debt := hdebt
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart, hnew]
  rw [max_eq_right
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hmass) hdebt')]
  rw [max_eq_left (by nlinarith [mul_nonneg hmass hdebt'])]
  dsimp [debt]
  ring

end GameTheory
