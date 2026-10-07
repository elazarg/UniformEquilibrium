import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.OneDateNeverHorizonNash

/-! # Exact finite horizons behind a nonsingleton sure-exit set

Two sure quitters screen every continuation even under a unilateral deviation.
The canonical semantic-pair formula gives exact terminal Nash for one date
followed by Never, and the existing cutoff consumer supplies every horizon.
Singleton sure sets are deliberately excluded from this tail-independent result.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

theorem oneDateThenNever_payoff_of_nonempty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (hnonempty : active.Nonempty) :
    quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) =
      quittingSetReward reward active := by
  funext who
  exact quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    active hnonempty (quittingAlwaysContinueProfile reward) who

theorem oneDateThenNever_terminalNash_of_sureExitSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hsure : IsQuittingSureExitSet reward active) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) := by
  have hsemantic := quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
    reward active hcard (quittingAlwaysContinueProfile reward)
  have htoggles := (isQuittingSureExitSet_iff_forall_max reward active).mp hsure
  intro who deviation
  have hgain := quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
    reward (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) who deviation
  change quittingTerminalPayoff reward (Function.update
      (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) who deviation) who -
    quittingTerminalPayoff reward
      (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) who ≤
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward (quittingPureSetRoot active)
        (quittingAlwaysContinueProfile reward))) who at hgain
  rw [hsemantic] at hgain
  dsimp only [quittingTerminalSemanticDebt, Prod.fst, Prod.snd] at hgain
  have htoggle := htoggles who
  simp only [add_zero]
  linarith

theorem oneDateThenNever_exactHorizon_of_sureExitSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hsure : IsQuittingSureExitSet reward active) (horizon : ℕ) :
    (quittingGame reward).IsεHorizonNash none horizon 0
      (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) :=
  quittingOneDateThenNeverProfile_exactHorizonNash reward (quittingPureSetRoot active)
    (oneDateThenNever_terminalNash_of_sureExitSet reward active hcard hsure) horizon

theorem oneDateThenNever_sameProfile_of_sureExitSet
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hsure : IsQuittingSureExitSet reward active) :
    ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon : ℕ, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy
          (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) who -
          quittingTerminalPayoff reward
            (quittingOneDateThenNeverProfile reward (quittingPureSetRoot active)) who| ≤ accuracy :=
  quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness reward
    (quittingPureSetRoot active)
    (oneDateThenNever_terminalNash_of_sureExitSet reward active hcard hsure)

end GameTheory
