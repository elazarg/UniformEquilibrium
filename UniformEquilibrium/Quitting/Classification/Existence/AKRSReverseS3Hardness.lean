/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.AKRSNullTailAlternative
import UniformEquilibrium.Quitting.Cycles.PeriodicJointSurvival
import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingExploitabilityRetraction

/-!
# One-added-player hardness of reverse S.3

An arbitrary finite quitting payoff table, including an arbitrary payoff at
Never, embeds into a table with one additional dummy player. The padded table
has a stationary exact row-perfect source that terminates after every restart,
while unrestricted terminal exploitability retracts pointwise with the sharp
positive factor. Thus universal reverse S.3 is equivalent to universal terminal
approximate-equilibrium existence, with a real one-player cardinal shift.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
  QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingLCPClassification

/-! ## One-dummy arbitrary-Never padding -/

/-- The normalized reward used inside one-dummy arbitrary-Never padding. -/
def QuittingPayoffTable.oneDummyPaddingNormalizedReward
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    {T : Finset (ι ⊕ PUnit) // T.Nonempty} → Payoff (ι ⊕ PUnit) :=
  quittingPassivePaddingReward (J := PUnit) table.zeroNeverReward
    (quittingPassivePaddingUpperEndpoint table.zeroNeverReward) penalty

/-- Add one passive dummy to an arbitrary-Never quitting table. Translation
after normalized padding restores every old terminal and Never coordinate. -/
def QuittingPayoffTable.oneDummyPadding [Nonempty ι]
    (table : QuittingPayoffTable ι) (penalty : ℝ) :
    QuittingPayoffTable (ι ⊕ PUnit) :=
  (repositoryQuittingPayoffTable
      (table.oneDummyPaddingNormalizedReward penalty)).translate
    (Sum.elim table.never (fun _ ↦ 0))

@[simp] theorem QuittingPayoffTable.oneDummyPadding_never_inl
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) (who : ι) :
    (table.oneDummyPadding penalty).never (.inl who) = table.never who := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable]

@[simp] theorem QuittingPayoffTable.oneDummyPadding_never_inr
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ)
    (dummy : PUnit) :
    (table.oneDummyPadding penalty).never (.inr dummy) = 0 := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable]

/-- Normalizing the arbitrary-Never padded table recovers the canonical
zero-Never passive-padding reward exactly. -/
theorem QuittingPayoffTable.oneDummyPadding_zeroNeverReward
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    (table.oneDummyPadding penalty).zeroNeverReward =
      table.oneDummyPaddingNormalizedReward penalty := by
  funext terminal player
  cases player <;>
    simp [QuittingPayoffTable.zeroNeverReward,
      QuittingPayoffTable.oneDummyPadding,
      QuittingPayoffTable.translate, repositoryQuittingPayoffTable]

/-- Canonical old-player upper endpoint of arbitrary-Never padding, including
the payoff of Never in the finite range. -/
def QuittingPayoffTable.oneDummyPaddingUpperEndpoint [Nonempty ι]
    (table : QuittingPayoffTable ι) (who : ι) : ℝ :=
  quittingPassivePaddingUpperEndpoint table.zeroNeverReward who +
    table.never who

/-- Every padded terminal coalition containing an old quitter reproduces the
original old-player terminal payoff after deleting the dummy. -/
theorem QuittingPayoffTable.oneDummyPadding_terminal_inl_of_oldPart_nonempty
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ)
    (terminal : {T : Finset (ι ⊕ PUnit) // T.Nonempty})
    (hold : (quittingPassivePaddingOldPart terminal.1).Nonempty) (who : ι) :
    (table.oneDummyPadding penalty).terminal terminal (.inl who) =
      table.terminal ⟨quittingPassivePaddingOldPart terminal.1, hold⟩ who := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingPassivePaddingReward, hold,
    QuittingPayoffTable.zeroNeverReward]

/-- Every padded terminal coalition containing an old quitter pays the dummy
zero. -/
theorem QuittingPayoffTable.oneDummyPadding_terminal_inr_of_oldPart_nonempty
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ)
    (terminal : {T : Finset (ι ⊕ PUnit) // T.Nonempty})
    (hold : (quittingPassivePaddingOldPart terminal.1).Nonempty)
    (dummy : PUnit) :
    (table.oneDummyPadding penalty).terminal terminal (.inr dummy) = 0 := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingPassivePaddingReward, hold]

/-- Dummy-only absorption pays each old player the canonical arbitrary-Never
upper endpoint. -/
theorem QuittingPayoffTable.oneDummyPadding_terminal_dummyOnly_inl
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) (who : ι) :
    (table.oneDummyPadding penalty).terminal
        (quittingSingletonTerminal (.inr PUnit.unit)) (.inl who) =
      table.oneDummyPaddingUpperEndpoint who := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    QuittingPayoffTable.oneDummyPaddingUpperEndpoint,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingPassivePaddingReward, quittingPassivePaddingOldPart,
    quittingSingletonTerminal]

/-- Dummy-only absorption charges the dummy exactly the positive penalty. -/
theorem QuittingPayoffTable.oneDummyPadding_terminal_dummyOnly_inr
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    (table.oneDummyPadding penalty).terminal
        (quittingSingletonTerminal (.inr PUnit.unit)) (.inr PUnit.unit) =
      -penalty := by
  simp [QuittingPayoffTable.oneDummyPadding,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingPassivePaddingReward, quittingPassivePaddingOldPart,
    quittingSingletonTerminal]

/-- The stationary root where every old player Continues and the unique
dummy Quits surely. -/
def oneDummySureQuitRoot : ι ⊕ PUnit → PMF Bool
  | .inl _ => PMF.pure false
  | .inr _ => PMF.pure true

/-- The exact stationary dummy-sure-Quit root sequence. -/
def oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool :=
  fun _ ↦ oneDummySureQuitRoot

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem oneDummySureQuitRoot_inl (who : ι) :
    oneDummySureQuitRoot (.inl who) = PMF.pure false := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem oneDummySureQuitRoot_inr (dummy : PUnit) :
    oneDummySureQuitRoot (ι := ι) (.inr dummy) = PMF.pure true := rfl

omit [Fintype ι] in
theorem oneDummySureQuitRoot_eq_pureSingleton :
    (oneDummySureQuitRoot : ι ⊕ PUnit → PMF Bool) =
      quittingPureSetRoot ({.inr PUnit.unit} : Finset (ι ⊕ PUnit)) := by
  funext label
  cases label with
  | inl who => simp [oneDummySureQuitRoot, quittingPureSetRoot,
      quittingSetAction]
  | inr dummy =>
      obtain rfl : dummy = PUnit.unit := Subsingleton.elim _ _
      simp [oneDummySureQuitRoot, quittingPureSetRoot, quittingSetAction]

omit [DecidableEq ι] in
theorem oneDummySureQuitRoot_continueMass_eq_zero :
    quittingStationaryContinueMass
      (oneDummySureQuitRoot : ι ⊕ PUnit → PMF Bool) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ (.inr PUnit.unit)) ?_
  simp [oneDummySureQuitRoot]

omit [DecidableEq ι] in
theorem oneDummySureQuitRoots_survivalLimit_eq_zero (start : ℕ) :
    quittingJointSurvivalLimit
      (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) start = 0 := by
  apply quittingJointSurvivalLimit_eq_zero_of_periodic
    oneDummySureQuitRoots (period := 1) (date := 0)
  · intro time
    rfl
  · omega
  · simp [oneDummySureQuitRoots, oneDummySureQuitRoot_continueMass_eq_zero]

/-- The normalized stationary source has the displayed old upper endpoint and
dummy penalty as its literal continuation vector after every restart. -/
theorem oneDummySureQuitRoots_tailVector
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) (start : ℕ) :
    quittingRootSequenceTailVector
        (table.oneDummyPaddingNormalizedReward penalty)
        oneDummySureQuitRoots start =
      Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty) := by
  funext player
  unfold quittingRootSequenceTailVector
  rw [quittingRootSequenceTerminalValue_eq_shift]
  change quittingRootSequenceTerminalValue
    (table.oneDummyPaddingNormalizedReward penalty)
    oneDummySureQuitRoots player 0 = _
  rw [quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero]
  · cases player with
    | inl who =>
        change quittingRootAbsorbingContribution
          (table.oneDummyPaddingNormalizedReward penalty)
          oneDummySureQuitRoot (.inl who) = _
        rw [show (oneDummySureQuitRoot : ι ⊕ PUnit → PMF Bool) =
            Sum.elim (fun _ ↦ PMF.pure false)
              (fun _ ↦ PMF.pure true) by
          funext label
          cases label <;> rfl]
        unfold QuittingPayoffTable.oneDummyPaddingNormalizedReward
        rw [quittingRootAbsorbingContribution_passivePadding_old]
        have holdContribution : quittingRootAbsorbingContribution
            table.zeroNeverReward (fun _ : ι ↦ PMF.pure false) who = 0 := by
          unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
          rw [pmfPi_pure, expect_pure]
          simp [quittingRootPayoff, quittingQuitters]
        have holdContinue : quittingStationaryContinueMass
            (fun _ : ι ↦ PMF.pure false) = 1 := by
          rw [quittingStationaryContinueMass_eq_prod_continueProbability]
          simp
        have hfreshAbsorb : quittingRootAbsorptionMass
            (fun _ : PUnit ↦ PMF.pure true) = 1 := by
          unfold quittingRootAbsorptionMass
          rw [quittingStationaryContinueMass_eq_prod_continueProbability]
          simp
        simp [holdContribution, holdContinue, hfreshAbsorb]
    | inr dummy =>
        change quittingRootAbsorbingContribution
          (table.oneDummyPaddingNormalizedReward penalty)
          oneDummySureQuitRoot (.inr dummy) = _
        rw [show (oneDummySureQuitRoot : ι ⊕ PUnit → PMF Bool) =
            Sum.elim (fun _ ↦ PMF.pure false)
              (fun _ ↦ PMF.pure true) by
          funext label
          cases label <;> rfl]
        unfold QuittingPayoffTable.oneDummyPaddingNormalizedReward
        rw [quittingRootAbsorbingContribution_passivePadding_fresh]
        have holdContinue : quittingStationaryContinueMass
            (fun _ : ι ↦ PMF.pure false) = 1 := by
          rw [quittingStationaryContinueMass_eq_prod_continueProbability]
          simp
        simp [holdContinue]
  · exact oneDummySureQuitRoot_continueMass_eq_zero

theorem oneDummySureQuitRoot_old_quitPayoff
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ)
    (who : ι) :
    quittingRootQuitPayoff (table.oneDummyPaddingNormalizedReward penalty)
      (Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty)) oneDummySureQuitRoot (.inl who) =
      table.zeroNeverReward (quittingSingletonTerminal who) who := by
  rw [oneDummySureQuitRoot_eq_pureSingleton,
    quittingRootQuitPayoff_pureSetRoot_eq_insert]
  have hset : ({x : ι | x = who} : Finset ι) = {who} := by
    ext player
    simp [eq_comm]
  simp [quittingSetReward,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    quittingPassivePaddingReward, quittingPassivePaddingOldPart,
    hset, quittingSingletonTerminal]

theorem oneDummySureQuitRoot_old_continuePayoff
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ)
    (who : ι) :
    quittingRootContinuePayoff
      (table.oneDummyPaddingNormalizedReward penalty)
      (Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty)) oneDummySureQuitRoot (.inl who) =
      quittingPassivePaddingUpperEndpoint table.zeroNeverReward who := by
  rw [oneDummySureQuitRoot_eq_pureSingleton,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · simp [quittingSetReward,
      QuittingPayoffTable.oneDummyPaddingNormalizedReward,
      quittingPassivePaddingReward, quittingPassivePaddingOldPart]
  · simp

theorem oneDummySureQuitRoot_dummy_quitPayoff
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    quittingRootQuitPayoff (table.oneDummyPaddingNormalizedReward penalty)
      (Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty)) oneDummySureQuitRoot (.inr PUnit.unit) =
      -penalty := by
  rw [oneDummySureQuitRoot_eq_pureSingleton,
    quittingRootQuitPayoff_pureSetRoot_eq_insert]
  simp [quittingSetReward,
    QuittingPayoffTable.oneDummyPaddingNormalizedReward,
    quittingPassivePaddingReward, quittingPassivePaddingOldPart]

theorem oneDummySureQuitRoot_dummy_continuePayoff
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    quittingRootContinuePayoff
      (table.oneDummyPaddingNormalizedReward penalty)
      (Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty)) oneDummySureQuitRoot (.inr PUnit.unit) =
      -penalty := by
  rw [oneDummySureQuitRoot_eq_pureSingleton,
    quittingRootContinuePayoff_pureSingleton_eq_tail]
  rfl

/-- The mixed successor value of the stationary source is its literal tail
vector. -/
theorem oneDummySureQuitRoot_successorPayoff
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    quittingRootSuccessorPayoff
        (table.oneDummyPaddingNormalizedReward penalty)
        (Sum.elim
          (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
          (fun _ ↦ -penalty)) oneDummySureQuitRoot =
      Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (fun _ ↦ -penalty) := by
  funext player
  have hrec := (quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
    (table.oneDummyPaddingNormalizedReward penalty)
    oneDummySureQuitRoots player 0).symm
  have htailZero := congrFun
    (oneDummySureQuitRoots_tailVector table penalty 0) player
  have htailOne := congrFun
    (oneDummySureQuitRoots_tailVector table penalty 1) player
  let target : Payoff (ι ⊕ PUnit) := Sum.elim
    (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
    (fun _ : PUnit ↦ -penalty)
  calc
    quittingRootSuccessorPayoff
          (table.oneDummyPaddingNormalizedReward penalty)
          target oneDummySureQuitRoot player =
        quittingRootSuccessorPayoff
          (table.oneDummyPaddingNormalizedReward penalty)
          (quittingRootSequenceTailVector
            (table.oneDummyPaddingNormalizedReward penalty)
            oneDummySureQuitRoots 1)
          oneDummySureQuitRoot player := by
            apply congrArg (fun tail ↦ quittingRootSuccessorPayoff
              (table.oneDummyPaddingNormalizedReward penalty)
              tail oneDummySureQuitRoot player)
            exact (oneDummySureQuitRoots_tailVector table penalty 1).symm
    _ = quittingRootSequenceTerminalValue
          (table.oneDummyPaddingNormalizedReward penalty)
          oneDummySureQuitRoots player 0 := hrec
    _ = quittingRootSequenceTailVector
          (table.oneDummyPaddingNormalizedReward penalty)
          oneDummySureQuitRoots 0 player := rfl
    _ = target player := htailZero

/-- Every row of the dummy-sure-Quit source is exactly row-perfect against
its own restarted terminal continuation. -/
theorem oneDummySureQuitRoots_rowZeroPerfect
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) (time : ℕ) :
    QuittingRowεPerfect (table.oneDummyPaddingNormalizedReward penalty)
      (quittingRootSequenceTailVector
        (table.oneDummyPaddingNormalizedReward penalty)
        oneDummySureQuitRoots (time + 1))
      (oneDummySureQuitRoots time) 0 := by
  rw [oneDummySureQuitRoots_tailVector table penalty (time + 1)]
  change QuittingRowεPerfect (table.oneDummyPaddingNormalizedReward penalty)
    (Sum.elim (quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
      (fun _ ↦ -penalty)) oneDummySureQuitRoot 0
  intro player
  unfold QuittingPlayerRowεPerfect
  cases player with
  | inl who =>
      have hquit := oneDummySureQuitRoot_old_quitPayoff table penalty who
      have hcontinue :=
        oneDummySureQuitRoot_old_continuePayoff table penalty who
      have hsuccess := congrFun
        (oneDummySureQuitRoot_successorPayoff table penalty) (.inl who)
      simp only [Sum.elim_inl] at hsuccess
      have hupper :=
        (quittingPassivePaddingReward_mem_canonicalInterval
          table.zeroNeverReward (quittingSingletonTerminal who) who).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hquit, hsuccess]
        simpa only [add_zero] using hupper
      · rw [hcontinue, hsuccess]
        simp
      · simp [oneDummySureQuitRoot]
      · intro _hused
        rw [hcontinue, hsuccess]
        simp
  | inr dummy =>
      obtain rfl : dummy = PUnit.unit := Subsingleton.elim _ _
      have hquit := oneDummySureQuitRoot_dummy_quitPayoff table penalty
      have hcontinue :=
        oneDummySureQuitRoot_dummy_continuePayoff table penalty
      have hsuccess := congrFun
        (oneDummySureQuitRoot_successorPayoff table penalty) (.inr PUnit.unit)
      simp only [Sum.elim_inr] at hsuccess
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hquit, hsuccess]
        simp
      · rw [hcontinue, hsuccess]
        simp
      · intro _hused
        rw [hquit, hsuccess]
        simp
      · simp [oneDummySureQuitRoot]

/-- The normalized one-dummy game has a single stationary exact row-perfect
source which terminates after every restart. -/
theorem QuittingPayoffTable.oneDummyPaddingNormalizedReward_has_exactEveryRestartSource
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    QuittingRootSequenceTerminatesAfterEveryRestart
        (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) ∧
      ∀ time, QuittingRowεPerfect
        (table.oneDummyPaddingNormalizedReward penalty)
        (quittingRootSequenceTailVector
          (table.oneDummyPaddingNormalizedReward penalty)
          oneDummySureQuitRoots (time + 1))
        (oneDummySureQuitRoots time) 0 := by
  exact ⟨oneDummySureQuitRoots_survivalLimit_eq_zero,
    oneDummySureQuitRoots_rowZeroPerfect table penalty⟩

/-- The arbitrary-Never padded table itself carries the same stationary exact
row-perfect, every-restart source. -/
theorem QuittingPayoffTable.oneDummyPadding_has_exactEveryRestartSource
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    QuittingRootSequenceTerminatesAfterEveryRestart
        (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) ∧
      IsCompletelyAbsorbing
        (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) ∧
      ∀ time, QuittingRowεPerfect (table.oneDummyPadding penalty).terminal
        ((table.oneDummyPadding penalty).rootSequenceTailVector
          oneDummySureQuitRoots (time + 1))
        (oneDummySureQuitRoots time) 0 := by
  have hevery : QuittingRootSequenceTerminatesAfterEveryRestart
      (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) :=
    oneDummySureQuitRoots_survivalLimit_eq_zero
  refine ⟨hevery, ?_, ?_⟩
  · unfold IsCompletelyAbsorbing
    have heq : quittingSurvivalPrefix
          (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) =
        quittingJointSurvivalWeight
          (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) 0 := by
      funext fuel
      rw [quittingJointSurvivalWeight_eq_prod]
      simp [quittingSurvivalPrefix]
    rw [heq]
    simpa [hevery 0] using
      (tendsto_quittingJointSurvivalLimit
        (oneDummySureQuitRoots : ℕ → ι ⊕ PUnit → PMF Bool) 0)
  · intro time
    let padded := table.oneDummyPadding penalty
    have hnormalized :=
      oneDummySureQuitRoots_rowZeroPerfect table penalty time
    rw [← table.oneDummyPadding_zeroNeverReward penalty] at hnormalized
    have hterminal : padded.terminal = fun S who ↦
        padded.zeroNeverReward S who + padded.never who := by
      funext S who
      simp [QuittingPayoffTable.zeroNeverReward]
    have htail : padded.rootSequenceTailVector
          oneDummySureQuitRoots (time + 1) = fun who ↦
        quittingRootSequenceTailVector padded.zeroNeverReward
          oneDummySureQuitRoots (time + 1) who + padded.never who := by
      funext who
      exact padded.rootSequenceTailVector_eq_add_never
        oneDummySureQuitRoots (time + 1) who
    change QuittingRowεPerfect padded.terminal
      (padded.rootSequenceTailVector oneDummySureQuitRoots (time + 1))
      (oneDummySureQuitRoots time) 0
    rw [hterminal, htail]
    exact (quittingRowεPerfect_translate_iff padded.zeroNeverReward
      padded.never _ (oneDummySureQuitRoots time) 0).2 hnormalized

/-- The one-dummy arbitrary-Never table satisfies branch S.3 via one fixed
stationary exact source, independently of the requested positive error. -/
theorem QuittingPayoffTable.oneDummyPadding_sequentiallyPerfectAbsorbing
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    (table.oneDummyPadding penalty).SequentiallyεPerfectAbsorbingExistence := by
  intro ε hε
  obtain ⟨_every, habsorbing, hperfect⟩ :=
    table.oneDummyPadding_has_exactEveryRestartSource penalty
  exact ⟨oneDummySureQuitRoots, habsorbing,
    fun time ↦ (hperfect time).mono hε.le⟩

/-! ## Pointwise unrestricted exploitability retraction -/

/-- Literal all-behavior terminal exploitability for an arbitrary-Never
table, definitionally normalized by subtracting its Never payoff. -/
def QuittingPayoffTable.terminalExploitability [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (profile : (quittingGame table.terminal).BehaviorProfile) : ℝ :=
  quittingTerminalExploitability table.zeroNeverReward profile

/-- Exact sharp lower retraction factor for every padded behavioral profile.
This includes the zero-width case without division by the width. -/
theorem QuittingPayoffTable.oneDummyPadding_retractionFactor_mul_exploitability_le
    [Nonempty ι] (table : QuittingPayoffTable ι)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (table.oneDummyPadding penalty).terminal).BehaviorProfile) :
    penalty / (penalty + quittingPassivePaddingWidth table.zeroNeverReward) *
        table.terminalExploitability
          (quittingPassivePaddingProjectProfile
            (upper := quittingPassivePaddingUpperEndpoint
              table.zeroNeverReward) (penalty := penalty)
            table.zeroNeverReward profile) ≤
      (table.oneDummyPadding penalty).terminalExploitability profile := by
  unfold QuittingPayoffTable.terminalExploitability
  rw [table.oneDummyPadding_zeroNeverReward]
  unfold QuittingPayoffTable.oneDummyPaddingNormalizedReward
  simpa [quittingPassivePaddingRetractionFactor] using
    (retractionFactor_mul_quittingTerminalExploitability_project_le
      (J := PUnit) table.zeroNeverReward hpenalty profile)

/-- Equivalent multiplier form of the pointwise unrestricted retraction. -/
theorem QuittingPayoffTable.oneDummyPadding_project_exploitability_le
    [Nonempty ι] (table : QuittingPayoffTable ι)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (table.oneDummyPadding penalty).terminal).BehaviorProfile) :
    table.terminalExploitability
        (quittingPassivePaddingProjectProfile
          (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
          (penalty := penalty) table.zeroNeverReward profile) ≤
      (1 + quittingPassivePaddingWidth table.zeroNeverReward / penalty) *
        (table.oneDummyPadding penalty).terminalExploitability profile := by
  let factor := quittingPassivePaddingRetractionFactor
    (J := PUnit) table.zeroNeverReward penalty
  let multiplier := quittingPassivePaddingRetractionMultiplier
    (J := PUnit) table.zeroNeverReward penalty
  have hmultiplier : 0 ≤ multiplier := by
    have hwidth := quittingPassivePaddingWidth_nonneg table.zeroNeverReward
    unfold multiplier quittingPassivePaddingRetractionMultiplier
    positivity
  have hretract :=
    table.oneDummyPadding_retractionFactor_mul_exploitability_le
      hpenalty profile
  have hretract' : factor * table.terminalExploitability
        (quittingPassivePaddingProjectProfile
          (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
          (penalty := penalty) table.zeroNeverReward profile) ≤
      (table.oneDummyPadding penalty).terminalExploitability profile := by
    simpa [factor, quittingPassivePaddingRetractionFactor] using hretract
  calc
    table.terminalExploitability
        (quittingPassivePaddingProjectProfile
          (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
          (penalty := penalty) table.zeroNeverReward profile) =
      multiplier * (factor * table.terminalExploitability
        (quittingPassivePaddingProjectProfile
          (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
          (penalty := penalty) table.zeroNeverReward profile)) := by
          rw [← mul_assoc, mul_comm multiplier factor,
            quittingPassivePaddingRetractionFactor_mul_multiplier
              (J := PUnit) table.zeroNeverReward hpenalty, one_mul]
    _ ≤ multiplier *
        (table.oneDummyPadding penalty).terminalExploitability profile :=
      mul_le_mul_of_nonneg_left hretract' hmultiplier
    _ = (1 + quittingPassivePaddingWidth table.zeroNeverReward / penalty) *
        (table.oneDummyPadding penalty).terminalExploitability profile := by
      simp [multiplier, quittingPassivePaddingRetractionMultiplier]

/-- A positive all-profile exploitability floor transports to the padded game
with the sharp one-dummy factor, while the padded game simultaneously carries
the exact every-restart S.3 source. -/
theorem QuittingPayoffTable.oneDummyPadding_negativeTransport
    [Nonempty ι] (table : QuittingPayoffTable ι)
    {penalty gap : ℝ} (hpenalty : 0 < penalty)
    (hgap : ∀ profile : (quittingGame table.terminal).BehaviorProfile,
      gap ≤ table.terminalExploitability profile) :
    (table.oneDummyPadding penalty).SequentiallyεPerfectAbsorbingExistence ∧
      ∀ profile : (quittingGame
          (table.oneDummyPadding penalty).terminal).BehaviorProfile,
        penalty / (penalty +
            quittingPassivePaddingWidth table.zeroNeverReward) * gap ≤
          (table.oneDummyPadding penalty).terminalExploitability profile := by
  refine ⟨table.oneDummyPadding_sequentiallyPerfectAbsorbing penalty, ?_⟩
  intro profile
  have hfactor : 0 ≤ penalty / (penalty +
      quittingPassivePaddingWidth table.zeroNeverReward) := by
    have hwidth := quittingPassivePaddingWidth_nonneg table.zeroNeverReward
    positivity
  exact (mul_le_mul_of_nonneg_left
      (hgap (quittingPassivePaddingProjectProfile
        (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
        (penalty := penalty) table.zeroNeverReward profile)) hfactor).trans
    (table.oneDummyPadding_retractionFactor_mul_exploitability_le
      hpenalty profile)

/-! ## Cardinal shift and universal hardness -/

/-- A literal stationary exact row-perfect source whose absorption persists
after every finite restart.  This is the restricted every-tail residue left
after the null-tail alternative; it does not quantify over merely initially
absorbing sources. -/
def QuittingPayoffTable.HasStationaryExactEveryRestartRowPerfectSource
    (table : QuittingPayoffTable ι) : Prop :=
  ∃ roots : ℕ → ι → PMF Bool,
    (∀ time, roots time = roots 0) ∧
      QuittingRootSequenceTerminatesAfterEveryRestart roots ∧
      ∀ time, QuittingRowεPerfect table.terminal
        (table.rootSequenceTailVector roots (time + 1)) (roots time) 0

/-- The one-dummy table carries the literal stationary exact every-restart
source required by the restricted hardness statement. -/
theorem QuittingPayoffTable.oneDummyPadding_has_stationaryExactEveryRestartSource
    [Nonempty ι] (table : QuittingPayoffTable ι) (penalty : ℝ) :
    (table.oneDummyPadding penalty).HasStationaryExactEveryRestartRowPerfectSource := by
  obtain ⟨hevery, _habsorbing, hperfect⟩ :=
    table.oneDummyPadding_has_exactEveryRestartSource penalty
  exact ⟨oneDummySureQuitRoots, fun _ ↦ rfl, hevery, hperfect⟩

/-- The reverse S.3 implication for one arbitrary-Never payoff table. -/
def QuittingPayoffTable.ReverseSequentiallyPerfectAbsorbing
    (table : QuittingPayoffTable ι) : Prop :=
  table.SequentiallyεPerfectAbsorbingExistence →
    table.ApproximateEquilibriumExistence

/-- Approximate equilibrium existence for the padded table retracts to the
old arbitrary-Never game at every positive accuracy. -/
theorem QuittingPayoffTable.approximateEquilibriumExistence_of_oneDummyPadding
    [Nonempty ι] (table : QuittingPayoffTable ι)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (hpadded : (table.oneDummyPadding penalty).ApproximateEquilibriumExistence) :
    table.ApproximateEquilibriumExistence := by
  intro ε hε
  let factor := quittingPassivePaddingRetractionFactor
    (J := PUnit) table.zeroNeverReward penalty
  have hfactor : 0 < factor :=
    quittingPassivePaddingRetractionFactor_pos
      (J := PUnit) table.zeroNeverReward hpenalty
  let η := ε * factor
  have hη : 0 < η := mul_pos hε hfactor
  obtain ⟨profile, hnash⟩ := hpadded η hη
  let projected := quittingPassivePaddingProjectProfile
    (upper := quittingPassivePaddingUpperEndpoint table.zeroNeverReward)
    (penalty := penalty) table.zeroNeverReward profile
  refine ⟨projected, (table.isεAsymptoticNash_iff ε projected).2 ?_⟩
  apply isεAsymptoticNash_of_quittingTerminalExploitability_le projected
  have hpaddedNash :=
    ((table.oneDummyPadding penalty).isεAsymptoticNash_iff η profile).1
      hnash
  have hpaddedExploit :
      (table.oneDummyPadding penalty).terminalExploitability profile ≤ η := by
    unfold QuittingPayoffTable.terminalExploitability
    exact quittingTerminalExploitability_le_of_isεAsymptoticNash
      (table.oneDummyPadding penalty).zeroNeverReward profile hη.le
      hpaddedNash
  have hretract :=
    table.oneDummyPadding_retractionFactor_mul_exploitability_le
      hpenalty profile
  have hscaled : factor * quittingTerminalExploitability
        table.zeroNeverReward projected ≤ factor * ε := by
    calc
      factor * quittingTerminalExploitability
          table.zeroNeverReward projected ≤
        (table.oneDummyPadding penalty).terminalExploitability profile := by
          simpa [factor, projected,
            QuittingPayoffTable.terminalExploitability,
            quittingPassivePaddingRetractionFactor] using hretract
      _ ≤ η := hpaddedExploit
      _ = factor * ε := by simp [η, mul_comm]
  nlinarith

/-- Approximate-equilibrium existence follows at the old player type if the
restricted stationary exact every-restart implication is known at the
one-dummy player type.  This is a cardinal-shift theorem, not a
same-cardinality statement. -/
theorem stationaryExactEveryRestartSource_sum_punit_implies_approximateEquilibriumExistence
    [Nonempty ι]
    (hrestricted : ∀ padded : QuittingPayoffTable (ι ⊕ PUnit),
      padded.HasStationaryExactEveryRestartRowPerfectSource →
        padded.ApproximateEquilibriumExistence)
    (table : QuittingPayoffTable ι) :
    table.ApproximateEquilibriumExistence := by
  let penalty : ℝ := 1
  have hpadded := hrestricted (table.oneDummyPadding penalty)
    (table.oneDummyPadding_has_stationaryExactEveryRestartSource penalty)
  exact table.approximateEquilibriumExistence_of_oneDummyPadding
    (penalty := penalty) (by norm_num) hpadded

/-- Reverse S.3 at the one-added-player type implies approximate equilibrium
existence for every old table. This is the literal cardinal shift. -/
theorem reverseS3_sum_punit_implies_approximateEquilibriumExistence
    [Nonempty ι]
    (hreverse : ∀ padded : QuittingPayoffTable (ι ⊕ PUnit),
      padded.ReverseSequentiallyPerfectAbsorbing)
    (table : QuittingPayoffTable ι) :
    table.ApproximateEquilibriumExistence := by
  let penalty : ℝ := 1
  have hpadded := hreverse (table.oneDummyPadding penalty)
    (table.oneDummyPadding_sequentiallyPerfectAbsorbing penalty)
  exact table.approximateEquilibriumExistence_of_oneDummyPadding
    (penalty := penalty) (by norm_num) hpadded

/-- Reverse S.3 for every finite player type. The quantifier ranges over the
table with its explicit Never payoff and over arbitrary behavioral profiles
inside approximate-equilibrium existence. -/
def UniversalReverseSequentiallyPerfectAbsorbing : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
    (table : QuittingPayoffTable players),
    table.ReverseSequentiallyPerfectAbsorbing

/-- Terminal approximate-equilibrium existence for every finite player type,
including the empty type. -/
def UniversalQuittingApproximateEquilibriumExistence : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
    (table : QuittingPayoffTable players),
    table.ApproximateEquilibriumExistence

/-- The literal restricted reverse implication left after null-tail
elimination: every finite quitting table which admits one stationary exact
row-perfect source terminating after every restart has an approximate
equilibrium. -/
def UniversalStationaryExactEveryRestartSourceImpliesApproximateEquilibrium :
    Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
    (table : QuittingPayoffTable players),
    table.HasStationaryExactEveryRestartRowPerfectSource →
      table.ApproximateEquilibriumExistence

/-- The restricted every-restart implication is universally equivalent to
general finite-quitting approximate-equilibrium existence.  The hard
direction embeds `players` into `players ⊕ PUnit`; it makes no
same-cardinality claim.  The empty old player type is handled directly. -/
theorem universalStationaryExactEveryRestartSource_iff_approximateExistence :
    UniversalStationaryExactEveryRestartSourceImpliesApproximateEquilibrium ↔
      UniversalQuittingApproximateEquilibriumExistence := by
  classical
  constructor
  · intro hrestricted players _ _ table
    cases isEmpty_or_nonempty players with
    | inl hempty =>
        letI : IsEmpty players := hempty
        intro ε _hε
        refine ⟨quittingAlwaysContinueProfile table.terminal, ?_⟩
        intro who
        exact isEmptyElim who
    | inr hnonempty =>
        letI : Nonempty players := hnonempty
        exact
          stationaryExactEveryRestartSource_sum_punit_implies_approximateEquilibriumExistence
            (fun padded hsource ↦
              hrestricted (players ⊕ PUnit) padded hsource) table
  · intro happrox players _ _ table _hsource
    exact happrox players table

/-- Universal reverse S.3 is equivalent to the general finite-quitting
approximate-equilibrium problem. The hard direction uses `players ⊕ PUnit`,
so this theorem makes no same-cardinality claim. The empty-player source case
is discharged directly by its unique vacuous behavioral profile. -/
theorem universalReverseS3_iff_universalApproximateEquilibriumExistence :
    UniversalReverseSequentiallyPerfectAbsorbing ↔
      UniversalQuittingApproximateEquilibriumExistence := by
  classical
  constructor
  · intro hreverse players _ _ table
    cases isEmpty_or_nonempty players with
    | inl hempty =>
        letI : IsEmpty players := hempty
        intro ε _hε
        refine ⟨quittingAlwaysContinueProfile table.terminal, ?_⟩
        intro who
        exact isEmptyElim who
    | inr hnonempty =>
        letI : Nonempty players := hnonempty
        exact reverseS3_sum_punit_implies_approximateEquilibriumExistence
          (fun padded ↦ hreverse (players ⊕ PUnit) padded) table
  · intro happrox players _ _ table _hbranch
    exact happrox players table

end QuittingLCPClassification

end GameTheory
