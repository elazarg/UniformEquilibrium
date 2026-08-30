/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CensoredFiniteClockOperationalEffect
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingReturnFloor

/-!
# Adjacent finite-deadline sources selected by a terminal gap

An exact Nash law at one finite deadline and another at the successor
deadline determine two literal behavioral profiles.  A global terminal
exploitability gap selects an observer whose old profile has positive debt.
The projective boundary formula turns that debt into gain from the newly
exposed date and forces quantitative adjacent total variation.

The final theorem records the exact finite-versus-`Never` split after the
successor law is censored.  It is only a source interface: neither arm is
declared to be a profitable behavioral edge or a minimum-fibre transition.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Consecutive exact finite timing Nash laws together with the observer
selected by a fixed terminal exploitability gap. -/
structure QuittingAdjacentDeadlineGapSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gamma bound : ℝ) where
  deadline : ℕ
  old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)
  new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))
  oldNash :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash old
  newNash :
    (quittingFiniteDeadlineTimingGame reward
      (deadline + 1)).mixedExtension.IsNash new
  observer : ι
  oldDebt_ge : gamma ≤ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingFiniteDeadlineTimingProfile reward deadline old)) observer
  oldBoundaryGain_ge : gamma ≤
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
      (quittingFiniteDeadlineTimingProfileInclude old) observer
      (quittingFiniteDeadlineTimingBoundaryAction deadline)
  newBoundaryGain_nonpos :
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
      new observer (quittingFiniteDeadlineTimingBoundaryAction deadline) ≤ 0
  adjacentTV_ge : gamma / (4 * bound) ≤
    quittingFiniteDeadlineAdjacentTV deadline old new

namespace QuittingAdjacentDeadlineGapSource

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}

/-- The actual old hard-tail behavioral profile carried by the source. -/
def oldProfile (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward source.deadline source.old

/-- The actual successor hard-tail behavioral profile carried by the source. -/
def newProfile (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (source.deadline + 1) source.new

/-- The old observer debt is literally the positive part of the displayed
new-boundary gain. -/
theorem oldDebt_eq_boundaryGain_pospart
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.oldProfile) source.observer =
      max 0
        ((quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain
            (quittingFiniteDeadlineTimingProfileInclude source.old)
            source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline)) := by
  exact quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart
    reward source.deadline source.old source.oldNash source.observer

/-- Construct the adjacent source from arbitrary exact Nash laws at the two
deadlines.  No compatible choice of Nash laws is assumed. -/
noncomputable def of_terminalExploitabilityGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gamma bound : ℝ} (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (gap : HasTerminalExploitabilityGap reward gamma)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (oldNash :
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash old)
    (newNash :
      (quittingFiniteDeadlineTimingGame reward
        (deadline + 1)).mixedExtension.IsNash new) :
    QuittingAdjacentDeadlineGapSource reward gamma bound := by
  let observer := Classical.choose <| gap.exists_debt_ge
    (quittingFiniteDeadlineTimingProfile reward deadline old)
  have hdebt := Classical.choose_spec <| gap.exists_debt_ge
    (quittingFiniteDeadlineTimingProfile reward deadline old)
  have hdebt' : gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline old)) observer :=
    hdebt
  have hdebtEq :=
    quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart
      reward deadline old oldNash observer
  have hboundary : gamma ≤
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude old) observer
        (quittingFiniteDeadlineTimingBoundaryAction deadline) := by
    rw [hdebtEq] at hdebt'
    rcases le_total 0
        ((quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          (quittingFiniteDeadlineTimingProfileInclude old) observer
          (quittingFiniteDeadlineTimingBoundaryAction deadline)) with hnonneg | hnonpos
    · simpa [max_eq_right hnonneg] using hdebt'
    · rw [max_eq_left hnonpos] at hdebt'
      linarith
  have hnewBoundary :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          new observer (quittingFiniteDeadlineTimingBoundaryAction deadline) ≤ 0 :=
    ((quittingFiniteDeadlineTimingGame reward
      (deadline + 1)).isNash_iff_gains_nonpos new).mp newNash observer _
  exact
    { deadline := deadline
      old := old
      new := new
      oldNash := oldNash
      newNash := newNash
      observer := observer
      oldDebt_ge := hdebt'
      oldBoundaryGain_ge := hboundary
      newBoundaryGain_nonpos := hnewBoundary
      adjacentTV_ge :=
        quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge
          reward deadline old new oldNash newNash observer hbound hreward hdebt' }

/-- The total old-clock displacement after censoring. -/
def censoredErrorMass
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ :=
  ∑ player, quittingFiniteDeadlineCensoredError source.deadline
    source.old source.new player

/-- The total mass participating at the newly exposed boundary date. -/
def boundaryParticipationMass
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ :=
  ∑ player, quittingFiniteDeadlineBoundaryParticipation source.deadline
    source.new player

/-- Literal `e+b` split forced by an adjacent gap.  The two alternatives are
not exclusive. -/
theorem censoredError_or_boundaryParticipation
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound) :
    gamma / (8 * bound) ≤ source.censoredErrorMass ∨
      gamma / (8 * bound) ≤ source.boundaryParticipationMass := by
  have hadjacent := source.adjacentTV_ge
  have hbudget := quittingFiniteDeadlineAdjacentTV_le_censorBudget
    source.deadline source.old source.new
  have htotal : gamma / (4 * bound) ≤
      source.censoredErrorMass + source.boundaryParticipationMass := by
    apply hadjacent.trans
    rw [show source.censoredErrorMass + source.boundaryParticipationMass =
        quittingFiniteDeadlineCensorBudget source.deadline source.old source.new by
      unfold censoredErrorMass boundaryParticipationMass
        quittingFiniteDeadlineCensorBudget
      rw [Finset.sum_add_distrib]]
    exact hbudget
  by_contra hnone
  push Not at hnone
  have hscale : gamma / (4 * bound) =
      gamma / (8 * bound) + gamma / (8 * bound) := by
    field_simp
    ring
  rw [hscale] at htotal
  linarith [hnone.1, hnone.2]

end QuittingAdjacentDeadlineGapSource

end GameTheory
