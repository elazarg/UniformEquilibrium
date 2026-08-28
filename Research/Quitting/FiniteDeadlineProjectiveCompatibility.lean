/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.CensoredFiniteClockOperationalEffect
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Projectively compatible finite-deadline timing Nash laws

This file isolates the honest positive content of exact compatibility.  A
family contains one actual mixed Nash law at every finite deadline, and
censoring the newly exposed date recovers the preceding law exactly.  The
new-boundary masses then telescope through the displayed Never masses and
tend to zero.  Exact censor compatibility identifies adjacent total variation
with their finite sum.  The existing adjacent-deadline estimate therefore
produces terminal approximate Nash profiles at every error and hence a
uniform-equilibrium payoff.

This route deliberately does not construct the inverse-limit stopping laws or
an exact terminal Nash profile.  It also does not construct a compatible Nash
family from deadlinewise Nash existence: the bonding map need not preserve
the Nash set.  In particular, separate minimizers of the adjacent distances
are not silently treated as an inverse system.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One exact Nash law at every finite deadline, with literal censor
compatibility between successive laws.  Deadline zero is harmless: its only
timing action is Never. -/
structure QuittingFiniteDeadlineCompatibleNashFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  mixed : ∀ deadline,
    ι → PMF (QuittingFiniteDeadlineTimingAction deadline)
  isNash : ∀ deadline,
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      (mixed deadline)
  censor_succ : ∀ deadline,
    quittingFiniteDeadlineTimingProfileCensor (mixed (deadline + 1)) =
      mixed deadline

/-- Finite positive criterion independent of inverse compatibility: exact
adjacent Nash pairs exist at arbitrarily small summed marginal TV distance.
The selected deadlines need not be cofinal.  If they remain bounded, compact
attainment would instead force an exact zero-distance pair. -/
def HasArbitrarilySmallFiniteDeadlineAdjacentNashTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ deadline : ℕ,
    ∃ old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
    ∃ new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)),
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
          old ∧
        (quittingFiniteDeadlineTimingGame reward
          (deadline + 1)).mixedExtension.IsNash new ∧
        quittingFiniteDeadlineAdjacentTV deadline old new ≤ ε

/-- A quantitatively close adjacent Nash pair produces one unrestricted
terminal approximate Nash profile. -/
theorem quittingFiniteDeadlineTimingProfile_isεAsymptoticNash_of_adjacentTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (holdNash :
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash old)
    (hnewNash :
      (quittingFiniteDeadlineTimingGame reward
        (deadline + 1)).mixedExtension.IsNash new)
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsmall : 4 * bound *
      quittingFiniteDeadlineAdjacentTV deadline old new ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingFiniteDeadlineTimingProfile reward deadline old) := by
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingFiniteDeadlineTimingProfile reward deadline old)
      who deviation
  have hdebt :=
    quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV
      reward deadline old new holdNash hnewNash who hbound hreward
  change quittingContinuationBestResponseValue reward
      (quittingFiniteDeadlineTimingProfile reward deadline old) who -
      quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline old) who ≤ _ at hdebt
  linarith

/-- **Adjacent-distance criterion.**  Arbitrarily close actual consecutive
finite timing Nash pairs produce a uniform-equilibrium payoff.  This consumes
the finite criterion without claiming that its pair selections form an
inverse system. -/
theorem exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (criterion : HasArbitrarilySmallFiniteDeadlineAdjacentNashTV reward)
    {bound : ℝ} (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  let tolerance := ε / (4 * bound)
  have htolerance : 0 < tolerance := div_pos hε (mul_pos (by norm_num) hbound)
  obtain ⟨deadline, old, new, holdNash, hnewNash, htv⟩ :=
    criterion tolerance htolerance
  have hsmall : 4 * bound * quittingFiniteDeadlineAdjacentTV deadline old new ≤ ε :=
    calc
      4 * bound * quittingFiniteDeadlineAdjacentTV deadline old new ≤
          4 * bound * tolerance :=
        mul_le_mul_of_nonneg_left htv
          (mul_nonneg (by norm_num) hbound.le)
      _ = ε := by
        dsimp only [tolerance]
        field_simp
  exact ⟨quittingFiniteDeadlineTimingProfile reward deadline old,
    quittingFiniteDeadlineTimingProfile_isεAsymptoticNash_of_adjacentTV
      reward deadline old new holdNash hnewNash hbound.le hreward hsmall⟩

namespace QuittingFiniteDeadlineCompatibleNashFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (family : QuittingFiniteDeadlineCompatibleNashFamily reward)

/-- The literal Never mass at one deadline. -/
def neverMass (deadline : ℕ) (player : ι) : ℝ :=
  (family.mixed deadline player none).toReal

/-- The mass newly exposed at one successor boundary. -/
def boundaryMass (deadline : ℕ) (player : ι) : ℝ :=
  quittingFiniteDeadlineBoundaryParticipation deadline
    (family.mixed (deadline + 1)) player

/-- Censoring a successor law adds exactly its new boundary atom to Never. -/
theorem censor_none_toReal_eq_add_boundary
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    ((law.map quittingFiniteDeadlineTimingActionCensor) none).toReal =
      (law none).toReal +
        (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
  cases deadline with
  | zero =>
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_option]
      simp [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingBoundaryAction]
      rw [ENNReal.toReal_add (PMF.apply_ne_top law none)
        (PMF.apply_ne_top law (some 0))]
  | succ deadline =>
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_option,
        Fin.sum_univ_succ]
      simp only [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingBoundaryAction, ↓reduceIte]
      rw [Finset.sum_eq_single (Fin.last deadline)]
      · simp [Fin.val_last]
        rw [ENNReal.toReal_add (PMF.apply_ne_top law none)
          (PMF.apply_ne_top law _)]
        congr 2
      · intro time _ htime
        have hlt : time.val < deadline := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ time.isLt) fun heq =>
            htime (Fin.ext heq)
        simp [hlt]
      · simp

/-- Exact telescope step for the family Never masses. -/
theorem neverMass_succ_add_boundaryMass
    (deadline : ℕ) (player : ι) :
    family.neverMass (deadline + 1) player +
        family.boundaryMass deadline player =
      family.neverMass deadline player := by
  have hcompat := congrFun (family.censor_succ deadline) player
  unfold quittingFiniteDeadlineTimingProfileCensor at hcompat
  unfold neverMass boundaryMass quittingFiniteDeadlineBoundaryParticipation
  rw [← hcompat]
  simpa [add_comm] using
    (censor_none_toReal_eq_add_boundary deadline
      (family.mixed (deadline + 1) player)).symm

/-- Never mass decreases as successive finite dates are exposed. -/
theorem neverMass_antitone (player : ι) :
    Antitone fun deadline => family.neverMass deadline player := by
  apply antitone_nat_of_succ_le
  intro deadline
  have hboundary : 0 ≤ family.boundaryMass deadline player :=
    ENNReal.toReal_nonneg
  linarith [family.neverMass_succ_add_boundaryMass deadline player]

/-- Every new-boundary mass tends to zero.  This is the difference of one
bounded monotone Never-mass sequence and its shift, not a compatibility
assumption added to the family. -/
theorem boundaryMass_tendsto_zero (player : ι) :
    Tendsto (fun deadline => family.boundaryMass deadline player)
      atTop (nhds 0) := by
  let limit : ℝ := ⨅ deadline, family.neverMass deadline player
  have hnever : Tendsto (fun deadline => family.neverMass deadline player)
      atTop (nhds limit) :=
    tendsto_atTop_ciInf (family.neverMass_antitone player)
      ⟨0, by
        rintro value ⟨deadline, rfl⟩
        exact ENNReal.toReal_nonneg⟩
  have hneverSucc : Tendsto
      (fun deadline => family.neverMass (deadline + 1) player)
      atTop (nhds limit) :=
    hnever.comp (tendsto_add_atTop_nat 1)
  have hdifference := hnever.sub hneverSucc
  have heq : Filter.EventuallyEq atTop
      (fun deadline => family.neverMass deadline player -
        family.neverMass (deadline + 1) player)
      (fun deadline => family.boundaryMass deadline player) :=
    Filter.Eventually.of_forall fun deadline => by
      linarith [family.neverMass_succ_add_boundaryMass deadline player]
  simpa only [sub_self] using hdifference.congr' heq

/-- Under exact censor compatibility, adjacent total variation is exactly the
sum of newly exposed boundary masses. -/
theorem adjacentTV_eq_sum_boundaryMass (deadline : ℕ) :
    quittingFiniteDeadlineAdjacentTV deadline (family.mixed deadline)
        (family.mixed (deadline + 1)) =
      ∑ player, family.boundaryMass deadline player := by
  unfold quittingFiniteDeadlineAdjacentTV
    quittingFiniteDeadlineTimingProfileInclude boundaryMass
    quittingFiniteDeadlineBoundaryParticipation
  apply Finset.sum_congr rfl
  intro player _
  have hcompat := congrFun (family.censor_succ deadline) player
  unfold quittingFiniteDeadlineTimingProfileCensor at hcompat
  rw [← hcompat]
  exact pmfTV_quittingFiniteDeadline_include_censor_eq_boundary deadline
    (family.mixed (deadline + 1) player)

/-- Exact compatibility forces adjacent Nash distances to vanish. -/
theorem adjacentTV_tendsto_zero :
    Tendsto (fun deadline => quittingFiniteDeadlineAdjacentTV deadline
      (family.mixed deadline) (family.mixed (deadline + 1)))
      atTop (nhds 0) := by
  simp_rw [family.adjacentTV_eq_sum_boundaryMass]
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ fun player _ =>
      family.boundaryMass_tendsto_zero player

/-- One sufficiently compatible adjacent pair is an unrestricted terminal
approximate Nash profile. -/
theorem isεAsymptoticNash_of_adjacentTV
    (deadline : ℕ) {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsmall : 4 * bound * quittingFiniteDeadlineAdjacentTV deadline
      (family.mixed deadline) (family.mixed (deadline + 1)) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingFiniteDeadlineTimingProfile reward deadline
        (family.mixed deadline)) := by
  exact quittingFiniteDeadlineTimingProfile_isεAsymptoticNash_of_adjacentTV
    reward deadline (family.mixed deadline) (family.mixed (deadline + 1))
    (family.isNash deadline) (family.isNash (deadline + 1)) hbound hreward hsmall

/-- Exact projective compatibility internally produces the adjacent-distance
criterion. -/
theorem hasArbitrarilySmallAdjacentNashTV
    (family : QuittingFiniteDeadlineCompatibleNashFamily reward) :
    HasArbitrarilySmallFiniteDeadlineAdjacentNashTV reward := by
  intro ε hε
  obtain ⟨deadline, hdeadline⟩ :=
    Metric.tendsto_atTop.1 (adjacentTV_tendsto_zero family) ε hε
  have hnonneg : 0 ≤ quittingFiniteDeadlineAdjacentTV deadline
      (family.mixed deadline) (family.mixed (deadline + 1)) :=
    Finset.sum_nonneg fun player _ => Math.Probability.pmfTV_nonneg _ _
  have hsmall : quittingFiniteDeadlineAdjacentTV deadline
      (family.mixed deadline) (family.mixed (deadline + 1)) ≤ ε := by
    have hdistance := hdeadline deadline le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hdistance
    exact hdistance.le
  exact ⟨deadline, family.mixed deadline, family.mixed (deadline + 1),
    family.isNash deadline, family.isNash (deadline + 1), hsmall⟩

/-- **Compatible-family consumer.**  A supplied exact projective family of
finite timing Nash laws produces a uniform-equilibrium payoff.  The family is
the only conditional input; its boundary decay and the terminal approximate
profiles are derived internally. -/
theorem exists_uniformEquilibriumPayoff
    (family : QuittingFiniteDeadlineCompatibleNashFamily reward)
    {bound : ℝ} (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV
    reward (hasArbitrarilySmallAdjacentNashTV family) hbound hreward

end QuittingFiniteDeadlineCompatibleNashFamily

end GameTheory
