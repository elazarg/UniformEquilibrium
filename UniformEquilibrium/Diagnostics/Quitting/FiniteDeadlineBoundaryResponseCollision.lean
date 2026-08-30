/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineGapSource
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingStageCoalitionMass
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization

/-!
# Boundary-response collision cylinders at finite deadlines

The boundary-participation arm of an adjacent deadline source contains one
new-date participant with quantitative mass.  Applying the global terminal
gap independently to the successor Nash profile selects an escape owner with
positive singleton reward and a product floor on its opponents' declared
`Never` masses.  A distinct deterministic boundary responder then exposes a
literal two-player collision cylinder.

The cylinder belongs to a counterfactual pure response.  This file does not
assert that the response is profitable or that the collision occurs under
prescribed play.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On a finite timing-law realization, survival of all opponents to the
deadline is exactly the product of their declared `Never` masses. -/
theorem quittingFiniteDeadlineOpponentSurvival_timingProfile_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingFiniteDeadlineOpponentSurvival reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed)
        deadline who =
      ∏ other ∈ Finset.univ.erase who, (mixed other none).toReal := by
  unfold quittingFiniteDeadlineOpponentSurvival
  rw [quittingOpponentSurvivalWeight_eq_prod_hazardSurvival]
  apply Finset.prod_congr rfl
  intro other _
  rw [quittingHazardSurvival_eq_prod]
  have hstack :=
    quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed other
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailMixedTimingRootStack at hstack
  rw [List.map_ofFn, List.prod_ofFn] at hstack
  rw [← Fin.prod_univ_eq_prod_range]
  simpa only [Function.comp_apply] using hstack

/-- The product-cylinder in which `participant` uses the new boundary atom,
`responder` deterministically uses that same atom, and every other player
declares `Never`. -/
def quittingFiniteDeadlineBoundaryResponseCylinderMass
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (responder participant : ι) : ℝ :=
  quittingFiniteDeadlineBoundaryParticipation deadline mixed participant *
    ∏ other ∈ (Finset.univ.erase responder).erase participant,
      (mixed other none).toReal

/-- The literal mixed timing response profile which forces one player to
quit at the newly exposed boundary date. -/
def quittingFiniteDeadlineBoundaryResponseProfile
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (responder : ι) :
    ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
  Function.update mixed responder
    (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction deadline))

/-- Source-faithful data for the quantitative counterfactual collision
cylinder.  The escape owner is selected from the successor profile and is
not conflated with the old boundary observer. -/
structure QuittingFiniteDeadlineBoundaryResponseCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gamma bound : ℝ) where
  source : QuittingAdjacentDeadlineGapSource reward gamma bound
  escapeOwner : ι
  responder : ι
  participant : ι
  responder_ne_participant : responder ≠ participant
  escapeSingleton_pos :
    0 < reward (quittingSingletonTerminal escapeOwner) escapeOwner
  escapeOpponentNever_ge : gamma / bound ≤
    ∏ other ∈ Finset.univ.erase escapeOwner,
      (source.new other none).toReal
  participantBoundary_ge : gamma /
      (8 * bound * (Fintype.card ι : ℝ)) ≤
    quittingFiniteDeadlineBoundaryParticipation source.deadline
      source.new participant
  cylinder_ge : gamma / (8 * bound * (Fintype.card ι : ℝ)) *
      (gamma / bound) ^ (Fintype.card ι - 2) ≤
    quittingFiniteDeadlineBoundaryResponseCylinderMass source.deadline
      source.new responder participant

namespace QuittingFiniteDeadlineBoundaryResponseCollision

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}

/-- The actual behavioral response profile represented by the collision
certificate. -/
def behavioralResponse
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound) :
    (quittingGame reward).BehaviorProfile :=
  quittingFiniteDeadlineTimingProfile reward (collision.source.deadline + 1)
    (quittingFiniteDeadlineBoundaryResponseProfile collision.source.deadline
      collision.source.new collision.responder)

/-- Every opponent of the selected escape owner inherits the displayed
`Never` floor from the opponent product. -/
theorem opponentNever_ge
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound)
    {other : ι} (hother : other ≠ collision.escapeOwner) :
    gamma / bound ≤ (collision.source.new other none).toReal := by
  have hmem : other ∈ Finset.univ.erase collision.escapeOwner := by
    simp [hother]
  have hfactor0 : ∀ player ∈ Finset.univ.erase collision.escapeOwner,
      0 ≤ (collision.source.new player none).toReal :=
    fun _ _ => ENNReal.toReal_nonneg
  have hfactor1 : ∀ player ∈ Finset.univ.erase collision.escapeOwner,
      (collision.source.new player none).toReal ≤ 1 := by
    intro player _
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((collision.source.new player).coe_le_one none)
  have hrest : (∏ player ∈
      (Finset.univ.erase collision.escapeOwner).erase other,
        (collision.source.new player none).toReal) ≤ 1 :=
    Finset.prod_le_one
      (fun player hplayer => hfactor0 player
        (Finset.mem_of_mem_erase hplayer))
      (fun player hplayer => hfactor1 player
        (Finset.mem_of_mem_erase hplayer))
  have hproductLe : (∏ player ∈ Finset.univ.erase collision.escapeOwner,
      (collision.source.new player none).toReal) ≤
        (collision.source.new other none).toReal := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase collision.escapeOwner)
      (fun player => (collision.source.new player none).toReal) hmem]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg hrest
  exact collision.escapeOpponentNever_ge.trans hproductLe

/-- The literal pair terminal used by the counterfactual boundary response. -/
def behavioralStagePairTerminal
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{collision.responder, collision.participant}, by simp⟩

/-- Actual behavioral mass of the displayed pair at the newly exposed
boundary stage. -/
def behavioralStagePairMass
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound) : ℝ :=
  quittingStageCoalitionMass reward collision.behavioralResponse
    collision.source.deadline collision.behavioralStagePairTerminal

/-- The counterfactual cylinder is exactly an actual behavioral-stage pair
atom, not only a product-law proxy. -/
theorem behavioralStagePairMass_eq_cylinderMass
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound) :
    collision.behavioralStagePairMass =
      quittingFiniteDeadlineBoundaryResponseCylinderMass
        collision.source.deadline collision.source.new
        collision.responder collision.participant := by
  unfold behavioralStagePairMass behavioralResponse
    behavioralStagePairTerminal
  rw [quittingStageCoalitionMass_finiteDeadlineTimingProfile_boundary_eq]
  unfold quittingFiniteDeadlineBoundaryResponseCylinderMass
    quittingFiniteDeadlineBoundaryResponseProfile
    quittingFiniteDeadlineBoundaryParticipation
  have hboundary : some (Fin.last collision.source.deadline) =
      quittingFiniteDeadlineTimingBoundaryAction
        collision.source.deadline := rfl
  rw [hboundary]
  rw [Finset.prod_insert (by simp [collision.responder_ne_participant]),
    Finset.prod_singleton, Function.update_self,
    Function.update_of_ne collision.responder_ne_participant.symm]
  simp only [PMF.pure_apply, if_pos, ENNReal.toReal_one, one_mul]
  have hcomplement :
      ({collision.responder, collision.participant} : Finset ι)ᶜ =
        (Finset.univ.erase collision.responder).erase
          collision.participant := by
    ext other
    simp [and_comm]
  rw [hcomplement]
  apply congrArg
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne]
  exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hother)

/-- The general collision floor is carried by the actual behavioral-stage
pair atom. -/
theorem behavioralStagePairMass_ge
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound) :
    gamma / (8 * bound * (Fintype.card ι : ℝ)) *
        (gamma / bound) ^ (Fintype.card ι - 2) ≤
      collision.behavioralStagePairMass := by
  rw [collision.behavioralStagePairMass_eq_cylinderMass]
  exact collision.cylinder_ge

private theorem exists_boundaryParticipant_ge_average
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hboundary : gamma / (8 * bound) ≤ source.boundaryParticipationMass) :
    ∃ participant, gamma / (8 * bound * (Fintype.card ι : ℝ)) ≤
      quittingFiniteDeadlineBoundaryParticipation source.deadline
        source.new participant := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp <| by
    by_contra hzero
    have hcard : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos hzero
    letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    have hemptySum : source.boundaryParticipationMass = 0 := by
      unfold QuittingAdjacentDeadlineGapSource.boundaryParticipationMass
      simp
    rw [hemptySum] at hboundary
    have hpositive : 0 < gamma / (8 * bound) := by positivity
    linarith
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by positivity
  let average := gamma / (8 * bound * (Fintype.card ι : ℝ))
  have hsum : (∑ _player : ι, average) ≤
      ∑ player, quittingFiniteDeadlineBoundaryParticipation source.deadline
        source.new player := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    dsimp only [average]
    have heq : (Fintype.card ι : ℝ) *
        (gamma / (8 * bound * (Fintype.card ι : ℝ))) =
      gamma / (8 * bound) := by field_simp
    rw [heq]
    exact hboundary
  obtain ⟨participant, _, hparticipant⟩ :=
    Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨participant, hparticipant⟩

/-- Construct the boundary-response collision from the boundary arm of the
adjacent `e+b` split. -/
noncomputable def of_boundaryParticipation
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hcard : 2 ≤ Fintype.card ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (gap : HasTerminalExploitabilityGap reward gamma)
    (hboundary : gamma / (8 * bound) ≤ source.boundaryParticipationMass) :
    QuittingFiniteDeadlineBoundaryResponseCollision reward gamma bound := by
  let newProfile := quittingFiniteDeadlineTimingProfile reward
    (source.deadline + 1) source.new
  let newCertificate := quittingFiniteDeadlineTimingProfile_isFiniteDeadline
    reward (source.deadline + 1) source.new source.newNash
  let escapeOwner := Classical.choose <| gap.exists_debt_ge newProfile
  have hescapeDebt := Classical.choose_spec <| gap.exists_debt_ge newProfile
  have hescapeCharge := newCertificate.semanticDebt_le_escapeCharge escapeOwner
  have hcharge : gamma ≤ quittingFiniteDeadlineEscapeCharge reward newProfile
      (source.deadline + 1) escapeOwner := hescapeDebt.trans hescapeCharge
  have hsurvival0 := quittingFiniteDeadlineOpponentSurvival_nonneg reward
    newProfile (source.deadline + 1) escapeOwner
  have hsurvival1 := quittingFiniteDeadlineOpponentSurvival_le_one reward
    newProfile (source.deadline + 1) escapeOwner
  have hsoloBound := hreward (quittingSingletonTerminal escapeOwner) escapeOwner
  have hsoloPos :
      0 < reward (quittingSingletonTerminal escapeOwner) escapeOwner := by
    unfold quittingFiniteDeadlineEscapeCharge at hcharge
    by_contra hnonpos
    rw [max_eq_left (le_of_not_gt hnonpos), mul_zero] at hcharge
    linarith
  have hsoloLe : reward (quittingSingletonTerminal escapeOwner) escapeOwner ≤ bound :=
    le_of_abs_le hsoloBound
  have hsurvivalFloor : gamma / bound ≤
      quittingFiniteDeadlineOpponentSurvival reward newProfile
        (source.deadline + 1) escapeOwner := by
    unfold quittingFiniteDeadlineEscapeCharge at hcharge
    rw [max_eq_right hsoloPos.le] at hcharge
    apply (div_le_iff₀ hbound).2
    nlinarith [mul_le_mul_of_nonneg_left hsoloLe hsurvival0]
  have hsurvivalEq :
      quittingFiniteDeadlineOpponentSurvival reward newProfile
          (source.deadline + 1) escapeOwner =
        ∏ other ∈ Finset.univ.erase escapeOwner,
          (source.new other none).toReal := by
    exact quittingFiniteDeadlineOpponentSurvival_timingProfile_eq_prod_none
      reward (source.deadline + 1) source.new escapeOwner
  have hneverFloor : ∀ other, other ≠ escapeOwner →
      gamma / bound ≤ (source.new other none).toReal := by
    intro other hother
    rw [hsurvivalEq] at hsurvivalFloor
    have hfactor0 : ∀ player ∈ Finset.univ.erase escapeOwner,
        0 ≤ (source.new player none).toReal := fun _ _ => ENNReal.toReal_nonneg
    have hfactor1 : ∀ player ∈ Finset.univ.erase escapeOwner,
        (source.new player none).toReal ≤ 1 := by
      intro player _
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((source.new player).coe_le_one none)
    have hmem : other ∈ Finset.univ.erase escapeOwner := by simp [hother]
    have hrest : (∏ player ∈ (Finset.univ.erase escapeOwner).erase other,
        (source.new player none).toReal) ≤ 1 :=
      Finset.prod_le_one
        (fun player hplayer => hfactor0 player
          (Finset.mem_of_mem_erase hplayer))
        (fun player hplayer => hfactor1 player
          (Finset.mem_of_mem_erase hplayer))
    have hprodLe : (∏ player ∈ Finset.univ.erase escapeOwner,
        (source.new player none).toReal) ≤ (source.new other none).toReal := by
      rw [← Finset.mul_prod_erase (Finset.univ.erase escapeOwner)
        (fun player => (source.new player none).toReal) hmem]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg hrest
    exact hsurvivalFloor.trans hprodLe
  let participant := Classical.choose <|
    exists_boundaryParticipant_ge_average source hgamma hbound hboundary
  have hparticipant := Classical.choose_spec <|
    exists_boundaryParticipant_ge_average source hgamma hbound hboundary
  have hcard' : 1 < Fintype.card ι := by omega
  let responder := if h : participant ≠ escapeOwner then escapeOwner
    else Classical.choose (Fintype.exists_ne_of_one_lt_card hcard' escapeOwner)
  have hresponderParticipant : responder ≠ participant := by
    dsimp only [responder]
    split_ifs with h
    · exact h.symm
    · have hparticipantEscape : participant = escapeOwner := not_ne_iff.mp h
      rw [hparticipantEscape]
      exact Classical.choose_spec
        (Fintype.exists_ne_of_one_lt_card hcard' escapeOwner)
  have hremainingNe : ∀ other,
      other ∈ (Finset.univ.erase responder).erase participant →
        other ≠ escapeOwner := by
    intro other hother
    by_cases h : participant ≠ escapeOwner
    · have hresponder : responder = escapeOwner := by simp [responder, h]
      rw [hresponder] at hother
      exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hother)
    · have hparticipantEscape : participant = escapeOwner := not_ne_iff.mp h
      exact fun heq =>
        (Finset.ne_of_mem_erase hother) (heq.trans hparticipantEscape.symm)
  have hfloor0 : 0 ≤ gamma / bound := (div_pos hgamma hbound).le
  have hproduct : (gamma / bound) ^ (Fintype.card ι - 2) ≤
      ∏ other ∈ (Finset.univ.erase responder).erase participant,
        (source.new other none).toReal := by
    -- The helper is deadline-polymorphic after elaboration of its mixed law.
    have hprod := Finset.prod_le_prod
      (s := (Finset.univ.erase responder).erase participant)
      (fun _ _ => hfloor0)
      (fun other hother => hneverFloor other (hremainingNe other hother))
    have hsetCard : ((Finset.univ.erase responder).erase participant).card =
        Fintype.card ι - 2 := by
      have hparticipantMem : participant ∈ Finset.univ.erase responder := by
        simp [hresponderParticipant.symm]
      rw [Finset.card_erase_of_mem hparticipantMem,
        Finset.card_erase_of_mem (Finset.mem_univ responder), Finset.card_univ]
      omega
    change (∏ _other ∈ (Finset.univ.erase responder).erase participant,
      gamma / bound) ≤ _ at hprod
    rw [Finset.prod_const, hsetCard] at hprod
    exact hprod
  have hcylinder : gamma / (8 * bound * (Fintype.card ι : ℝ)) *
        (gamma / bound) ^ (Fintype.card ι - 2) ≤
      quittingFiniteDeadlineBoundaryResponseCylinderMass source.deadline
        source.new responder participant := by
    unfold quittingFiniteDeadlineBoundaryResponseCylinderMass
    exact mul_le_mul hparticipant hproduct (pow_nonneg hfloor0 _)
      ENNReal.toReal_nonneg
  exact
    { source := source
      escapeOwner := escapeOwner
      responder := responder
      participant := participant
      responder_ne_participant := hresponderParticipant
      escapeSingleton_pos := hsoloPos
      escapeOpponentNever_ge := hsurvivalEq ▸ hsurvivalFloor
      participantBoundary_ge := hparticipant
      cylinder_ge := hcylinder }

/-- Four-player specialization of the collision-cylinder floor. -/
theorem cylinder_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound)
    (hbound : 0 < bound) :
    gamma ^ 3 / (32 * bound ^ 3) ≤
      quittingFiniteDeadlineBoundaryResponseCylinderMass
        collision.source.deadline collision.source.new
        collision.responder collision.participant := by
  have h := collision.cylinder_ge
  norm_num only [Fintype.card_fin, Nat.reduceSubDiff] at h
  have hscale : gamma / (8 * bound * 4) * (gamma / bound) ^ 2 =
      gamma ^ 3 / (32 * bound ^ 3) := by
    field_simp
    ring
  rw [← hscale]
  exact h

/-- Four-player floor on the literal actual behavioral-stage pair atom. -/
theorem behavioralStagePairMass_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (collision : QuittingFiniteDeadlineBoundaryResponseCollision
      reward gamma bound)
    (hbound : 0 < bound) :
    gamma ^ 3 / (32 * bound ^ 3) ≤
      collision.behavioralStagePairMass := by
  rw [collision.behavioralStagePairMass_eq_cylinderMass]
  exact collision.cylinder_ge_finFour hbound

end QuittingFiniteDeadlineBoundaryResponseCollision

end GameTheory
