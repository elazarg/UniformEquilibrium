/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineRetainedTailReprojection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport

/-!
# Adjacent-deadline singleton-separated-tail dispatch

A supplied adjacent exact timing source and a supplied actual behavioral tail
whose payoff is uniformly separated from every own singleton reward yield four
literal outputs: lossless zero-`Never` response, paid pass response, paid
reverse participant, or the unresolved raw censor-error arm.

The dispatch is conditional on the displayed source and tail.  It does not
select either object, place the tail on a minimum fibre, make the tail Nash, or
produce chronology, return, renewal, terminal approximation, or a
uniform-equilibrium payoff.  The raw censor-error arm is returned unchanged.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem pmf_apply_toReal_sub_le_pmfTV
    {action : Type} [Fintype action]
    (first second : PMF action) (choice : action) :
    (first choice).toReal - (second choice).toReal ≤
      Math.Probability.pmfTV first second := by
  change _ ≤ ∑ other, max
    ((first other).toReal - (second other).toReal) 0
  calc
    (first choice).toReal - (second choice).toReal ≤
        max ((first choice).toReal - (second choice).toReal) 0 :=
      le_max_left _ _
    _ ≤ ∑ other, max
        ((first other).toReal - (second other).toReal) 0 :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun other =>
          max ((first other).toReal - (second other).toReal) 0)
        (fun other _ => le_max_right _ _) (Finset.mem_univ choice)

private theorem product_erase_le_factor
    (f : ι → ℝ) (owner other : ι) (hother : other ≠ owner)
    (hzero : ∀ player, 0 ≤ f player) (hone : ∀ player, f player ≤ 1) :
    (∏ player ∈ Finset.univ.erase owner, f player) ≤ f other := by
  have hmem : other ∈ Finset.univ.erase owner := by simp [hother]
  rw [← Finset.mul_prod_erase (Finset.univ.erase owner) f hmem]
  exact mul_le_of_le_one_right (hzero other) <|
    Finset.prod_le_one
      (fun player _ => hzero player)
      (fun player _ => hone player)

/-! ## Unrestricted cap and exact debt transport -/

/-- The reverse participant update keeps the mover's unrestricted behavioral
best-response value unchanged. -/
theorem finiteDeadlineCensoredGraft_bestResponseValue_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :
    quittingContinuationBestResponseValue reward
        (quittingAdjacentDeadlineCensoredGraft source tail) participant =
      quittingContinuationBestResponseValue reward
        (quittingAdjacentDeadlineParticipantGraft source tail participant)
        participant := by
  rw [quittingAdjacentDeadlineCensoredGraft_eq_update_participant,
    quittingContinuationBestResponseValue_update_self]

/-- Exact mover-debt subtraction along the reverse participant update. -/
theorem finiteDeadlineCensoredGraft_semanticDebt_eq_sub_payoffGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAdjacentDeadlineCensoredGraft source tail)) participant =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant))
          participant -
        (quittingTerminalPayoff reward
            (quittingAdjacentDeadlineCensoredGraft source tail) participant -
          quittingTerminalPayoff reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant)
            participant) := by
  rw [quittingAdjacentDeadlineCensoredGraft_eq_update_participant]
  exact quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward (quittingAdjacentDeadlineParticipantGraft source tail participant)
      participant
      (quittingAdjacentDeadlineCensoredGraft source tail participant)

/-- Quantitative reverse-edge floor once a participant carries the averaged
boundary mass and the censored opponent cylinder has the reviewed lower
bound.  The later dispatch proves these two localization hypotheses. -/
theorem finiteDeadlineCensoredGraft_payoffGain_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (htail : delta / 2 ≤
      quittingTerminalPayoff reward tail participant -
        reward (quittingSingletonTerminal participant) participant)
    (hboundary : gamma / (8 * bound * (Fintype.card ι : ℝ)) ≤
      (source.new participant
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal)
    (hcylinder :
      (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) *
          (gamma / bound) ≤
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant) :
    3 * delta * (gamma / bound) ^ 2 /
          (64 * (Fintype.card ι : ℝ)) *
        (7 / 8 : ℝ) ^ (Fintype.card ι - 2) ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant := by
  rw [finiteDeadlineCensoredGraft_sub_participantGraft_eq]
  have hcardNat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨participant⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  have hpow : 0 ≤ (7 / 8 : ℝ) ^ (Fintype.card ι - 2) := by positivity
  have hboundaryNonneg : 0 ≤ (source.new participant
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal :=
    ENNReal.toReal_nonneg
  have hcylinderNonneg : 0 ≤
      quittingAdjacentDeadlineCensoredOpponentNeverProduct
        source participant := by
    unfold quittingAdjacentDeadlineCensoredOpponentNeverProduct
    exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  calc
    3 * delta * (gamma / bound) ^ 2 /
          (64 * (Fintype.card ι : ℝ)) *
        (7 / 8 : ℝ) ^ (Fintype.card ι - 2) =
      (gamma / (8 * bound * (Fintype.card ι : ℝ))) *
        ((3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) *
          (gamma / bound)) * (delta / 2) := by
        field_simp
        ring
    _ ≤ (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant *
        (quittingTerminalPayoff reward tail participant -
          reward (quittingSingletonTerminal participant) participant) := by
      gcongr

/-! ## Localization from the adjacent source -/

/-- Positive old observer support converts the selected old boundary gain
into a lower bound on the old opponent-`Never` product. -/
theorem quittingAdjacentDeadlineOldOpponentNeverProduct_ge_div_of_support
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsupport : source.old source.observer none ≠ 0) :
    gamma / bound ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source := by
  have hgainEq := finiteDeadline_supportNever_boundaryGain_eq source hsupport
  have hgain := source.oldBoundaryGain_ge
  rw [hgainEq] at hgain
  have hre := le_of_abs_le
    (hreward (quittingSingletonTerminal source.observer) source.observer)
  have hproduct :
      0 ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    unfold quittingAdjacentDeadlineOldOpponentNeverProduct
    exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  apply (div_le_iff₀ hbound).2
  calc
    gamma ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source *
        reward (quittingSingletonTerminal source.observer) source.observer := hgain
    _ ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source * bound := by
      gcongr

/-- Every old opponent `Never` coefficient inherits the old product floor. -/
theorem quittingAdjacentDeadlineOldNever_ge_div_of_ne_observer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsupport : source.old source.observer none ≠ 0)
    {other : ι} (hother : other ≠ source.observer) :
    gamma / bound ≤ (source.old other none).toReal := by
  exact
    (quittingAdjacentDeadlineOldOpponentNeverProduct_ge_div_of_support
      source hbound hreward hsupport).trans <|
    product_erase_le_factor
      (fun player => (source.old player none).toReal)
      source.observer other hother
      (fun _ => ENNReal.toReal_nonneg)
      (fun player => ENNReal.toReal_mono ENNReal.one_ne_top
        ((source.old player).coe_le_one none))

/-- The spectator condition and `gamma / bound ≤ 1` imply literal positive
old observer `Never` support. -/
theorem quittingAdjacentDeadlineOldObserverNever_ne_zero_of_smallPass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hscale : gamma / bound ≤ 1)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8) :
    source.old source.observer none ≠ 0 := by
  have hscalePos : 0 < gamma / bound := div_pos hgamma hbound
  have hneverPos : 0 < (source.old source.observer none).toReal := by
    nlinarith
  intro hzero
  rw [hzero] at hneverPos
  exact (lt_irrefl 0) hneverPos

private theorem censoredError_lt_of_total_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound threshold : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (htotal : source.censoredErrorMass < threshold) (player : ι) :
    quittingFiniteDeadlineCensoredError source.deadline source.old source.new
        player < threshold := by
  apply lt_of_le_of_lt _ htotal
  unfold QuittingAdjacentDeadlineGapSource.censoredErrorMass
  exact Finset.single_le_sum
    (fun other _ => Math.Probability.pmfTV_nonneg _ _)
    (Finset.mem_univ player)

private theorem oldNever_sub_censoredError_le_censoredNever
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (player : ι) :
    (source.old player none).toReal -
        quittingFiniteDeadlineCensoredError source.deadline source.old source.new
          player ≤
      ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal := by
  unfold quittingFiniteDeadlineCensoredError
  have h := pmf_apply_toReal_sub_le_pmfTV
    (source.old player)
    (quittingFiniteDeadlineTimingProfileCensor source.new player) none
  linarith

private theorem distinguished_product_erase_ge
    (old censored : ι → ℝ) (owner selected : ι) (a : ℝ)
    (holdNonneg : ∀ player, 0 ≤ old player)
    (holdLeOne : ∀ player, old player ≤ 1)
    (hcensoredNonneg : ∀ player, 0 ≤ censored player)
    (howner : (3 / 4 : ℝ) ≤ censored owner)
    (hothers : ∀ player, player ≠ owner →
      (7 / 8 : ℝ) * old player ≤ censored player)
    (ha : 0 ≤ a)
    (holdProduct : a ≤ ∏ player ∈ Finset.univ.erase owner, old player) :
    (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) * a ≤
      ∏ player ∈ Finset.univ.erase selected, censored player := by
  have hcardPos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨owner⟩
  by_cases hselected : selected = owner
  · subst selected
    have hprod :
        (∏ player ∈ Finset.univ.erase owner,
            (7 / 8 : ℝ) * old player) ≤
          ∏ player ∈ Finset.univ.erase owner, censored player := by
      exact Finset.prod_le_prod
        (fun player _ => mul_nonneg (by norm_num) (holdNonneg player))
        (fun player hplayer => hothers player (Finset.ne_of_mem_erase hplayer))
    have hcoefficient :
        (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) ≤
          (7 / 8 : ℝ) ^ (Fintype.card ι - 1) := by
      by_cases hcardOne : Fintype.card ι = 1
      · simp [hcardOne]
        norm_num
      · have hcardTwo : 2 ≤ Fintype.card ι := by omega
        rw [show Fintype.card ι - 1 =
          (Fintype.card ι - 2) + 1 by omega, pow_succ]
        have hpow : 0 ≤ (7 / 8 : ℝ) ^ (Fintype.card ι - 2) := by
          positivity
        nlinarith
    calc
      (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) * a ≤
          (7 / 8 : ℝ) ^ (Fintype.card ι - 1) * a := by
        gcongr
      _ ≤ (7 / 8 : ℝ) ^ (Fintype.card ι - 1) *
          (∏ player ∈ Finset.univ.erase owner, old player) := by
        gcongr
      _ = ∏ player ∈ Finset.univ.erase owner,
          ((7 / 8 : ℝ) * old player) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_erase_of_mem,
          Finset.mem_univ, Finset.card_univ]
      _ ≤ ∏ player ∈ Finset.univ.erase owner, censored player := hprod
  · have hownerMem : owner ∈ Finset.univ.erase selected := by
      simp [Ne.symm hselected]
    have hselectedMem : selected ∈ Finset.univ.erase owner := by
      simp [hselected]
    let rest := (Finset.univ.erase selected).erase owner
    have hrestEq : rest = (Finset.univ.erase owner).erase selected := by
      ext player
      simp [rest, and_comm]
    have hrestCard : rest.card = Fintype.card ι - 2 := by
      dsimp only [rest]
      rw [Finset.card_erase_of_mem hownerMem,
        Finset.card_erase_of_mem (Finset.mem_univ selected),
        Finset.card_univ]
      omega
    have hprodRest :
        (∏ player ∈ rest, (7 / 8 : ℝ) * old player) ≤
          ∏ player ∈ rest, censored player := by
      exact Finset.prod_le_prod
        (fun player _ => mul_nonneg (by norm_num) (holdNonneg player))
        (fun player hplayer => by
          apply hothers
          exact Finset.ne_of_mem_erase hplayer)
    have holdProductLeRest :
        (∏ player ∈ Finset.univ.erase owner, old player) ≤
          ∏ player ∈ rest, old player := by
      rw [← Finset.mul_prod_erase (Finset.univ.erase owner) old hselectedMem,
        ← hrestEq]
      exact mul_le_of_le_one_left
        (Finset.prod_nonneg fun player _ => holdNonneg player)
        (holdLeOne selected)
    rw [← Finset.mul_prod_erase (Finset.univ.erase selected) censored
      hownerMem]
    calc
      (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) * a ≤
          (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) *
            (∏ player ∈ rest, old player) := by
        exact mul_le_mul_of_nonneg_left
          (holdProduct.trans holdProductLeRest)
          (mul_nonneg (by norm_num) (by positivity))
      _ = (3 / 4 : ℝ) *
          (∏ player ∈ rest, (7 / 8 : ℝ) * old player) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, hrestCard]
        ring
      _ ≤ censored owner *
          (∏ player ∈ rest, censored player) := by
        exact mul_le_mul howner hprodRest
          (Finset.prod_nonneg fun player _ =>
            mul_nonneg (by norm_num) (holdNonneg player))
          (hcensoredNonneg owner)

private theorem censoredOpponentNeverProduct_ge_of_small_pass_and_error
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (selected : ι)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsupport : source.old source.observer none ≠ 0)
    (hpassSmall : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (herrorSmall : source.censoredErrorMass < gamma / bound / 8) :
    (3 / 4 : ℝ) * (7 / 8 : ℝ) ^ (Fintype.card ι - 2) *
          (gamma / bound) ≤
      quittingAdjacentDeadlineCensoredOpponentNeverProduct source selected := by
  let oldNever := fun player => (source.old player none).toReal
  let censoredNever := fun player =>
    ((quittingFiniteDeadlineTimingProfileCensor source.new) player none).toReal
  have ha : 0 ≤ gamma / bound := (div_pos hgamma hbound).le
  have holdProduct :=
    quittingAdjacentDeadlineOldOpponentNeverProduct_ge_div_of_support
    source hbound hreward hsupport
  have holdProductLeOne :
      quittingAdjacentDeadlineOldOpponentNeverProduct source ≤ 1 := by
    unfold quittingAdjacentDeadlineOldOpponentNeverProduct
    exact Finset.prod_le_one
      (fun player _ => ENNReal.toReal_nonneg)
      (fun player _ => ENNReal.toReal_mono ENNReal.one_ne_top
        ((source.old player).coe_le_one none))
  have haLeOne : gamma / bound ≤ 1 :=
    holdProduct.trans holdProductLeOne
  have herror : ∀ player,
      quittingFiniteDeadlineCensoredError source.deadline source.old source.new
          player < gamma / bound / 8 :=
    censoredError_lt_of_total_lt source herrorSmall
  have hcensoredLower : ∀ player,
      oldNever player -
          quittingFiniteDeadlineCensoredError source.deadline source.old
            source.new player ≤ censoredNever player :=
    oldNever_sub_censoredError_le_censoredNever source
  have howner : (3 / 4 : ℝ) ≤ censoredNever source.observer := by
    have holdNear :
        1 - gamma / bound / 8 < oldNever source.observer := by
      dsimp only [oldNever]
      linarith
    have hcensor := hcensoredLower source.observer
    have he := herror source.observer
    dsimp only [oldNever, censoredNever] at holdNear hcensor
    linarith
  have hothers : ∀ player, player ≠ source.observer →
      (7 / 8 : ℝ) * oldNever player ≤ censoredNever player := by
    intro player hplayer
    have hold := quittingAdjacentDeadlineOldNever_ge_div_of_ne_observer
      source hbound hreward hsupport hplayer
    have hcensor := hcensoredLower player
    have he := herror player
    dsimp only [oldNever, censoredNever] at hold hcensor
    nlinarith
  apply distinguished_product_erase_ge oldNever censoredNever
    source.observer selected (gamma / bound)
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun player => ENNReal.toReal_mono ENNReal.one_ne_top
      ((source.old player).coe_le_one none)
  · exact fun _ => ENNReal.toReal_nonneg
  · exact howner
  · exact hothers
  · exact ha
  · exact holdProduct

/-- Some successor-boundary participant carries at least the average of any
supplied lower bound on total boundary participation. -/
theorem exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average_of_total
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound total : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hboundary : total ≤ source.boundaryParticipationMass) :
    ∃ participant,
      total / (Fintype.card ι : ℝ) ≤
        (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨source.observer⟩
  let average := total / (Fintype.card ι : ℝ)
  have hsum : (∑ _player : ι, average) ≤
      ∑ player, (source.new player
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    dsimp only [average]
    have heq : (Fintype.card ι : ℝ) *
        (total / (Fintype.card ι : ℝ)) = total := by field_simp
    rw [heq]
    simpa [QuittingAdjacentDeadlineGapSource.boundaryParticipationMass,
      quittingFiniteDeadlineBoundaryParticipation] using hboundary
  obtain ⟨participant, _, hparticipant⟩ :=
    Finset.exists_le_of_sum_le
      (show (Finset.univ : Finset ι).Nonempty from
        ⟨source.observer, Finset.mem_univ source.observer⟩)
      hsum
  exact ⟨participant, hparticipant⟩

/-- Robust-dispatch specialization of the arbitrary boundary-mass averaging
helper. -/
theorem exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hboundary : gamma / (8 * bound) ≤ source.boundaryParticipationMass) :
    ∃ participant,
      gamma / (8 * bound * (Fintype.card ι : ℝ)) ≤
        (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal := by
  obtain ⟨participant, hparticipant⟩ :=
    exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average_of_total
      source hboundary
  refine ⟨participant, ?_⟩
  convert hparticipant using 1
  ring

/-! ## Literal singleton-separated-tail dispatch -/

/-- The zero-`Never` arm, including the literal old-profile boundary update
whose grafted gain is unchanged from the hard timing game. -/
structure QuittingAdjacentDeadlineLosslessOldResponse
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) : Prop where
  zeroNever : source.old source.observer none = 0
  update_eq : quittingAdjacentDeadlineOldBoundaryProfile source tail =
    Function.update (quittingAdjacentDeadlineOldGraft source tail)
      source.observer
      (quittingAdjacentDeadlineOldBoundaryProfile source tail source.observer)
  boundaryGain_eq :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldBoundaryProfile source tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldGraft source tail) source.observer =
      (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain
        (quittingAdjacentDeadlineOldIncludedTiming source) source.observer
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)

/-- The pass arm records its literal update, exact actual payoff identity, and
the reviewed fixed lower bound. -/
structure QuittingAdjacentDeadlinePaidPassResponse
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) : Prop where
  update_eq : quittingAdjacentDeadlineOldPassProfile source tail =
    Function.update (quittingAdjacentDeadlineOldGraft source tail)
      source.observer
      (quittingAdjacentDeadlineOldPassProfile source tail source.observer)
  payoffGain_eq :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldPassProfile source tail) source.observer -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldGraft source tail) source.observer =
      quittingAdjacentDeadlineOldOpponentNeverProduct source *
        (1 - (source.old source.observer none).toReal) *
        quittingTerminalPayoff reward tail source.observer
  payoffGain_ge : (gamma / bound) * gamma / 8 ≤
    quittingTerminalPayoff reward
        (quittingAdjacentDeadlineOldPassProfile source tail) source.observer -
      quittingTerminalPayoff reward
        (quittingAdjacentDeadlineOldGraft source tail) source.observer

/-- The reverse participant arm records the selected player, literal
behavioral update, exact payoff formula, unchanged cap, exact debt transport,
and quantitative payment. -/
structure QuittingAdjacentDeadlinePaidReverseParticipant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) : Prop where
  update_eq : quittingAdjacentDeadlineCensoredGraft source tail =
    Function.update
      (quittingAdjacentDeadlineParticipantGraft source tail participant)
      participant
      (quittingAdjacentDeadlineCensoredGraft source tail participant)
  payoffGain_eq :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant =
      (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct source participant *
        (quittingTerminalPayoff reward tail participant -
          reward (quittingSingletonTerminal participant) participant)
  bestResponseValue_eq : quittingContinuationBestResponseValue reward
      (quittingAdjacentDeadlineCensoredGraft source tail) participant =
    quittingContinuationBestResponseValue reward
      (quittingAdjacentDeadlineParticipantGraft source tail participant)
      participant
  semanticDebt_eq_sub_payoffGain :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAdjacentDeadlineCensoredGraft source tail)) participant =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant))
          participant -
        (quittingTerminalPayoff reward
            (quittingAdjacentDeadlineCensoredGraft source tail) participant -
          quittingTerminalPayoff reward
            (quittingAdjacentDeadlineParticipantGraft source tail participant)
            participant)
  payoffGain_ge :
    3 * delta * (gamma / bound) ^ 2 /
          (64 * (Fintype.card ι : ℝ)) *
        (7 / 8 : ℝ) ^ (Fintype.card ι - 2) ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant

/-- Supplied singleton-separated actual tails produce the four reviewed
literal outputs.  The last arm is returned as an unresolved macroscopic
timing-law displacement, not as an operational or equilibrium conclusion. -/
theorem quittingAdjacentDeadline_singletonSeparatedTail_dispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    QuittingAdjacentDeadlineLosslessOldResponse source tail ∨
      QuittingAdjacentDeadlinePaidPassResponse source tail ∨
      (∃ participant, QuittingAdjacentDeadlinePaidReverseParticipant
        (delta := delta) source tail participant) ∨
      gamma / bound / 8 ≤ source.censoredErrorMass := by
  by_cases hzero : source.old source.observer none = 0
  · left
    refine ⟨hzero,
      quittingAdjacentDeadlineOldBoundaryProfile_eq_update source tail, ?_⟩
    exact finiteDeadline_zeroNever_boundaryGain_graft_eq source tail hzero
      (quittingAdjacentDeadlineOldIncludedTiming source) rfl
  · right
    by_cases hpass : gamma / bound / 8 ≤
        1 - (source.old source.observer none).toReal
    · left
      refine ⟨quittingAdjacentDeadlineOldPassProfile_eq_update source tail,
        finiteDeadlineOldPassProfile_sub_oldGraft_eq source tail hzero, ?_⟩
      have hlower := finiteDeadlineOldPassProfile_payoffGain_ge
        source tail hdelta (htail source.observer) hzero
      calc
        (gamma / bound) * gamma / 8 =
            (gamma / bound / 8) * gamma := by ring
        _ ≤ (1 - (source.old source.observer none).toReal) * gamma :=
          mul_le_mul_of_nonneg_right hpass hgamma.le
        _ ≤ _ := hlower
    · right
      by_cases herror : gamma / bound / 8 ≤ source.censoredErrorMass
      · exact Or.inr herror
      · left
        have hsplit := source.censoredError_or_boundaryParticipation hbound
        have hscale : gamma / (8 * bound) = gamma / bound / 8 := by
          field_simp
        rw [hscale] at hsplit
        have hboundary : gamma / bound / 8 ≤
            source.boundaryParticipationMass := hsplit.resolve_left herror
        have hboundary' : gamma / (8 * bound) ≤
            source.boundaryParticipationMass := by
          convert hboundary using 1
        obtain ⟨participant, hparticipant⟩ :=
          exists_quittingAdjacentDeadlineBoundaryParticipant_ge_average
            source hboundary'
        have hcylinder :=
          censoredOpponentNeverProduct_ge_of_small_pass_and_error
            source participant hgamma hbound hreward hzero
              (lt_of_not_ge hpass) (lt_of_not_ge herror)
        refine ⟨participant, ⟨
          quittingAdjacentDeadlineCensoredGraft_eq_update_participant
            source tail participant,
          finiteDeadlineCensoredGraft_sub_participantGraft_eq
            source tail participant,
          finiteDeadlineCensoredGraft_bestResponseValue_eq
            source tail participant,
          finiteDeadlineCensoredGraft_semanticDebt_eq_sub_payoffGain
            source tail participant, ?_⟩⟩
        exact finiteDeadlineCensoredGraft_payoffGain_ge
          source tail participant hgamma hbound hdelta (htail participant)
            hparticipant hcylinder

/-- Four-player normalization of the generic reverse-participant floor. -/
theorem QuittingAdjacentDeadlinePaidReverseParticipant.payoffGain_ge_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    {source : QuittingAdjacentDeadlineGapSource reward gamma bound}
    {tail : (quittingGame reward).BehaviorProfile} {participant : Fin 4}
    (edge : QuittingAdjacentDeadlinePaidReverseParticipant
      (delta := delta) source tail participant) :
    147 * delta * (gamma / bound) ^ 2 / 16384 ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant := by
  convert edge.payoffGain_ge using 1
  norm_num only [Fintype.card_fin, Nat.reduceSubDiff]
  ring

/-- Fin4 form of the literal dispatch, with the reverse-edge payment displayed
as `147 · delta · (gamma / bound)² / 16384`. -/
theorem quittingAdjacentDeadline_singletonSeparatedTail_dispatch_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    QuittingAdjacentDeadlineLosslessOldResponse source tail ∨
      QuittingAdjacentDeadlinePaidPassResponse source tail ∨
      (∃ participant,
        QuittingAdjacentDeadlinePaidReverseParticipant
            (delta := delta) source tail participant ∧
          147 * delta * (gamma / bound) ^ 2 / 16384 ≤
            quittingTerminalPayoff reward
                (quittingAdjacentDeadlineCensoredGraft source tail) participant -
              quittingTerminalPayoff reward
                (quittingAdjacentDeadlineParticipantGraft
                  source tail participant) participant) ∨
      gamma / bound / 8 ≤ source.censoredErrorMass := by
  rcases quittingAdjacentDeadline_singletonSeparatedTail_dispatch
      source tail hgamma hbound hdelta hreward htail with
    hlossless | hpass | hreverse | herror
  · exact Or.inl hlossless
  · exact Or.inr (Or.inl hpass)
  · obtain ⟨participant, edge⟩ := hreverse
    exact Or.inr <| Or.inr <| Or.inl
      ⟨participant, edge, edge.payoffGain_ge_finFour⟩
  · exact Or.inr <| Or.inr <| Or.inr herror

end GameTheory
