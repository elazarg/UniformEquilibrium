import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtPairedSourceRegeneration
import Research.Quitting.FinFourProducerAtlas.SupportContractedRenewal

/-!
# Full-debt entry into a support-contracted renewal trace

The literal copied-prefix edge runs from the fixed interior chord to the
minimum target.  The original producer is retained only as the hard-residual
donor.  Renewal starts from the regenerated target producer's own chronology,
not from the separately retained paired chronology.
-/

noncomputable section

namespace GameTheory

/-- One literal copied-prefix chord-to-target edge whose target support is a
strict subset of the fixed interior chord support. -/
structure FinFourFullDebtChordToSupportContractedTargetEdge
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification)
    (regeneration : FinFourFullDebtPairedSourceChronologyRegeneration data)
    (targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)) where
  targetPoint_eq : targetPoint = base.targetPoint
  rank : ℕ
  edge : FinFourPairedSameResidualSourceChronologyRegeneration.OriginEdge
    regeneration.regeneration rank
  targetSupport_ssubset_chordSupport :
    quittingPositiveDebtSupport targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1

namespace FinFourFullDebtPairedSourceChronologyRegeneration

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}
  {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification : FinFourFullDebtFixedWeightChordCompactification
    base minimumTarget weight hweight0 hweight1}
  {data : FinFourFullDebtCommonPrefixResponse compactification}

/-- The literal copied-prefix response at rank zero is a one-use edge into
the strict-support target. -/
def chordToSupportContractedTargetEdge
    (regeneration : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    FinFourFullDebtChordToSupportContractedTargetEdge
      data regeneration base.targetPoint where
  targetPoint_eq := rfl
  rank := 0
  edge := regeneration.originEdge 0
  targetSupport_ssubset_chordSupport :=
    compactification.targetSupport_ssubset_chordSupport

/-- Forget the full-debt-specific construction into the generic renewal
input.  The original producer contributes only its hard residual; the
regenerated target supplies the chronology used by the renewable trace. -/
def toSupportContractedRenewalInput
    (regeneration : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    FinFourSupportContractedRenewalInput source base.targetPoint
      (fun targetPoint => Nonempty
        (FinFourFullDebtChordToSupportContractedTargetEdge
          data regeneration targetPoint)) where
  incoming := ⟨regeneration.chordToSupportContractedTargetEdge⟩
  target := regeneration.producer
  target_point_eq := regeneration.producer_point_eq
  target_residual_eq_origin := regeneration.producer_residual_eq
  targetSupport_card_le_three := regeneration.targetSupport_card_le_three

/-- The regenerated target begins a renewable trace with at most two further
strict-support descents, while retaining the one-use chord edge separately. -/
theorem nonempty_supportContractedRenewalResult
    (regeneration : FinFourFullDebtPairedSourceChronologyRegeneration data) :
    Nonempty (FinFourSupportContractedRenewalResult
      regeneration.toSupportContractedRenewalInput) :=
  nonempty_finFourSupportContractedRenewalResult
    regeneration.toSupportContractedRenewalInput

end FinFourFullDebtPairedSourceChronologyRegeneration

/-- Complete branch-local node-6-to-renewal attachment. -/
structure FinFourFullDebtSupportContractedRenewal
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification) where
  regeneration : FinFourFullDebtPairedSourceChronologyRegeneration data
  renewal : FinFourSupportContractedRenewalResult
    regeneration.toSupportContractedRenewalInput

/-- A supplied full-debt copied-prefix family reaches the existing renewable
trace without a uniform marked-stage floor. -/
theorem nonempty_finFourFullDebtSupportContractedRenewal
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {base : FinFourFullDebtCapBandTargetCompactification source M}
    {minimumTarget : FinFourFullDebtCapBandMinimumTarget base}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourFullDebtFixedWeightChordCompactification
      base minimumTarget weight hweight0 hweight1}
    (data : FinFourFullDebtCommonPrefixResponse compactification) :
    Nonempty (FinFourFullDebtSupportContractedRenewal data) := by
  obtain ⟨regeneration⟩ :=
    nonempty_finFourFullDebtPairedSourceChronologyRegeneration data
  obtain ⟨renewal⟩ := regeneration.nonempty_supportContractedRenewalResult
  exact ⟨⟨regeneration, renewal⟩⟩

end GameTheory
